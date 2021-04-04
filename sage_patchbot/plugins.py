"""
A plugin is any callable.

It is called after the ticket has been successfully applied and built,
but before tests are run. It should print out any analysis to stdout,
raising an exception if anything went wrong.  Alternatively, it may return
a PluginResult indicating success or failure, along with other data.

The parameters are as follows:

- ticket -- a dictionary of all the ticket information
- sage_binary -- the path to $SAGE_ROOT/sage
- baseline -- if a PluginResult was returned with a baseline for ticket 0,
  it will be returned here for comparison

It is recommended that a plugin ignore extra keywords to be
compatible with future options.
"""
import math
import re
import io
import os
import sys
import subprocess
import time
import json

from .trac import do_or_die
from .util import describe_branch

from pyflakes.api import checkPath, isPythonFile
from pyflakes.reporter import Reporter
from pycodestyle import StyleGuide


# hardcoded list of plugins
plugins_available = [
    "commit_messages",
    "coverage",
    "non_ascii",
    "deprecation_number",
    "doctest_continuation",
    "foreign_latex",
    "python3_pyx",
    "python3",
    "pyflakes",
    "pycodestyle",
    "blocks",
    "triple_colon",
    "trac_links",
    "trailing_whitespace",
    "startup_time",
    "startup_modules",
    "docbuild",
    "docbuild_pdf",
    "git_rev_list"]


class PluginResult(object):
    """
    Container class for the results of plugins
    """
    Passed = "Passed"
    Failed = "Failed"

    def __init__(self, status, data=None, baseline=None):
        assert status in (self.Passed, self.Failed)
        self.status = status
        self.data = data
        self.baseline = baseline or data


# --- several general plugins ---


def git_rev_list(ticket, **kwds):
    """
    some comparison of git branches
    """
    if str(ticket['id']) != '0':
        base_only = int(subprocess.check_output(["git", "rev-list", "--count", "patchbot/ticket_upstream..patchbot/base"]))
        ticket_only = int(subprocess.check_output(["git", "rev-list", "--count", "patchbot/base..patchbot/ticket_upstream"]))
        print("only in ticket ({})".format(ticket_only))
        print("only in base ({})".format(base_only))
        base = describe_branch('patchbot/ticket_upstream', tag_only=True)
        do_or_die("git diff --stat %s..patchbot/ticket_upstream" % base)
        do_or_die("git log --oneline %s..patchbot/ticket_upstream" % base)
        do_or_die("git log %s..patchbot/ticket_upstream" % base)


def coverage(ticket, sage_binary, baseline=None, **kwds):
    """
    Try to check that coverage did increase.

    .. TODO::

        This does not check that tests were added to existing doctests for
        new functionality.
    """
    all = subprocess.check_output([sage_binary, '-coverageall'],
                                  universal_newlines=True)
    current = {}
    total_funcs = 0
    total_docs = 0
    status = "Passed"

    def format(docs, funcs, prec=None):
        if funcs == 0:
            return "N/A"
        else:
            percent = 100.0 * docs / funcs
            if prec is None:
                percent = int(percent)
            else:
                percent = ("%%0.%sf" % prec) % percent
            return "{} / {} = {}%".format(docs, funcs, percent)

    for line in all.split('\n'):
        m = re.match(r"(.*): .*\((\d+) of (\d+)\)", line)
        if m:
            module, docs, funcs = m.groups()
            docs = int(docs)
            funcs = int(funcs)
            current[module] = docs, funcs
            total_docs += docs
            total_funcs += funcs
            if baseline:
                old_docs, old_funcs = baseline.get(module, (0, 0))
                if old_funcs == 0:
                    if funcs != docs:
                        msg = "Missing doctests in {}: {}"
                        print(msg.format(module, format(docs, funcs)))
                        status = "Failed"
                    else:
                        msg = "Full doctests in {}: {}"
                        print(msg.format(module, format(docs, funcs)))
                elif funcs - docs > old_funcs - old_docs:
                    msg = "Decreased doctests in {}: from {} to {}"
                    print(msg.format(module, format(old_docs, old_funcs),
                                     format(docs, funcs)))
                    status = "Failed"
                elif funcs - docs < old_funcs - old_docs:
                    msg = "Increased doctests in {}: from {} to {}"
                    print(msg.format(module, format(old_docs, old_funcs),
                                     format(docs, funcs)))

    current[None] = total_docs, total_funcs
    if baseline:
        if baseline[None] == current[None]:
            print("Coverage remained unchanged.")
        else:
            msg = "Coverage went from {} to {}"
            print(msg.format(format(*baseline[None], prec=3),
                             format(*current[None], prec=3)))
        current_set = set((key, current[key])
                          for key in current if key is not None)
        baseline_set = set((key, baseline[key])
                           for key in baseline if key is not None)
        data = sorted(current_set - baseline_set)
    else:
        data = None

    if baseline:
        print("=" * 20)
    print(all)

    return PluginResult(status, baseline=current, data=data)


def docbuild(ticket, make, **kwds):
    """
    Build the html documentation.
    """
    do_or_die('{} doc'.format(make))


def docbuild_pdf(ticket, make, **kwds):
    """
    Build the PDF documentation.

    This requires a very complete LaTeX installation.

    It may report false failures if some LaTeX packages are missing.

    STILL EXPERIMENTAL! needs to be tested.
    """
    do_or_die('{} doc-pdf'.format(make))


# --- pattern-exclusion helper functions ---


def exclude_new_file_by_file(ticket, regex, file_condition, msg, **kwds):
    """
    Search in new code for patterns that should be avoided.

    The pattern in given by a regular expression ``regex``. See the next
    functions `trailing_whitespace`, `non_ascii`, etc for several such
    patterns.

    INPUT:

    ``regex`` is either one regular expression or a list of regular exp.

    Proceeding file by file, it will only look inside the files that
    pass the chosen file condition.

    .. SEEALSO:: `exclude_new`

    This is used to check for unicode declaration.
    """
    if not isinstance(regex, (list, tuple)):
        regex = [regex]

    changed_files = list(subprocess.Popen(['git', 'diff', '--name-only', 'patchbot/base..patchbot/ticket_merged'], stdout=subprocess.PIPE).stdout)
    changed_files = [f.decode('utf8').strip("\n") for f in changed_files]

    bad_lines = 0
    for a_file in changed_files:
        try:
            if file_condition(a_file):
                gitdiff = list(subprocess.Popen(['git', 'diff', 'patchbot/base..patchbot/ticket_merged', a_file], stdout=subprocess.PIPE).stdout)
                gitdiff = [f.decode('utf8') for f in gitdiff]
                for r in regex:
                    bad_lines += exclude_new_in_diff(gitdiff, r)
        except IOError:  # file has been deleted or moved
            pass

    full_msg = "{} inserted on {} non-empty lines"
    full_msg = full_msg.format(msg, bad_lines)
    print(full_msg)
    if bad_lines:
        raise ValueError(full_msg)


def pyflakes(ticket, **kwds):
    """
    run pyflakes on the modified .py files

    we do not check the files names "all.py" and "__init__.py" that
    usually just contain unused import lines, always triggering non-pertinent
    pyflakes warnings

    same thing for files named "*catalog*.py"
    """
    changed_files = list(subprocess.Popen(['git', 'diff', '--name-only', 'patchbot/base..patchbot/ticket_merged'], stdout=subprocess.PIPE).stdout)
    changed_files = [f.decode('utf8').strip("\n") for f in changed_files]

    errors = 0
    msg_list = []
    msg_here = '{} pyflakes errors in file {}'
    for a_file in changed_files:
        if os.path.exists(a_file) and isPythonFile(a_file):
            filename = os.path.split(a_file)[1]
            if not (filename == "all.py" or filename == "__init__.py" or
                    "catalog" in filename):
                error_stream = io.StringIO()
                report = Reporter(error_stream, sys.stderr)
                errors_here = checkPath(a_file, report)  # run pyflakes
                if errors_here:
                    # here we try to care for lazy imported names
                    lazys = list(find_lazy_imports(a_file))  # ok
                    if lazys:
                        for err in error_stream.getvalue().splitlines():
                            if any(x in err.split(' ')[-1] for x in lazys):
                                errors_here -= 1
                            else:
                                print(err)
                    else:
                        print(error_stream.getvalue())
                error_stream.close()
                if errors_here:
                    errors += errors_here
                    msg_list.append(msg_here.format(errors_here, a_file))

    full_msg = "found {} pyflakes errors in the modified files"
    full_msg = full_msg.format(errors)
    print(full_msg)
    if errors:
        raise ValueError(full_msg)


def process_one_lazy_import(txt):
    what = txt[12:-1]
    what = ','.join(term for term in what.split(',') if '=' not in term)
    what = u'[' + what + u']'
    what = json.loads(what.replace(u"'", u'"'))

    if len(what) == 2:
        names = what[1]
    elif len(what) == 3:
        names = what[2]

    if isinstance(names, list):
        yield from names
    else:
        yield names


def find_lazy_imports(a_file):
    """
    Return an iterator over the names of functions or classes
    that are lazily imported inside the given file ``a_file``.

    This works, but restricted to ``'lazy_import'`` that fits
    on at most 6 lines.
    """
    lazys = list(subprocess.Popen(['git', 'grep', '-h', '-A6',
                                   'lazy_import', a_file],
                                  stdout=subprocess.PIPE).stdout)
    lazys = [f.decode('utf8').strip("\n").strip() for f in lazys]
    stored_lines = []
    for line in lazys:
        # trying to handle multi-line lazy imports
        if line.startswith('lazy_import'):
            start_line = True
            stored_lines = [line]
        else:
            start_line = False
        if stored_lines:
            if not start_line:
                stored_lines.append(line)
            if line.endswith(')'):
                yield from process_one_lazy_import(''.join(stored_lines))
                stored_lines = []


def pycodestyle(ticket, **kwds):
    """
    run ``pycodestyle`` on the modified .py files

    see http://pycodestyle.pycqa.org/en/latest/intro.html

    we do not check the files names "all.py" and "__init__.py" that
    usually just contain unused import lines

    same thing for files named "*catalog*.py"
    """
    changed_files = list(subprocess.Popen(['git', 'diff', '--name-only', 'patchbot/base..patchbot/ticket_merged'], stdout=subprocess.PIPE).stdout)
    changed_files = [f.decode('utf8').strip("\n") for f in changed_files]

    style = StyleGuide()
    errors = 0
    for a_file in changed_files:
        if os.path.exists(a_file) and os.path.splitext(a_file)[1] == '.py':
            filename = os.path.split(a_file)[1]
            if not (filename == "all.py" or filename == "__init__.py" or
                    "catalog" in filename):
                rep = style.check_files([a_file])
                errors = rep.file_errors
                # this should print the errors out, with files and lines

    full_msg = "found {} invalid escape sequences in the modified files"
    full_msg = full_msg.format(errors)
    print(full_msg)
    if errors:
        raise ValueError(full_msg)


def exclude_new(ticket, regex, msg, **kwds):
    """
    Search in new code for patterns that should be avoided.

    The pattern in given by a regular expression.

    ``regex`` is either one regular expression or a list of regular exp.

    See the next functions `trailing_whitespace`, `non_ascii`, etc
    for several such patterns.

    Proceeding just once for all the changed files.

    .. SEEALSO:: `exclude_new_file_by_file`
    """
    if not isinstance(regex, (list, tuple)):
        regex = [regex]

    gitdiff = subprocess.Popen(['git', 'diff',
                                'patchbot/base..patchbot/ticket_merged'],
                               stdout=subprocess.PIPE,
                               universal_newlines=True).stdout

    if len(regex) > 1:
        gitdiff = list(gitdiff)

    bad_lines = 0
    for r in regex:
        bad_lines += exclude_new_in_diff(gitdiff, r)
    full_msg = "{} inserted on {} non-empty lines"
    full_msg = full_msg.format(msg, bad_lines)
    print(full_msg)
    if bad_lines:
        raise ValueError(full_msg)


def exclude_new_in_diff(gitdiff, regex):
    r"""
    Search in the given diff for patterns that should be avoided.

    The pattern in given by a regular expression, for example r':::$'

    INPUT: ``regex`` is one regular expression

    OUTPUT: the number of lines matching the given regular exp.

    See the next functions `trailing_whitespace`, `non_ascii`, etc
    for several such patterns.
    """
    # looking for the regular expression 'regex' only in the added lines
    if regex[0] == '^':
        bad = re.compile(r'\+' + regex[1:])
    else:
        bad = re.compile(r'\+.*' + regex)

    bad_lines = 0
    for line in gitdiff:
        line = line.strip()
        if line[:3] == '---' or line == '+':
            pass
        elif line[:3] == '+++':
            file_line = 'inside file: ' + line[3:]
            file_line_printed = False
        elif line[:3] == '@@ ':
            pos_line = line
            pos_line_printed = False
        elif bad.match(line):
            if not file_line_printed:
                print(file_line)
                file_line_printed = True
            if not pos_line_printed:
                print(pos_line)
                pos_line_printed = True
            print(line)
            bad_lines += 1
    return bad_lines


# --- plugins with file-by-file pattern exclusion ---


def check_unicode_declaration(file):
    """
    Check if the encoding is declared as utf-8 as in PEP0263.

    Return True if there is a correct utf-8 declaration.

    This is one example of the file condition that can be used
    in exclude_new_file_by_file.

    This is useful in the `non_ascii` plugin.
    """
    regex = re.compile(r"coding[:=]\s*([-\w.]+)")
    with open(file) as f:
        L0 = regex.split(f.readline())
        L1 = regex.split(f.readline())
    if len(L0) >= 2 and L0[1] == 'utf-8':
        return True
    if len(L1) >= 2 and L1[1] == 'utf-8':
        return True
    return False


def non_ascii(ticket, **kwds):
    """
    Look for the presence of non-ascii characters in python and cython files.

    This should be done file by file to check for unicode declaration.
    """

    def not_declared(a_file):
        return (not(check_unicode_declaration(a_file)) and
                a_file.split(os.path.extsep)[-1] == 'py')
    exclude_new_file_by_file(ticket, regex=r'[^\x00-\x7F]',
                             file_condition=not_declared,
                             msg="Non-ascii characters", **kwds)


def python3_py(ticket, **kwds):
    """
    Look for some patterns in a python or rst file.

    0) xrange

    1) .iterkeys, .itervalues, .iteritems

    2) basestring

    3) __nonzero__

    These are allowed in cython files.
    """
    def not_cython(a_file):
        return a_file.split(os.path.extsep)[-1] in ['py', 'rst']
    regexps = [r'xrange\(',
               r'\.iterkeys\(', r'\.itervalues\(', r'\.iteritems\(',
               r'basestring',
               r'__nonzero__\(']
    exclude_new_file_by_file(ticket, regex=regexps,
                             file_condition=not_cython,
                             msg="Python3 incompatible code", **kwds)


def python3_pyx(ticket, **kwds):
    """
    Look for some patterns in a cython file

    0) "import six" and "from six import"

    These are allowed in python files.
    """
    def is_cython(a_file):
        return a_file.split(os.path.extsep)[-1] == 'pyx'
    regexps = [r'import six',
               r'from six import']
    exclude_new_file_by_file(ticket, regex=regexps,
                             file_condition=is_cython,
                             msg="Python3 incompatible code", **kwds)

# --- simple pattern-exclusion plugins ---


def python3(ticket, **kwds):
    r"""
    Check that some python3 incompatible code does not appear

    2) ifilter, imap, izip

    3) raise statements

    4) cmp

    6) <>

    7) <type '[a-z]*'> (no longer needed)

    8) next

    9) __metaclass__

    10) except Exception, var

    11) apply

    12) sagenb

    13) six is no longer allowed
    """
    def python_or_cython_or_rst(a_file):
        return a_file.split(os.path.extsep)[-1] in ['py', 'pyx', 'rst']

    regexps = (r'import.*ifilter', r'import.*imap', r'import.*izip',
               r'^\s*raise\s*[A-Za-z]*Error\s*,'
               r'[\s,\(]cmp\s*=', r'[^_a-z]cmp\(',
               r'<>',
               r'\.next\(\)',
               r'__metaclass__',
               r'except\s*[A-Za-z]\s*,',
               r'[^_a-z]apply\(',
               r'sagenb',
               r'import six', r'from six import')
    exclude_new_file_by_file(ticket, regex=regexps,
                             file_condition=python_or_cython_or_rst,
                             msg="Python3 incompatible code", **kwds)


def foreign_latex(ticket, **kwds):
    r"""
    Check that some bad latex code does not appear.

    including \over, \choose, etc
    """
    regexps = [r'\\choose', r'\\over[^l]', r'\\atop', r'\\above',
               r'\\overwithdelims', r'\\atopwithdelims',
               r'\\abovewithdelims']
    exclude_new(ticket, regex=regexps,
                msg="Foreign commands in LaTeX", **kwds)


def deprecation_number(ticket, **kwds):
    """
    in case of deprecation, check that the ticket number is correct
    """
    gitdiff = subprocess.Popen(['git', 'diff',
                                'patchbot/base..patchbot/ticket_merged'],
                               stdout=subprocess.PIPE,
                               universal_newlines=True).stdout
    rx = re.compile(r"\((?P<tn>[0-9]*),")
    ticket_id = ticket['id']
    bad_lines = 0
    for line in gitdiff:
        line = line.strip()
        if line.startswith('-'):
            continue
        if "deprecation(" in line or "deprecated_function_alias(" in line:
            if ticket_id != int(rx.search(line).group('tn')):
                print(line)
                bad_lines += 1

    msg = "Wrong deprecation number"
    full_msg = "{} inserted on {} non-empty lines"
    full_msg = full_msg.format(msg, bad_lines)
    print(full_msg)
    if bad_lines:
        raise ValueError(full_msg)


def doctest_continuation(ticket, **kwds):
    """
    Check that doctest continuation use syntax `....:`.
    """
    exclude_new(ticket, regex=r'^\s*\.\.\.\s',
                msg="Old-style doctest continuation", **kwds)


def blocks(ticket, **kwds):
    """
    some check for the blocks

    1) correct syntax is .. SEEALSO::

    2) TESTS and EXAMPLES should be plural, NOTE singular

    3) no :: after INPUT and OUTPUT blocks

    4) no :: after REFERENCE blocks

    5) no " :" at the end of lines

    6) no "Returns" at the start of lines
    """
    regexps = [r'\.\.SEE', r'SEE ALSO', r'SEEALSO:($|[^:])',
               r'^\s*TEST:', r'^\s*EXAMPLE:', r'^\s*NOTES:',
               r'^\s*[A-Z]*PUT::',
               r'^\s*REFERENCES?::', r'\s:$', r'^\s*Returns']
    exclude_new(ticket, regex=regexps,
                msg="wrong syntax for blocks (INPUT, OUTPUT, EXAMPLES, NOTE, etc)",
                **kwds)


def oldstyle_print(ticket, **kwds):
    """
    Check that print is using python 3 syntax.
    """
    badprint = r'[^a-z]print((\s\s*[^\(])|(\s*$))'
    rex1 = r'^\s*(()|(.*[:;]\s*))' + badprint  # in a code line
    rex2 = r'^\s*sage:.*' + badprint            # in doc after sage:
    rex3 = r'^\s*\.\.\.\.:.*' + badprint        # in doc after ....:
    rex4 = r'^\s*\.\.\..*' + badprint           # in doc after ...
    exclude_new(ticket, regex=(rex1, rex2, rex3, rex4),
                msg="python2-only print syntax", **kwds)


def trac_links(ticket, **kwds):
    """
    Look for the presence of badly formatted trac roles ``:trac:``,
    missing the initial colon.
    """
    exclude_new(ticket, regex=r'[^:]trac:`[0-9]', msg="Bad trac link", **kwds)


def trailing_whitespace(ticket, **kwds):
    """
    Look for the presence of trailing whitespaces.
    """
    exclude_new(ticket, regex=r'\s+$', msg="Trailing whitespace", **kwds)


def triple_colon(ticket, **kwds):
    """
    Look for the presence of triple colons `:::` or `: ::`.
    """
    exclude_new(ticket, regex=r':\s*::', msg="Triple colon (:::)", **kwds)


# --- not pattern-related plugins ---


def commit_messages(ticket, patches, **kwds):
    """
    Check for the existence of a commit message for every commit.

    This is now for git only.
    """
    for patch_path in patches:
        patch = os.path.basename(patch_path)
        print("Looking at {}".format(patch))
        header = []
        for line in open(patch_path):
            if line.startswith('diff '):
                break
            header.append(line)
        else:
            print(''.join(header[:10]))
            raise ValueError("Not a valid patch file: " + patch)
        print(''.join(header))
    print("All patches good.")


def startup_modules(ticket, sage_binary, baseline=None, **kwds):
    """
    Count modules imported at startup.

    And compares to stored data.
    """
    # Sometimes the first run does something different...
    do_or_die(sage_binary + " -c ''")
    # Print out all the modules imported at startup.
    # old way:
    # list_command = r"print '\n'.join(sorted(u for u in sys.modules.keys()))"
    # new way:
    list_command = r"print('\n'.join(sorted(u for u, v in sys.modules.items() if v)))"
    modules = subprocess.check_output([sage_binary,
                                       "-c", list_command],
                                      universal_newlines=True)
    modules = modules.split('\n')

    print("Total count: {}".format(len(modules)))
    if baseline is None:
        status = PluginResult.Passed
        data = {}
    else:
        module_set = set(modules)
        baseline_set = set(baseline)
        new = sorted(module_set - baseline_set)
        removed = sorted(baseline_set - module_set)
        if new:
            status = PluginResult.Failed
            print("New:")
            print("\n    ".join(new))
        else:
            status = PluginResult.Passed
        if removed:
            print("Removed:")
            print("\n    ".join(removed))
        data = {'new': new, 'removed': removed}

    if baseline:
        print("=" * 20)
    print('\n'.join(modules))
    return PluginResult(status, baseline=modules, data=data)


def startup_time(ticket, make, sage_binary, loops=5, total_samples=50,
                 dry_run=False, **kwds):
    """
    Try to decide if the startup time is getting worse.
    """
    if dry_run:
        loops //= 2
        total_samples //= 5

    print("{} samples in {} loops".format(total_samples, loops))
    ticket_id = ticket['id']
    choose_base = "git checkout patchbot/base; {} build > /dev/null".format(make)
    choose_ticket = "git checkout patchbot/ticket_merged; {} build  > /dev/null".format(make)

    def startup_times(samples):
        do_or_die(sage_binary + " -c ''")
        all_times = []
        for k in range(samples):
            start = time.time()
            do_or_die(sage_binary + " -c ''")
            all_times.append(time.time() - start)
        return all_times

    try:
        main_timings = []
        do_or_die(choose_base)
        for k in range(loops):
            main_timings.extend(startup_times(total_samples //
                                              loops + 2 * k - loops + 1))
        ticket_timings = []
        do_or_die(choose_ticket)
        for k in range(loops):
            ticket_timings.extend(startup_times(total_samples //
                                                loops + 2 * k - loops + 1))

        print("main_timings = {}".format(main_timings))
        print("ticket_timings = {}".format(ticket_timings))

        n1 = len(main_timings)
        p1 = mean(main_timings)
        s1 = std_dev(main_timings)

        n2 = len(ticket_timings)
        p2 = mean(ticket_timings)
        s2 = std_dev(ticket_timings)

        base = p1
        diff = abs(p2 - p1)
        increased = p1 < p2
        inc_or_dec = ['decreased', 'increased']

        print("Main:   %0.5g sec (%s samples, std_dev=%0.3g)" % (p1, n1, s1))
        print("Ticket: %0.5g sec (%s samples, std_dev=%0.3g)" % (p2, n2, s2))
        print("Average %s of %0.2g secs or %0.2g%%." %
              (inc_or_dec[increased][:-1], diff, 100 * diff / base))
        print("Using the Mann-Whitney U test to determine significance.")

        mann_whitney_U(main_timings, ticket_timings)
        confidence_intervals = []
        for lower_bound in (1, .5, .25, .1, .05, .025, .01, 0.005, .0025, .001):
            z = mann_whitney_U(main_timings, ticket_timings,
                               offset=base * lower_bound)
            confidence = CDF(z)
            if confidence > 0.25:
                confidence_intervals.append((confidence, lower_bound))
            if len(confidence_intervals) >= 5:
                break

        status = PluginResult.Passed
        if not confidence_intervals:
            print("No statistically significant difference.")
        else:
            print("May have caused a slowdown.")
        for confidence, lower_bound, in confidence_intervals:
            if increased and confidence >= .95 and lower_bound >= .001:
                status = PluginResult.Failed
            confidence = 1 - float(("%0.1g" if confidence > .9
                                    else "%0.2g") % (1 - confidence))
            print("With %g%% confidence, startup time %s by at least %0.2g%%" % (
                100 * confidence, inc_or_dec[increased], 100 * lower_bound))

        if not increased:
            confidence_intervals = [(x, -y) for x, y in confidence_intervals]
        data = dict(confidence_intervals=confidence_intervals,
                    main_timings=main_timings, ticket_timings=ticket_timings,
                    loops=loops, total_samples=total_samples)
        if str(ticket_id) == '0':
            # Never fail the initial startup.
            status = PluginResult.Passed
        return PluginResult(status, data=data)

    finally:
        do_or_die(choose_ticket)


# Some statistical utility functions.


def mann_whitney_U(a, b, offset=0):
    all_points = [(x, 0) for x in a] + [(x - offset, 1) for x in b]
    all_points.sort()
    R = [0, 0]
    for ix, (x, k) in enumerate(all_points):
        R[k] += ix + 1
    n0 = len(a)
    n1 = len(b)
    U = [R[0] - n1 * (n0 + 1) / 2, R[1] - n1 * (n1 + 1) / 2]
    mU = n0 * n1 / 2
    sU = math.sqrt(n0 * n1 * (n0 + n1 + 1) / 12.0)
    return (U[1] - mU) / sU


sqrt_pi_over_8 = math.sqrt(math.pi / 8)


def mean(a):
    return 1.0 * sum(a) / len(a)


def std_dev(a):
    xbar = mean(a)
    return math.sqrt(sum((x - xbar) ** 2 for x in a) / (len(a) - 1.0))

# Aludaat, K.M. and Alodat, M.T. (2008). A note on approximating the
# normal distribution function. Applied Mathematical Sciences, Vol 2,
# no 9, pgs 425-429.


def CDF(x):
    """
    The cumulative distribution function to within 0.00197323.
    """
    if x < 0:
        return 1 - CDF(-x)
    return 0.5 + 0.5 * math.sqrt(1 - math.exp(-sqrt_pi_over_8 * x * x))


if __name__ == '__main__':
    plugin = globals()[sys.argv[1]]
    kwds = {}
    for arg in sys.argv[2:]:
        m = re.match("--([_a-zA-Z0-9]+)=(([_a-zA-Z]*).*)", arg)
        if not m:
            print("{} must be of the form --kwd=expr".format(arg))
            sys.exit(1)
        key = m.group(1)
        if m.group(2) == m.group(3):
            value = m.group(2)
        else:
            value = eval(m.group(2))
        kwds[key] = value
    plugin(**kwds)
