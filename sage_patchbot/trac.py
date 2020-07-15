# global python imports
import re
import hashlib
import os
import sys
import shutil
import tempfile
import traceback
import time
import subprocess
import pprint

# Python 3.3+
from xmlrpc.client import ServerProxy
from .digest_transport import DigestTransport
from urllib import parse as url_parse
from urllib.request import urlopen

# imports from patchbot sources
from .cached_property import cached_property
from .util import (do_or_die, now_str, describe_branch,
                   temp_build_suffix, ensure_free_space,
                   ConfigException, SkipTicket)
from .trac_ticket import TracTicket


TRAC_URL = "https://trac.sagemath.org/sage_trac"
TRAC_REPO = "git://trac.sagemath.org/sage.git"


def digest(s):
    """
    Compute a cryptographic hash of the string s.
    """
    return hashlib.md5(s).hexdigest()


def get_url(url):
    """
    Return the contents of url as a string.
    """
    url = url.replace(' ', '%20')
    with urlopen(url, timeout=15) as handle:
        data = handle.read()
    return data.decode('utf8')


def is_closed_on_trac(ticket_id):
    """
    Make damn sure that the ticket is closed on trac.
    """
    if not ticket_id:
        return False
    trac_server = TracServer(Config())
    trac_info = trac_server.load(ticket_id)
    return trac_info.status == 'closed'


def get_ticket_info_from_trac_server(ticket_id):
    """
    Get the info on a ticket contained in its trac page.
    """
    ticket_id = int(ticket_id)

    # special case for ticket 0
    if ticket_id == 0:
        return {
            'id': ticket_id,
            'title': 'base',
            'page_hash': '0',
            'status': 'base',
            'priority': 'base',
            'component': 'base',
            'depends_on': [],
            'spkgs': [],
            'authors': [],
            'participants': []}

    # link to the trac server
    trac_server = TracServer(Config())
    trac_info = trac_server.load(ticket_id)

    # this part is about finding the authors and it needs work !
    authors = set()
    git_commit_of_branch = git_commit(trac_info.branch)
    if trac_info.branch:
        branch = trac_info.branch
        if branch.startswith('u/'):
            authors.add((branch.split('/')[1]).strip())
    authors = list(authors)

    authors_fullnames = set()
    for auth in trac_info.author.split(','):
        author = auth.strip()
        if author:
            authors_fullnames.add(author)
    authors_fullnames = list(authors_fullnames)

    # needed to extract the participants
    rss = get_url("{}/ticket/{}?format=rss".format(TRAC_URL, ticket_id))

    return {'id': ticket_id,
            'title': trac_info.title,
            'status': trac_info.status,
            'resolution': trac_info.resolution,
            'milestone': trac_info.milestone,
            'priority': trac_info.priority,
            'component': trac_info.component,
            'depends_on': extract_depends_on(trac_info.dependencies),
            'spkgs': bool('packages' in trac_info.component),
            'authors': authors,
            'authors_fullnames': authors_fullnames,
            'participants': extract_participants(rss),
            'git_branch': trac_info.branch,
            'git_repo': TRAC_REPO if trac_info.branch.strip() else None,
            'git_commit': git_commit_of_branch,
            'last_activity': now_str(),
            'last_trac_activity': trac_info.mtime_str}


def scrape(ticket_id, force=False, db=None):
    """
    Return available information about given ticket
    from the patchbot database, and update this information if necessary.

    The information is either taken from the patchbot database,
    or obtained from the trac database.

    If the trac-ticket-info has changed since the last update of the
    patchbot-ticket-info, then the patchbot-ticket-info is refreshed.

    If ``force`` is ``True``, it will update the patchbot-ticket-info
    even if the trac-ticket-info has not changed.

    OUTPUT:

    a dictionary

    EXAMPLES::

        sage: scrape(18033)
    """
    ticket_id = int(ticket_id)

    if db is None:
        return get_ticket_info_from_trac_server(ticket_id)

    # special case for ticket 0
    if ticket_id == 0:
        db_info = db.lookup_ticket(ticket_id)
        if db_info is not None:
            return db_info

    # try to get data from the patchbot database
    db_info = db.lookup_ticket(ticket_id)

    # check if this data is fresh enough
    if not force and db_info is not None:
        # when did the trac page was last modified ?
        trac_server = TracServer(Config())
        trac_info = trac_server.load(ticket_id)
        last_trac_activity = trac_info.mtime_str

        known_trac_activity = db_info.get('last_trac_activity',
                                          '1916-01-21 07:03:56')

        if known_trac_activity == last_trac_activity:
            return db_info

    # nothing in the database or need to refresh
    # now fetch the info from trac server
    data = get_ticket_info_from_trac_server(ticket_id)
    db.save_ticket(data)
    return db.lookup_ticket(ticket_id)


def git_commit(branch):
    """
    Retrieve the hash of the commit.

    EXAMPLES::

        sage: git_commit('develop')
        '408796407339cf8ba46d3c5ab9365bdb0f1e456f'
    """
    if branch.strip():
        try:
            return subprocess.check_output(['git', 'ls-remote',
                                            TRAC_REPO, branch],
                                           universal_newlines=True).split()[0]
        except Exception:
            return "unknown"


def extract_tag(sgml, tag):
    """
    Find the first occurrence of the tag start (including attributes) and
    return the contents of that tag (really, up until the next end tag
    of that type).

    Crude but fast.
    """
    tag_name = tag[1:-1]
    if ' ' in tag_name:
        tag_name = tag_name[:tag_name.index(' ')]
    end = "</%s>" % tag_name
    start_ix = sgml.find(tag)
    if start_ix == -1:
        return None
    end_ix = sgml.find(end, start_ix)
    if end_ix == -1:
        return None
    return sgml[start_ix + len(tag): end_ix].strip()


def extract_participants(rss):
    """
    Extracts any participants for a ticket from the html page.

    This is done using the rss feed.

    This needs work ! In particular to remove people only in cc if possible!
    """
    all = set()
    for item in rss.split('<item>'):
        who = extract_tag(item, '<dc:creator>')
        if who:
            all.add(who)
    return list(all)


def extract_depends_on(deps_field):
    deps = []
    for dep in re.finditer(r'#(\d+)', deps_field):
        deps.append(int(dep.group(1)))
    version = re.search(r'sage-\d+(\.\d)+(\.\w+)?', deps_field)
    if version:
        deps.insert(0, version.group(0))
    return deps


def inplace_safe():
    """
    Return whether it is safe to test this ticket inplace.

    This must be called after the merge has succeeded.
    """
    # TODO: Are removed files sufficiently cleaned up?
    cmd = ["git", "diff", "--name-only",
           "patchbot/base..patchbot/ticket_merged"]
    for file in subprocess.check_output(cmd,
                                        universal_newlines=True).split('\n'):
        if not file:
            continue
        if (file.startswith("src/sage") or
                file.startswith("src/doc") or
                file.startswith("build/pkgs") or
                file in ("src/setup.py", "src/module_list.py",
                         ".lgtm.yml", "tox.ini", "condarc.yml",
                         "README.md", ".gitignore",
                         "VERSION.txt", "src/bin/sage-banner",
                         "src/bin/sage-version.sh")):
            continue
        else:
            msg = "Unsafe file: {}".format(file)
            print(msg)
            return False
    return True


def pull_from_trac(sage_root, ticket_id, branch=None, force=None,
                   safe_only=False):
    """
    Create four branches from base and ticket.

    If ticket deemed unsafe then clone git repo to temp directory.

    Set some global and environment variables.

    There are four branches at play here:

    - patchbot/base -- the latest release that all tickets are merged into
      for testing
    - patchbot/base_upstream -- temporary staging area for patchbot/base
    - patchbot/ticket_upstream -- pristine clone of the ticket on trac
    - patchbot/ticket_merged -- merge of patchbot/ticket_upstream into
      patchbot/base
    """
    merge_failure = False
    is_safe = False
    temp_dir = None
    try:
        os.chdir(sage_root)
        info = scrape(ticket_id)
        ensure_free_space(sage_root)
        do_or_die("git checkout patchbot/base")
        if ticket_id == 0:
            do_or_die("git branch -f patchbot/ticket_upstream patchbot/base")
            do_or_die("git branch -f patchbot/ticket_merged patchbot/base")
            return
        branch = info['git_branch']
        repo = info['git_repo']
        do_or_die("git fetch %s +%s:patchbot/ticket_upstream" % (repo, branch))
        base = describe_branch('patchbot/ticket_upstream', tag_only=True)
        do_or_die("git rev-list --left-right --count %s..patchbot/ticket_upstream" % base)
        do_or_die("git branch -f patchbot/ticket_merged patchbot/base")
        do_or_die("git checkout patchbot/ticket_merged")
        try:
            do_or_die("git merge -X patience patchbot/ticket_upstream")
        except Exception:
            do_or_die("git merge --abort")
            merge_failure = True
            raise

        is_safe = inplace_safe()
        if not is_safe:
            if safe_only:
                raise SkipTicket("unsafe")
            # create temporary dir
            temp_dir = tempfile.mkdtemp(temp_build_suffix + str(ticket_id))
            ensure_free_space(temp_dir)
            do_or_die("git clone . '{}'".format(temp_dir))
            os.chdir(temp_dir)
            os.symlink(os.path.join(sage_root, "upstream"), "upstream")
            os.environ['SAGE_ROOT'] = temp_dir
            do_or_die("git branch -f patchbot/base remotes/origin/patchbot/base")
            do_or_die("git branch -f patchbot/ticket_upstream remotes/origin/patchbot/ticket_upstream")
            do_or_die("make configure")
            do_or_die("./configure")
    except Exception as exn:
        if not is_safe and not safe_only:
            if temp_dir and os.path.exists(temp_dir):
                # Reset to the original sage_root
                os.chdir(sage_root)
                os.environ['SAGE_ROOT'] = sage_root
                shutil.rmtree(temp_dir)  # delete temporary dir

        if merge_failure or (not is_safe):
            raise
        else:
            raise ConfigException(exn.message)

# ===================

# use XMLRPC to communicate with trac
# taken from git-trac-plugin


class Config(object):

    @property
    def server_hostname(self):
        return 'https://trac.sagemath.org'

    @property
    def server_anonymous_xmlrpc(self):
        return 'xmlrpc'


class TracServer(object):

    def __init__(self, config):
        self.config = config

    @cached_property
    def url_anonymous(self):
        return url_parse.urljoin(self.config.server_hostname,
                                 self.config.server_anonymous_xmlrpc)

    @cached_property
    def anonymous_proxy(self):
        transport = DigestTransport()
        return ServerProxy(self.url_anonymous, transport=transport)

    def __repr__(self):
        return "Trac server at " + self.config.server_hostname

    def load(self, ticket_number):
        ticket_number = int(ticket_number)
        ticket = TracTicket(ticket_number, self.anonymous_proxy)
        return ticket

    def remote_branch(self, ticket_number):
        ticket = self.load(ticket_number)
        branch = ticket.branch
        if branch == '':
            msg = '"Branch:" field is not set on ticket #{}'
            raise ValueError(msg.format(ticket_number))
        return branch


# ===================


if __name__ == '__main__':
    force = apply = False
    for ticket in sys.argv[1:]:
        if ticket == '-f':
            force = True
            continue
        elif ticket == '-a':
            apply = True
            continue
        elif '-' in ticket:
            start, end = ticket.split('-')
            tickets = range(int(start), int(end) + 1)
        else:
            tickets = [int(ticket)]

        for tick in tickets:
            try:
                print(tick)
                pprint.pprint(scrape(tick))
                if apply:
                    pull_from_trac(os.environ['SAGE_ROOT'], tick, force=True)
                time.sleep(1)
            except Exception:
                msg = "Error for {}".format(tick)
                print(msg)
                traceback.print_exc()
        force = apply = False
