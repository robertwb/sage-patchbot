#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Main script for the patchbot client.

This is the main script for the patchbot client. It pulls branches
from trac, applies them, and publishes the results of the tests to a
server running ``serve.py``.  Configuration is primarily done via an
optional ``conf.json`` file (json format) passed in as a command line
argument.
"""

# -------------------------------------------------------------------
#          Author: Robert Bradshaw <robertwb@gmail.com>
#
#               Copyright 2010-14 (C) Google, Inc.
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  https://www.gnu.org/licenses/
# -------------------------------------------------------------------

# global python imports
import codecs
import hashlib
import signal
import getpass
import glob
import os
import shutil
import sys
import subprocess
import time
import traceback
import tempfile
import bz2
import json
import socket
import pprint
import multiprocessing

import pickle

from urllib.request import urlopen
from urllib.error import HTTPError
from urllib.parse import urlencode

from datetime import datetime

# imports from patchbot sources
import sage_patchbot
from .trac import get_ticket_info_from_trac_server, pull_from_trac, TracServer, Config, is_closed_on_trac
from .util import (now_str, prune_pending, do_or_die,
                   get_sage_version, current_reports, git_commit,
                   branch_updates_some_package,
                   describe_branch, comparable_version, temp_build_suffix,
                   ensure_free_space, get_python_version,
                   ConfigException, SkipTicket, TestsFailed)
from .http_post_file import post_multipart
from .plugins import PluginResult, plugins_available

# name of the log files
LOG_RATING = 'rating.log'
LOG_RATING_SHORT = 'rating_summary.txt'
LOG_MAIN = ('patchbot.log', sys.stdout)
LOG_MAIN_SHORT = 'history.txt'
LOG_CONFIG = 'config.txt'


def filter_on_authors(tickets, authors):
    """
    Keep only tickets with authors among the given ones.

    Every ticket is a dict.

    INPUT:

    a list of tickets and a list of authors

    OUTPUT:

    a list of tickets
    """
    if authors is not None:
        authors = set(authors)
    for ticket in tickets:
        if authors is None or set(ticket['authors']).issubset(authors):
            yield ticket


def compare_machines(a, b, machine_match=None):
    """
    Compare two machines a and b.

    Return a list.

    machine_match is a number of initial things to look at.

    EXAMPLES::

        >>> m1 = ['Ubuntu', '14.04', 'i686', '3.13.0-40-generic', 'arando']
        >>> m2 = ['Fedora', '19', 'x86_64', '3.10.4-300.fc19.x86_64', 'desktop']
        >>> compare_machines(m1, m2)
    """
    if machine_match is not None:
        a = a[:machine_match]
        b = b[:machine_match]
    diff = [x != y for x, y in zip(a, b)]
    if len(a) != len(b):
        diff.append(1)
    return diff


class TimeOut(Exception):
    pass


def alarm_handler(signum, frame):
    raise TimeOut


class Tee(object):
    def __init__(self, filepath, time=False, timeout=None, timer=None):
        if timeout is None:
            timeout = 60 * 60 * 24
        self.filepath = filepath
        self.time = time
        self.timeout = timeout
        self.timer = timer

    def __enter__(self):
        self._saved = os.dup(sys.stdout.fileno()), os.dup(sys.stderr.fileno())
        self.tee = subprocess.Popen(["tee", self.filepath],
                                    stdin=subprocess.PIPE)
        os.dup2(self.tee.stdin.fileno(), sys.stdout.fileno())
        os.dup2(self.tee.stdin.fileno(), sys.stderr.fileno())
        if self.time:
            print(now_str())
            self.start_time = time.time()

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.timer:
            self.timer.print_all()
        if exc_type is not None:
            traceback.print_exc()
        if self.time:
            print(now_str())
            msg = "{} seconds".format(int(time.time() - self.start_time))
            print(msg)
        self.tee.stdin.close()
        time.sleep(1)
        os.dup2(self._saved[0], sys.stdout.fileno())
        os.dup2(self._saved[1], sys.stderr.fileno())
        os.close(self._saved[0])
        os.close(self._saved[1])
        time.sleep(1)
        try:
            signal.signal(signal.SIGALRM, alarm_handler)
            signal.alarm(self.timeout)
            self.tee.wait()
            signal.alarm(0)
        except TimeOut:
            traceback.print_exc()
            raise
        return False


class Timer(object):
    def __init__(self):
        self._starts = {}
        self._history = []
        self.start()

    def start(self, label=None):
        self._last_activity = self._starts[label] = time.time()

    def finish(self, label=None):
        try:
            elapsed = time.time() - self._starts[label]
        except KeyError:
            elapsed = time.time() - self._last_activity
        self._last_activity = time.time()
        self.print_time(label, elapsed)
        self._history.append((label, elapsed))

    def print_time(self, label, elapsed):
        msg = '{} -- {} seconds'.format(label, int(elapsed))
        print(msg)

    def print_all(self):
        for label, elapsed in self._history:
            self.print_time(label, elapsed)


status = {'started': 'ApplyFailed',
          'applied': 'BuildFailed',
          'built': 'TestsFailed',
          'tested': 'TestsPassed',
          'tests_passed_on_retry': 'TestsPassedOnRetry',
          'tests_passed_plugins_failed': 'PluginFailed',
          'plugins': 'PluginOnly',
          'plugins_failed': 'PluginOnlyFailed',
          'spkg': 'Spkg',
          'network_error': 'Pending',
          'skipped': 'Pending'}


def boundary(name, text_type):
    """
    Return text that bound parts of the reports.

    type can be 'plugin', 'plugin_end', 'ticket' and 'spkg'
    """
    if text_type == 'plugin':
        letter = '='
        length = 10
    elif text_type == 'plugin_end':
        name = 'end ' + name
        letter = '='
        length = 10
    elif text_type == 'ticket':
        letter = '='
        length = 30
    elif text_type == 'spkg':
        letter = '+'
        length = 10
    return ' '.join((letter * length, str(name), letter * length))


def machine_data():
    """
    Return the machine data as a list of strings.

    This uses ``os.uname`` to find the data.

    EXAMPLES::

        m1 = ['Ubuntu', '14.04', 'i686', '3.13.0-40-generic', 'arando']
        m2 = ['Fedora', '19', 'x86_64', '3.10.4-300.fc19.x86_64', 'desktop']
    """
    first_cleanup = [txt.replace(" ", "_") for txt in os.uname()]
    system, node, release, version, arch = [txt.replace("#", "")
                                            for txt in first_cleanup]
    return [system, version, arch, release, node]


def parse_time_of_day(s):
    """
    Parse the 'time_of_day' config.

    Examples of syntax: default is "0-0" from midnight to midnight

    "06-18" start and end hours

    "22-07" idem during the night

    "10-12,14-18" several time ranges

    "17" for just one hour starting at given time
    """
    def parse_interval(ss):
        ss = ss.strip()
        if '-' in ss:
            start, end = ss.split('-')
            return float(start), float(end)
        else:
            return float(ss), float(ss) + 1
    return [parse_interval(ss) for ss in s.split(',')]


def check_time_of_day(hours):
    """
    Check that the time is inside the allowed running hours.

    This is with respect to local time.
    """
    now = datetime.now(None)
    hour = now.hour + now.minute / 60.
    for start, end in parse_time_of_day(hours):
        if start < end:
            if start <= hour <= end:
                return True
        elif hour <= end or start <= hour:
            return True
    return False


def sha1file(path, blocksize=None):
    """
    Return SHA-1 of file.

    This is used to check spkgs.

    should now be working in py3

    EXAMPLES::

        In [2]: sha1file('sage/upstream/tachyon-0.98.9.tar.bz2')
        Out[2]: '9866dc93e129115994708efa6e7ca16e20d58237'
    """
    if blocksize is None:
        blocksize = 2 ** 16
    h = hashlib.sha1()
    with open(path, 'rb') as handle:
        buf = handle.read(blocksize)
        while len(buf):
            h.update(buf)
            buf = handle.read(blocksize)
    return h.hexdigest()


class OptionDict(object):
    r"""
    Fake option class built from a dictionary.

    This used to run the patchbot in a IPython console. It contains default
    values for the 10 options that can be provided from command line. These
    default can be changed by passing a dictionary to the constructor.

    EXAMPLES::

        >>> OptionDict().sage_root
        None
        >>> OptionDict({'sage_root': '/path/to/sage/root/'}).sage_root
        '/path/to/sage/root'
    """
    sage_root = None
    server = 'https://patchbot.sagemath.org'
    config = None
    cleanup = False
    dry_run = False
    no_banner = False
    owner = None
    plugin_only = False
    safe_only = True
    skip_base = True
    retries = None
    skip_doc_clean = False

    def __init__(self, d):
        for key, value in d.items():
            setattr(self, key, value)


class Patchbot(object):
    """
    Main class of the patchbot.

    This can be used in an interactive python or ipython session.

    INPUT:

    - options -- an option class or a dictionary

    EXAMPLES::

        >>> from sage_patchbot.patchbot import Patchbot
        >>> P = Patchbot({'sage_root': '/homes/leila/sage'})
        >>> P.test_a_ticket(12345)

    How to more or less ban an author: have

    {"bonus":{"proust":-1000}}

    written inside the config.json file passed using --config=config.json
    """
    # hardcoded default config and bonus
    default_config = {"sage_root": None,
                      "server": "https://patchbot.sagemath.org/",
                      "idle": 300,
                      "time_of_day": "0-0",  # midnight-midnight
                      "parallelism": min(3, multiprocessing.cpu_count()),
                      "timeout": 3 * 60 * 60,
                      "plugins": ["commit_messages",
                                  "coverage",
                                  "non_ascii",
                                  "doctest_continuation",
                                  "python3",
                                  "python3_py",
                                  "python3_pyx",
                                  "oldstyle_print",
                                  "blocks",
                                  "triple_colon",
                                  "foreign_latex",
                                  "trac_links",
                                  "startup_time",
                                  "startup_modules",
                                  "docbuild",
                                  "git_rev_list"],
                      "plugins_disabled": [],
                      "plugins_enabled": [],
                      "bonus": {},
                      "machine": machine_data(),
                      "machine_match": 5,
                      "user": getpass.getuser(),
                      "keep_open_branches": True,
                      "base_repo": "git://github.com/sagemath/sage.git",
                      "base_branch": "develop",
                      "max_behind_commits": 0,
                      "max_behind_days": 1.0,
                      "use_ccache": True,
                      "tested_files": "all",   # either 'all' or 'py3' or 'py3+changed'
                      "test_options": None,    # transmitted to --optional
                      # 6 options that can also be changed using sage --xx
                      "dry_run": False,
                      "no_banner": False,
                      "owner": "unknown owner",
                      "plugin_only": False,
                      "safe_only": True,
                      "skip_base": False,
                      "retries": 0,
                      "cleanup": False,
                      "skip_doc_clean": False}

    default_bonus = {"needs_review": 1000,
                     "positive_review": 500,
                     "blocker": 100,
                     "critical": 60,
                     "major": 10,
                     "unique": 40,
                     "applies": 20,
                     "behind": 1}

    def __init__(self, options=None):
        if isinstance(options, dict):
            # when this is run in a IPython session
            options = OptionDict(options)

        self.options = options
        self.reload_config()

        self.trac_server = TracServer(Config())
        self.__version__ = sage_patchbot.__version__
        self.last_pull = 0
        self.to_skip = {}
        self.idling = False

        self.write_log('Patchbot {} initialized with SAGE_ROOT={} (pid: {})'.format(
            self.__version__, self.sage_root, os.getpid()), LOG_MAIN)

    def idle(self):
        """
        Sleep for ``idle`` seconds, where ``idle`` is the option supplied by
        the patchbot configuration.

        While idling, the ``idling`` attribute is set to ``True``.
        """

        self.idling = True
        time.sleep(self.config['idle'])
        self.idling = False

    def write_log(self, msg, logfile=None, date=True):
        r"""
        Write ``msg`` in a logfile.

        INPUT:

        - ``logfile`` -- (optional)

           * if not provided, write on stdout

           * if it is a string then append ``msg`` to the file ``logfile``

           * if it is a tuple or a list, then call write_log for each member of
             that list

        - ``date`` -- (default ``True``) whether to write the date at the
          beginning of the line
        """
        if logfile is None:
            logfile = sys.stdout
            close = False
        elif isinstance(logfile, str):
            filename = os.path.join(self.log_dir, logfile)
            logfile = codecs.open(filename, 'a', encoding='utf-8')
            close = True
        elif isinstance(logfile, (tuple, list)):
            for f in logfile:
                self.write_log(msg, f, date)
            return
        else:  # logfile is a file
            close = False

        try:
            if date:
                logfile.write(u"[{}] ".format(now_str()))
            logfile.write(msg)
            logfile.write(u"\n")
        except AttributeError:
            raise ValueError("logfile = {} must be either None, or a string or a list or a file".format(logfile))

        if close:
            logfile.close()
        else:
            logfile.flush()

    def delete_log(self, logfile):
        r"""
        Delete ``logfile``
        """
        filename = os.path.join(self.log_dir, logfile)
        if os.path.isfile(filename):
            os.remove(filename)

    def version(self):
        """
        Return the version of the patchbot.

        Something like '2.3.7'

        EXAMPLES::

            In [3]: P.version()
            Out[3]: u'2.5.3'
        """
        return self.__version__

    def banner(self):
        """
        A banner for the patchbot

        EXAMPLES::

            In [7]: print(P.banner())
            ┌─┬──────┐
            │░│ ⊙  ʘ │        SageMath patchbot
            │░│      │
            │░│ ──── │        version 2.5.3
            ╘═╧══════╛
        """
        s = u'┌─┬──────┐\n'
        s += u'│░│ ⊙  ʘ │        SageMath patchbot\n'
        s += u'│░│      │\n'
        s += u'│░│ ──── │        version {}\n'.format(self.version())
        s += u'╘═╧══════╛'
        return s

    def load_json_from_server(self, path, retry=1):
        """
        Load a json file from the patchbot server.

        This is one connection between patchbot server and clients.

        INPUT:

        - ``path`` -- the query for the server

        - ``retry`` -- the number of times we retry to get a connection
        """
        while True:
            retry -= 1
            try:
                ad = "{}/{}".format(self.server, path)
                full_str = urlopen(ad, timeout=10).read().decode('utf8')
                return json.loads(full_str)
            except HTTPError as err:
                self.write_log(" retry {}; {}".format(retry, str(err)), [LOG_MAIN, LOG_MAIN_SHORT])
                if retry == 0:
                    raise
            except socket.timeout:
                self.write_log(" retry {}; timeout while querying the patchbot server with '{}'".format(retry, path), [LOG_MAIN, LOG_MAIN_SHORT])
                if retry == 0:
                    raise

            time.sleep(30)

    def lookup_ticket(self, t_id, verbose=False):
        """
        Retrieve information about one ticket from the patchbot server.

        (or from trac if the patchbot server does not answer)

        For an example of the page it calls:

        https://patchbot.sagemath.org/ticket/?raw&query={"id":11529}

        For humans:

        https://patchbot.sagemath.org/ticket/?raw&query={"id":11529}&pretty
        """
        path = "ticket/?" + urlencode({'raw': True,
                                       'query': json.dumps({'id': t_id})})
        res = self.load_json_from_server(path, retry=3)
        if res:
            if verbose:
                print('data retrieved from patchbot server')
            return res[0]
        else:
            if verbose:
                print('data retrieved from trac server')
            return get_ticket_info_from_trac_server(t_id)

    def get_local_config(self):
        """
        Return the configuration obtained from the command line option and the
        local configuration file.

        This is done in the following order:

        1) pick default values for all parameters

        2) override with values from json config file if given

        3) override from the options class given in argument
        """
        # start from a fresh copy of the default configuration
        conf = self.default_config.copy()

        # override the default by the json config file
        if self.options.config is not None:
            with open(self.options.config) as f:
                for key, value in json.load(f).items():
                    conf[str(key)] = value

        # complete back the default bonus if needed
        for key, value in self.default_bonus.items():
            if key not in conf['bonus']:
                conf['bonus'][key] = value

        # now override with the values of the 9 options (all except 'config')
        # coming from the patchbot commandline
        for opt in ('sage_root', 'server', 'cleanup', 'dry_run', 'no_banner',
                    'owner', 'plugin_only', 'safe_only', 'skip_base',
                    'retries', 'skip_doc_clean'):
            value = getattr(self.options, opt)
            if value is not None:
                conf[opt] = value

        # plugin setup
        plugins = set(conf['plugins'])
        plugins.update(conf.pop("plugins_enabled"))
        # always use the pyflakes and pycodestyle plugins
        plugins.add("pyflakes")
        plugins.add("pycodestyle")
        plugins.difference_update(conf.pop("plugins_disabled"))
        # for backward compatibility (allow both plugins.X and just X)
        plugins = set(name.split('.')[-1] for name in plugins)

        if not conf['plugin_only']:
            plugins.add("docbuild")  # docbuild is mandatory so that tests pass

        plugins = [p for p in plugins_available if p in plugins]

        def locate_plugin(name):
            plugin = getattr(__import__("sage_patchbot.plugins",
                                        fromlist=[name]), name)
            assert callable(plugin)
            return plugin

        conf["plugins"] = [(name, locate_plugin(name)) for name in plugins]

        return conf

    def reload_config(self):
        """
        Reload the configuration.

        This method has for main purpose to set properly the attribute
        ``config`` (the configuration dictionary).
        """
        self.config = self.get_local_config()

        # Now we set sage_root and some other attributes that depend on
        # sage_root. (here might not be the right place to do it)
        self.sage_root = self.config["sage_root"]
        if (self.sage_root is None or
                not os.path.isdir(self.sage_root) or
                not os.path.isabs(self.sage_root) or
                not os.path.isfile(os.path.join(self.sage_root, "sage"))):
            raise ValueError("the sage_root option should be specified "
                             "as an absolute path to a Sage installation (either from "
                             "the command line option --sage-root=/path/to/sage or inside "
                             "the configuration file provided with "
                             "--config=path/to/config.json)")

        self.sage_command = os.path.join(self.sage_root, "sage")

        self.python_version = get_python_version(self.sage_command)

        self.base = get_sage_version(self.sage_root)

        # TODO: this should be configurable
        self.log_dir = os.path.join(self.sage_root, "logs", "patchbot")

        self.server = self.config["server"]

        # make sure that the log directory is writable and writhe the
        # configuration file there
        if not os.path.exists(self.log_dir):
            os.makedirs(self.log_dir)
        with codecs.open(os.path.join(self.log_dir, 'install.log'), 'a',
                         encoding='utf8'):
            pass

        # write the config in logfile
        self.delete_log(LOG_CONFIG)
        self.write_log("Configuration for the patchbot\n{}\n".format(now_str()), LOG_CONFIG, False)
        self.write_log(pprint.pformat(self.config), LOG_CONFIG, False)

        return self.config

    def reset_root(self):
        """
        Ensure that we are in the correct SAGE_ROOT.
        """

        # Don't do this is self.sage_root is None; we never want to set
        # SAGE_ROOT to None
        if self.sage_root is not None:
            os.chdir(self.sage_root)
            os.environ['SAGE_ROOT'] = self.sage_root

    def check_base(self):
        """
        Check that the patchbot/base is synchro with 'base_branch'.

        Usually 'base_branch' is set to 'develop'.

        This will update the patchbot/base if necessary.
        """
        os.chdir(self.sage_root)
        self.write_log("Check base.", LOG_MAIN)
        try:
            do_or_die("git checkout patchbot/base")
        except Exception:
            do_or_die("git checkout -b patchbot/base")

        do_or_die("git fetch %s +%s:patchbot/base_upstream" %
                  (self.config['base_repo'], self.config['base_branch']))

        only_in_base = int(subprocess.check_output(["git", "rev-list", "--count", "patchbot/base_upstream..patchbot/base"]))

        only_in_upstream = int(subprocess.check_output(["git", "rev-list", "--count", "patchbot/base..patchbot/base_upstream"]))

        max_behind_time = self.config['max_behind_days'] * 60 * 60 * 24
        if (only_in_base > 0 or
                only_in_upstream > self.config['max_behind_commits'] or
                (only_in_upstream > 0 and
                 time.time() - self.last_pull < max_behind_time)):
            do_or_die("git checkout patchbot/base_upstream")
            do_or_die("git branch -f patchbot/base patchbot/base_upstream")
            do_or_die("git checkout patchbot/base")
            self.last_pull = time.time()
            return False
        return True

    def human_readable_base(self):
        """
        Return the human name of the base branch.
        """
        # TODO: Is this stable?
        version = get_sage_version(self.sage_root)
        commit_count = int(subprocess.check_output(['git', 'rev-list',
                                                    '--count',
                                                    '%s..patchbot/base' % version]))
        return "{} + {} commits".format(version, commit_count)

    def get_one_ticket(self, status='open', verbose=0):
        """
        Return one ticket with its rating.

        If no ticket is found, return ``None``.

        INPUT:

        - ``verbose`` -- if set to 0 then nothing is print on stdout, if 1 then
          only the summary is print on stdout and if 2 then also the details of
          the rating

        OUTPUT:

        A pair (rating, ticket data). The rating is a tuple of integer values.
        """
        query = "raw&status={}".format(status)

        self.write_log("Getting ticket list...", LOG_MAIN)
        if self.to_skip:
            s = ', '.join('#{} (until {})'.format(k, v)
                          for k, v in self.to_skip.items())
            self.write_log('The following tickets will be skipped: ' + s, LOG_MAIN)
        all_tickets = self.load_json_from_server("ticket/?" + query, retry=10)

        # rating for all tickets
        self.delete_log(LOG_RATING)
        self.write_log("Rating tickets...", LOG_MAIN)
        all_tickets = [(self.rate_ticket(ti, verbose=(verbose == 2)), ti)
                       for ti in all_tickets]

        # remove all tickets with None rating
        all_tickets = [ti for ti in all_tickets if ti[0] is not None]

        # sort tickets using their ratings
        all_tickets.sort()

        self.delete_log(LOG_RATING_SHORT)
        if verbose >= 1:
            logfile = [LOG_RATING_SHORT, sys.stdout]
        else:
            logfile = [LOG_RATING_SHORT]
        for rating, ticket in reversed(all_tickets):
            self.write_log(u'#{:<6}{:30}{}'.format(ticket['id'],
                                                   str(rating[:2]),
                                                   ticket['title']),
                           logfile, date=False)

        if all_tickets:
            return all_tickets[-1]
        else:
            return None

    def rate_ticket(self, ticket, verbose=False):
        """
        Evaluate the interest to test this ticket.

        Return nothing when the ticket should not be tested.
        """
        os.chdir(self.sage_root)
        log_rat_path = os.path.join(self.log_dir, LOG_RATING)
        with codecs.open(log_rat_path, "a", encoding="utf-8") as log_rating:

            if verbose:
                logfile = [log_rating, sys.stdout]
            else:
                logfile = [log_rating]

            if isinstance(ticket, (int, str)):
                ticket = self.lookup_ticket(ticket)

            rating = 0
            if ticket['id'] == 0:
                return ((100), 100, 0)

            if not ticket.get('git_branch'):
                self.write_log('#{}: no git branch'.format(ticket['id']), logfile)
                return

            if not(ticket['status'] in ('needs_review', 'positive_review',
                                        'needs_info', 'needs_work')):
                msg = '#{}: bad status (={})'
                self.write_log(msg.format(ticket['id'],
                                          ticket['status']), logfile)
                return

            self.write_log(u"#{}: start rating".format(ticket['id']), logfile)

            if ticket['milestone'] in ('sage-duplicate/invalid/wontfix',
                                       'sage-feature', 'sage-pending',
                                       'sage-wishlist'):
                self.write_log(' do not test if the milestone is not good (got {})'.format(ticket['milestone']),
                               logfile, False)
                return

            bonus = self.config['bonus']  # load the dict of bonus

            if ticket.get('git_commit', 'unknown') == 'unknown':
                self.write_log(' do not test if git_commit is unknown',
                               logfile, False)
                return

            if not ticket.get('authors_fullnames', []):
                self.write_log(' do not test if no author is given',
                               logfile, False)
                return

            for author in ticket['authors_fullnames']:
                rating += 2 * bonus.get(author, 0)  # bonus for authors

            for author in ticket['authors']:
                rating += 2 * bonus.get(author, 0)  # bonus for authors

            self.write_log(' rating {} after authors'.format(rating),
                           logfile, False)

            for participant in ticket['participants']:
                rating += bonus.get(participant, 0)  # bonus for participants

            self.write_log(' rating {} after participants'.format(rating),
                           logfile, False)

            if 'component' in ticket:
                rating += bonus.get(ticket['component'], 0)  # bonus for components

            self.write_log(' rating {} after components'.format(rating),
                           logfile, False)

            rating += bonus.get(ticket['status'], 0)
            rating += bonus.get(ticket['priority'], 0)
            rating += bonus.get(str(ticket['id']), 0)

            msg = ' rating {} after status ({})/priority ({})/id ({})'
            self.write_log(msg.format(rating, ticket['status'],
                                      ticket['priority'], ticket['id']),
                           logfile, False)

            prune_pending(ticket)

            retry = ticket.get('retry', False)
            # by default, do not retry the ticket

            uniqueness = (100,)
            # now let us look at previous reports
            if not retry:
                self.write_log(' start report scanning', logfile, False)
                for report in self.current_reports(ticket, newer=True):
                    if report.get('git_base'):
                        try:
                            only_in_base = int(subprocess.check_output(["git", "rev-list", "--count", "%s..patchbot/base" % report['git_base']],
                                                                       stderr=subprocess.PIPE))
                        except (ValueError, subprocess.CalledProcessError):
                            # report['git_base'] not in our repo
                            self.write_log(' commit {} not in the local git repository'.format(report['git_base']),
                                           logfile, date=False)
                            only_in_base = -1
                        rating += bonus['behind'] * only_in_base
                    self.write_log(' rating {} after behind'.format(rating),
                                   logfile, False)

                    report_uniqueness = compare_machines(report['machine'],
                                                         self.config['machine'],
                                                         self.config['machine_match'])
                    report_uniqueness = tuple(int(x) for x in report_uniqueness)
                    if only_in_base and not any(report_uniqueness):
                        report_uniqueness = (0, 0, 0, 0, 1)
                    uniqueness = min(uniqueness, report_uniqueness)

                    if report['status'] != 'ApplyFailed':
                        rating += bonus.get("applies", 0)
                    self.write_log(' rating {} after applies'.format(rating),
                                   logfile, False)
                    rating -= bonus.get("unique", 0)
                    self.write_log(' rating {} after uniqueness'.format(rating),
                                   logfile, False)
            self.write_log(' rating {} after report scanning'.format(rating),
                           logfile, False)

            if not any(uniqueness):
                self.write_log(' already done', logfile, False)
                return

            if ticket['id'] in self.to_skip:
                if self.to_skip[ticket['id']] < time.time():
                    del self.to_skip[ticket['id']]
                else:
                    self.write_log(' do not test if still in the skip delay',
                                   logfile, False)
                    return

            return uniqueness, rating, -int(ticket['id'])

    def current_reports(self, ticket, newer=False):
        """
        Return the list of current reports on a ticket.

        EXAMPLES::

            In [4]: P.current_reports(20240)
            Out[4]: []
        """
        if isinstance(ticket, (int, str)):
            ticket = self.lookup_ticket(ticket)
        return current_reports(ticket, base=self.base, newer=newer)

    def test_some_tickets(self, ticket_list):
        """
        Launch the tests of several tickets (in the given order).

        Useful for manual trigger.

        INPUT:

        - ``ticket`` -- a list of integers
        """
        for t in ticket_list:
            self.test_a_ticket(t)

    def test_a_ticket(self, ticket=None):
        """
        Launch the test of a ticket.

        INPUT:

        - ``ticket``

          * if ``None`` then pick a ticket using :meth:`get_one_ticket`

          * if an integer or a string, use this ticket number
        """
        self.reset_root()
        # ------------- selection of ticket -------------
        if ticket is None:
            ask_for_one = self.get_one_ticket()
            if ask_for_one:
                rating, ticket = ask_for_one
                self.write_log('testing found ticket #{}'.format(ticket['id']), LOG_MAIN)

        else:
            N = int(ticket)
            ticket = self.lookup_ticket(N)
            rating = None
            self.write_log('testing given ticket #{}'.format(N), LOG_MAIN)

        if not ticket:
            self.write_log('no more tickets, take a nap',
                           [LOG_MAIN, LOG_MAIN_SHORT])
            self.idle()
            return

        # this should be a double check and never happen
        if ticket.get('status') == 'closed' or is_closed_on_trac(ticket['id']):
            self.write_log('tried to test a closed ticket! shame!',
                           [LOG_MAIN, LOG_MAIN_SHORT])
            # here call for refresh ?
            self.to_skip[ticket['id']] = time.time() + 120 * 60 * 60
            return

        if ticket['id'] == 0:
            self.write_log('testing the base', LOG_MAIN)
            rating = 100

        if rating is None:
            self.write_log("warning: rating is None, testing #{} at your own risk".format(ticket['id']),
                           LOG_MAIN)

        if not(ticket.get('git_branch') or ticket['id'] == 0):
            self.write_log("no git branch for #{}, hence no testing".format(ticket['id']),
                           LOG_MAIN)
            return

        # ------------- initialisation -------------
        print("\n\n")
        print(boundary(ticket['id'], 'ticket'))
        print(ticket['title'])
        print("score = {}".format(rating))
        print("\n\n")
        log = os.path.join(self.log_dir, '{}-log.txt'.format(ticket['id']))
        self.write_log('#{}: init phase'.format(ticket['id']), [LOG_MAIN, LOG_MAIN_SHORT])
        if not self.config['plugin_only']:
            self.report_ticket(ticket, status='Pending', log=log)
        plugins_results = []
        if not self.config['no_banner']:
            print(self.banner())
        botmake = os.getenv('MAKE', "make -j{}".format(self.config['parallelism']))
        os.environ['GIT_AUTHOR_NAME'] = os.environ['GIT_COMMITTER_NAME'] = 'patchbot'
        os.environ['GIT_AUTHOR_EMAIL'] = os.environ['GIT_COMMITTER_EMAIL'] = 'patchbot@localhost'
        os.environ['GIT_AUTHOR_DATE'] = os.environ['GIT_COMMITTER_DATE'] = '1970-01-01T00:00:01'
        try:
            t = Timer()
            with Tee(log, time=True, timeout=self.config['timeout'], timer=t):
                state = 'started'

                # ------------- pull and apply -------------
                pull_from_trac(self.sage_root, ticket['id'], force=True,
                               safe_only=self.config['safe_only'])
                t.finish("Apply")
                state = 'applied'
                if not self.config['plugin_only']:
                    self.report_ticket(ticket, status='Pending',
                                       log=log, pending_status=state)

                is_spkg = branch_updates_some_package() or ticket['spkgs']
                if is_spkg:
                    # ------------- treatment of spkgs -------------
                    state = 'spkg'
                    print("Ticket updates some package, hence not tested.")
                    self.to_skip[ticket['id']] = time.time() + 240 * 60 * 60

                if not is_spkg:
                    # ------------- make -------------
                    if not self.config['skip_doc_clean']:
                        do_or_die('{} doc-clean'.format(botmake))
                    do_or_die("{} build".format(botmake))
                    do_or_die(os.path.join(self.sage_root,
                                           'build', 'bin', 'sage-starts'))
                    # doc is made later in a plugin
                    t.finish("Build")
                    state = 'built'
                    if not self.config['plugin_only']:
                        self.report_ticket(ticket, status='Pending',
                                           log=log, pending_status=state)

                    # ------------- plugins -------------
                    patch_dir = tempfile.mkdtemp()  # create temporary dir
                    if ticket['id'] != 0:
                        do_or_die("git format-patch -o '%s' patchbot/base..patchbot/ticket_merged" % patch_dir)

                    kwds = {
                        "make": botmake,
                        "patches": [os.path.join(patch_dir, p)
                                    for p in os.listdir(patch_dir)],
                        "sage_binary": self.sage_command,
                        "dry_run": self.config['dry_run'],
                    }
                    # the keyword "patches" is used in plugin commit_messages

                    for name, plugin in self.config['plugins']:
                        try:
                            plug0log = os.path.join(self.log_dir, '0', name)
                            if ticket['id'] != 0 and os.path.exists(plug0log):
                                baseline = pickle.load(open(plug0log, 'rb'))
                            else:
                                baseline = None
                            print(boundary(name, 'plugin'))
                            do_or_die("git checkout patchbot/ticket_merged")
                            res = plugin(ticket, is_git=True,
                                         baseline=baseline, **kwds)
                            passed = True
                        except Exception:
                            traceback.print_exc()
                            passed = False
                            res = None
                        finally:
                            if isinstance(res, PluginResult):
                                if res.baseline is not None:
                                    plugin_dir = os.path.join(self.log_dir,
                                                              str(ticket['id']))
                                    if not os.path.exists(plugin_dir):
                                        os.mkdir(plugin_dir)
                                    pickle.dump(res.baseline, open(os.path.join(plugin_dir, name), 'wb'))
                                    passed = res.status == PluginResult.Passed
                                    print("{} {}".format(name, res.status))
                                    plugins_results.append((name, passed,
                                                            res.data))
                            else:
                                plugins_results.append((name, passed, None))
                            t.finish(name)
                            print(boundary(name, 'plugin_end'))
                    plugins_passed = all(passed for (name, passed, data)
                                         in plugins_results)

                    if patch_dir and os.path.exists(patch_dir):
                        shutil.rmtree(patch_dir)  # delete temporary dir

                    self.report_ticket(ticket, status='Pending', log=log,
                                       pending_status='plugins_passed'
                                       if plugins_passed else 'plugins_failed')

                    if self.config['plugin_only']:
                        state = 'plugins' if plugins_passed else 'plugins_failed'
                    else:
                        # ------------- run tests -------------
                        if self.config['dry_run']:
                            test_target = os.path.join(self.sage_root,
                                                       "src", "sage", "misc",
                                                       "a*.py")
                        elif self.config['tested_files'] in ['py3', 'py3+changed']:
                            path = os.path.join(self.sage_root, 'src', 'ext',
                                                'doctest',
                                                'python3-known-passing.txt')
                            with open(path) as f:
                                good_guys = ' '.join(f.read().splitlines())
                            if self.config['tested_files'] == 'py3+changed':
                                changed_files = subprocess.check_output(
                                    ["git", "diff", "--name-only", "patchbot/base..patchbot/ticket_merged"],
                                    universal_newlines=True).strip().split('\n')
                                changed_guys = ' ' + ' '.join(changed_files)
                            else:
                                changed_guys = ''
                            test_target = "--long " + good_guys + changed_guys
                        else:
                            test_target = "--all --long"

                        if self.config['parallelism'] > 1:
                            test_cmd = "p {}".format(self.config['parallelism'])
                        else:
                            test_cmd = ""

                        # Allow patchbot owners to activate tests
                        # for internet or m*ple or whatever they want.
                        # The value must be a valid string for --optional
                        # such as "sage,external"
                        if self.config['test_options'] is not None:
                            test_options = "--optional=" + self.config['test_options']
                        else:
                            test_options = ""

                        test_cmd = "{} -t{} {} {}".format(self.sage_command,
                                                          test_cmd,
                                                          test_options,
                                                          test_target)

                        max_tries = self.config.get('retries', 0) + 1
                        n_try = 1

                        while n_try <= max_tries:
                            try:
                                do_or_die(test_cmd, exn_class=TestsFailed)
                            except TestsFailed as exc:
                                if n_try == max_tries:
                                    raise exc
                            else:
                                if n_try == 1:
                                    state = 'tested'
                                else:
                                    state = 'tests_passed_on_retry'

                                break

                            if n_try == 1:
                                test_cmd += ' --failed'

                            n_try += 1

                        t.finish("Tests")

                        if not plugins_passed:
                            state = 'tests_passed_plugins_failed'

        except (HTTPError, socket.error, ConfigException):
            # Do not report failure because the network/trac died...
            self.write_log('network failure... skip this ticket', LOG_MAIN)
            t.print_all()
            traceback.print_exc()
            # Do not try this again for at least an hour.
            self.to_skip[ticket['id']] = time.time() + 60 * 60
            state = 'network_error'
        except SkipTicket as exn:
            self.to_skip[ticket['id']] = time.time() + exn.seconds_till_retry
            state = 'skipped'
            msg = "Skipping #{} for {} seconds: {}"
            self.write_log(msg.format(ticket['id'],
                                      exn.seconds_till_retry, exn),
                           [LOG_MAIN, LOG_MAIN_SHORT])
        except Exception as exn:
            msg = "#{} raises an exception: {}"
            self.write_log(msg.format(ticket['id'], exn),
                           [LOG_MAIN, LOG_MAIN_SHORT])
            traceback.print_exc()
            self.to_skip[ticket['id']] = time.time() + 12 * 60 * 60
        except:
            # Do not try this again for a while.
            self.to_skip[ticket['id']] = time.time() + 12 * 60 * 60
            raise

        # ------------- reporting to patchbot server -------------
        for _ in range(5):
            try:
                self.write_log("Reporting #{} with status {}".format(ticket['id'], status[state]),
                               LOG_MAIN)
                self.report_ticket(ticket, status=status[state], log=log,
                                   plugins=plugins_results,
                                   dry_run=self.config['dry_run'])
                self.write_log("Done reporting #{}".format(ticket['id']), LOG_MAIN)
                print(ticket['title'])
                break
            except IOError:
                traceback.print_exc()
                self.idle()
        else:
            self.write_log("Error reporting #{}".format(ticket['id']), LOG_MAIN)
        maybe_temp_root = os.environ.get('SAGE_ROOT')
        if maybe_temp_root.endswith(temp_build_suffix + str(ticket['id'])):
            # Make sure we switch back to the original sage_root
            self.reset_root()
            if os.path.exists(maybe_temp_root):
                shutil.rmtree(maybe_temp_root)
        return status[state]

    def report_ticket(self, ticket, status, log, plugins=(),
                      dry_run=False, pending_status=None):
        """
        Report about a ticket.

        INPUT:

        - ticket -- the ticket id, for example '21345'
        - status -- can be 'Pending', 'TestsPassed', etc
        - log -- the log
        - plugins -- results of the plugins
        - dry_run -- ?
        - pending_status -- can be 'applied', 'built', 'plugins_passed',
          'plugins_failed', etc
        """
        report = {'status': status,
                  'deps': ticket['depends_on'],
                  'spkgs': ticket['spkgs'],
                  'base': self.base,
                  'user': self.config['user'],
                  'owner': self.config['owner'],
                  'machine': self.config['machine'],
                  'time': now_str(),
                  'plugins': plugins,
                  'patchbot_version': self.__version__,
                  'python_version': self.python_version}

        if pending_status:
            report['pending_status'] = pending_status
        try:
            tags = [describe_branch('patchbot/base', tag_only=True),
                    describe_branch('patchbot/ticket_upstream', tag_only=True)]
            report['base'] = ticket_base = sorted(tags, key=comparable_version)[-1]
            report['git_base'] = self.git_commit('patchbot/base')
            report['git_base_human'] = describe_branch('patchbot/base')
            if ticket['id'] != 0:  # not on fake ticket 0
                report['git_branch'] = ticket.get('git_branch', None)
                report['git_log'] = subprocess.check_output(['git', 'log', '--oneline', '%s..patchbot/ticket_upstream' % ticket_base], universal_newlines=True).strip().split('\n')
                # If apply failed, we do not want to be stuck in an
                # infinite loop.
                report['git_commit'] = self.git_commit('patchbot/ticket_upstream')
                report['git_commit_human'] = describe_branch('patchbot/ticket_upstream')
                report['git_merge'] = self.git_commit('patchbot/ticket_merged')
                report['git_merge_human'] = describe_branch('patchbot/ticket_merged')
            else:  # on fake ticket 0
                report['git_branch'] = self.config['base_branch']
                report['git_commit'] = report['git_base']
                report['git_commit_human'] = report['git_base_human']
                report['git_merge'] = report['git_base']
                report['git_merge_human'] = report['git_base_human']
                report['git_log'] = []

        except Exception:
            traceback.print_exc()

        if status != 'Pending':
            self.write_log("#{}: {}{}".format(ticket['id'], status,
                                              " dry_run" if dry_run else ""),
                           [LOG_MAIN, LOG_MAIN_SHORT])

        print("REPORT")
        pprint.pprint(report)
        print("{}: {}".format(ticket['id'], status))
        fields = {'report': json.dumps(report)}
        if os.path.exists(log):
            # py3 : opens the file, get bytes
            # py2 : opens the file, get str=bytes
            with open(log, 'rb') as f:
                local_log = f.read()
            compressed = bz2.compress(local_log)
            files = [('log', 'log', compressed)]
        else:
            files = []
        if not dry_run or status == 'Pending':
            print(post_multipart("{}/report/{}".format(self.server,
                                                       ticket['id']),
                                 fields, files))

    def git_commit(self, branch):
        return git_commit(self.sage_root, branch)


_received_sigusr1 = False


def main(args=None):
    """
    Most configuration is done in the json config file, which is
    reread between each ticket for live configuration of the patchbot.
    """
    # NOTE: From Python 2.7 optparse is deprecated in favor of argparse
    from optparse import OptionParser
    parser = OptionParser()

    # 10 options that are passed to the patchbot via the class "options"
    # Don't provide defaults for these options (except for --sage-root) so
    # that we can tell whether or not they were given explicitly (i.e. their
    # value is not None) and should override settings from the config file.
    parser.add_option("--sage-root", dest="sage_root",
                      default=os.environ.get('SAGE_ROOT'),
                      help="specify another sage root directory")
    parser.add_option("--server", dest="server",
                      help="specify another patchbot server adress")
    parser.add_option("--config", dest="config",
                      help="specify the json config file")
    parser.add_option("--cleanup", action="store_true", dest="cleanup",
                      help="whether to cleanup the temporary files")
    parser.add_option("--dry-run", action="store_true", dest="dry_run")
    parser.add_option("--no-banner", action="store_true", dest="no_banner",
                      help="whether to print the utf8 banner")
    parser.add_option("--owner", dest="owner",
                      help="name and email of the human behind the bot")
    parser.add_option("--plugin-only", action="store_true", dest="plugin_only",
                      help="run the patchbot in plugin-only mode")
    parser.add_option("--safe-only", action="store_true", dest="safe_only",
                      help="whether to run the patchbot in safe-only mode")
    parser.add_option("--skip-base", action="store_true", dest="skip_base",
                      help="whether to check that the base is errorless")
    parser.add_option("--retries", type=int, metavar="N",
                      help="retry failed tests up to N times; if previously "
                           "failing tests pass on a retry the test run is "
                           "considered passed")
    parser.add_option("--skip-doc-clean", action="store_true", dest="skip_doc_clean",
                      help="whether to clean documentation during initialization")

    # and options that are only used in the main loop below
    parser.add_option("--count", dest="count",
                      default=1000000,
                      help="how many tickets to test")
    parser.add_option("--list", action="store_true", dest="list",
                      help="only write informations about tickets "
                           "that would be tested in the form: "
                           "[ticket id] [rating] [ticket title]")
    parser.add_option("--conf", action="store_true", dest="conf",
                      help="write the configuration on standard "
                           "output and quit")
    parser.add_option("--ticket", dest="ticket",
                      help="test only a list of tickets, for example"
                           " '12345,19876'")
    parser.add_option("--free-giga", dest="free_giga",
                      type="float", default=4,
                      help="number of required free gigabytes (0 means "
                           "no minimum space required)"
                      )

    (options, args) = parser.parse_args(args)

    # the configuration file might be a relative path...
    if options.config is not None:
        options.config = os.path.abspath(options.config)

    try:
        patchbot = Patchbot(options)
    except ValueError as msg:
        print("Error: {}".format(msg))
        sys.exit(1)

    if options.ticket:
        # only test the given list of tickets
        tickets = [int(t) for t in options.ticket.split(',')]
        count = len(tickets)
    else:
        tickets = None
        count = int(options.count)

    if options.conf:
        # the option "--conf" allows to see the configuration
        pprint.pprint(patchbot.config)
        sys.exit(0)

    if options.list:
        # the option "--list" allows to see tickets that will be tested
        patchbot.get_one_ticket(verbose=1)
        sys.exit(0)

    if options.sage_root == os.environ.get('SAGE_ROOT'):
        print("WARNING: Do not use this copy of sage while the patchbot is running.")

    if options.free_giga > 0:
        ensure_free_space(patchbot.sage_root, N=options.free_giga)

    if patchbot.config['use_ccache']:
        do_or_die("%s -i ccache" %
                  patchbot.sage_command, exn_class=ConfigException)
        # If we rebuild the (same) compiler we still want to share the cache.
        os.environ['CCACHE_COMPILERCHECK'] = '%compiler% --version'

    # Install the SIGUSR1 handler; if SIGUSR1 is received then patchbot will
    # exit before testing the next ticket.
    def _handle_sigusr1(*args):
        global _received_sigusr1
        _received_sigusr1 = True
        if patchbot.idling:
            patchbot.write_log(
                "Received SIGUSR1; the patchbot is not currently testing "
                "any tickets, so exiting immediately.")
            sys.exit(0)
        else:
            patchbot.write_log(
                "Received SIGUSR1; the patchbot will exit after testing the "
                "current ticket.")

    signal.signal(signal.SIGUSR1, _handle_sigusr1)

    if not patchbot.config['skip_base']:
        patchbot.check_base()

        def good(report):
            return (report['machine'] == patchbot.config['machine'] and
                    report['status'].startswith('TestsPassed'))

        if patchbot.config['plugin_only'] or not any(good(report) for report in patchbot.current_reports(0)):
            res = patchbot.test_a_ticket(0)
            if res not in ('TestsPassed', 'TestsPassedOnRetry', 'PluginOnly'):
                print("\n\n")
                print("Current base: {} {}".format(patchbot.config['base_repo'],
                                                   patchbot.config['base_branch']))
                print("Failing tests in your base install: exiting.")
                sys.exit(1)

    for k in range(count):
        if patchbot.config['cleanup']:
            for path in glob.glob(os.path.join(tempfile.gettempdir(),
                                               "*%s*" % temp_build_suffix)):
                patchbot.write_log("Cleaning up {}".format(path),
                                   [LOG_MAIN, LOG_MAIN_SHORT])
                shutil.rmtree(path)

        if _received_sigusr1:
            break

        try:
            if tickets:
                ticket = tickets.pop(0)
            else:
                ticket = None

            # This reset_root call is probably not necessary, but it does
            # ensure that, after a previous ticket was tested, we restore the
            # correct SAGE_ROOT if for some reason patchbot.test_a_ticket did
            # not reset it correctly
            patchbot.reset_root()

            patchbot.reload_config()
            if check_time_of_day(patchbot.config['time_of_day']):
                if not patchbot.check_base():
                    patchbot.test_a_ticket(0)
                patchbot.test_a_ticket(ticket)
            else:
                patchbot.write_log("Idle.", [LOG_MAIN, LOG_MAIN_SHORT])
                patchbot.idle()
        except Exception:
            traceback.print_exc()
            patchbot.idle()


if __name__ == '__main__':
    # this script is the entry point for the bot clients
    args = list(sys.argv)
    main(args)
