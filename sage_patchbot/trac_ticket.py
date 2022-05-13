"""
A Trac Ticket

EXAMPLES::

    sage: from datetime import datetime
    sage: create_time = datetime.utcfromtimestamp(1376149000)
    sage: modify_time = datetime.utcfromtimestamp(1376150000)
    sage: from git_trac.trac_ticket import TracTicket_class
    sage: t = TracTicket_class(123, create_time, modify_time, {})
    sage: t
    <git_trac.trac_ticket.TracTicket_class object at 0x...>
    sage: t.number
    123
    sage: t.title
    '<no summary>'
    sage: t.ctime
    datetime.datetime(2013, 8, 10, 15, 36, 40)
    sage: t.mtime
    datetime.datetime(2013, 8, 10, 15, 53, 20)
"""

##############################################################################
#  The "git trac ..." command extension for git
#  Copyright (C) 2013  Volker Braun <vbraun.name@gmail.com>
#
#  This program is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program.  If not, see <https://www.gnu.org/licenses/>.
##############################################################################
from __future__ import annotations
from typing import Iterator

import textwrap
from datetime import datetime
from xml.parsers.expat import ExpatError


def format_trac(text: str) -> str:
    text = text.strip()
    accumulator = []
    for line in text.splitlines():
        line = '\n'.join(textwrap.wrap(line, 78))
        accumulator.append(line)
    return '\n'.join(accumulator)


def make_time(time) -> datetime:
    """
    Convert xmlrpc DateTime objects to datetime.datetime
    """
    if isinstance(time, datetime):
        return time
    return datetime.strptime(time.value, "%Y%m%dT%H:%M:%S")


def TicketChange(changelog_entry):
    time, author, change, data1, data2, data3 = changelog_entry
    # print(time, author, change, data1, data2, data3)
    if change == 'comment':
        return TicketComment_class(time, author, change, data1, data2, data3)
    return TicketChange_class(time, author, change, data=(data1, data2, data3))


class TicketChange_class():

    def __init__(self, time, author: str, change, data=None):
        self._time = make_time(time)
        self._author = author
        self._change = change
        if data:
            self._data = data
        else:
            self._data = ('', '', 1)

    def get_data(self) -> str:
        try:
            return ' [' + str(self._data) + ']'
        except AttributeError:
            return ''

    @property
    def ctime(self):
        return self._time

    @property
    def ctime_str(self) -> str:
        return str(self.ctime)

    @property
    def author(self) -> str:
        return self._author

    @property
    def change(self):
        return self._change

    @property
    def change_capitalized(self):
        return self._change.capitalize()

    @property
    def old(self):
        return self._data[0]

    @property
    def new(self):
        return self._data[1]

    @property
    def change_action(self) -> str:
        if not self.old:
            return f'set to {self.new}'
        if not self.new:
            return f'{self.old} deleted'
        return f'changed from {self.old} to {self.new}'

    def __repr__(self) -> str:
        txt = self._author + ' changed ' + self._change
        txt += self.get_data()
        return txt


class TicketComment_class(TicketChange_class):

    def __init__(self, time, author: str, change, data1, data2, data3):
        TicketChange_class.__init__(self, time, author, change)
        self._number = data1
        self._comment = data2

    @property
    def number(self):
        return self._number

    @property
    def comment(self):
        return self._comment

    @property
    def comment_formatted(self) -> str:
        return format_trac(self.comment)

    def __repr__(self) -> str:
        return self.author + ' commented "' + \
            self.comment + '" [' + self.number + ']'


def TracTicket(ticket_number: int, server_proxy) -> TracTicket_class:
    ticket_number = int(ticket_number)
    try:
        change_log = server_proxy.ticket.changeLog(ticket_number)
    except ExpatError:
        print('Failed to parse the trac changelog, malformed XML!')
        change_log = []
    data = server_proxy.ticket.get(ticket_number)
    ticket_changes = [TicketChange(entry) for entry in change_log]
    return TracTicket_class(data[0], data[1], data[2], data[3], ticket_changes)


class TracTicket_class():

    def __init__(self, number: int, ctime, mtime, data, change_log=None):
        self._number = number
        self._ctime = make_time(ctime)
        self._mtime = make_time(mtime)
        self._last_viewed = None
        self._download_time = None
        self._data = data
        self._change_log = change_log

    @property
    def timestamp(self):
        """
        Timestamp for XML-RPC calls

        The timestamp is an integer that must be set in subsequent
        ticket.update() XMLRPC calls to trac.
        """
        return self._data['_ts']

    @property
    def number(self) -> int:
        return self._number

    __int__ = number

    @property
    def title(self) -> str:
        return self._data.get('summary', '<no summary>')

    @property
    def ctime(self):
        return self._ctime

    @property
    def mtime(self):
        return self._mtime

    @property
    def ctime_str(self) -> str:
        return str(self.ctime)

    @property
    def mtime_str(self) -> str:
        return str(self.mtime)

    @property
    def branch(self) -> str:
        return self._data.get('branch', '').strip()

    @property
    def dependencies(self) -> str:
        return self._data.get('dependencies', '')

    @property
    def description(self) -> str:
        default = '+++ no description +++'
        return self._data.get('description', default)

    @property
    def description_formatted(self):
        return format_trac(self.description)

    def change_iter(self) -> Iterator:
        for change in self._change_log:
            yield change

    def comment_iter(self) -> Iterator:
        for change in self._change_log:
            if isinstance(change, TicketComment_class):
                yield change

    def grouped_comment_iter(self):
        change_iter = iter(self._change_log)
        change = next(change_iter)

        def sort_key(c):
            return (-int(c.change == 'comment'), c.change)
        while True:
            stop = False
            time = change.ctime
            accumulator = [(sort_key(change), change)]
            while True:
                try:
                    change = next(change_iter)
                except StopIteration:
                    stop = True
                    break
                if change.ctime == time:
                    accumulator.append((sort_key(change), change))
                else:
                    break
            yield tuple(c[1] for c in sorted(accumulator))
            if stop:
                return

    @property
    def author(self):
        return self._data.get('author', '<no author>')

    @property
    def cc(self):
        return self._data.get('cc', '')

    @property
    def component(self):
        return self._data.get('component', '')

    @property
    def reviewer(self):
        return self._data.get('reviewer', '<no reviewer>')

    @property
    def reporter(self):
        return self._data.get('reporter', '<no reporter>')

    @property
    def milestone(self):
        return self._data.get('milestone', '<no milestone>')

    @property
    def owner(self):
        return self._data.get('owner', '<no owner>')

    @property
    def priority(self):
        return self._data.get('priority', '<no priority>')

    @property
    def commit(self):
        return self._data.get('commit', '')

    @property
    def keywords(self):
        return self._data.get('keywords', '')

    @property
    def ticket_type(self):
        return self._data.get('type', '<no type>')

    @property
    def upstream(self):
        return self._data.get('upstream', '<no upstream status>')

    @property
    def status(self):
        return self._data.get('status', '<no status>')

    @property
    def resolution(self):
        return self._data.get('resolution', '<no resolution>')

    @property
    def work_issues(self):
        return self._data.get('work_issues', '')
