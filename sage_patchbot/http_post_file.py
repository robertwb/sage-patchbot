"""
reference:

https://code.activestate.com/recipes/146306-http-client-to-post-using-multipartform-data/
"""
from urllib.request import urlopen, Request

import mimetypes
import string
import random


def id_generator(size=26, chars=string.ascii_uppercase + string.digits) -> str:
    """
    substitute for mimetools.choose_boundary()
    """
    return ''.join(random.choice(chars) for _ in range(size))


def post_multipart(url, fields, files):
    """
    Post fields and files to an http host as multipart/form-data.
    fields is a sequence of (name, value) elements for regular form
    fields.  files is a sequence of (name, filename, value) elements
    for data to be uploaded as files

    Return the server's response page.
    """
    content_type, body = encode_multipart_formdata(fields, files)
    headers = {'Content-Type': content_type,
               'Content-Length': str(len(body))}
    r = Request(url, body, headers)
    return urlopen(r).read().decode('utf-8')


def by(utf_string: str) -> bytes:
    """
    py2: takes a unicode object and return a str object
    py3: takes a str object and return a bytes object
    """
    return utf_string.encode('utf8')


def encode_multipart_formdata(fields, files):
    """
    fields is a sequence of (name, value) elements for regular form
    fields.  files is a sequence of (name, filename, value) elements
    for data to be uploaded as files

    Return (content_type, body) ready for httplib.HTTP instance

    EXAMPLES::

        In [2]: encode_multipart_formdata([],[])
        Out[2]:
        ('multipart/form-data; boundary=JPS2ZAVEEIQZW6K5JVQB1IJE2W',
         '--JPS2ZAVEEIQZW6K5JVQB1IJE2W--\r\n')
    """
    # BOUNDARY = mimetools.choose_boundary()
    UTF_BOUNDARY = id_generator()
    BOUNDARY = by(UTF_BOUNDARY)
    CRLF = by('\r\n')
    dd = by('--')
    L = []
    if isinstance(fields, dict):
        fields = fields.items()
    for (key, value) in fields:
        L.append(dd + BOUNDARY)
        L.append(by(f'Content-Disposition: form-data; name="{key}"'))
        L.append(by(''))
        L.append(by(value))
    for (key, filename, value) in files:
        L.append(dd + BOUNDARY)
        cont = f'Content-Disposition: form-data; name="{key}"; filename="{filename}"'
        L.append(by(cont))
        L.append(by(f'Content-Type: {get_content_type(filename)}'))
        L.append(by(''))
        L.append(value)   # here are bytes ??
    L.append(dd + BOUNDARY + dd)
    L.append(by(''))
    body: bytes = CRLF.join(L)
    content_type = f'multipart/form-data; boundary={UTF_BOUNDARY}'
    return content_type, body


def get_content_type(filename: str) -> str:
    return mimetypes.guess_type(filename)[0] or 'application/octet-stream'
