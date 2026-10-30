"""Web S: the node's own web face as a translator of the one NNTP model.

SPEC-MAP
 decision / effect                                  source
 the face decides nothing: sign-in is AUTHINFO on    specs/human-client.md:137-156 (WEB-003),
   the session's connection (281 session, 481        161-205 (WEB-005)
   "don't match"); an account is XREDEEM; a post is
   the served POST; a removal is the cancel, then
   STAT (430 removed, 223 still there)
 a session reads what its login reads (access rules) WEB-003 (NNT-046 hides a group as absent)
 pages escape every octet from a reply or form;      WEB-005; docs/web.md:135-150
   CSP default-src 'none'; no page carries a password
 GET/HEAD /health 200 `ready\n`, text/plain,         WEB-005 Q10d; docs/web.md:157-175
   no-store; HEAD keeps Content-Length 6, no body
 15 routes on 12 paths; HEAD on every GET route;     RELEASE-PLAN §1 rows 92-97;
   404 / 405 with Allow; 501 for other methods       books/web-request.lisp (fn1)
 sessions end at sign-out (cookie cleared, the old   WEB-005 (session table node-local)
   token refused)
 Where the docs name no status or redirect, the model carries fn1's (HZ2 web probe, hbox image
 c14e9e8e, build/coordinator/fn2/lanes/h-quests/webprobe.json): a signed-out GET of a session page is
 303 to /signin?next=<the path and query> (`/` and HEAD: plain /signin; POST: /signin); a form without
 its fnr_pre token, or a redeem whose passwords differ, is 400; a signed-in POST without the session's
 CSRF token is 403; an empty subject or body is 400; a refused POST is 403 "The server said no"; a bad
 invitation code is 403 "didn't work"; signed in, /a, /g, /new and /remove without their parameters
 and a group or post the login cannot read are 404; /new?g=G is 200 for any G (the node decides at
 POST); POST /theme is 303 / signed in or out. The page markup read here (the groups table's count
 cell and `/g?name=` links, the group table's `/a?g=&n=` links, the article's <h1> and body <pre>) is
 fn1's layout, the layout fn2 keeps.

Profile: <=3 logins, <=12 posts, two browsers, one group set; plain HTTP on loopback; every request
is one connection. A removal targets a post on the page, never a forged id. "We couldn't tell"
(503, an uncertain submission) is not reachable in this profile and fails the run if seen.
"""
from dataclasses import dataclass
import html
import re
from urllib.parse import quote

from . import framing
from .nntp_model import NntpModel

GROUPS = ('hz.web', 'hz.other', 'control.cancel')
DOMAIN = 'friends.invalid'
SESSION_PATHS = ('/', '/a', '/g', '/new', '/post', '/remove', '/signout')
GET_PATHS = ('/', '/a', '/g', '/health', '/new', '/redeem', '/remove', '/signin', '/style.css')
POST_PATHS = ('/post', '/redeem', '/remove', '/signin', '/signout', '/theme')
PATHS = tuple(sorted(set(GET_PATHS) | set(POST_PATHS)))
ADJUDICATIONS = ()  # W01 (fn2/docs/h-harness.md) is outside this profile: access never changes under an open session.


@dataclass
class Browser:
    """What one browser holds: its cookies' meaning, never their values."""
    name: str
    login: str | None = None
    pre: bool = False          # holds a live fnr_pre from a sign-in/redeem page
    csrf: str | None = None    # the session's CSRF token, once a page carried it
    conn: object = None        # the session's own reader connection (NntpModel Conn)


@dataclass(frozen=True)
class Request:
    browser: str
    method: str
    path: str                  # with its query
    fields: tuple | None = None
    csrf: str = 'none'         # none | session | wrong (POST forms behind a session)
    pre: bool = True           # send the form's fnr_pre (sign-in/redeem forms)

    @property
    def route(self):
        return self.path.partition('?')[0]

    @property
    def query(self):
        out = {}
        for part in self.path.partition('?')[2].split('&'):
            if part:
                key, _, value = part.partition('=')
                out[key] = value
        return out

    def form(self):
        return dict(self.fields or ())


@dataclass
class Post:
    group: str
    number: int
    ident: str
    author: str
    subject: str
    body: str
    removed: bool = False


class Expect:
    """One request's predicate; update commits only what the reply showed."""

    def __init__(self, model, request, status, *, location=None, allow=None, page=(), absent=(),
                 kind='html', effect=None, outcome=None):
        self.model, self.request = model, request
        self.status, self.location, self.allow = status, location, allow
        self.page, self.absent, self.kind, self.effect, self.outcome = page, absent, kind, effect, outcome

    def check(self, reply):
        r, status = self.request, reply['status']
        allowed = self.status if isinstance(self.status, tuple) else (self.status,)
        if status not in allowed:
            return f'{r.method} {r.path}: status {status}, expected {allowed}'
        headers = reply['headers']
        if 'default-src \'none\'' not in headers.get('Content-Security-Policy', ''):
            return 'Content-Security-Policy default-src \'none\' missing'
        if self.location is not None and headers.get('Location') != self.location:
            return f'Location {headers.get("Location")!r}, expected {self.location!r}'
        if self.allow is not None and headers.get('Allow') != self.allow:
            return f'Allow {headers.get("Allow")!r}, expected {self.allow!r}'
        page = reply['page']
        for login, account in self.model.nntp.accounts.items():
            if account['password'] in page:
                return 'a page carried a password'
        if r.method == 'HEAD':
            if page:
                return 'HEAD carried a body'
            return None
        if self.kind == 'health':
            if (page, headers.get('Content-Type'), headers.get('Cache-Control')) != (
                    'ready\n', 'text/plain; charset=utf-8', 'no-store'):
                return 'health: ready, text/plain, no-store'
        elif self.kind == 'css':
            if not headers.get('Content-Type', '').startswith('text/css'):
                return 'style sheet content type'
        elif status not in (303,) and not headers.get('Content-Type', '').startswith('text/html'):
            return 'pages are text/html'
        outcome = self.outcome(page) if self.outcome else None
        wants = self.page(outcome) if callable(self.page) else self.page
        for text in wants:
            if (text.search(page) is None) if hasattr(text, 'search') else text not in page:
                return f'{r.method} {r.path}: page lacks {getattr(text, "pattern", text)!r}'
        for text in self.absent:
            if text in page:
                return f'{r.method} {r.path}: page shows {text!r}'
        return None

    def update(self, reply):
        problem = self.check(reply)
        if problem:
            raise AssertionError(problem)
        if self.effect:
            self.effect(reply)


def escaped(text):
    """The renderer's escapes for the characters the profile generates."""
    return text.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')


class WebModel:
    def __init__(self, groups=GROUPS, target='fake'):
        self.target = target
        self.nntp = NntpModel({g: {} for g in groups}, [], {}, {'posting': True, 'stored_articles': {}})
        self.browsers = {}
        self.pending = []           # invitation codes the fixture minted
        self.posts = []
        self.serial = 0

    def browser(self, name):
        return self.browsers.setdefault(name, Browser(name))

    # The one NNTP oracle. A session is one reader connection, signed in by its
    # AUTHINFO (WEB-003/005); it pins its view and listing as any connection does
    # and re-pins at GROUP (specs/nntp.md:465-475, 1938-1945): the groups page is
    # LIST ACTIVE on the pinned view, a group or article page selects the group.
    def connect(self, login):
        conn = self.nntp.connect(tls=True, implicit_tls=False)
        for command, code in ((b'AUTHINFO USER ' + login.encode(), 381),
                              (b'AUTHINFO PASS ' + self.nntp.accounts[login]['password'].encode(), 281)):
            self.commit(conn.send(command + b'\r\n'), code)
        return conn

    @staticmethod
    def commit(expected, code, text=b'web'):
        """Commit the reply code the face's page showed (or the one permitted)."""
        status = b'%d %s\r\n' % (code, text)
        verdict = expected.check(status, None)
        if not verdict.ok:
            raise AssertionError(('nntp', code, verdict))
        expected.update(status, None)

    def authinfo(self, login, password):
        """The code the node's AUTHINFO answers (281 or 481): NntpModel decides."""
        if login not in self.nntp.accounts:
            return 481
        conn = self.nntp.connect(tls=True, implicit_tls=False)
        try:
            self.commit(conn.send(b'AUTHINFO USER ' + login.encode() + b'\r\n'), 381)
            permitted = sorted(conn.send(b'AUTHINFO PASS ' + password.encode() + b'\r\n')._get().codes)
        finally:
            conn.quit = True
        if len(permitted) != 1:
            raise AssertionError(('AUTHINFO not determined by the model', permitted))
        return permitted[0]

    def begin(self, b, login):
        self.end(b)
        b.login, b.pre, b.csrf, b.conn = login, False, None, self.connect(login)

    @staticmethod
    def end(b):
        if b.conn is not None:
            b.conn.quit = True
        b.login, b.csrf, b.conn = None, None, None

    @staticmethod
    def served(b, select=None):
        """The groups B's connection is served and each one's readable numbers;
        SELECT re-pins first, as GROUP does."""
        conn = b.conn
        if select is not None:
            # A failed selection keeps the connection's pin
            # (fn-served-failed-selection-keeps-the-connection).
            kept = (conn.pinned_version, conn.view_groups, conn.view_articles, conn.view_withdrawn,
                    conn.view_watermarks, conn.view_flags, conn.view_stamps)
            conn._pin()
            if not conn._visible(select):
                conn._pin(kept)
        return {g: [n for n, _ in conn._available(g)] for g in conn.view_groups if conn._visible(g)}

    def visible(self, login):
        """What a fresh connection of LOGIN reads (the fixture's own bookkeeping)."""
        conn = self.connect(login)
        try:
            return {g: [n for n, _ in conn._available(g, live=True)]
                    for g in self.nntp.groups if conn._visible(g, live=True)}
        finally:
            conn.quit = True

    # Expectations, one request at a time.
    def rule(self, r):
        b, route, method = self.browser(r.browser), r.route, r.method
        if method not in ('GET', 'HEAD', 'POST'):
            return Expect(self, r, 501)
        if route not in PATHS:
            return Expect(self, r, 404, page=('Not found',))
        allowed = (GET_PATHS if method in ('GET', 'HEAD') else POST_PATHS)
        if route not in allowed:
            return Expect(self, r, 405, allow='GET, HEAD' if route in GET_PATHS else 'POST')
        if route == '/health':
            return Expect(self, r, 200, kind='health')
        if route == '/style.css':
            return Expect(self, r, 200, kind='css')
        if route == '/theme':
            return Expect(self, r, 303, location='/')
        if route in SESSION_PATHS and b.login is None:
            if method == 'GET' and route != '/':
                where = '/signin?next=' + quote(r.path, safe='')
            else:
                where = '/signin'
            return Expect(self, r, 303, location=where)
        if route == '/signin':
            return self.signin(r, b)
        if route == '/redeem':
            return self.redeem(r, b)
        if method == 'POST' and (r.csrf != 'session' or b.csrf is None):
            # The session's CSRF token is on its pages; before one is read the
            # browser has none to send.
            return Expect(self, r, 403, page=('Not allowed',))
        return getattr(self, 'page_' + route.strip('/') if route != '/' else 'page_groups')(r, b)

    @staticmethod
    def offer_pre(b, r):
        """Every sign-in/redeem answer carries fnr_pre (the same token while the
        browser presents a live one); a page also carries its form field. HEAD
        carries no field, so it changes nothing the browser can send."""
        def effect(reply):
            if r.method != 'HEAD':
                b.pre = True
        return effect

    def signin(self, r, b):
        if r.method != 'POST':
            return Expect(self, r, 200, page=('Sign in',), effect=self.offer_pre(b, r))
        if not (r.pre and b.pre):
            return Expect(self, r, 400, page=('Sign in',), effect=self.offer_pre(b, r))
        form = r.form()
        # fn1: an empty name or password is the node's refusal page (401).
        code = self.authinfo(form['user'], form['password']) if form.get('user') and form.get('password') else 481
        if code == 481:
            return Expect(self, r, 401, page=('don&#39;t match',), effect=self.offer_pre(b, r))
        nxt = form.get('next', '/')
        where = nxt if nxt.startswith('/') and not nxt.startswith('//') else '/'
        return Expect(self, r, 303, location=where, effect=lambda reply: self.begin(b, form['user']))

    def redeem(self, r, b):
        if r.method != 'POST':
            return Expect(self, r, 200, page=('Make your account',), effect=self.offer_pre(b, r))
        form = r.form()
        if (not (r.pre and b.pre) or any(not form.get(k) for k in ('code', 'user', 'password'))
                or form['password'] != form.get('again')):
            return Expect(self, r, 400, page=('Make your account',), effect=self.offer_pre(b, r))
        if form['code'] not in self.pending or form['user'] in self.nntp.accounts:
            return Expect(self, r, 403, page=('didn&#39;t work',), effect=self.offer_pre(b, r))
        def effect(reply):
            self.pending.remove(form['code'])
            self.nntp.accounts[form['user']] = {'password': form['password'], 'posting': True}
            self.begin(b, form['user'])
        return Expect(self, r, 303, location='/', effect=effect)

    def page_groups(self, r, b):
        groups = self.served(b)
        rows = [re.compile(r"<td class='num'>%d</td><td><a class='title' href='/g\?name=%s'>"
                           % (len(numbers), re.escape(g))) for g, numbers in groups.items()]
        hidden = [f"href='/g?name={g}'" for g in self.nntp.groups if g not in groups]
        return Expect(self, r, 200, page=['<span>' + b.login + '</span>', *rows], absent=hidden)

    def page_g(self, r, b):
        name = r.query.get('name')
        groups = self.served(b, select=name)
        if name not in groups:
            return Expect(self, r, 404, page=('No such group',))
        listed = set(groups[name])
        rows, absent = [], []
        for p in self.posts:
            if p.group == name:
                link = f"href='/a?g={name}&amp;n={p.number}'>"
                if p.number in listed:
                    rows.append(link + escaped(p.subject))
                else:
                    absent.append(link)
        return Expect(self, r, 200, page=rows, absent=absent)

    def page_a(self, r, b):
        q = r.query
        groups = self.served(b, select=q.get('g'))
        post = next((p for p in self.posts if p.group == q.get('g') and str(p.number) == q.get('n')), None)
        if post is None or post.number not in groups.get(post.group, ()):
            return Expect(self, r, 404, page=('Not here',))
        wants = ['<h1>' + escaped(post.subject) + '</h1>', escaped(post.body),
                 f'{post.author} &lt;{post.author}@{DOMAIN}&gt;']
        own = post.author == b.login
        return Expect(self, r, 200, page=wants + (['Remove my post'] if own else []),
                      absent=() if own else ('Remove my post',))

    def page_new(self, r, b):
        if 'g' not in r.query:
            return Expect(self, r, 404)
        return Expect(self, r, 200, page=('Post to ' + r.query['g'],))

    def page_remove(self, r, b):
        if r.method != 'POST':
            if 'id' not in r.query:
                return Expect(self, r, 404, page=('Not here',))
            return Expect(self, r, 200, page=('Remove my post',))
        post = next(p for p in self.posts if p.ident == r.form()['id'])
        withdraws = post.author == b.login or post.removed
        # The face's cancel is a served POST under the session's own access, naming the post's group (nightly
        # 2026-10-30: fn1 answers 441 "a named newsgroup is not carried here" to a login removing a post in a
        # group it cannot post to): the session's read and post rules decide, as for any POST.
        if not (b.conn._visible(post.group) and b.conn._access(post.group, 'post')):
            return Expect(self, r, 403, page=('The server said no',))
        def effect(reply):
            # The face's cancel is a served POST into control.cancel either way;
            # only the author's withdraws (SEC-006). The session's own accepted
            # POST re-pins it, so its STAT reads 430 for a withdrawn post.
            self.serial += 1
            self.nntp.add_article(f'<web-cancel-{self.serial}@model.invalid>', b'\r\n', ['control.cancel'])
            if post.author == b.login and not post.removed:
                post.removed = True
                self.nntp.withdraw(post.ident)
            b.conn._pin()
        page = ('Your post has been removed',) if withdraws else ('Still there',)
        return Expect(self, r, 200, page=page, effect=effect)

    def page_post(self, r, b):
        form = r.form()
        if not form.get('subject') or not form.get('body'):
            return Expect(self, r, 400, page=('Post to',))
        self.serial += 1
        ident = f'<web-{self.serial}@model.invalid>'
        source = (f'From: {b.login} <{b.login}@{DOMAIN}>\r\nNewsgroups: {form["g"]}\r\n'
                  f'Subject: {form["subject"]}\r\nMessage-ID: {ident}\r\n'
                  f'Date: Thu, 29 Oct 2026 12:00:00 +0000\r\n\r\n{form["body"]}\r\n').encode()
        # The session connection copied the policy when it opened: give it the
        # read-back projection the served POST's effect needs.
        b.conn.policy['stored_articles'][ident] = source
        self.nntp.policy['stored_articles'][ident] = source
        conn = b.conn
        first = conn.send(b'POST\r\n')
        if 340 not in first._get().codes:
            codes, block = {441}, None
            self.commit(first, 440)
        else:
            self.commit(first, 340)
            block = conn.send_block(framing.encode_block(source))
            codes = set(block._get().codes)
        def outcome(page):
            return 240 if 'Posted!' in page else 441 if 'The server said no' in page else None
        status = tuple(sorted({240: 200, 441: 403}[c] for c in codes if c in (240, 441)))
        def effect(reply):
            code = outcome(reply['page'])
            if code not in codes:
                raise AssertionError(('post outcome', code, codes))
            if block is not None:
                said = re.search(r"<p class='said dim'>(\d{3}) ([^<]*)</p>", reply['page'])
                text = html.unescape(said.group(2)).encode() if said and int(said.group(1)) == code else b'web'
                self.commit(block, code, text)
            if code == 240:
                number = dict((m, n) for n, m in self.nntp.groups[form['g']])[ident]
                self.posts.append(Post(form['g'], number, ident, b.login, form['subject'], form['body']))
        def page(code):
            return {240: ('Posted!',), 441: ('The server said no',)}.get(code, ('Posted! or The server said no',))
        return Expect(self, r, status, page=page, outcome=outcome, effect=effect)

    def page_signout(self, r, b):
        return Expect(self, r, 303, location='/signin', effect=lambda reply: self.end(b))
