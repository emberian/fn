"""Web S: an independent finite face, the live Exercise run against it, and mutation controls.

FakeFace never calls WebModel, NntpModel or framing: it keeps its own accounts, sessions (each with a
pinned copy of the article table, refreshed where the face selects a group or its own post lands),
CSRF and pre tokens, and renders its own pages in fn1's observed markup. These are model controls,
not live conformance evidence.
"""
import fnmatch
import re
import secrets
import unittest
from unittest.mock import patch
from urllib.parse import parse_qsl, quote, unquote

from fn2.tests.surface.web.test_model_web import Exercise, machine

CSP = "default-src 'none'; style-src 'self'"
GET = {'/', '/a', '/g', '/health', '/new', '/redeem', '/remove', '/signin', '/style.css'}
POST = {'/post', '/redeem', '/remove', '/signin', '/signout', '/theme'}
SESSION = {'/', '/a', '/g', '/new', '/post', '/remove', '/signout'}


def esc(text):
    return (text.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
            .replace('"', '&quot;').replace("'", '&#39;'))


class FakeFace:
    adjudication_target = 'fake'

    def __init__(self, case=None, plant=None):
        self.plant = plant
        self.groups = {'hz.web': [], 'hz.other': [], 'control.cancel': []}   # [number, id, author, subj, body, gone]
        self.high = dict.fromkeys(self.groups, 0)
        self.accounts, self.access_rules, self.codes = {}, {}, set()
        self.sessions, self.pres, self.jars = {}, set(), {}
        self.serial = 0

    # Fixture verbs, as the operator CLI.
    def invite(self):
        code = secrets.token_hex(16)
        self.codes.add(code)
        return code

    def access(self, login, read, post):
        self.access_rules[login] = (read, post)
        return 0

    def allowed(self, rules, login, group, kind):
        if self.plant == 'access-ignored':
            return True
        patterns = rules.get(login, ('*', '*'))[kind]
        ok = False
        for part in patterns.split(','):
            if fnmatch.fnmatchcase(group, part.lstrip('!')):
                ok = not part.startswith('!')
        return ok

    def snapshot(self):
        return {g: [list(row) for row in rows] for g, rows in self.groups.items()}, dict(self.access_rules)

    def view(self, session, group=None):
        rows, rules = session['pin']
        return {g: [r for r in rows[g] if not r[5]] for g in rows if self.allowed(rules, session['login'], g, 0)}

    def repin(self, session, group):
        pin = self.snapshot()
        rows, rules = pin
        if group in rows and self.allowed(rules, session['login'], group, 0):
            session['pin'] = pin

    # HTTP.
    def jar(self, browser):
        return self.jars.setdefault(browser, {})

    def send(self, browser, method, path, fields):
        jar = self.jar(browser)
        status, page, extra, cookies = self.answer(jar, method, path, dict(fields) if fields is not None else {})
        headers = {'Content-Security-Policy': CSP, 'Cache-Control': 'no-store', **extra}
        if status != 303 and 'Content-Type' not in headers:
            headers['Content-Type'] = 'text/html; charset=utf-8'
        for key, value in cookies.items():
            if value is None:
                jar.pop(key, None)
            else:
                jar[key] = value
        return dict(status=status, page='' if method == 'HEAD' else page, headers=headers)

    def frame(self, title, body, session=None):
        bar = f"<span>{esc(session['login'])}</span> <form><input type='hidden' name='csrf' value='{session['csrf']}'></form>" if session else ''
        return f"<html><head><title>{esc(title)}</title></head><body>{bar}<main id='main'>{body}</main></body></html>"

    def pre_page(self, jar, title, note='', status=200, nxt='/'):
        token = jar.get('fnr_pre') if jar.get('fnr_pre') in self.pres else secrets.token_hex(8)
        self.pres.add(token)
        session = self.sessions.get(jar.get('fnr_session'))
        body = f"<h1>{title}</h1>{note}<input type='hidden' name='pre' value='{token}'><input type='hidden' name='next' value='{esc(nxt)}'>"
        return status, self.frame(title, body, session), {}, {'fnr_pre': token}

    def answer(self, jar, method, path, form):
        route, _, query = path.partition('?')
        q = dict(parse_qsl(query))
        if method not in ('GET', 'HEAD', 'POST'):
            return 501, self.frame('Not implemented', '501 Not Implemented'), {}, {}
        if route not in GET | POST:
            return 404, self.frame('Not found', '<h1>Not found</h1>'), {}, {}
        if route not in (GET if method in ('GET', 'HEAD') else POST):
            return 405, self.frame('Method not allowed', ''), {'Allow': 'GET, HEAD' if route in GET else 'POST'}, {}
        if route == '/health':
            return 200, 'ready\n', {'Content-Type': 'text/plain; charset=utf-8', 'Content-Length': '6'}, {}
        if route == '/style.css':
            return 200, '/* --bar-bg */', {'Content-Type': 'text/css; charset=utf-8', 'Cache-Control': 'max-age=3600'}, {}
        if route == '/theme':
            return 303, '', {'Location': '/'}, {'fnr_theme': 'dark'}
        session = self.sessions.get(jar.get('fnr_session'))
        if route in SESSION and session is None:
            where = '/signin?next=' + quote(path, safe='') if method == 'GET' and route != '/' else '/signin'
            return 303, '', {'Location': where}, {}
        if route == '/signin':
            if method != 'POST':
                return self.pre_page(jar, 'Sign in', nxt=q.get('next', '/'))
            if form.get('pre') not in self.pres or form.get('pre') != jar.get('fnr_pre'):
                return self.pre_page(jar, 'Sign in', status=400)
            login = form.get('user', '')
            if not login or self.accounts.get(login) != form.get('password'):
                return self.pre_page(jar, 'Sign in', '<p>That name and password don&#39;t match.</p>', 401)
            return self.begin(login, form.get('next', '/'))
        if route == '/redeem':
            if method != 'POST':
                return self.pre_page(jar, 'Make your account')
            if (form.get('pre') != jar.get('fnr_pre') or not all(form.get(k) for k in ('code', 'user', 'password'))
                    or form['password'] != form.get('again')):
                return self.pre_page(jar, 'Make your account', status=400)
            if form['code'] not in self.codes or form['user'] in self.accounts:
                return self.pre_page(jar, 'Make your account', '<p>That code didn&#39;t work.</p>', 403)
            self.codes.discard(form['code'])
            self.accounts[form['user']] = form['password']
            return self.begin(form['user'], '/')
        if method == 'POST' and (form.get('csrf') != session['csrf'] and self.plant != 'csrf-unchecked'):
            return 403, self.frame('Not allowed', '<h1>Not allowed</h1>', session), {}, {}
        handler = getattr(self, 'route_' + (route.strip('/') or 'groups'))
        return handler(session, method, q, form)

    def begin(self, login, nxt):
        token = secrets.token_hex(12)
        self.sessions[token] = dict(login=login, csrf=secrets.token_hex(8), pin=self.snapshot())
        where = nxt if nxt.startswith('/') and not nxt.startswith('//') else '/'
        return 303, '', {'Location': where}, {'fnr_session': token, 'fnr_pre': None}

    def route_groups(self, session, method, q, form):
        view = self.view(session)
        rows = ''.join(f"<tr><td class='num'>{len(rows)}</td><td><a class='title' href='/g?name={g}'>{g}</a></td></tr>"
                       for g, rows in view.items())
        if self.plant == 'hidden-listed':
            rows += "<tr><td class='num'>0</td><td><a class='title' href='/g?name=hz.other'>hz.other</a></td></tr>"
        return 200, self.frame('Groups', '<h1>Groups</h1><table>' + rows + '</table>', session), {}, {}

    def route_g(self, session, method, q, form):
        self.repin(session, q.get('name'))
        view = self.view(session)
        if q.get('name') not in view:
            return 404, self.frame('No such group', '<h1>No such group</h1>', session), {}, {}
        rows = ''.join(f"<tr><td>{r[0]}</td><td><a class='title' href='/a?g={q['name']}&amp;n={r[0]}'>{esc(r[3])}</a></td></tr>"
                       for r in reversed(view[q['name']]))
        return 200, self.frame(q['name'], '<table>' + rows + '</table>', session), {}, {}

    def route_a(self, session, method, q, form):
        self.repin(session, q.get('g'))
        row = next((r for r in self.view(session).get(q.get('g'), ()) if str(r[0]) == q.get('n')), None)
        if row is None:
            return 404, self.frame('Not here', '<h1>Not here</h1>', session), {}, {}
        body = row[4] if self.plant == 'unescaped' else esc(row[4])
        own = row[2] == session['login'] or self.plant == 'remove-link-everyone'
        link = f"<a href='/remove?g={q['g']}&amp;id={quote(row[1], safe='')}'>Remove my post</a>" if own else ''
        text = (f"<h1>{esc(row[3])}</h1><pre>From: {esc(row[2])} &lt;{esc(row[2])}@friends.invalid&gt;</pre>"
                f"<pre class='body'>{body}</pre>{link}")
        return 200, self.frame(row[3], text, session), {}, {}

    def route_new(self, session, method, q, form):
        if 'g' not in q:
            return 404, self.frame('Post', '<h1>Post</h1>', session), {}, {}
        return 200, self.frame('Post', f"<h1>Post to {esc(q['g'])}</h1>", session), {}, {}

    def route_post(self, session, method, q, form):
        if not form.get('subject') or not form.get('body'):
            return 400, self.frame('Post', '<h1>Post to ' + esc(form.get('g', '')) + '</h1>', session), {}, {}
        g = form['g']
        rows, rules = session['pin']
        if g not in self.groups or not self.allowed(rules, session['login'], g, 1):
            return 403, self.frame('Not posted', "<p>The server said no.</p><p class='said dim'>441 posting failed; a named newsgroup is not carried here</p>", session), {}, {}
        self.add(g, f'<fake-{self.serial}@fake.invalid>', session['login'], form['subject'], form['body'])
        session['pin'] = self.snapshot()
        return 200, self.frame('Posted!', '<h1>Posted!</h1>', session), {}, {}

    def add(self, group, ident, author, subject, body):
        self.serial += 1
        self.high[group] += 1
        self.groups[group].append([self.high[group], ident, author, subject, body, False])

    def route_remove(self, session, method, q, form):
        if method != 'POST':
            if 'id' not in q:
                return 404, self.frame('Not here', '<h1>Not here</h1>', session), {}, {}
            return 200, self.frame('Remove my post', f"<input type='hidden' name='id' value='{esc(q['id'])}'>", session), {}, {}
        row = next(r for rows in self.groups.values() for r in rows if r[1] == form.get('id'))
        self.add('control.cancel', f'<fake-cancel-{self.serial}@fake.invalid>', session['login'], 'cmsg', 'x')
        if row[2] == session['login'] or self.plant == 'remove-any':
            row[5] = True
        session['pin'] = self.snapshot()
        text = 'Your post has been removed' if row[5] else 'Still there'
        return 200, self.frame(text, '<h1>' + text + '</h1>', session), {}, {}

    def route_signout(self, session, method, q, form):
        if self.plant != 'signout-keeps-session':
            self.sessions = {k: v for k, v in self.sessions.items() if v is not session}
        return 303, '', {'Location': '/signin'}, {'fnr_session': None}


class WebTests(unittest.TestCase):
    def test_fixed_witnesses(self):
        e = Exercise(self, FakeFace())
        e.witnesses()
        self.assertGreaterEqual(len(e.trace), 130)
        self.assertEqual({p.group for p in e.model.posts}, {'hz.web', 'hz.other'})

    def test_generated_interleavings(self):
        from hypothesis import settings
        from hypothesis.stateful import run_state_machine_as_test
        run_state_machine_as_test(machine(self, FakeFace), settings=settings(
            max_examples=40, stateful_step_count=30, deadline=None, database=None, derandomize=True))

    def test_mutation_controls(self):
        for plant in ('access-ignored', 'hidden-listed', 'csrf-unchecked', 'unescaped',
                      'remove-link-everyone', 'remove-any', 'signout-keeps-session'):
            with self.subTest(plant=plant):
                e = Exercise(self, FakeFace(plant=plant))
                with patch('fn2.tests.surface.web.test_model_web.record_failure') as record:
                    with self.assertRaises(AssertionError):
                        e.witnesses()
                    self.assertTrue(record.called)

    def test_pinned_counts_follow_selection(self):
        # Another session's post reaches a session's groups page only after it selects the group.
        e = Exercise(self, FakeFace())
        e.account('a', 'wren')
        e.account('b', 'robin', 'other-fixture-password')
        e.request('a', 'GET', '/')
        e.request('b', 'GET', '/')                  # b's CSRF token
        e.post('b', 'hz.web', 'From robin', 'hello')
        e.request('a', 'GET', '/')                  # still 0 for hz.web: pinned
        e.request('a', 'GET', '/g?name=hz.web')     # GROUP re-pins
        page = e.request('a', 'GET', '/')['page']
        self.assertIn("<td class='num'>1</td><td><a class='title' href='/g?name=hz.web'>", page)

    def test_password_never_on_a_page(self):
        class Leaky(FakeFace):
            def route_groups(self, session, method, q, form):
                status, page, h, c = super().route_groups(session, method, q, form)
                return status, page + self.accounts[session['login']], h, c
        e = Exercise(self, Leaky())
        with patch('fn2.tests.surface.web.test_model_web.record_failure'):
            with self.assertRaises(AssertionError):
                e.witnesses()


if __name__ == '__main__':
    unittest.main()
