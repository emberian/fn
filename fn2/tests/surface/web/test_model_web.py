"""Web S: fixed witnesses over every route and the friend's flows, then 30 generated steps.

One fresh node per example (the developer image, FN_NATIVE_DEVELOPER_HOST: its [web] face), STORE_INIT,
loopback only, plain HTTP. Every HTTP request is one connection with a 10 s timeout and a 256 KiB page
bound; CLI calls 10 s (init/start 60 s). Two browsers, <=3 logins, <=12 posts. These are test-work
bounds, not product ceilings; the enclosing surface child supplies the hard wall bound.
"""
from contextlib import ExitStack
import html
import http.client
import os
import re
import unittest
from urllib.parse import urlencode

from fn2.tests.model.limits_model import STORE_INIT
from fn2.tests.model.web_model import DOMAIN, GROUPS, PATHS, Request, WebModel
from fn2.tests.surface import SurfaceCase, owned_ports, serving
from fn2.tests.surface.live_evidence import capture_step, json_value, record_failure, run_live_machine

PASSWORD = 'web-fixture-password-1'  # FAKE-SECRET
OTHER_PASSWORD = 'web-fixture-password-2'  # FAKE-SECRET
KEEP = ('Location', 'Allow', 'Content-Type', 'Content-Security-Policy', 'Cache-Control', 'Content-Length')
PAGE_BOUND = 262144


def form_value(page, name):
    found = re.search(r"name='%s' value='([^']*)'" % name, page)
    return html.unescape(found.group(1)) if found else None


class WebTarget:
    @owned_ports
    def __init__(self, case):
        from tests.native_harness import EXIT, Node, free_port, native_image
        self.adjudication_target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
        self.node = node = Node(case, native_image('FN_NATIVE_DEVELOPER_HOST'), name='web-s')
        node.use_tls(alt_name=True, protected_only=False)
        self.port = free_port()
        node.write_config(extra=(
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n\n[auth]\nrequired = true\nprotected_only = true\n\n'
            '[web]\nport = {}\nsite = "Surface news"\ndomain = "{}"\n').format(
                node.tls_port, node.cert, node.root / 'key.pem', self.port, DOMAIN))
        flags = [w for k, v in STORE_INIT.items() for w in ('--' + k, str(v))]
        node.operator('init', '--profile', 'development', *flags, *GROUPS, timeout=60, expect=EXIT.OK)
        node.listening = 3
        node.start(timeout=60)
        self.cookies = {}

    def invite(self):
        from tests.native_harness import EXIT
        out = self.node.operator('account', 'invite', '--expires', '3600', timeout=10, expect=EXIT.OK).stdout
        return re.findall(rb'^[0-9a-f]{32}$', out, re.M)[0].decode()

    def access(self, login, read, post):
        result = self.node.operator('account', 'access', login, '--read', read, '--post', post, timeout=10)
        return result.returncode

    def jar(self, browser):
        return self.cookies.setdefault(browser, {})

    def send(self, browser, method, path, fields):
        jar = self.jar(browser)
        host = '127.0.0.1:%d' % self.port
        headers = {'Host': host}
        if jar:
            headers['Cookie'] = '; '.join('%s=%s' % kv for kv in jar.items())
        body = None
        if fields is not None:
            body = urlencode(fields)
            headers['Content-Type'] = 'application/x-www-form-urlencoded'
            headers['Origin'] = 'http://' + host
        conn = http.client.HTTPConnection('127.0.0.1', self.port, timeout=10)
        try:
            conn.request(method, path, body=body, headers=headers)
            reply = conn.getresponse()
            data = reply.read(PAGE_BOUND + 1)
            if len(data) > PAGE_BOUND:
                raise AssertionError('web fixture page bound exceeded')
            cookies = reply.msg.get_all('Set-Cookie') or []
            out = dict(status=reply.status, page=data.decode('utf-8'),
                       headers={k: reply.getheader(k) for k in KEEP if reply.getheader(k) is not None})
        finally:
            conn.close()
        for value in cookies:
            key, _, rest = value.partition('=')
            if 'Max-Age=0' in value:
                jar.pop(key, None)
            else:
                jar[key] = rest.split(';')[0]
        return out


class Exercise:
    def __init__(self, case, target, trace=None):
        self.case, self.target = case, target
        self.model = WebModel(target=getattr(target, 'adjudication_target', 'fake'))
        self.trace = trace if trace is not None else []
        self.tokens = {}            # browser -> {'pre': ..., 'csrf': ...} as last read
        self.ids = {}               # model ident -> the node's Message-ID, read off the author's page

    def require(self, good, *, rule, request, reply, detail):
        if not good:
            record_failure(self.case, 'web', rule=rule, request=request, reply=reply,
                           verdict=dict(ok=False, detail=detail), trace=self.trace)
        self.case.assertTrue(good, (detail, request, reply and reply.get('status')))

    @capture_step(None, 'web', request=lambda self, browser, method, path, *a, **kw: dict(browser=browser, method=method, path=path))
    def request(self, browser, method, path, fields=None, *, csrf='session', pre=True):
        r = Request(browser, method, path, tuple(sorted(fields.items())) if fields is not None else None,
                    csrf=csrf, pre=pre)
        expected = self.model.rule(r)
        sent = None
        if fields is not None:
            tokens = self.tokens.get(browser, {})
            sent = dict(fields)
            if 'id' in sent:
                sent['id'] = self.ids.get(sent['id'], sent['id'])
            if r.route in ('/signin', '/redeem'):
                if pre and tokens.get('pre'):
                    sent['pre'] = tokens['pre']
            elif csrf == 'session':
                sent['csrf'] = tokens.get('csrf') or ''
            elif csrf == 'wrong':
                sent['csrf'] = 'wrong'
        reply = self.target.send(browser, method, path, sent)
        self.trace.append(dict(request=r, reply=dict(status=reply['status'], headers=reply['headers'],
                                                     page=reply['page'][:2000])))
        problem = expected.check(reply)
        self.require(problem is None, rule=method + ' ' + r.route, request=r, reply=reply, detail=problem)
        expected.update(reply)
        tokens = self.tokens.setdefault(browser, {})
        for name in ('pre', 'csrf'):
            value = form_value(reply['page'], name)
            if value is not None:
                tokens[name] = value
        if self.model.browser(browser).login is None:
            tokens.pop('csrf', None)
        self.model.browser(browser).csrf = tokens.get('csrf')
        return reply

    def invite(self):
        code = self.target.invite()
        self.model.pending.append(code)
        return code

    def account(self, browser, login, password=PASSWORD):
        self.request(browser, 'GET', '/redeem')
        self.request(browser, 'POST', '/redeem', dict(code=self.invite(), user=login, password=password,
                                                       again=password))

    def post(self, browser, group, subject, body, **kw):
        before = len(self.model.posts)
        reply = self.request(browser, 'POST', '/post', dict(g=group, subject=subject, body=body), **kw)
        if len(self.model.posts) > before:
            # Read the node's Message-ID off the author's own page (its remove link).
            p = self.model.posts[-1]
            if p.number not in self.model.visible(p.author).get(p.group, ()):
                return reply  # the author cannot read it here, so it has no remove link
            page = self.request(browser, 'GET', f'/a?g={p.group}&n={p.number}')['page']
            found = re.search(r"href='/remove\?g=[^&']+&amp;id=([^']+)'>Remove my post", page)
            self.require(found is not None, rule='remove-link', request=p.ident, reply=None,
                         detail='the author sees a remove link')
            from urllib.parse import unquote
            self.ids[p.ident] = unquote(found.group(1))
        return reply

    def remove(self, browser, post, csrf='session'):
        node_id = self.ids[post.ident]
        from urllib.parse import quote
        self.request(browser, 'GET', f'/remove?g={post.group}&id={quote(node_id, safe="")}')
        self.request(browser, 'POST', '/remove', dict(id=post.ident, g=post.group), csrf=csrf)

    def matrix(self, browser, note):
        for path in PATHS + ('/nope',):
            for method in ('GET', 'HEAD', 'POST'):
                self.request(browser, method, path, {} if method == 'POST' else None, csrf='none')
        self.request(browser, 'PUT', '/', {}, csrf='none')

    def access(self, login, read, post):
        code = self.target.access(login, read, post)
        self.require(code == 0, rule='account access', request=(login, read, post), reply=None,
                     detail='fixture access rule')
        self.model.nntp.accounts[login].update(read=read, post=post)

    @capture_step(None, 'web')
    def witnesses(self):
        self.matrix('a', 'signed out')
        self.request('a', 'GET', '/g?name=hz.web')
        self.request('a', 'POST', '/signin', dict(user='x', password='y', next='/'), pre=False)
        self.request('a', 'GET', '/redeem')
        self.request('a', 'POST', '/redeem', dict(code=self.invite(), user='wren', password=PASSWORD,
                                                   again='mismatch-' + PASSWORD))
        self.request('a', 'POST', '/redeem', dict(code=self.model.pending[-1], user='wren',
                                                   password=PASSWORD, again=PASSWORD))
        self.matrix('a', 'signed in')
        self.request('a', 'GET', '/')
        self.request('a', 'GET', '/new?g=hz.web')
        self.post('a', 'hz.web', 'S0', 'b0', csrf='wrong')
        self.post('a', 'hz.web', 'First <&> post', 'body one <b>not bold</b> & more')
        self.post('a', 'hz.absent', 'S2', 'b2')
        self.post('a', 'hz.web', '', 'b3')
        self.post('a', 'hz.web', 'S4', '')
        self.post('a', 'hz.other', 'Second', 'two')
        for path in ('/', '/g?name=hz.web', '/g?name=hz.absent', '/g?name=hz.other',
                     '/a?g=hz.web&n=999', '/a?g=hz.web&n=x', '/a?g=hz.absent&n=1'):
            self.request('a', 'GET', path)
        self.account('b', 'robin', OTHER_PASSWORD)
        first = self.model.posts[0]
        self.request('b', 'GET', f'/a?g={first.group}&n={first.number}')
        self.remove('b', first)
        self.remove('a', first, csrf='wrong')
        self.remove('a', first)
        self.remove('a', first)
        self.request('a', 'GET', '/g?name=hz.web')
        self.request('a', 'GET', '/')
        self.request('a', 'POST', '/theme', dict(theme='dark'), csrf='none')
        self.request('a', 'POST', '/signout', {}, csrf='wrong')
        jar = self.target.jar('a')
        kept = dict(jar)
        self.request('a', 'POST', '/signout', {})
        self.request('a', 'GET', '/')
        jar.update(kept)                             # the old session cookie, replayed
        self.request('a', 'GET', '/')
        jar.clear()
        self.request('a', 'GET', '/signin')
        self.request('a', 'POST', '/signin', dict(user='wren', password='not-the-password', next='/'))
        self.request('a', 'GET', '/signin?next=%2Fg%3Fname%3Dhz.web')
        self.request('a', 'POST', '/signin', dict(user='wren', password=PASSWORD, next='/g?name=hz.web'))
        self.request('a', 'GET', '/g?name=hz.web')
        self.request('b', 'POST', '/signout', {})
        self.request('b', 'GET', '/redeem')
        self.request('b', 'POST', '/redeem', dict(code='0' * 32, user='other', password=PASSWORD,
                                                   again=PASSWORD))
        self.request('b', 'GET', '/signin')
        self.request('b', 'POST', '/signin', dict(user='robin', password=OTHER_PASSWORD, next='/'))
        # An access rule hides a group exactly as an absent one, for reading and posting,
        # in a session that begins after it (an open one keeps its pin: W01 is outside).
        self.access('robin', '*,!hz.other', '*,!hz.other')
        self.request('b', 'POST', '/signout', {})   # no page read since sign-in: no token, 403
        self.request('b', 'GET', '/new?g=hz.web')
        self.request('b', 'POST', '/signout', {})
        self.request('b', 'GET', '/signin')
        self.request('b', 'POST', '/signin', dict(user='robin', password=OTHER_PASSWORD, next='/'))
        self.request('b', 'GET', '/')
        self.request('b', 'GET', '/g?name=hz.other')
        self.post('b', 'hz.other', 'Hidden', 'not for robin')
        self.request('a', 'GET', '/')


STEPS = ('/', '/g?name=hz.web', '/g?name=hz.other', '/new?g=hz.web', '/health', '/style.css', '/nope',
         '/signin', '/redeem')


def machine(case, target_factory=WebTarget, traces=None):
    from hypothesis import strategies as st
    from hypothesis.stateful import RuleBasedStateMachine, precondition, rule

    class WebMachine(RuleBasedStateMachine):
        @capture_step(case, 'web')
        def __init__(self):
            super().__init__()
            self.cleanup, self.trace = ExitStack(), []
            resources = unittest.TestCase()
            resources.addCleanup = self.cleanup.callback
            try:
                self.exercise = Exercise(case, target_factory(resources), self.trace)
                self.exercise.witnesses()
            except BaseException:
                if traces is not None:
                    traces.append(self.trace)
                self.cleanup.close()
                raise

        def login(self, browser):
            return self.exercise.model.browser(browser).login

        @rule(browser=st.sampled_from('ab'), path=st.sampled_from(STEPS), head=st.booleans())
        @capture_step(case, 'web')
        def read(self, browser, path, head):
            self.exercise.request(browser, 'HEAD' if head else 'GET', path)

        @rule(browser=st.sampled_from('ab'), index=st.integers(0, 11))
        @capture_step(case, 'web')
        def read_post(self, browser, index):
            posts = self.exercise.model.posts
            if posts:
                p = posts[index % len(posts)]
                self.exercise.request(browser, 'GET', f'/a?g={p.group}&n={p.number}')

        @precondition(lambda self: len(self.exercise.model.posts) < 12)
        @rule(browser=st.sampled_from('ab'), group=st.sampled_from(('hz.web', 'hz.other', 'hz.absent')),
              csrf=st.sampled_from(('session', 'session', 'wrong')), empty=st.booleans())
        @capture_step(case, 'web')
        def post(self, browser, group, csrf, empty):
            if self.login(browser) is None:
                return
            n = len(self.exercise.model.posts)
            self.exercise.post(browser, group, f'Generated {n} <x>', '' if empty else f'body {n} & <y>', csrf=csrf)

        @rule(browser=st.sampled_from('ab'), index=st.integers(0, 11))
        @capture_step(case, 'web')
        def remove(self, browser, index):
            posts = [p for p in self.exercise.model.posts if p.ident in self.exercise.ids]
            if posts and self.login(browser) is not None:
                self.exercise.remove(browser, posts[index % len(posts)])

        @rule(browser=st.sampled_from('ab'), wrong=st.booleans())
        @capture_step(case, 'web')
        def session(self, browser, wrong):
            e = self.exercise
            if self.login(browser) is not None:
                e.request(browser, 'POST', '/signout', {}, csrf='wrong' if wrong else 'session')
                return
            login, password = ('wren', PASSWORD) if browser == 'a' else ('robin', OTHER_PASSWORD)
            e.request(browser, 'GET', '/signin')
            e.request(browser, 'POST', '/signin', dict(user=login, password='nope' if wrong else password, next='/'))

        def teardown(self):
            if traces is not None:
                traces.append(self.trace)
            self.cleanup.close()

    return WebMachine


class TestSurface(SurfaceCase):
    family, form = 'web', 'S'

    @serving('web')
    def test_live_state_machine(self):
        self.evidence['recorded_differences'] = []
        traces = self.evidence['traces'] = []
        run_live_machine(self, 'web', machine(self, traces=traces))
