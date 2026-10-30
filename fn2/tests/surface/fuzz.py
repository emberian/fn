"""F fuzz drivers for the families other than nntp (README "Provisioning and driver hooks": argv + --seconds).

One hook for every family: `FN2_SURFACE_FUZZ_<FAMILY>=fn2.tests.surface.fuzz:fuzz`. It returns the argv the
surface runner supervises; the runner appends `--seconds`. Each driver owns its oracle and its mutation
controls:

- tls_auth, peering: the seeded wire differential (fn2.tests.model.differential) with its generator narrowed
  to the family's commands (`--focus auth`: AUTHINFO USER/PASS/SASL arguments, XREDEEM, STARTTLS;
  `--focus feed`: IHAVE/CHECK/TAKETHIS and XFNCATCHUP). H2's model judges every reply, and the runner
  adjudicates mismatches against model/adjudications.json exactly as for nntp. Mutation controls: the
  fake target's `auth-wrong-accepted` and `feed-wrong-id` plants (fn2/tests/model/test_differential.py).
- operator, store_ops: fn2.tests.surface.argv_fuzz, seeded argv mutation of every modelled verb, judged by the
  exit-class table, the ARGV-MALFORMED preflight, the usage class and the families' models (OperatorModel,
  StoreOpsModel); one node per seed, `--seconds` bounds the seeds. Mutation controls: its plants
  (fn2/tests/surface/test_argv_fuzz.py).
- config_limits: fn2.tests.surface.config_fuzz, seeded fn.toml mutation judged by specs/native-config.md's
  sentences through `operator PATH show` (accepted 0, refused usage 5). Mutation controls: its plants
  against an independent reading of the same sentences (fn2/tests/surface/test_config_fuzz.py).
- web: fn2.tests.surface.http_fuzz, seeded request-head mutation of the developer image's web face, each
  case's status decided by RFC 9112 / 9110 and the face's stated policy (books/web-request.lisp); /health
  must stay 200. Mutation controls: its plants (fn2/tests/surface/test_http_fuzz.py).
- consumer: fn2.tests.surface.fncu_fuzz, seeded `fncu` v1 cursor mutation through the developer image's
  `consumer-inspect`, judged by specs/consumer-progress.md's encoding (with the pins P-FNCU-HEADER and
  P-FNCU-EPOCH), then fn2.tests.surface.fnct_fuzz on the remaining time: captured control frames, mutated,
  against a live owner (integrity: no mutated frame gets the success reply; the owner keeps answering).
- bp: fn2.tests.surface.bp_fuzz, seeded BPv7 mutation of the captured bundles through the DTN image's
  `bp decode`, judged by RFC 9171 (CRC, framing, lifetime and the Bundle Age path), then
  fn2.tests.surface.tcpcl_fuzz on the remaining time: RFC 9174 sessions carrying the captured bundle to
  `bp receive` (with a Store whose boundary admits the peer), one mutation each. Mutation controls for both: fn2/tests/surface/test_codec_fuzz.py.
"""
import sys

from fn2.tests.surface import RUN

DIFFERENTIAL = {'tls_auth': ('auth', 'reader'), 'peering': ('feed', 'peer')}


def fuzz(*, case, target, family, out, seconds, corpus):
    if family in DIFFERENTIAL:
        focus, mode = DIFFERENTIAL[family]
        return [sys.executable, '-m', 'fn2.tests.model.differential', '--target', target, '--focus', focus,
                '--mode', mode, '--seeds', f"0..{RUN.get('examples', 200) - 1}", '--steps', '50',
                '--minimize-seconds', '5', '--out', str(out / 'fuzz')]
    if family in ('operator', 'store_ops'):
        return [sys.executable, '-m', 'fn2.tests.surface.argv_fuzz', '--family', family, '--target', target,
                '--seeds', '0..99999', '--steps', '20', '--out', str(out / 'fuzz')]
    if family == 'config_limits':
        return [sys.executable, '-m', 'fn2.tests.surface.config_fuzz', '--target', target, '--seeds', '0..999999',
                '--out', str(out / 'fuzz')]
    if family == 'web':
        return [sys.executable, '-m', 'fn2.tests.surface.http_fuzz', '--target', target, '--seeds', '0..999999',
                '--out', str(out / 'fuzz')]
    if family == 'consumer':
        return [sys.executable, '-m', 'fn2.tests.surface.fncu_fuzz', '--target', target, '--seeds', '0..999999',
                '--out', str(out / 'fuzz'), '--with-fnct']
    if family == 'bp':
        return [sys.executable, '-m', 'fn2.tests.surface.bp_fuzz', '--target', target, '--seeds', '0..999999',
                '--out', str(out / 'fuzz'), '--with-tcpcl']
    raise ValueError(f'no fuzz driver for {family}')
