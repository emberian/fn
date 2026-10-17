# reach-seams-c continuation
Tools: /tmp/reach-seams-c-q.py (reachable?), /tmp/reach-seams-c-chain.py (host chain), events list /tmp/reach-seams-c-events.txt, before log /tmp/reach-seams-c-before.log.
Pattern P1: host projects result via ACL2 fn A; book thm (implies (equal r (C ..)) (equal (U ..) (A r))).
## done (b)
- PRF-1057 fn-pio-close-waits-for-every-worker: books/page-read-direct.lisp fn-pio-direct-quiet-equals-clear (REPL ok)
- PRF-960 fn-frb-control-decode-is-reference: books/native-control-buffer.lisp fn-frb-control-decode-is-decode-with (REPL ok)
## planned
- PRF-1020 splan->qplan equalities (2 events); BP contact-next P1 (3); PRF-932 fn-oop-* via fn-oct-* P1 (4)
## (c) candidates (note on item): bp fragment aux/memo/select/1051 (host runs fn-bpfj-next-candidate); bp scan/held/own-entry (host runs cursor scan); PRF-253/254/255 (crash model, no host fn); PRF-192 (superseded by plan); PRF-949 x2 (test twin/invariant); PRF-1020 ovw x3 (dispatcher reaches fn-nntp-over-range-indexed not -ovw); PRF-288; PRF-180; PRF-274
- certify PID 15079 started; logs /tmp/reach-seams-c-cert.local.log (local), remote /tmp/reach-seams-c-cert.log on persvati; attach: tools/remote_check.sh attach persvati --log /tmp/reach-seams-c-cert.log
