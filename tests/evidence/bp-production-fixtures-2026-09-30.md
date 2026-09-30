# BP production injection fixtures

Source work for Q4e; matching native execution is pending.

`tests/bp_producer.py` receives the explicit DEFAULT production image from
`FN_NATIVE_HOST`. It configures a scratch Store's path identity, starts its
tracked operator owner, posts each fixture through `operator CONFIG post`,
and captures the owner's NNTP ARTICLE bytes. A `finally` stops and waits for
the owner before FNWF or BP can open the Store. Refused or uncertain posting
fails the fixture through the exact native exit class; there is no fallback.

After that stop, the production core's read-only `store inspect` returns the
portable stored source. The node and application fixtures author their BP
request from those bytes, rather than the pre-injection input. Python does
not trim ARTICLE's serving Xref or derive a content identity. Captured NNTP
bytes remain in the producer scratch directory.

Converted modules: `test_bp_obligation_native`, `test_bp_node_native`,
`test_bp_app_native`, and `test_native_bp_carry_abandon`. The source-corpus
module already posts through NNTP; its topology description is corrected.
The consumer-owned four-node mission runner remains separately owned.

Validation: Python syntax compilation, the existing obligation caller
boundary source test and a fake executable with actual loopback NNTP pass.
The fake inspection fails if its owner is still active, and its returned
core record differs from both input and served Xref-bearing ARTICLE.
Refused (1) and uncertain (3) fake posts both abort and stop that owner.
These checks do not establish native producer acceptance,
BP delivery, signature integration, or persistence behavior at these bytes.
Earlier module verdicts are not transferred to these changed fixtures.
