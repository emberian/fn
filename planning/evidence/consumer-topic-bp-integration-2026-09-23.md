# Consumer, topic authorship and BP admission integration

Source `0143f87e` combines E2 maintained consumer Store recovery and native
OS-authenticated local commands/bootstrap, topic authorship binding, fragment
exclusion from whole-article dispatch, and the explicit loopback BP channel
trust profile. `make check` passed locally; it is a scaffolding check, not
runtime or proof evidence.

The full Makefile-root incremental run `run-20260923T221336Z-48f3` used hbox
`/tank/fn/gates/consumer-topic-bp-20260923`, ACL2 8.7 on SBCL 2.6.8, the
w28 executable `/tank/fn/toolchains/w28/acl2-literal-4g`, and four jobs.
The [original manifest](manifests/certify-20260923T221404Z-303098.json)
records the exact source/toolchain digests and command. All 257 newly
certified books passed; 281 matching cached books completed the dependency
closure. Certification took 340.165 seconds, with zero recorded slot wait.
The longest book was `books/bp-receiver-evolving-store-invariants` at
130.938 seconds; hints/local-lemma optimization is assigned separately,
without weakening its maintained consumer relation. The source archive has
no `.git`; manifest source digests, not its null git revision, bind the run.

Review found that request/receipt trust was checked before owner lock
acquisition. `4f66e6b0` adds a second current-configuration check inside
serialization before publication. `python3 -m unittest
 tests.test_native_bp_node_admission_lock -v` passed in 0.028 seconds on this
Mac. It loads the shipped native functions and changes the controlled trust
observation between preflight and lock, observing refusal and zero publisher
calls. It is a targeted boundary test, not a live configuration race campaign.
The ACL2 source is identical between the certified cut and `4f66e6b0`.

The next isolated image subject is `4f66e6b0`. No native result is claimed
here. The live `da5fd8cb` node is unchanged. Poll/fetch, consumer inbox/outbox
composition, durable topic admission, fragment assembly and expiry remain
separate active joins. The BP channel profile trusts all co-resident loopback
originators explicitly and is not cryptographic peer authentication.
