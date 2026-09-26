# heap-from-profile (2026-09-26): the process heap from the store profile

Lane heap-from-profile (Opus; D35 release item; PKT-016). Ids: PRF-198, HST-013,
SCN-127, PKT-581 (what remains), PKT-582 (decisions). Branch lane/heap-from-profile
from dev 8dc094f9 with lane/launcher-env merged in (bcca6fef), implementation 14e046e3.

## Where the 32000 was set
- Frozen image launcher: packaging/freeze-native-image.sh copies the build launcher's
  `exec` line, which is ACL2 `save-exec`'s output (host/native/build.lisp, build-dtn.lisp):
  `--dynamic-space-size 32000` is the building session's figure. The line splices
  `${SBCL_USER_ARGS}` after it, and SBCL takes the last figure.
- Installed bin/fn (packaging/fn, copied by install-native.sh / release-tarball.sh): after
  launcher-env it execs libexec/fn/fn-host and ignored the heap: 32000.
- Developer/test launchers: build/fn-host-developer (save-exec, 32000), called directly
  or through a checkout's packaging/fn.
Unchanged by this lane: the image launchers keep 32000; the figure is passed on top.

## The derivation (books/heap-figure.lisp)
`fn-heap-decide (profile core nursery observations)`; figure octets
CORE + NURSERY + 2 x 16 x (2H + R) + 2 x fn-ock-capture-budget(profile), in MiB rounded up:
- CORE: the saved core's length (the image's dynamic content is at most that).
- NURSERY: host/native/io.lisp +fnn-gc-nursery-octets+ (64 MiB), consed between collections.
- 16 x (2H + R): one cons per octet (rep-wave-d-2026-09-25.md §1.2, measured to 0.2%):
  the retained history H, the open's second copy of it (same section: the checkpoint
  decode's copy, the recovery list beside the replay), one record of R in flight.
- x 2 on the lists: gencgc copies live objects; free space equal to the live lists.
- 2 x F, F = fn-ock-capture-budget = fn-sccr-file-read-bound(H, R) = 3H + segment framing:
  the publication buffer (fn-octets-pub) and the reader's buffer at open; byte vectors.
- The machine: the least positive observation among sysconf physical pages, RLIMIT_DATA,
  and on Linux RLIMIT_AS and each cgroup memory.max from the process's group up (the file's
  octets parsed by fn-heap-limit-of-octets). Past it: (:refused :machine-cannot-hold-profile
  MB MACHINE-MB), outcome class :refused, exit 1.
- No existing store (help, --version, a fresh configuration, non-store verbs): the image and
  nursery must fit, then the figure is the machine.

## Theorems (PRF-198; admitted with the test book in the persvati REPL, w25 toolchain)
- KEYSTONE fn-heap-decide-admits-every-store-the-profile-admits: admitted profile, decision
  :heap, USED <= H, natp core and nursery => CORE + NURSERY + 32(2 USED + R) + 2F <=
  MB x 2^20 <= machine. `(natp used)` was dropped after the weakened theorem was proved.
- fn-heap-decide-refuses-exactly-past-the-machine (both arms, exact numbers);
  fn-heap-decision-exit-code-of-a-refusal (1); fn-heap-machine-octets-is-at-most-each-
  observation / -is-an-observation.
- fn-heap-small-profile-fits-a-small-machine: core <= 512 MiB, nursery <= 64 MiB, machine
  >= 1536 MiB => :heap (natp core/nursery dropped after proving the weakened form).
- fn-heap-init-request-on-a-small-machine-is-small / -keeps-the-operators-request.
Host subject lines: host/native/heap.lisp fnn-heap-decision (called from fnn-command-heap,
the `heap -- ARGV` probe, and fnn-heap-print-store-line, which host/native/operator.lisp
fnn-operator-execute-status / -health call); fnn-heap-init-request from
fnn-operator-execute-init.
Teeth (tests/acl2/heap-figure-tests.lisp): the preset figures; the keystone's reachable
witness (small store full to H) and, per hypothesis, a counterexample with the others true,
the omitted one false and the conclusion false, plus the must-fail of the theorem without
it (5); the small-machine witness at the bound and a counterexample per hypothesis plus a
must-fail without the machine bound; memory.max parsing; the report lines; init's default.
Certification: hbox certified books/heap-figure in the native run (logs in the run tree);
the batch certifies both roots (Makefile roots added).

## Assurance chain
native entry (bin/fn -> `heap -- ARGV`) -> executed subject fn-heap-decide over the
store's saved profile (fnn-load-config, ACL2's decode) -> no representation boundary (a
natural and a profile value) -> relation: the store budget keeps history <= H
(fn-sbud-verdict-at), established at init and preserved by every commit -> behavioural
theorem: the keystone -> observed: SCN-127 below.

## The small preset
Development base with T 16,384, H 8 MiB, R 196,608, G 16, K 128 (A 32,768 from the base;
the development base's own R is 17,138,486 for G 65,535, past this H). Figure on the
69046a76 core (389,141,032 octets): 1,002 MB; on this lane's image 1,012 MB. `init` with a
bare request on a machine under 4 GiB writes it. Figures: development 2,671 MB (2,681 on
this image), scale 54,751 MB, default about 73.4 million MB (refused everywhere: PKT-582).

## Native (hbox, tools/hbox_native.sh --images production --mem 2G 14e046e3)
Module run under `systemd-run --user --scope -p MemoryMax=2G`; the host read the machine as
2048 MB (the scope's memory.max). tests.test_native_heap_from_profile OK (2 ran, 0 skipped).
- Fresh node: init (no profile word) wrote H = 8388608; status `heap=1012 MB profile=small
  machine=2048 MB`; run under that figure; 100 POSTs of 2 KiB all 240; ARTICLE first/last
  220, GROUP 211 100, OVER 100 rows; `CHECKPOINT auto sequence=100 suffix=100
  octets=839540 ms=66`; SIGTERM exit 0; status `open=checkpoint:100 suffix=0`; restarted,
  served the same. VmHWM run 1 148,272 kB, run 2 136,324 kB.
- Refusal: `init --profile development` through bin/fn: exit 1, `fn: refused
  machine-cannot-hold-profile heap=2681 MB machine=2048 MB`, no store made; the same store
  made by the image directly: `run` and `status` through bin/fn exit 1 with that line,
  nothing on stdout, nothing listening.
Logs: heap-from-profile-2026-09-26/native-heap.log sha256
e608941e2b7a6cad2110feb23cd805ae756d4e2132182fd87b71fa533c6f01e4; run.log
4bad1551c5f19ef46fd192af28aad1ab579215a4f24d72cf2df6aa0a55728a9a.
Laptop: sh tests/test_native_cli_launcher.sh (probe figure passed, caller's
SBCL_USER_ARGS/FN_TEST_HEAP_MB ignored when installed, refusal exit propagates, no-figure
probe exit 4, checkout FN_TEST_HEAP_MB) and sh tests/test_native_distribution.sh pass.

## Changes beside the book
packaging/fn (installed: probe then exec with the figure; checkout: FN_TEST_HEAP_MB);
host/native/heap.lisp (new; loaded by build.lisp and build-dtn.lisp after operator.lisp);
operator.lisp (status/health line, init's default); tests/test_native_friends_feed.py and
_friends_accounts.py: a friend on an installed bin/fn inits with the small fields, because
the D27 default is now refused by name; docs/operator.md (heap paragraph, preset table);
specs/host.md "Process heap" (HST-013).

## Not done (PKT-581) and decisions (PKT-582)
See the backlog lines: no `--profile small` word (needs byte-store-frame and
native-operator); OpenBSD constants unexecuted; a store full to H not measured under 2G;
upgrade-profile does not refuse past the machine. Decisions: the D27 default (1 TiB) is
refused on every machine (default taken: refuse by name; recommended: init picks the
largest preset the machine holds); the headroom constant (x2 for gencgc, one open copy).
