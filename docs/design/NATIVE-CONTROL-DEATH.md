# Native acceptance control-path pilot

`tests/native-control-death.py` binds one selected native image's actual
accepted POST and fresh-process ARTICLE to two independent ACL2 control
replays. It does not prove physical byte effects, disk honesty, or complete
native crash-point correspondence. The default native-program gate stays red
until its broader mapping is established.

The test invokes the real CLI through `native-control-launcher.py`. That test
launcher preserves the selected `tools/image-node.lsp` and inserts only an
evidence hook before its unchanged main call. The hook records the actual
image profile, actual `fn2-boot-start` arguments/result and bounded native
trace. Its separate evidence stream never syncs or closes the image device.

After the final expected Send has been recorded, the executor pauses before
the normal `post` boundary. The parent must independently receive the complete
socket response, compare the captured Send bytes with that receipt, and observe
the matching pause marker before SIGKILLing its recorded child PID. This fixes
the observed cut and prevents a truncated evidence form. In the accepted phase
the receipt includes 240; in a fresh process it includes exact GROUP and ARTICLE
bytes, including generated Xref and dot transparency.

Each replay starts a fresh executor with the captured profile and calls the
actual boot-start function. `fn2-envelope-steps` checks operation identity,
allowed completions and Send bytes. The resulting client transcript must match
the independently observed peer port and both sent and received bytes. Changed
peer bytes and duplicate peer identity have negative controls.
Send constraints come from the current exact/unknown-prefix matcher, not from
the consumed-byte accumulator. The pause pilot accepts only successful Send
segments; separate logical controls retain ambiguity for failed segments.
Recorded disk Read bytes remain external observations; replay does not establish that they
were produced by the earlier Write/Fence operations. In particular, this test
does not interpret a process-death image snapshot as a durable prefix or erase
an uncertain persistence outcome.

Source controls (no node is launched):

```sh
python3 tests/test_native_control_capture.py
python3 -m py_compile tests/native-control-launcher.py tests/native-control-death.py tests/native-image-restart.py
```

Runtime prerequisite: exact-current qualified `books/node-profile`,
`books/native-b3-evidence`, and `tests/native-control-replay` closures.
The optional effect replay additionally requires `sim/native-device-envelope` (including the effect reducer). Supply explicit test
origin/history environment settings as required by current startup. Inside a
reserved 6 GiB timed job, run:

```sh
FN2_ORIGIN_LINEAGE=701 FN2_ORIGIN_DOMAIN=702 FN2_ORIGIN_INCARNATION=1 \
FN2_HISTORY_ID=703 FN2_HISTORY_INCARNATION=1 \
python3 tests/native-control-death.py --directory build/native-control-death-current
```

These names are for this isolated fixture only; they do not establish a production
origin assignment. The real CLI prepares its selected BLAKE3 library at startup;
this plain-socket fixture supplies no TLS or compression enablement.

The directory must be new. It retains the image, process receipts, full wire
receipts, test-owned Lisp data traces and peer inputs, and fresh replay logs.
No completed runtime result is claimed by this source change; the current
canonical node closure and this test root must qualify before execution.

Optional device evidence (`--device-effects`) additionally loads the test-only
`native-device-effects-capture.lsp` recorder. It records submitted descriptors,
physical call begins, and raw return/errno values on a separate evidence stream.
The fixture preserves `before-accepted.img` after its setup process is reaped,
and `after-accepted-kill.img` before any restart. It also preserves the image
after the restart observation process is killed. `image-observations.json`
records exact copy sizes and SHA-256 digests. Copies do not sync the node device.
These are process-death-visible bytes, not an asserted durable prefix. Missing
returns and ambiguous errors remain obligations of the separate effect reducer;
this option alone does not establish persisted-effect refinement.

With device evidence enabled, the fresh replay calls
`fn2-native-device-control-replay` on the same control trace and captured device
records. It requires `:pass` and checks independent peer receipts against that
joined replay's capabilities. The actual selected device fd and backend come
from `fn2-device-start`'s returned object, recorded in the phase `.device` file.
The whole-image consumer runs inside the same records/fd bindings. It checks
the whole equal-size before/after images and physical Read observations, using
64 KiB scratch chunks. Each phase retains an effect-result JSON verdict:
`:EXACT-PROCESS-VIEW` or `:UNCERTAIN-EFFECT-BOUND`. Neither means durable; raw
Fence truth remains external. The joined checker is a runtime prerequisite; independent control and image
passes cannot substitute for it. Its new current closure and slab/loan binding
must qualify before the optional campaign can run.

The optional launcher refuses a missing, duplicated, or late adapter load.
At hook load, the actual `fn2-n-storage-submit` and `fn2-device-start` functions
must already exist. The schema-10 recorder observes the host slab during
`fn2-n-storage-submit`; joined replay compares its address/length against
`fn2-host-op-span`, its backing-object tokens, and the submitted Write bytes.
Before runtime, qualify the current `sim/native-device-envelope` and its unit
controls along with the selected node, native BLAKE3 evidence, and control
replay roots. The leaf/scalar effect gate alone does not qualify this join.
The raw image consumer must honor the dynamically bound records/fd and use
the extent-validating complete-image finish check.
