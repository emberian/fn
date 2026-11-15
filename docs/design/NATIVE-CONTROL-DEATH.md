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
`books/merkle`, and `tests/native-control-replay` closures. Supply explicit test
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
