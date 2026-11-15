# Native APPEND and recovered FETCH

`fn stream fetch MESSAGE_ID --domain D --position P --control-sock PATH`
fetches an occurrence reported by APPEND or READ. It writes the exact article
bytes to stdout. `--json` instead returns `article_hex` and `octets`, preserving
binary data without text replacement. `--as PRINCIPAL` uses the existing local
owner-authorized principal binding. The node decides identity and authorization.
The client encodes the declared octets16 Message-ID, u32be domain, and u64be
position from `books/consumer-codec.lisp`; it rejects truncated or trailing
accepted result data.

`tests/native-append-fetch-restart.py` uses the actual image launcher and local
FNCT socket. In a new isolated image it creates a test principal and grants
read/append through the existing owner-only control channel. It APPENDs a
multi-block article, requires the independently received accepted/committed
reply, and SIGKILLs only its recorded runtime PID. A new node process FETCHes
the returned occurrence and compares every submitted article byte. A changed
Message-ID for that occurrence must be refused without article bytes. Process
PIDs, replies, submitted/fetched articles, and node logs remain in the output
directory. This does not introduce a production service or change authorization.

The runtime prerequisites are the exact current `books/node-profile` and
`books/native-b3-evidence` closures, then the selected raw host load/interface
gate. Reuse the shared application prefix; no separate cold build is needed.
After those qualify, inside the allocated timed runtime scope, build the
selected native BLAKE3 library before the host load gate. `host/b3-native.lisp`
qualifies this shared object while loading; it cannot wait for the later
`fn init` preparation. The command below is the same designated recipe used
by `prepare_native_crypto` in `tools/fn_admin.py`. The current Makefile has no
native library build target (its only executable target is `certify`).

```sh
sh host/build-blake3.sh build/lib
python3 tools/host_check.py --load
python3 tools/interface_emit.py --check
FN2_ORIGIN_LINEAGE=711 FN2_ORIGIN_DOMAIN=712 FN2_ORIGIN_INCARNATION=1 \
FN2_HISTORY_ID=713 FN2_HISTORY_INCARNATION=1 \
python3 tests/native-append-fetch-restart.py --directory build/native-append-fetch-current
```

These origin names are assigned only to this disposable isolated fixture.
The fixture explicitly selects crash-only recovery under the honest-fence
assumption. It tests process-death visibility, not power-loss durability.
The pending POST240/ARTICLE campaign and its joined control/device replay are
separate follow-on work; those also require the current envelope/control test
books and their fixture donor. They are not prerequisites for this basic socket
APPEND/FETCH gate. Neither gate has been run by
this source change.

Source controls:

```sh
python3 tests/test_fn_admin_codec.py ReplyDecoding.test_fetch_canonical_widths_and_exact_binary_reply ReplyDecoding.test_truncated_accepted_results_never_decode_as_accepted InvalidReplyOutcome.test_fetch_cli_preserves_binary_and_rejects_truncation
python3 tests/test_native_append_fetch.py
```

`fn init IMAGE --article-max OCTETS` and `fn serve IMAGE --article-max OCTETS`
select an explicit article byte limit. The default remains 32768. The launcher
passes the text unchanged; ACL2 parses it, checks the upload manifest domain,
and applies the same execution/resource admission as other profile settings.
Invalid text or an unsupported profile is refused rather than replaced with the
default. Use the same explicit setting when initializing and reopening a test
image; this runtime admission setting is not persisted in the image. An omitted
option uses `FN2_ARTICLE_MAX` when set, otherwise the default profile. This
option does not change the on-disk format. A larger limit
alone does not establish rolling-window support or bypass upload capacity.

Separate large-article campaigns (not part of the fast gates):

```sh
python3 tests/native-large-article-refusal.py --directory build/native-large-refusal
python3 tests/native-large-article-restart.py --directory build/native-large-accepted
```

The first requires two explicit 96 KiB refusals and then recovers a subsequently
accepted 6 KiB article. A refusal alone does not identify which admission layer
refused it. The second requires the coherent rolling producer and qualified
current native roots, and supplies `--article-max 100000` to initialization
and both opens. It requires two distinct 96 KiB articles to be accepted and
recovered exactly, and refuses a cross-paired Message-ID/occurrence.

The accepted campaign inserts a test-only observer before the actual native
entry through `tests/native-rolling-launcher.py`; `FN_ACL2` must explicitly name
the qualified real launcher. The observer calls the original rolling-reset
function exactly once and forwards every return value unchanged. It records
existing upload identity and reset-counter values only. The campaign requires
multiple actual counter increases under each accepted operation's same upload
identity. This is executed reset-control evidence, not a proof of native disk
effects. Recovery uses the unmodified launcher. Neither large campaign has been
run by this source change.
