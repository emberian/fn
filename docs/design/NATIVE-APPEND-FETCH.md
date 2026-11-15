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
After those qualify, inside the allocated timed runtime scope:

```sh
python3 tools/host_check.py --load
python3 tools/interface_emit.py --check
FN2_ORIGIN_LINEAGE=711 FN2_ORIGIN_DOMAIN=712 FN2_ORIGIN_INCARNATION=1 \
FN2_HISTORY_ID=713 FN2_HISTORY_INCARNATION=1 \
python3 tests/native-append-fetch-restart.py --directory build/native-append-fetch-current
```

These origin names are assigned only to this disposable isolated fixture.
The fixture explicitly selects crash-only recovery under the honest-fence
assumption. It tests process-death visibility, not power-loss durability.
The existing POST240/ARTICLE campaign and its joined control/device replay are
separate follow-on checks documented in `NATIVE-CONTROL-DEATH.md`; those also
require the current envelope/control test books. Neither gate has been run by
this source change.

Source controls:

```sh
python3 tests/test_fn_admin_codec.py ReplyDecoding.test_fetch_canonical_widths_and_exact_binary_reply ReplyDecoding.test_truncated_accepted_results_never_decode_as_accepted InvalidReplyOutcome.test_fetch_cli_preserves_binary_and_rejects_truncation
python3 tests/test_native_append_fetch.py
```
