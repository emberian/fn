# Pinned ION sender bundle-ID observation

Source: `tests/ltp/fn_ltp_send.c` SHA-256
`4f5338b2449258d5267bf35a76f5ac5605739b8125ec35f4c8e8604ece3d24b9`.
Pinned ION-DTN 4.2.1-a.1 source revision
`4912bf82de7d03a9a11bf5d68614cc002f9ac911`, configured as
`tests/ltp/pin.json`; hbox Ubuntu gcc 14.2.0. The helper compiled with
`-std=c11 -Wall -Wextra -Werror`, ION's installed public headers and the
revision-pinned private `bpP.h`; binary SHA-256
`9d0cdffce8b52b911f40bf5f17b9c7be52888bd2c6a6c98c31e3a0ee2d00335d`.
The private header dependency is an explicit ION ABI dependency.

An opt-in, isolated hbox two-node test ran with `ION_ROOT=/tank/fn/ltp`,
`FN_LTP_SEND_BIN=/tank/fn/ltp/run/fn_ltp_send` and
`bash tests/ltp/run_native_send_id.sh /tank/fn/ltp/run/native-send5`.
The exact run script SHA-256 was
`0a46a206ae00d7a27a591df5180efd72a8ef85475a933e4209af6a0a2f550578`.
It exited 0 and reported source EID `ipn:1.1`, creation time
`843544024799`, sequence `4`; the receiver's durable staged file had exactly
the same three fields. The 26-byte sent and staged ADUs both had SHA-256
`e603888821272910d5e3c7d25ad4996ac4fde8005ebae0328bf2b3dbaf81939c`.
The observation file SHA-256 was
`28ba2e2e59614369486edfc961b9af7a93b225e0acdca65eb018a80c78b4a956`;
the sender stdout log SHA-256 was
`ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb`.
Both laboratory nodes were stopped by the per-node scripts, and a process
check found no remaining LTP daemons. The live fn node was untouched.

The observed ID is an ION transport observation, not fn acceptance. The
helper has not been joined to native `fnn-bps-send-effect`, the ACL2 attempt
transition, receiver application acceptance, or a returned receipt. In
particular, the staged receiver still has ION's irreversible
`bp_receive()`-to-fsync loss window, and the app-level peer EID
`dtn://fn.lab/inbox` is separate from the ION destination `ipn:2.1`.

The next executable boundary should accept the observation file only after
exit 0, decode its bounded fields in ACL2, compare the application peer EID
with the durable work item and the BP destination with the configured route,
then record the observed BP identity against the still-outstanding attempt.
An exit 3, a malformed or missing file, or a crash after send but before
observation publication must leave that attempt uncertain and recoverable.
Only an ACL2-authorized application receipt may discharge the obligation.
