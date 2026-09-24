# Pinned ION source lifetime repair

The pinned ION `4.2.1-a.1` source at revision
`4912bf82de7d03a9a11bf5d68614cc002f9ac911` shows that
`zco_create_file_ref` stores the source pathname, inode and length; it closes
the source fd before `bp_send`. The bundle can read that path later. In
`bpv7/library/libbpP.c::bpSend`, a negative return is possible after the
final `sdr_end_xn` call, where the caller cannot tell whether the bundle was
committed. The previous helper could destroy its ADU ZCO on that uncertain
return.

`tests/ltp/fn_ltp_send.c` now freezes a bounded byte copy in a private
mode-0700 observation directory, fsyncs the mode-0600 file and directory
before `bp_send`, gives ION an unlink-on-final-reference file ref, and keeps
the caller's original ADU for retry. It never destroys the ZCO after entering
`bp_send`; an uncertain returned bundle pointer is not released. These are
source-lifetime and ownership rules for the experimental helper, not a
durable workflow binding or application acceptance.

On hbox, gcc 14.2.0 with `-std=c11 -Wall -Wextra -Werror` built the pinned
helper source SHA-256
`ba4d34ed3e49488d730ce72b0e66fc61d360f14a683c68c8bd5e52ba15fdbd01`
to binary SHA-256
`a09cad9c1ca0f7f86a6c8bda0a4bf54652bf1dad275fa6888ff9fdbcf4e6f61f`.
The opt-in two-node command was:

```
FN_LTP_SEND_BIN=/tank/fn/lanes/ion-observation-binding/fn_ltp_send \
  bash tests/ltp/run_native_send_id.sh \
  /tank/fn/lanes/ion-observation-binding/ion-source-test-final
```

It matched the sender's observed ID to receiver staging
`ipn:1.1|843545305360|6` and the exact 26-byte request ADU (SHA-256
`e603888821272910d5e3c7d25ad4996ac4fde8005ebae0328bf2b3dbaf81939c`).
The observation SHA-256 was
`6665689d31c8177ee2c335f13ea5ab5ee947091694d2836a804dc10fce69b663`;
after receiver delivery, ION removed the private `.source` file, while the
caller-owned request ADU remained. The run used loopback nodes and no fault
injection. Error-after-entry and process-death ownership cuts remain to be
exercised before a production native caller uses this helper.
