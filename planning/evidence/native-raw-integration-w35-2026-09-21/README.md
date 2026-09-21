# Native raw boundary integration check — W35

Source revision: `0f0a0c7e5073cc0d6e218b26a795147cd7f358c6`.

The two commands below passed after native control, transaction namespace, and outbound feed component integration. This exercises the actual raw functions with the test fixtures/stubs declared in those scripts. It is not a saved ACL2 image, a new certification, or a two-node interoperability result.

```sh
sbcl --noinform --script tests/native_io_progress.lisp
sh tests/test_native_feed_service_raw.sh
```

Tool: `SBCL 2.6.8`; platform: `Darwin 25.6.0 arm64`.

Both processes exited 0; their final markers are `native-io-progress: ok` and `native feed raw phase/sequencing test passed`. Logs: [I/O](native-io.log), [feed](feed-raw.log).

The separate `test_owner_feed_connection_host.sh` transcript is not relied on: its unconditional post-load marker can survive an ACL2 load failure, and that harness is being repaired before its wrapper result is cited.

| Input | SHA-256 |
| --- | --- |
| `host/native/io.lisp` | `283f67b6186318f0bf1cd043523969e0f46d9bd621a90ce55beaf750139079eb` |
| `host/native/feed-service.lisp` | `c1f48707c8b772203aa0158881cc4dda66b23ebf6fe336b98ee9e53f185e6f93` |
| `tests/native_io_progress.lisp` | `f849296a752cd0fd34e1c4dd696f73cde36c78dc14465846ffd084c7eb94cb6e` |
| `tests/native_feed_service_raw.lisp` | `31da22292b89de77f9c507e16bf1232c37693678914d3afbf6be311bf22703bb` |
| `tests/test_native_feed_service_raw.sh` | `a4dba8b75cf115b1f7fc7f9fe93a29d9719b4768c0d4e8ac9da0b68493121f00` |
| `native-io.log` | `95dcc46a0febb0b4d54f809ff0d2d5a617f62cdefabcf266937b4f0bfd5d857c` |
| `feed-raw.log` | `3956987c35775bf4f1cfe3cc2b1ad80b9235d2ec6276b161a7ae88bd0385ceb4` |
