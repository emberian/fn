# Try the local storage and NNTP reader experiment

This exercises the current development implementation: local CLI submission,
immutable transaction files, ACL2 replay, and a loopback NNTP reader. It has no
network POST, authentication, or native author signatures. The CLI stores the
given octets; it is not yet an RFC article injector. Use a disposable store with
this provisional format. See [implementation status](implementation.md) and the
[storage experiment](../specs/store-experiment.md) for the exact boundaries.

Install the documented ACL2/SBCL toolchain, then run from the repository root:

```sh
make test
fn_demo_root=$(mktemp -d)
python3 tools/run_store.py --store "$fn_demo_root/store" init
```

Create an example article with explicit CRLF octets:

```sh
python3 - "$fn_demo_root/article.eml" <<'PY'
from pathlib import Path
import sys
Path(sys.argv[1]).write_bytes(
    b"From: Example <human@example.invalid>\r\n"
    b"Date: Fri, 18 Sep 2026 12:00:00 +0000\r\n"
    b"Message-ID: <first-letter@example.invalid>\r\n"
    b"Newsgroups: fn.letters,fn.test\r\n"
    b"Subject: A letter that survives reopening\r\n"
    b"\r\n"
    b"Hello from the local fn experiment.\r\n")
PY
python3 tools/run_store.py --store "$fn_demo_root/store" post \
  --message-id '<first-letter@example.invalid>' \
  --group fn.letters --group fn.test --payload "$fn_demo_root/article.eml"
python3 tools/run_store.py --store "$fn_demo_root/store" recover
python3 tools/run_store.py --store "$fn_demo_root/store" inspect \
  --message-id '<first-letter@example.invalid>'
```

Each CLI invocation starts a fresh ACL2 process and recovers the store. Repeating
the exact post reports a duplicate and preserves the original memberships and
archive obligation. Reusing its Message-ID with different payload or group-list
bytes is refused by this experimental profile. The CLI's Message-ID and group
arguments are not yet checked against article headers by a complete injector;
keep them consistent in examples.

To read the stored article over NNTP:

```sh
python3 tools/run_reader.py --store "$fn_demo_root/store" --port 8119
```

Connect a client to `127.0.0.1:8119`. The supported subset includes `CAPABILITIES`,
`GROUP fn.letters`, `ARTICLE 1`, `HEAD`, `BODY`, `STAT`, `NEXT`, `LAST`, `LIST`,
`HELP`, and `QUIT`; it does not advertise a complete READER bundle. Port `0`
chooses an available port and prints it. Omit `--store` to run the separate seeded
reader experiment used by `tests/interop_nntplib.py`.

The stored reader holds a shared lock for its lifetime and serves the recovered
snapshot. Posting through the CLI is refused while that reader is running;
stop it, post, and restart to see additional articles. This deliberately simple
ownership model precedes a shared live state owner. Startup refuses payloads that
the ACL2 reader cannot safely project as NNTP. That projection check is not full
RFC article validation.

For injected storage outcomes, `post --inject-fault prepublish` reports a known
abort. `post --inject-fault postpublish` reports an indeterminate result and
requires recovery; the complete article may then be present. Neither operation
reports a successful post before the required commit barriers. These are
process/I/O experiments, not power-loss qualification.
