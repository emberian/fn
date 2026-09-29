# Try a node from a checkout

This walks one node on your own machine from a checkout: build the image,
initialize a store, post an article, reopen it, and read it over NNTP. It is
the same image a release carries (the SBCL core, no ACL2 at run time) and the
same verbs [Running your node](operator.md) documents; nothing here is a
separate development host. (The Python development host this page used to
describe, `tools/run_store.py` and `tools/run_reader.py`, was retired on
2026-09-28.) Use a disposable directory.

Build the production image (it certifies the books with ACL2 first, so this
needs the documented ACL2/SBCL toolchain; it writes `build/fn-host`), then
write a configuration that keeps everything under one directory:

```sh
tools/build_native_host.sh
demo=$(mktemp -d)
cat > "$demo/fn.toml" <<EOF
[store]
path = "$demo/store"
[listener]
host = "127.0.0.1"
port = 8119
[log]
path = "$demo/fn.log"
[control]
path = "$demo/store/control.sock"
EOF
```

Initialize the store with its groups, and write an article with explicit CRLF
octets:

```sh
packaging/fn operator "$demo/fn.toml" init fn.letters fn.test
printf 'From: Example <human@example.invalid>\r\nDate: Fri, 18 Sep 2026 12:00:00 +0000\r\nMessage-ID: <first-letter@example.invalid>\r\nNewsgroups: fn.letters,fn.test\r\nSubject: A letter that survives reopening\r\n\r\nHello from a local fn node.\r\n' > "$demo/article.eml"
```

Post it, reopen the store, and look it up:

```sh
packaging/fn operator "$demo/fn.toml" post \
   --message-id '<first-letter@example.invalid>' \
   --payload "$demo/article.eml" --group fn.letters
packaging/fn operator "$demo/fn.toml" recover
packaging/fn operator "$demo/fn.toml" store inspect '<first-letter@example.invalid>'
```

Repeating the exact post reports a duplicate. Reusing the Message-ID with a
different article is refused (`CONFLICT`). Every command writes one outcome
line and exits with its code: `0` accepted, `1` refused, `3` uncertain and
needing recovery, `4` fault, `5` usage ([the table](operator-internals.md#post-and-read)).

To read it over NNTP, run the node in the foreground:

```sh
packaging/fn operator "$demo/fn.toml" run
```

and connect a client to `127.0.0.1:8119` (`GROUP fn.letters`, `ARTICLE 1`,
`LIST ACTIVE fn.*`; `CAPABILITIES` names what is served). While it runs,
`post` goes to the running owner through the control socket. Stop it with
`SIGTERM` (Ctrl-C): the clean shutdown releases the writer lock and removes
the socket.

Crash and fault experiments use the developer image
(`FN_NATIVE_PROFILE=developer tools/build_native_host.sh`, `build/fn-host-developer`)
and its selectors, listed in
[Developer selectors](operator-internals.md#developer-selectors); a
production image refuses to start with any of them set.
