# Default native-image operator integration check

Source: `w15/native-operator-integrated` code commit `e3147e8` and runtime-test commit `2941fce`, formed from current
`dev`, the native operator packet, and owner convergence callback commit
`177123f`. The hbox integration tree was
`/tank/fn/gates/w15-native-operator-integrated`; the grammar closure records
its source digests in [the manifest](manifests/certify-20260921T092131Z-1938920.json).

The default `host/native/build.lisp` includes `books/native-operator`, loads
`host/native-operator-host.lisp`, and loads `host/native/operator.lisp`
immediately after `host/native/owner.lisp`. The DTN build remains unchanged.
The raw operator sends an accepted `:run` plan only to
`fnn-owner-run-normalized` with ACL2-projected store/listener octets, port,
once boolean, and max connections. It has no direct post path; post remains
usage 5 until shared submission intent is callable.

On hbox, a loopback-only store was initialized, then the saved default image
was invoked directly (no Python child):

```
./build/fn-host --fn operator /missing/fn.toml help run
./build/fn-host --fn operator /missing/fn.toml status
./build/fn-host --fn operator /tmp/fnop/c status
./build/fn-host --fn operator /tmp/fnop/c run --once
```

The first returned 0 and printed the ACL2-selected run help. The missing-config
status returned 5. Status on the initialized store returned 0. The one-shot
run bound 127.0.0.1:39461, answered a loopback client `200` greeting and `205`
QUIT, then exited 0 and emitted its accepted result after service completion.
The exact transcript is [here](native-operator-installed-20260921T0920-transcript.txt).

The seven-book ACL2 8.7 / SBCL 2.6.8 closure passed in 4.840 seconds. The
native build script itself returned 1 because this isolated rsync gate has no
pre-existing `.cert` files for its full default-image dependency set; ACL2 did
save `build/fn-host` and `build/fn-host.core`, which were used only for this
runtime diagnostic. This is not a certified or deployable image build. The
closure manifest certifies the exact native-operator grammar and host wrapper,
not all default-image roots. `python3 -m unittest tests.test_native_operator_cli -v` against that direct image also passed: missing, directory, and 16,385-octet configs were usage 5; an unreadable regular config was fault 4.
