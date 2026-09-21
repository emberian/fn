# Native control accept/shutdown evidence

## Reproduced failure

On Darwin 25.6.0 at revision `e87f4138`, the focused disabled-posting test
reached its final `SIGTERM` but the owner did not exit within 30 seconds:

```text
python3 -m unittest \
  tests.test_native_control.NativeControlTests.test_disabled_posting_refuses_cli_and_served_post \
  -v

subprocess.TimeoutExpired: Command '[... fn-host ... operator ... run]'
timed out after 30 seconds
Ran 1 test in 31.143s
FAILED (errors=1)
```

A process sample during the timeout showed the owner main thread still inside
the TCP listener's blocking `accept(2)`, while the control listener thread was
inside its bounded readiness wait. The process-global SIGTERM request had no
ordinary owner-thread opportunity to enter cleanup because Darwin did not wake
that blocking accept after the handler's raw `shutdown(2)`.

## Repair and focused result

Revision `ea20ed2c` adds the shared `fnn-accept-observe` boundary. It makes a
listener nonblocking, waits at most one second for readiness, and returns an
accepted socket or `:timeout`, leaving socket errors for the owner or control
loop to classify. Both listener loops use this boundary. Signal context still
only sets the monotonic process-global request and invokes raw `shutdown(2)`;
it takes no mutex and performs no allocation or core call.

The exact five-test output is in
`planning/evidence/native-control-ea20ed2c-2026-09-21-tests.log`. It covers the
previously failing idle-listener stop plus shared-path lease refusal, two
successful control clients, repeated SIGTERM during cleanup with active NNTP
and partial-frame control clients, pre-listener SIGTERM, uncertain lost reply,
restart, and disabled posting. All five tests passed in 17.202 seconds.

The local saved image loaded the exact raw sources and produced this behavioral
trace, but its build command returned nonzero because copied certificates for
unrelated existing books carried different absolute book names. It is not the
clean native build gate; the exact-origin remote build and run are recorded
separately when complete.
