# The reply send deadline: a no-progress rule decided in ACL2 (CONVERGE-2 row 20)

**The owner cuts a reader that is still reading.** The mux gives every queued reply window 10 s to be accepted by the socket (`+fnn-mux-send-seconds+`, host/native/mux.lisp:57, armed at :560 and :713, fired at :1502 as `etimedout`). On the CONVERGE-2 developer image (401c7ab86), test_native_over_pins' slow-drain test sends a 12 MiB ARTICLE to a client with a 4 KiB SO_RCVBUF that reads lines at 38 KB/s (1 MiB per 27.4 s). The owner's writes never block until it has handed the kernel 3,383,427 octets, 20.1 s after the 220 line (trace hook hbox:/tank/fn/scratch/n-row20/hook.lisp, stderr se/*-5-fn-operator.stderr, t = 89.95 s to 110.03 s). The next write gets EAGAIN; the 10 s deadline then expires because the kernel does not report the socket writable until far more than 10 s of reading has drained that queue (at 38 KB/s, 3.38 MB is 89 s). The owner logs `send-reply: [Errno 110]`, closes, and the client reads the buffered 3.2 MB and then EOF. The same numbers repeat on the p-ast-guard image, so render cost (row 21) is not the cause. The test is right: a reader that keeps draining is not stalled.

## The rule

ACL2 decides, the host observes and enforces (ruling, coordinator 11:50):

- **Observation** (host, each mux tick while a window waits): the kernel's unsent octets for the socket (`ioctl(fd, SIOCOUTQ)` on Linux; `FIONWRITE` on the BSDs), the monotonic time, and the octets of the reply handed over so far.
- **Decision** (a new book, `books/send-progress.lisp`): `fn-send-progress-verdict` over the previous observation, the new one and two `books/profile-limits.lisp` rows: `:send-stall-seconds` (no octet leaves the kernel queue for this long: refuse `:send-stalled`) and `:send-min-octets-per-second` (over a whole reply, a pace below this: refuse `:reader-too-slow`). Anything else answers `:continue` and re-arms the deadline. Keystones: a reader whose queue shrinks within every `:send-stall-seconds` window and whose pace stays at the floor is never refused (the witness is this test's 38 KB/s reader); a queue that does not shrink for `:send-stall-seconds` is refused by name; the verdict reads only its arguments.
- **Enforcement** (host): mux.lisp replaces the fixed deadline with the verdict; a refusal closes the connection with the named reason in the owner's log (`send refused reason=send-stalled|reader-too-slow`), never `Errno 110`.

The floor's default must admit the slowest reader the tests name (38 KB/s) with margin, and the stall default keeps today's 10 s. Both numbers are profile rows so an operator can tighten them against a slow-read attack; the existing per-connection memory budget already bounds what a slow reader can hold.

## Gates

Red before: test_native_over_pins `test_a_large_article_drained_slowly_refreshes_the_idle_deadline` on the c2 image (hbox:/tank/fn/scratch/n-row18/overpins1.log). Green after: the same test on the lane's image, plus a new native case with a reader that stops reading entirely, which must be refused `send-stalled` within `:send-stall-seconds` plus one tick. Certify the new book and profile-limits' affected closure; host_check --load for mux.lisp.
