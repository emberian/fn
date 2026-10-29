| G1 label | ORIGINAL random (3 seeds) | ORIGINAL exhaustive | All mutant campaigns |
|---|---:|---:|---:|
| `(:run fn2-listener :accepting)` | 8181 | 626 | 3714 |
| `(:run fn2-listener :closing)` | 1201 | unexercised | 80 |
| `(:observe fn2-listener :accept-result)` | 4899 | 20 | 1048 |
| `(:observe fn2-listener :close-result)` | 1127 | unexercised | 77 |
| `(:run fn2-echo :free)` | unexercised | unexercised | unexercised |
| `(:run fn2-echo :command)` | 2150 | unexercised | 403 |
| `(:run fn2-echo :reply)` | 2031 | unexercised | 517 |
| `(:run fn2-echo :closing)` | 1289 | unexercised | 92 |
| `(:run fn2-echo :draining)` | 1163 | unexercised | 85 |
| `(:run fn2-echo :retired)` | unexercised | unexercised | unexercised |
| `(:observe fn2-echo :receive-result)` | 2029 | unexercised | 390 |
| `(:observe fn2-echo :send-result)` | 1349 | unexercised | 229 |
| `(:observe fn2-echo :borrow-released)` | 1347 | unexercised | 108 |
| `(:observe fn2-echo :close-result)` | 1194 | unexercised | 85 |
| `(:run fn2-scribe :free)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :reserve)` | 659 | 151 | 831 |
| `(:run fn2-scribe :fill)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :patch)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :write)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :write-result)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :fence)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :fence-result)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :reset)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :read)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :read-result)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :verify)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :next)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :stopped)` | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :write-result)` | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :fence-result)` | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :read-result)` | unexercised | unexercised | unexercised |
| `(:router :fallback)` | unexercised | unexercised | unexercised |
| `(:executor :clock)` | 9278 | 28 | 1630 |
| `(:executor :signal)` | unexercised | unexercised | unexercised |
| `(:executor :service 0)` | 16015 | 646 | 4951 |
| `(:executor :service 1)` | 16015 | 646 | 4951 |
| `(:executor :service 2)` | 16015 | 646 | 4951 |
| `(:executor :service 3)` | 16015 | 646 | 4951 |
| `(:executor :empty-principal)` | 48045 | 1938 | 14853 |
