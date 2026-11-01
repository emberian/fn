| Label | C1 random | C1 iterative | C1 3b | C2/data ORIGINAL | All mutants |
|---|---:|---:|---:|---:|---:|
| `(:run fn2-listener :accepting)` | 8181 | 5597 | 5487 | 29930 | 108250 |
| `(:run fn2-listener :closing)` | 1201 | unexercised | unexercised | 27 | 656 |
| `(:observe fn2-listener :accept-result)` | 4899 | 376 | 478 | 9382 | 26380 |
| `(:observe fn2-listener :close-result)` | 1127 | unexercised | unexercised | 22 | 626 |
| `(:run fn2-echo :free)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-echo :command)` | 2150 | unexercised | 8 | 7957 | 19373 |
| `(:run fn2-echo :reply)` | 2031 | unexercised | unexercised | 14236 | 29489 |
| `(:run fn2-echo :closing)` | 1289 | unexercised | unexercised | 1270 | 4803 |
| `(:run fn2-echo :draining)` | 1163 | unexercised | unexercised | 1245 | 2538 |
| `(:run fn2-echo :retired)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:observe fn2-echo :receive-result)` | 2029 | unexercised | unexercised | 7775 | 19109 |
| `(:observe fn2-echo :send-result)` | 1349 | unexercised | unexercised | 6739 | 13003 |
| `(:observe fn2-echo :borrow-released)` | 1347 | unexercised | unexercised | 3027 | 5685 |
| `(:observe fn2-echo :close-result)` | 1194 | unexercised | unexercised | 1259 | 2564 |
| `(:run fn2-scribe :free)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :reserve)` | 659 | 1871 | 2381 | 7513 | 32718 |
| `(:run fn2-scribe :fill)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :patch)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :write)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :write-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :fence)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :fence-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :reset)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :read)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :read-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :verify)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :next)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :stopped)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :write-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :fence-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :read-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:router :fallback)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:executor :clock)` | 9278 | 629 | 801 | 22230 | 58529 |
| `(:executor :signal)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:executor :service 0)` | 16015 | 5933 | 5835 | 55344 | 168498 |
| `(:executor :service 1)` | 16015 | 5933 | 5835 | 55344 | 168498 |
| `(:executor :service 2)` | 16015 | 5933 | 5835 | 55343 | 168495 |
| `(:executor :service 3)` | 16015 | 5932 | 5835 | 55342 | 168490 |
| `(:executor :empty-principal)` | 48045 | 17799 | 17505 | 166033 | 505500 |
