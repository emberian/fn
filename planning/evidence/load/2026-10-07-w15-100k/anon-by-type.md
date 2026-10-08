## Anonymous heap by type: W15 on image (/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer)

| type | 1k | 25k | 50k | 100k | exponent (value vs n) | growth over 1k, B per article at 100k |
|---|---|---|---|---|---|---|
| CONS | 420816608 | 464804176 | 628218592 | 691163520 | 0.106 | 2730.8 |
| strings | 40146096 | 78546112 | 118521120 | 198521680 | 0.328 | 1599.8 |
| u64 arrays | - | 2266288 | 75020640 | 367716144 | 3.67 | - |
| u8 arrays | 3340000 | 14869232 | 28511040 | 51136592 | 0.585 | 482.8 |
| stobjs (CAT+ARENA+HIST; inside the type rows, not additive) | 780976 | 18317232 | 36594784 | 73139584 | 0.984 | 730.9 |
| others (dynamic space minus the four type rows) | 66912496 | 72616560 | 75366160 | 116108320 | 0.089 | 496.9 |
| dynamic space total | 531215200 | 633102368 | 925637552 | 1424646256 | 0.19 | 9024.6 |

## Anonymous heap by type: W15 on fn-core (/tank/fn/scratch/extract-core/tree4/build/core/fn-core)

| type | 1k | 25k | 50k | 100k | exponent (value vs n) | growth over 1k, B per article at 100k |
|---|---|---|---|---|---|---|
| CONS | 66099568 | 110087136 | 289566672 | 336420368 | 0.365 | 2730.5 |
| strings | 2195104 | 40595136 | 80570384 | 160571568 | 0.931 | 1599.8 |
| u64 arrays | - | 2233488 | 74987840 | 367830832 | 2.78 | - |
| u8 arrays | 3584512 | 15113776 | 28756864 | 51391536 | 0.57 | 482.9 |
| stobjs (CAT+ARENA+HIST; inside the type rows, not additive) | 780976 | 18317232 | 36594784 | 73139584 | 0.984 | 730.9 |
| others (dynamic space minus the four type rows) | 22740320 | 27726000 | 32665408 | 84733664 | 0.22 | 626.2 |
| dynamic space total | 94619504 | 195755536 | 506547168 | 1000947968 | 0.488 | 9154.8 |
