| cut | entry | reached | killed step | recover rc | reread after cut | resume rcs | again | reread after resume | third POST rc | GROUP high before -> after | pass |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `candidate-file` | developer | True | 0 | 0 | True | 0,0,0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `candidate-file` | operator | True | 0 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `candidate-link` | developer | True | 0 | 0 | True | 0,0,0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `candidate-link` | operator | True | 0 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `candidate-directory` | developer | True | 0 | 0 | True | 0,0,0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `candidate-directory` | operator | True | 0 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `selection-file` | developer | True | 0 | 0 | True | 0,0,0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `selection-file` | operator | True | 0 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `selection-replace` | developer | True | 0 | 0 | True | 0,0,0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `selection-replace` | operator | True | 0 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `selection-directory` | developer | True | 0 | 0 | True | 0,0,0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `selection-directory` | operator | True | 0 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `pack-reclaim-unlink` | developer | True | 1 | 0 | True | 0,0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `pack-reclaim-unlink` | operator | True | 0 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `pack-reclaim-directory` | developer | True | 1 | 0 | True | 0,0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `pack-reclaim-directory` | operator | True | 0 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `pack-retire-unlink` | developer | True | 2 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `pack-retire-unlink` | operator | True | 0 | 0 | True | 1 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `pack-retire-directory` | developer | True | 2 | 0 | True | 0 | 1 already-compact | True | 0 | 2 -> 3 | PASS |
| `pack-retire-directory` | operator | True | 0 | 0 | True | 1 | 1 already-compact | True | 0 | 2 -> 3 | PASS |

checkpoint observations: 20 of 20 pass; cuts 10
