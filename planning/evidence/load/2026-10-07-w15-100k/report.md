# Load run w15-100k

## W15@1k  target=image arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.599 | - | - | - | - | 620576 | 56324 | 564252 | 690336 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 608488 | 44236 | 564252 | 690336 | 0.03 | 0 | 0 | - | - |
| census | 1.5 | - | - | - | - | 608152 | 43900 | 564252 | 690336 | 1.43 | 0 | 0 | - | - |
| publish | 1.34 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 0.572 | - | - | - | - | 610848 | 46240 | 564608 | 643424 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [14.35, 14.42, 16.07] at start and [16.94, 14.95, 16.19] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-100k/W15_1k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-100k/W15_1k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@10k  target=image arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 4.84 | - | - | - | - | 665164 | 101108 | 564056 | 810028 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 646748 | 82692 | 564056 | 810028 | 0.05 | 0 | 0 | - | - |
| census | 2 | - | - | - | - | 646548 | 82492 | 564056 | 810028 | 1.56 | 0 | 0 | - | - |
| publish | 9.34 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 1.88 | - | - | - | - | 664288 | 99904 | 564384 | 754448 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [16.94, 14.95, 16.19] at start and [16.59, 15.1, 16.19] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-100k/W15_10k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-100k/W15_10k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@25k  target=image arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 10.8 | - | - | - | - | 743564 | 179084 | 564480 | 924132 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 710968 | 146488 | 564480 | 924132 | 0.06 | 0 | 0 | - | - |
| census | 2 | - | - | - | - | 711092 | 146612 | 564480 | 924132 | 1.48 | 0 | 0 | - | - |
| publish | 20.8 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 3.25 | - | - | - | - | 754848 | 190304 | 564544 | 998352 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [16.59, 15.1, 16.19] at start and [17.06, 15.6, 16.3] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-100k/W15_25k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-100k/W15_25k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@50k  target=image arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 20.5 | - | - | - | - | 947412 | 383048 | 564364 | 1205956 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 1036204 | 471840 | 564364 | 1205956 | 20.9 | 0 | 0 | - | - |
| census | 2.5 | - | - | - | - | 945312 | 380948 | 564364 | 1205956 | 2.71 | 0 | 0 | - | - |
| publish | 45.2 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 7.38 | - | - | - | - | 904096 | 339712 | 564384 | 1308984 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [17.06, 15.6, 16.3] at start and [16.57, 15.79, 16.29] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-100k/W15_50k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-100k/W15_50k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@100k  target=image arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 45 | - | - | - | - | 1171996 | 607712 | 564284 | 1544916 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 1650792 | 1086508 | 564284 | 1650792 | 20.8 | 0 | 0 | - | - |
| census | 3 | - | - | - | - | 1280724 | 716440 | 564284 | 1792680 | 3.12 | 0 | 0 | - | - |
| publish | 101.9 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 13.7 | - | - | - | - | 1179972 | 615564 | 564408 | 2390512 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [16.57, 15.79, 16.29] at start and [19.81, 17.86, 17.03] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-100k/W15_100k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-100k/W15_100k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| T-OPEN | owner start to LISTENING from checkpoint at 50k (the fixture nearest F6's 40k, so stricter) and the exponent of open time against n (full replay and checkpoint) | open_s.checkpoint@50k <= 10 | 7.16 | NOT-MEASURED (per-core busy on the cell's cores was not recorded (load 14.35)) |
|  |  | open_s.checkpoint.exponent <= 1 | 0.784 |  |
|  |  | open_s.replay.exponent <= 1 | 0.925 |  |
| T-PUB | publication (checkpoint) of a 50k store: octets written O(changed) not O(store) (exponent against n <= 0.5); longest POST stall while it runs <= 2 s (time check) | publish.stall_max_s <= 2 | - | FAIL |
|  |  | publish.write_octets.exponent <= 0.5 | 0.961 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|

Metrics by store size (octets/KiB/seconds as named; exponent = fitted slope of log value on log n):

| metric | 1k | 10k | 25k | 50k | 100k | exponent |
|---|---|---|---|---|---|---|
| anon.raw.ARENA | 25248 | 393888 | 787104 | 1573536 | 3146400 | 1.04 |
| anon.raw.ARENA.slot0:T | 16496 | 262256 | 524400 | 1048688 | 2097264 | 1.04 |
| anon.raw.ARENA.slot1:T | 8208 | 131088 | 262160 | 524304 | 1048592 | 1.04 |
| anon.raw.ARENA.slot2:T | 16 | 16 | 16 | 16 | 16 | 0 |
| anon.raw.ARENA.slot3:T | 528 | 528 | 528 | 528 | 528 | 0 |
| anon.raw.CAT | 712688 | 6779952 | 16579312 | 33120160 | 66191552 | 0.983 |
| anon.raw.CAT.slot0:T | 646496 | 5996128 | 14908640 | 29786976 | 59539488 | 0.982 |
| anon.raw.CAT.slot1:T | 40512 | 532752 | 1057808 | 2107920 | 4208144 | 0.999 |
| anon.raw.CAT.slot2:T | 25424 | 250816 | 612608 | 1225008 | 2443664 | 0.991 |
| anon.raw.CAT.slot3:HASH-TABLE | 128 | 128 | 128 | 128 | 128 | 0 |
| anon.raw.CAT.slot4:HASH-TABLE | 128 | 128 | 128 | 128 | 128 | 0 |
| anon.raw.CAT.slot5:(INTEGER_0_4611686018427387903) | 0 | 0 | 0 | 0 | 0 | - |
| anon.raw.HIST | 43040 | 406048 | 950816 | 1901088 | 3801632 | 0.97 |
| anon.raw.HIST.slot0:T | 8528 | 131408 | 262480 | 524624 | 1048912 | 1.04 |
| anon.raw.HIST.slot1:HASH-TABLE | 34512 | 274640 | 688336 | 1376464 | 2752720 | 0.95 |
| anon.raw.HIST.slot2:BIT | 0 | 0 | 0 | 0 | 0 | - |
| anon.raw.HIST.slot3:(INTEGER_0_4611686018427387903) | 0 | 0 | 0 | 0 | 0 | - |
| anon.raw.HIST.slot4:BIT | 0 | 0 | 0 | 0 | 0 | - |
| anon.raw.dynamic_usage | 531215200 | 569696048 | 633102368 | 925637552 | 1424646256 | 0.19 |
| anon.raw.large.(UNSIGNED-BYTE_32).bytes | 7242976 | 7242976 | 7242976 | 7767296 | 9628576 | 0.046 |
| anon.raw.large.(UNSIGNED-BYTE_64).bytes | - | - | - | 70221840 | 358498416 | - |
| anon.raw.large.(UNSIGNED-BYTE_8).bytes | 1310800 | 1310800 | 1310800 | 2621552 | 1310800 | 0.06 |
| anon.raw.large.CHARACTER.bytes | 1172880 | 1172880 | 1172880 | 1172880 | 1172880 | 0 |
| anon.raw.large.FIXNUM.bytes | 8000016 | 8000016 | 8000016 | 8000016 | 8000016 | 0 |
| anon.raw.large.T.bytes | 12783104 | 12783104 | 14723104 | 16662976 | 20542720 | 0.094 |
| open_cpu_s.replay | 0.59 | 4.87 | 10.9 | 20.7 | 45.4 | 0.93 |
| open_s.checkpoint | 0.352 | 1.62 | 3.07 | 7.16 | 13.5 | 0.784 |
| open_s.replay | 0.599 | 4.84 | 10.8 | 20.5 | 45 | 0.925 |
| publish.cpu_s | 1.07 | 9.25 | 20.7 | 45.2 | 91.1 | 0.96 |
| publish.wall_s | 1.07 | 9.23 | 20.6 | 45 | 90.9 | 0.959 |
| publish.write_octets | 5437555 | 50793698 | 116556822 | 232032894 | 463208285 | 0.961 |
| rss.at_rest.anon | 44236 | 82692 | 146488 | 471840 | 1086508 | 0.67 |
| rss.at_rest.file | 564252 | 564056 | 564480 | 564364 | 564284 | 0 |
| rss.at_rest.vmrss | 608488 | 646748 | 710968 | 1036204 | 1650792 | 0.189 |
| rss.peak.anon | 44236 | 101108 | 179084 | 596692 | 1082668 | 0.688 |
| rss.peak.hwm | 690336 | 810028 | 924132 | 1205956 | 1650792 | 0.174 |
| site.fdatasync_p50_ms | 0.001 | 0.001 | 0.001 | 0.001 | 0.001 | 0 |
| site.fdatasync_p99_ms | 0.004 | 0.004 | 0.003 | 0.003 | 0.004 | -0.034 |
| size.config.json | 175 | 175 | 175 | 175 | 175 | 0 |
| size.config/#.cfg | 124 | 124 | 124 | 124 | 124 | 0 |
| size.decisions/decisions.fnj | 168444 | 168450 | 168456 | 168456 | 168493 | 0 |
| size.filesystem-identity.fnmi | 79 | 79 | 79 | 79 | 79 | 0 |
| size.journal/#.log | 1048802 | 1048802 | 1048802 | 1048802 | 1048802 | -0 |
| size.keys/node-secret.key | 61 | 61 | 61 | 61 | 61 | 0 |
| size.peer-flight-profile | 52 | 52 | 52 | 52 | 52 | -0 |
| size.store-checkpoint.fnsc | 4388979 | 49745122 | 115508246 | 230984318 | 462159709 | 1.01 |
| size.writer.lock | 0 | 0 | 0 | 0 | 0 | - |
| store.octets | 5606716 | 50962865 | 116725995 | 232202067 | 463377495 | 0.955 |

Conditions: box hbox (16 cores), load [14.35, 14.42, 16.07] at start and [19.81, 17.86, 17.03] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-100k/W15_1k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-100k/W15_1k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@1k  target=fn-core arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.506 | - | - | - | - | 173912 | 52928 | 120984 | 244184 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 162016 | 41032 | 120984 | 244184 | 0.03 | 0 | 0 | - | - |
| census | 0.501 | - | - | - | - | 161220 | 40236 | 120984 | 244184 | 0.23 | 0 | 0 | - | - |
| publish | 1.05 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 0.351 | - | - | - | - | 163816 | 42688 | 121128 | 182204 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [19.81, 17.86, 17.03] at start and [19.2, 17.91, 17.07] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-100k/W15_1k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@10k  target=fn-core arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 4.12 | - | - | - | - | 218644 | 97444 | 121200 | 383948 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 200384 | 79184 | 121200 | 383948 | 0.04 | 0 | 0 | - | - |
| census | 1 | - | - | - | - | 200692 | 79492 | 121200 | 383948 | 0.33 | 0 | 0 | - | - |
| publish | 8.42 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 1.63 | - | - | - | - | 216440 | 95572 | 120868 | 307172 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [19.2, 17.91, 17.07] at start and [18.57, 17.93, 17.11] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-100k/W15_10k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@25k  target=fn-core arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 10.3 | - | - | - | - | 295548 | 174656 | 120892 | 485436 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 263088 | 142196 | 120892 | 485436 | 0.07 | 0 | 0 | - | - |
| census | 1 | - | - | - | - | 263256 | 142364 | 120892 | 485436 | 0.44 | 0 | 0 | - | - |
| publish | 20.3 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 3.51 | - | - | - | - | 308656 | 187252 | 121404 | 581968 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [18.52, 17.93, 17.12] at start and [15.28, 17.13, 16.89] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-100k/W15_25k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@50k  target=fn-core arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 21.3 | - | - | - | - | 495232 | 374180 | 121052 | 670748 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 600444 | 479392 | 121052 | 863108 | 21.1 | 0 | 0 | - | - |
| census | 1.5 | - | - | - | - | 504392 | 383340 | 121052 | 863108 | 1.67 | 0 | 0 | - | - |
| publish | 43.9 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 7.07 | - | - | - | - | 454068 | 332960 | 121108 | 830092 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [15.28, 17.13, 16.89] at start and [16.57, 17.05, 16.89] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-100k/W15_50k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@100k  target=fn-core arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 40.7 | - | - | - | - | 751136 | 629904 | 121232 | 1112396 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 1248500 | 1127268 | 121232 | 1248500 | 21.2 | 0 | 0 | - | - |
| census | 1.5 | - | - | - | - | 817376 | 696144 | 121232 | 1465460 | 1.71 | 0 | 0 | - | - |
| publish | 102.5 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 16 | - | - | - | - | 730488 | 609248 | 121240 | 1953152 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [16.57, 17.05, 16.89] at start and [16.37, 16.58, 16.72] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-100k/W15_100k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15  target=fn-core arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| T-OPEN | owner start to LISTENING from checkpoint at 50k (the fixture nearest F6's 40k, so stricter) and the exponent of open time against n (full replay and checkpoint) | open_s.checkpoint@50k <= 10 | 6.96 | NOT-MEASURED (per-core busy on the cell's cores was not recorded (load 19.81)) |
|  |  | open_s.checkpoint.exponent <= 1 | 0.881 |  |
|  |  | open_s.replay.exponent <= 1 | 0.956 |  |
| T-PUB | publication (checkpoint) of a 50k store: octets written O(changed) not O(store) (exponent against n <= 0.5); longest POST stall while it runs <= 2 s (time check) | publish.stall_max_s <= 2 | - | FAIL |
|  |  | publish.write_octets.exponent <= 0.5 | 0.961 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|

Metrics by store size (octets/KiB/seconds as named; exponent = fitted slope of log value on log n):

| metric | 1k | 10k | 25k | 50k | 100k | exponent |
|---|---|---|---|---|---|---|
| anon.raw.ARENA | 25248 | 393888 | 787104 | 1573536 | 3146400 | 1.04 |
| anon.raw.ARENA.slot0:T | 16496 | 262256 | 524400 | 1048688 | 2097264 | 1.04 |
| anon.raw.ARENA.slot1:T | 8208 | 131088 | 262160 | 524304 | 1048592 | 1.04 |
| anon.raw.ARENA.slot2:T | 16 | 16 | 16 | 16 | 16 | 0 |
| anon.raw.ARENA.slot3:T | 528 | 528 | 528 | 528 | 528 | 0 |
| anon.raw.CAT | 712688 | 6779952 | 16579312 | 33120160 | 66191552 | 0.983 |
| anon.raw.CAT.slot0:T | 646496 | 5996128 | 14908640 | 29786976 | 59539488 | 0.982 |
| anon.raw.CAT.slot1:T | 40512 | 532752 | 1057808 | 2107920 | 4208144 | 0.999 |
| anon.raw.CAT.slot2:T | 25424 | 250816 | 612608 | 1225008 | 2443664 | 0.991 |
| anon.raw.CAT.slot3:HASH-TABLE | 128 | 128 | 128 | 128 | 128 | 0 |
| anon.raw.CAT.slot4:HASH-TABLE | 128 | 128 | 128 | 128 | 128 | 0 |
| anon.raw.CAT.slot5:(INTEGER_0_4611686018427387903) | 0 | 0 | 0 | 0 | 0 | - |
| anon.raw.HIST | 43040 | 406048 | 950816 | 1901088 | 3801632 | 0.97 |
| anon.raw.HIST.slot0:T | 8528 | 131408 | 262480 | 524624 | 1048912 | 1.04 |
| anon.raw.HIST.slot1:HASH-TABLE | 34512 | 274640 | 688336 | 1376464 | 2752720 | 0.95 |
| anon.raw.HIST.slot2:BIT | 0 | 0 | 0 | 0 | 0 | - |
| anon.raw.HIST.slot3:(INTEGER_0_4611686018427387903) | 0 | 0 | 0 | 0 | 0 | - |
| anon.raw.HIST.slot4:BIT | 0 | 0 | 0 | 0 | 0 | - |
| anon.raw.dynamic_usage | 94619504 | 132751376 | 195755536 | 506547168 | 1000947968 | 0.488 |
| anon.raw.large.(UNSIGNED-BYTE_32).bytes | - | - | - | 262160 | 1415632 | - |
| anon.raw.large.(UNSIGNED-BYTE_64).bytes | - | - | - | 70221840 | 358531184 | - |
| anon.raw.large.(UNSIGNED-BYTE_8).bytes | 1835120 | 1835120 | 1835120 | 3145872 | 1835120 | 0.047 |
| anon.raw.large.T.bytes | 1443072 | 1443072 | 2937392 | 4431616 | 9202688 | 0.381 |
| open_cpu_s.replay | 0.5 | 4.15 | 10.4 | 21.5 | 41.2 | 0.961 |
| open_s.checkpoint | 0.242 | 1.52 | 3.4 | 6.96 | 14.6 | 0.881 |
| open_s.replay | 0.506 | 4.12 | 10.3 | 21.3 | 40.7 | 0.956 |
| publish.cpu_s | 0.834 | 8.28 | 20.2 | 43.9 | 92.9 | 1.02 |
| publish.wall_s | 0.831 | 8.25 | 20.1 | 43.7 | 93.2 | 1.02 |
| publish.write_octets | 5437555 | 50793698 | 116556822 | 232032894 | 463208285 | 0.961 |
| rss.at_rest.anon | 41032 | 79184 | 142196 | 479392 | 1127268 | 0.694 |
| rss.at_rest.file | 120984 | 121200 | 120892 | 121052 | 121232 | 0 |
| rss.at_rest.vmrss | 162016 | 200384 | 263088 | 600444 | 1248500 | 0.408 |
| rss.peak.anon | 41032 | 97444 | 142196 | 729384 | 1111524 | 0.72 |
| rss.peak.hwm | 244184 | 383948 | 485436 | 863108 | 1248500 | 0.343 |
| site.fdatasync_p50_ms | 0.001 | 0.001 | 0.002 | 0.001 | 0.001 | 0.022 |
| site.fdatasync_p99_ms | 0.003 | 0.002 | 0.004 | 0.003 | 0.003 | 0.025 |
| size.config.json | 175 | 175 | 175 | 175 | 175 | 0 |
| size.config/#.cfg | 124 | 124 | 124 | 124 | 124 | 0 |
| size.decisions/decisions.fnj | 168444 | 168450 | 168456 | 168456 | 168530 | 0 |
| size.filesystem-identity.fnmi | 79 | 79 | 79 | 79 | 79 | 0 |
| size.journal/#.log | 1048802 | 1048802 | 1048802 | 1048802 | 1048802 | -0 |
| size.keys/node-secret.key | 61 | 61 | 61 | 61 | 61 | 0 |
| size.peer-flight-profile | 52 | 52 | 52 | 52 | 52 | -0 |
| size.store-checkpoint.fnsc | 4388979 | 49745122 | 115508246 | 230984318 | 462159709 | 1.01 |
| size.writer.lock | 0 | 0 | 0 | 0 | 0 | - |
| store.octets | 5606716 | 50962865 | 116725995 | 232202067 | 463377532 | 0.955 |

Conditions: box hbox (16 cores), load [19.81, 17.86, 17.03] at start and [16.37, 16.58, 16.72] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-100k/W15_1k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-w15-100k/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
