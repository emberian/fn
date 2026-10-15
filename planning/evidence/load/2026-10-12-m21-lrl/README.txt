L-FRESH (memory, not time) at lane/memory-run-launch f5963543b images (persvati native tree m21-lrl-6; fn-core built
there by tools/extract/core.sh), 2026-10-12, by lfresh.sh: development-flag small store, fresh; the launcher's probe
and the run under systemd-run MemoryMax=LIMIT, MemorySwapMax=0; one POST and one ARTICLE; VmHWM of the image process.
image (core file)              LIMIT   probe heap  run                                         VmHWM kB  RssAnon kB
fn-core (74 MB)                 256    343 MB      serves C'=31 sum 212/246 MB                  78,168    19,908
fn-core (74 MB)                1024    1111 MB     serves C'=31 sum 215/1014 MB                 80,312    19,804
fn-host production (250 MB)     256    511 MB      refused memory-cannot-hold-the-store sum 346 > 246 MB (store/FILE term)
fn-host production (250 MB)    1024    1279 MB     serves C'=31 sum 384/1014 MB                139,352    21,764
fn-host-developer (683 MB)      256    924 MB      refused memory-cannot-hold-the-store sum 759 > 246 MB
fn-host-developer (683 MB)     1024    1692 MB     serves C'=31 sum 797/1014 MB                162,472    21,940
Which image the bar judges is ember's (DECISIONS item 8). RssFile is the mapped core (file-backed, discounted by
DECISIONS 7).
