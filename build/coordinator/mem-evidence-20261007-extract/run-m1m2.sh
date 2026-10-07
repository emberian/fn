#!/bin/sh
# usage: run-m1m2.sh OUTDIR [m1m2.py args]   one hbox job, timeout 40 min
exec env SWARM_MEM_MAX=36G timeout 2400 swarm-build python3 /tank/fn/scratch/extract-measure/m1m2.py "$@"
