#!/bin/sh
# wait for the after setup to finish, then run the alternated rounds; give up after 90 minutes of waiting
S=/tank/fn/scratch/rep-wave-c; cd $S; i=0
while ! grep -q "build rc=" $S/after-setup.out 2>/dev/null; do sleep 20; i=$((i+1)); if [ $i -gt 270 ]; then echo WAIT-TIMEOUT > $S/all.done; exit 1; fi; done
if ! grep -q BUILD-OK $S/after-build.log; then echo SETUP-FAILED > $S/all.done; exit 1; fi
sh $S/rounds.sh
