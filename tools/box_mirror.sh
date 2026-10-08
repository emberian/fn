#!/bin/sh
# Keep the rented build boxes' copies of hbox's canonical stores fresh.
#
# Runs ON hbox, from the systemd user timer fn-box-mirror.timer (every 5
# minutes), one instance at a time (flock).  For each live line of
# ~/.config/fn/mirror-targets -- `NAME ADDRESS UNTIL` (UNTIL an ISO UTC
# time; a line past it is skipped) -- it pushes, as fn@ADDRESS:
#   /tank/fn/images/SET  each image set published after the newest one the
#                        box holds (SHA256SUMS present), whole
# Nothing is deleted on either side.  Log: ~/.cache/fn-box-mirror.log.
#
#   tools/box_mirror.sh            one pass (what the timer runs)
#   tools/box_mirror.sh install    copy this script to ~/.local/bin on hbox
#                                  and enable the timer (run on hbox)
#   tools/box_mirror.sh remove     disable the timer (run on hbox)
set -u
TARGETS=$HOME/.config/fn/mirror-targets
LOG=$HOME/.cache/fn-box-mirror.log
case ${1:-} in
    install)
        mkdir -p "$HOME/.local/bin" "$HOME/.config/systemd/user" "$HOME/.config/fn" "$HOME/.cache"
        cp "$0" "$HOME/.local/bin/fn-box-mirror" && chmod 755 "$HOME/.local/bin/fn-box-mirror"
        printf '[Unit]\nDescription=push hbox image sets to rented fn boxes\n[Service]\nType=oneshot\nNice=10\nExecStart=%s/.local/bin/fn-box-mirror\n' "$HOME" \
            > "$HOME/.config/systemd/user/fn-box-mirror.service"
        printf '[Unit]\nDescription=fn-box-mirror every 5 minutes\n[Timer]\nOnActiveSec=3min\nOnUnitInactiveSec=5min\n[Install]\nWantedBy=timers.target\n' \
            > "$HOME/.config/systemd/user/fn-box-mirror.timer"
        touch "$TARGETS"
        systemctl --user daemon-reload && systemctl --user enable --now fn-box-mirror.timer
        exit $? ;;
    remove)
        systemctl --user disable --now fn-box-mirror.timer; exit $? ;;
    '') ;;
    *) sed -n '2,20p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2 ;;
esac
exec 9>"$HOME/.cache/fn-box-mirror.lock"
flock -n 9 || exit 0
now=$(date -u +%s)
[ -f "$TARGETS" ] || exit 0
SSH='ssh -o BatchMode=yes -o ConnectTimeout=20 -o StrictHostKeyChecking=accept-new'
while read -r name addr until; do
    case $name in ''|'#'*) continue ;; esac
    end=$(date -u -d "$until" +%s 2>/dev/null || echo 0)
    [ "$end" -gt "$now" ] || continue
    {
        echo "$(date -u +%FT%TZ) $name $addr"
        have=$($SSH -n "fn@$addr" 'ls /tank/fn/images 2>/dev/null')
        # Only sets published after the newest one the box holds (hbox keeps
        # older sets no lane asks a rented box for).
        floor=0
        for set in $have; do
            m=$(stat -c %Y "/tank/fn/images/$set" 2>/dev/null || echo 0)
            [ "$m" -gt "$floor" ] && floor=$m
        done
        for set in /tank/fn/images/*/; do
            set=$(basename "$set")
            [ -f "/tank/fn/images/$set/SHA256SUMS" ] || continue   # still being published
            echo "$have" | grep -qx "$set" && continue
            [ "$(stat -c %Y "/tank/fn/images/$set")" -gt "$floor" ] || continue
            rsync -a -e "$SSH" "/tank/fn/images/$set" "fn@$addr:/tank/fn/images/" && echo "  image set $set" || echo "  image set $set rsync exit $?"
        done
    } >> "$LOG" 2>&1 < /dev/null
done < "$TARGETS"
