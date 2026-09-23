#!/bin/sh
set -eu
[ "$1" = "--fn" ] && [ "$2" = "hybrid-verify-source" ] && [ "$#" -eq 4 ] || exit 64
remote_dir=$(ssh hbox 'mktemp -d /tmp/fn-mini-p2.XXXXXX')
case "$remote_dir" in /tmp/fn-mini-p2.*) ;; *) exit 70;; esac
trap 'ssh hbox "rm -rf $remote_dir" >/dev/null 2>&1 || true' EXIT HUP INT TERM
scp -q "$3" "hbox:$remote_dir/carrier"
scp -q "$4" "hbox:$remote_dir/ml.pem"
ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 /tank/fn/gates/integrate-reader-repair-20260923/build/fn-host-developer --fn hybrid-verify-source $remote_dir/carrier $remote_dir/ml.pem"
