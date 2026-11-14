#!/bin/sh
# Build the carrier beside the caller-selected native artifacts, never in source.
set -eu
if [ "$#" -ne 1 ]; then
  echo 'usage: host/build-deflate.sh OUTPUT-LIBRARY' >&2
  exit 2
fi
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
case "$(uname -s)" in
  Darwin) link_flag=-dynamiclib ;;
  *) link_flag=-shared ;;
esac
exec "${CC:-cc}" "$link_flag" -fPIC -O2 -Wall -Wextra -Werror \
  "$script_dir/fn2-deflate.c" -lz -o "$1"
