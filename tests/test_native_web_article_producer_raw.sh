#!/bin/sh
# witness: raw composition; shared producer required, no owner/image claim.
set -eu
cd "$(dirname "$0")/.."
exec "${FN_SBCL:-sbcl}" --noinform --script tests/native_web_article_producer_raw.lisp
