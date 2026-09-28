#!/bin/sh
# Build a qualified ACL2 for proof_repl on a machine that is not a farm box
# (the laptop), and name it in ~/.config/fn/acl2.
#
#   tools/build_local_acl2.sh [DEST]        (default ~/tools/acl2-fn)
#
# The same ACL2 the boxes run: the github acl2 8.7 tag tarball (sha256
# d6013c22..., hbox's /tank/fn/acl2.tar.gz and Homebrew's source), built
# non-parallel on SBCL (SBCL=, default the one on PATH, resolved to its real
# binary and SBCL_HOME), with the system books fn includes certified by that
# core.  The launcher it writes, DEST/acl2-literal-4g-tls64k, is a literal
# `exec sbcl --core` with hbox's flags (--tls-limit 65536,
# --dynamic-space-size 4096), which tools/acl2_toolchain.py qualifies.
#
# Why not Homebrew's `acl2` (lane laptop-acl2, 2026-09-28): its saved_acl2
# splices ${SBCL_USER_ARGS} (unqualified), runs at --tls-limit 16384 (an
# image world exhausts it), and the formula builds ACL2 and ACL2(p) in one
# tree, after which `(local (include-book "arithmetic-5/top" :dir :system))`
# inside an encapsulate fails ("INCREMENT-TIMER@PAR ... not a rule name"),
# so every book that includes arithmetic-5 locally refuses.
#
# Idempotent: each step is skipped when its product exists.  Not for the farm
# boxes (their launchers are tools/farm.py HOSTS).
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
dest=${1:-$HOME/tools/acl2-fn}
url=https://github.com/acl2/acl2/archive/refs/tags/8.7.tar.gz
sum=d6013c22e190cbd702870d296b5370a068c14625bf7f9d305d2d87292b594d52
books="arithmetic/top arithmetic-5/top ihs/quotient-remainder-lemmas std/lists/append
std/lists/rev std/lists/revappend std/testing/assert-bang std/testing/assert-equal
std/testing/must-fail"
sbcl=$(command -v "${SBCL:-sbcl}") || { echo "build_local_acl2: no sbcl" >&2; exit 2; }
mkdir -p "$dest"
cd "$dest"
if [ ! -f acl2.tar.gz ]; then
    curl -fsSL "$url" -o acl2.tar.gz.part && mv acl2.tar.gz.part acl2.tar.gz
fi
if command -v sha256sum >/dev/null; then echo "$sum  acl2.tar.gz" | sha256sum -c -
else echo "$sum  acl2.tar.gz" | shasum -a 256 -c -; fi
if [ ! -d acl2-8.7 ]; then
    rm -rf acl2-8.7.part && mkdir acl2-8.7.part
    tar xzf acl2.tar.gz -C acl2-8.7.part --strip-components 1 && mv acl2-8.7.part acl2-8.7
fi
[ -f acl2-8.7/saved_acl2.core ] || make -C acl2-8.7 LISP="$sbcl" USE_QUICKLISP=0
# The runtime and SBCL_HOME the generated saved_acl2 names (literal paths).
runtime=$(sed -n 's/^exec "\([^"]*\)".*/\1/p' acl2-8.7/saved_acl2)
home=$(sed -n "s/^export SBCL_HOME='\([^']*\)'.*/\1/p" acl2-8.7/saved_acl2)
[ -x "$runtime" ] && [ -n "$home" ] || { echo "build_local_acl2: cannot read acl2-8.7/saved_acl2" >&2; exit 3; }
# Two jobs: these run outside tools/acl2_slots.py's pool.
make -C acl2-8.7/books -j 2 ACL2="$dest/acl2-8.7/saved_acl2" USE_QUICKLISP=0 \
    $(for book in $books; do printf '%s.cert ' "$book"; done)
launcher=$dest/acl2-literal-4g-tls64k
cat > "$launcher.part" <<LAUNCHER
#!/bin/sh
# fn's local ACL2 (tools/build_local_acl2.sh): ACL2 8.7, hbox's acl2-literal-4g-tls64k flags.
export SBCL_HOME='$home'
exec "$runtime" --tls-limit 65536 --dynamic-space-size 4096 --control-stack-size 64 --disable-ldb --core "$dest/acl2-8.7/saved_acl2.core" --end-runtime-options --no-userinit --eval '(acl2::sbcl-restart)' "\$@"
LAUNCHER
chmod +x "$launcher.part" && mv "$launcher.part" "$launcher"
python3 "$root/tools/acl2_toolchain.py" identity "$launcher"
mkdir -p "$HOME/.config/fn"
printf '%s\n' "$launcher" > "$HOME/.config/fn/acl2"
echo "build_local_acl2: $launcher (named in ~/.config/fn/acl2)"
