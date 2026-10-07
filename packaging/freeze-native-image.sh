#!/bin/sh
# Freeze already-built native images into a relocatable, source-pinned directory.
#
#   packaging/freeze-native-image.sh BUILD_DIR OUTPUT_DIR
#
# The directory carries the cores, the SBCL runtime, libsodium and the
# ML-DSA-65 library (BUILD_DIR/lib/libfn-mldsa65.so, tools/build_mldsa65.sh)
# in lib/.  On Linux it also carries the TLS library fn ships (D59,
# PRF-1327): OpenSSL 3.5.8's libcrypto.so.3 and libssl.so.3 under
# openssl/lib/, from FN_FREEZE_OPENSSL (a prefix; the release build names
# packaging/floor-openssl.sh's output, built against the glibc floor), else
# FN_OPENSSL_PREFIX; with neither set the freeze refuses (D64: no default
# prefix).  Each launcher exports FN_OPENSSL_PREFIX as that directory unless
# the caller named one.  It is never put in lib/ (LD_LIBRARY_PATH).  OpenBSD
# keeps the base system's LibreSSL (HST-016) until the OpenBSD conversion.
#
# On OpenBSD, FN_FREEZE_SODIUM names the libsodium to bundle (pkg_add
# libsodium: /usr/local/lib/libsodium.so.11.1 on 7.9, kept under its own
# name for ld.so), and every other shared object the SBCL runtime needs
# outside the base system (libzstd) is bundled beside it; image.sha256 is in
# sha256(1)'s BSD format there.  FN_FREEZE_DYNAMIC_SPACE_MB replaces the heap
# the build inherited (--dynamic-space-size, 32000 MB from ACL2's save) in the
# frozen launchers; SBCL_USER_ARGS at run time still overrides it (SBCL takes
# the last such option).  FN_FREEZE_RUNTIME names the SBCL runtime to bundle
# in place of the one the build ran (packaging/floor-runtime.sh: the same
# version and build-id, built against the Linux release's glibc floor); it
# must print the same --version and start the fn-host core, or nothing is
# frozen.
set -eu
[ "$#" -eq 2 ] || { echo 'usage: freeze-native-image.sh BUILD_DIR OUTPUT_DIR' >&2; exit 2; }
build=$1 out=$2
[ ! -e "$out" ] || { echo "freeze-native-image: output exists: $out" >&2; exit 4; }
case $out in /*) ;; *) echo 'freeze-native-image: output must be absolute' >&2; exit 2;; esac
system=$(uname -s)
case $system in Linux|OpenBSD) ;; *) echo "freeze-native-image: unsupported system $system" >&2; exit 4;; esac
heap=${FN_FREEZE_DYNAMIC_SPACE_MB:-}
case $heap in *[!0-9]*) echo 'freeze-native-image: FN_FREEZE_DYNAMIC_SPACE_MB must be a number of MB' >&2; exit 2;; esac
first=$build/fn-host
[ -x "$first" ] && [ -s "$first.core" ] || { echo 'freeze-native-image: missing production build' >&2; exit 4; }
runtime=$(sed -n 's/^exec "\([^"]*\)" .*/\1/p' "$first")
sbcl_home=$(sed -n "s/^export SBCL_HOME='\([^']*\)'/\1/p" "$first")
[ -x "$runtime" ] && [ -d "$sbcl_home" ] || { echo 'freeze-native-image: missing SBCL runtime' >&2; exit 4; }
mldsa=$build/lib/libfn-mldsa65.so
[ -s "$mldsa" ] || { echo "freeze-native-image: missing $mldsa (tools/build_mldsa65.sh)" >&2; exit 4; }
deflate=$build/lib/libfn-deflate.so
[ -s "$deflate" ] || { echo "freeze-native-image: missing $deflate (tools/build_deflate.sh)" >&2; exit 4; }
blake3=$build/lib/libfn-blake3.so
[ -s "$blake3" ] || { echo "freeze-native-image: missing $blake3 (tools/build_blake3.sh)" >&2; exit 4; }
if [ -n "${FN_FREEZE_SODIUM:-}" ]; then
  sodium=$FN_FREEZE_SODIUM
elif [ "$system" = Linux ]; then
  command -v ldconfig >/dev/null || { echo 'freeze-native-image: Linux ldconfig required' >&2; exit 4; }
  sodium=$(ldconfig -p | awk '/libsodium\.so\.23 / {print $NF; exit}')
else
  echo 'freeze-native-image: set FN_FREEZE_SODIUM to the libsodium to bundle' >&2; exit 4
fi
[ -n "$sodium" ] && [ -s "$sodium" ] || { echo 'freeze-native-image: missing libsodium' >&2; exit 4; }
if [ "$system" = Linux ]; then
  sodium_name=libsodium.so.23
  hash_tool=sha256sum
else
  sodium_name=$(basename "$sodium")
  case $sodium_name in libsodium.so.[0-9]*.[0-9]*) ;; *)
    echo "freeze-native-image: OpenBSD libsodium must be libsodium.so.MAJOR.MINOR: $sodium" >&2; exit 4;; esac
  hash_tool=sha256   # BSD-format lines; checked with sha256 -c
fi
openssl_lib=
if [ "$system" = Linux ]; then
  openssl_prefix=${FN_FREEZE_OPENSSL:-${FN_OPENSSL_PREFIX:-}}
  [ -n "$openssl_prefix" ] || {
    echo "freeze-native-image: FN_FREEZE_OPENSSL or FN_OPENSSL_PREFIX must name the shipped OpenSSL 3.5.8" >&2; exit 2; }
  for d in "$openssl_prefix/lib64" "$openssl_prefix/lib"; do
    if [ -s "$d/libcrypto.so.3" ] && [ -s "$d/libssl.so.3" ]; then openssl_lib=$d; break; fi
  done
  [ -n "$openssl_lib" ] || {
    echo "freeze-native-image: no OpenSSL libcrypto.so.3/libssl.so.3 pair under $openssl_prefix (FN_FREEZE_OPENSSL)" >&2; exit 4; }
  grep -aq 'OpenSSL 3\.5\.8 ' "$openssl_lib/libcrypto.so.3" || {
    echo "freeze-native-image: $openssl_lib/libcrypto.so.3 is not OpenSSL 3.5.8" >&2; exit 4; }
fi
if [ -n "${FN_FREEZE_RUNTIME:-}" ]; then
  [ -x "$FN_FREEZE_RUNTIME" ] || { echo "freeze-native-image: FN_FREEZE_RUNTIME is not executable: $FN_FREEZE_RUNTIME" >&2; exit 4; }
  [ "$("$FN_FREEZE_RUNTIME" --version)" = "$("$runtime" --version)" ] || {
    echo 'freeze-native-image: FN_FREEZE_RUNTIME is not the build'"'"'s SBCL version' >&2; exit 4; }
  # The runtime refuses a core saved under another build-id; this starts
  # the core and exits, with no ACL2 or fn code run.
  SBCL_HOME=$sbcl_home "$FN_FREEZE_RUNTIME" --core "$first.core" --noinform --disable-ldb \
    --end-runtime-options --no-userinit --non-interactive --eval '(sb-ext:exit :code 0)' || {
      echo 'freeze-native-image: FN_FREEZE_RUNTIME does not start the fn-host core' >&2; exit 4; }
  runtime=$FN_FREEZE_RUNTIME
fi
mkdir -p "$out/runtime/sbcl-home" "$out/lib"
cp -p "$runtime" "$out/runtime/sbcl"
cp -RL "$sbcl_home"/. "$out/runtime/sbcl-home"/
cp -L "$sodium" "$out/lib/$sodium_name"
cp -L "$mldsa" "$out/lib/libfn-mldsa65.so"
cp -L "$deflate" "$out/lib/libfn-deflate.so"
cp -L "$blake3" "$out/lib/libfn-blake3.so"
if [ -n "$openssl_lib" ]; then
  mkdir -p "$out/openssl/lib"
  cp -L "$openssl_lib/libcrypto.so.3" "$out/openssl/lib/libcrypto.so.3"
  cp -L "$openssl_lib/libssl.so.3" "$out/openssl/lib/libssl.so.3"
fi
if [ "$system" = OpenBSD ]; then
  # The runtime's DT_NEEDED objects outside the base system (/usr/lib) travel
  # with it: pkg_add sbcl links libzstd from /usr/local/lib.
  for needed in $(objdump -p "$runtime" | awk '$1 == "NEEDED" {print $2}'); do
    [ -e "/usr/lib/$needed" ] && continue
    [ -s "/usr/local/lib/$needed" ] || { echo "freeze-native-image: runtime needs $needed, not found" >&2; exit 4; }
    cp -L "/usr/local/lib/$needed" "$out/lib/$needed"
  done
fi
variants="fn-host fn-host-developer fn-host-dtn"
if [ "${FN_FREEZE_VARIANTS+x}" = x ]; then
  [ -n "$FN_FREEZE_VARIANTS" ] || { echo 'freeze-native-image: empty variant selection' >&2; exit 2; }
  variants=
  set -f
  for name in $FN_FREEZE_VARIANTS; do
    case $name in
      fn-host|fn-host-developer|fn-host-dtn|fn-host-dtn-developer|fn-host-reference) ;;
      *) echo "freeze-native-image: unknown variant: $name" >&2; exit 2 ;;
    esac
    case " $variants " in
      *" $name "*) echo "freeze-native-image: duplicate variant: $name" >&2; exit 2 ;;
    esac
    variants="$variants $name"
  done
  set +f
  case " $variants " in
    *" fn-host "*) ;;
    *) echo 'freeze-native-image: fn-host must be selected' >&2; exit 2 ;;
  esac
else
  if [ -e "$build/fn-host-dtn-developer" ] || [ -e "$build/fn-host-dtn-developer.core" ]; then
    variants="$variants fn-host-dtn-developer"
  fi
  # The release's unstripped reference twin, when the build made it.
  if [ -e "$build/fn-host-reference" ] || [ -e "$build/fn-host-reference.core" ]; then
    variants="$variants fn-host-reference"
  fi
fi
for name in $variants; do
  src=$build/$name
  [ -x "$src" ] && [ -s "$src.core" ] || { echo "freeze-native-image: missing $name" >&2; exit 4; }
  source_core=$(sed -n 's/.*--core "\([^"]*\)".*/\1/p' "$src")
  [ -n "$source_core" ] && [ -s "$source_core" ] && cmp -s "$source_core" "$src.core" || {
    echo "freeze-native-image: launcher/core mismatch: $name" >&2; exit 4; }
  [ "$(sed -n '/^exec "/p' "$src" | wc -l | tr -d ' ')" = 1 ] || {
    echo "freeze-native-image: launcher invocation not unique: $name" >&2; exit 4; }
  cp -p "$src.core" "$out/$name.core"
  # A stripped image's build-derived dependency set travels with it.
  if [ -s "$src.world-deps" ]; then cp -p "$src.world-deps" "$out/$name.world-deps"; fi
  {
    echo '#!/bin/sh'
    echo '# fn frozen image launcher v2'
    echo 'here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)'
    echo 'export SBCL_HOME="$here/runtime/sbcl-home/"'
    echo 'export LD_LIBRARY_PATH="$here/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"'
    if [ -n "$openssl_lib" ]; then
      echo 'FN_OPENSSL_PREFIX="${FN_OPENSSL_PREFIX:-$here/openssl}"; export FN_OPENSSL_PREFIX'
    fi
    sed -n '/^exec "/p' "$src" |
      sed -e 's|^exec "[^"]*"|exec "$here/runtime/sbcl"|' \
          -e "s|--core \"[^\"]*\"|--core \"\$here/$name.core\"|" \
          -e "${heap:+s|--dynamic-space-size [0-9][0-9]*|--dynamic-space-size $heap|}"
  } > "$out/$name"
  chmod 0755 "$out/$name"
done
(cd "$out" && find fn-host* runtime lib $( [ -z "$openssl_lib" ] || echo openssl ) -type f | LC_ALL=C sort | xargs $hash_tool > image.sha256)
