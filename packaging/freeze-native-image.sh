#!/bin/sh
# Freeze already-built native images into a relocatable, source-pinned directory.
#
#   packaging/freeze-native-image.sh BUILD_DIR OUTPUT_DIR
#
# The directory carries the cores, the SBCL runtime, libsodium and the
# ML-DSA-65 library (BUILD_DIR/lib/libfn-mldsa65.so, tools/build_mldsa65.sh)
# in lib/.  It carries no TLS library: the system provides libssl (OpenSSL
# 3.0+ or LibreSSL 3+), HST-016.
set -eu
[ "$#" -eq 2 ] || { echo 'usage: freeze-native-image.sh BUILD_DIR OUTPUT_DIR' >&2; exit 2; }
build=$1 out=$2
[ ! -e "$out" ] || { echo "freeze-native-image: output exists: $out" >&2; exit 4; }
case $out in /*) ;; *) echo 'freeze-native-image: output must be absolute' >&2; exit 2;; esac
first=$build/fn-host
[ -x "$first" ] && [ -s "$first.core" ] || { echo 'freeze-native-image: missing production build' >&2; exit 4; }
runtime=$(sed -n 's/^exec "\([^"]*\)" .*/\1/p' "$first")
sbcl_home=$(sed -n "s/^export SBCL_HOME='\([^']*\)'/\1/p" "$first")
[ -x "$runtime" ] && [ -d "$sbcl_home" ] || { echo 'freeze-native-image: missing SBCL runtime' >&2; exit 4; }
mldsa=$build/lib/libfn-mldsa65.so
[ -s "$mldsa" ] || { echo "freeze-native-image: missing $mldsa (tools/build_mldsa65.sh)" >&2; exit 4; }
if [ -n "${FN_FREEZE_SODIUM:-}" ]; then
  sodium=$FN_FREEZE_SODIUM
else
  command -v ldconfig >/dev/null || { echo 'freeze-native-image: Linux ldconfig required' >&2; exit 4; }
  sodium=$(ldconfig -p | awk '/libsodium\.so\.23 / {print $NF; exit}')
fi
[ -n "$sodium" ] && [ -s "$sodium" ] || { echo 'freeze-native-image: missing libsodium.so.23' >&2; exit 4; }
mkdir -p "$out/runtime/sbcl-home" "$out/lib"
cp -p "$runtime" "$out/runtime/sbcl"
cp -RL "$sbcl_home"/. "$out/runtime/sbcl-home"/
cp -L "$sodium" "$out/lib/libsodium.so.23"
cp -L "$mldsa" "$out/lib/libfn-mldsa65.so"
variants="fn-host fn-host-developer fn-host-dtn"
if [ "${FN_FREEZE_VARIANTS+x}" = x ]; then
  [ -n "$FN_FREEZE_VARIANTS" ] || { echo 'freeze-native-image: empty variant selection' >&2; exit 2; }
  variants=
  set -f
  for name in $FN_FREEZE_VARIANTS; do
    case $name in
      fn-host|fn-host-developer|fn-host-dtn|fn-host-dtn-developer) ;;
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
  {
    echo '#!/bin/sh'
    echo '# fn frozen image launcher v2'
    echo 'here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)'
    echo 'export SBCL_HOME="$here/runtime/sbcl-home/"'
    echo 'export LD_LIBRARY_PATH="$here/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"'
    sed -n '/^exec "/p' "$src" |
      sed -e 's|^exec "[^"]*"|exec "$here/runtime/sbcl"|' \
          -e "s|--core \"[^\"]*\"|--core \"\$here/$name.core\"|"
  } > "$out/$name"
  chmod 0755 "$out/$name"
done
(cd "$out" && find fn-host* runtime lib -type f | sort | xargs sha256sum > image.sha256)
