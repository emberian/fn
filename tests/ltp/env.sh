# Shared environment for the fn ION/LTP laboratory on the Linux build host.
# ION_ROOT holds the pinned checkout, the --prefix install and the run state.
export ION_ROOT=${ION_ROOT:-/tank/fn/ltp}
export PATH="$ION_ROOT/install/bin:$PATH"
export LD_LIBRARY_PATH="$ION_ROOT/install/lib:${LD_LIBRARY_PATH:-}"
# ION's multi-node support keys every node's working directory off this file.
export ION_NODE_LIST_DIR="$ION_ROOT/run"
mkdir -p "$ION_NODE_LIST_DIR"
