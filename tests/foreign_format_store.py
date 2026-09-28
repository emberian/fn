"""A synthesized store of another release (D34: one store format, no migrations).

A store whose config.json names another format word is refused at open by
name: "not an fn store of this release: redeploy fresh".  The refusal tests
need such a store; `make_store(image, root)` initialises a fresh store with
the image under test (`operator CONFIG init`), then replaces its config.json
with ANOTHER_FORMAT_CONFIG: a profile frame sealed under this build's digest
whose word is fn-store-11, followed by three u64 fields.  The octets are
literal, never computed here (Python decides nothing the open decides), and
pinned to ACL2 by tests/acl2/store-profile-open-tests.lisp
(`(equal (spot-other-short) *spot-other-short-octets*)'); the open answers
(:refused :store-format)
(books/store-profile-open.lisp
fn-spo-config-open-store-format-is-exactly-a-foreign-frame).

The rest of the store is this release's, so the only reason the open can
give is the profile frame's.
"""
import os
from pathlib import Path
import socket
import subprocess

ANOTHER_FORMAT_CONFIG = bytes.fromhex(
    "464e534d010100000025000b666e2d73746f72652d3131000000000000000100"
    "0000000000000200000000000000032de1dff908c7ced663c11ae768cbad1d50"
    "2711429adc221942ca476df97b928e")

# The line ACL2 renders for the refusal (fn-spo-refusal-text).
LINE = "open refused reason=store-format: not an fn store of this release: redeploy fresh"


def write_config(root, store, name="fn"):
    """A loopback fn.toml for STORE under ROOT; returns its path."""
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        port = probe.getsockname()[1]
    config = Path(root) / (name + ".toml")
    config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                      '[control]\npath = "{}"\n'.format(store, port,
                                                           Path(root) / (name + "-control.sock")),
                      encoding="ascii")
    return config


def make_store(image, root, env=None, argv=None):
    """A store under ROOT/another-format/store whose config.json names
    another format word.

    Returns (store, config, own): OWN is the config.json octets this
    release wrote, which the control case puts back.  IMAGE is a native
    launcher (run as IMAGE --fn ...); ARGV, when given, replaces [IMAGE,
    "--fn"] (a release's bin/fn)."""
    base = Path(root) / "another-format"
    base.mkdir(parents=True)
    store = base / "store"
    config = write_config(base, store)
    env = dict(os.environ if env is None else env, ACL2_CUSTOMIZATION="NONE")
    env.pop("ACL2_SYSTEM_BOOKS", None)
    head = list(argv) if argv else [str(image), "--fn"]
    init = subprocess.run(head + ["operator", str(config), "init", "fn.test"],
                          env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600)
    if init.returncode != 0:
        raise RuntimeError("operator init exited {}: {}".format(
            init.returncode, init.stderr.decode("utf-8", "replace")[-2000:]))
    path = store / "config.json"
    own = path.read_bytes()
    mode = path.stat().st_mode & 0o777
    path.write_bytes(ANOTHER_FORMAT_CONFIG)
    path.chmod(mode)
    return store, config, own
