"""Synthesized stores made by another release (D34, PKT-705, PKT-695, PKT-697).

D34 keeps one store format and no migrations: a store made by another
release is refused at open by name, and the way out is `store export` on the
release that made it and `store import` on this one.  The refusal tests need
such a store; they do not keep one forever.  `make_store(kind, image, root)`
initialises a fresh store with the image under test (`operator CONFIG
init`), then replaces its config.json with a profile frame another release
wrote.  The frames are literal octets, never computed here (Python decides
nothing the open decides); each is pinned to ACL2 by
tests/acl2/store-profile-open-tests.lisp:

* OLDER_RELEASE_CONFIG: the config.json of hbox:/tank/fn/scratch/fixtures/
  n1k-2k/store as it was before batch AS (dev 6407de336's throughput-gate
  image, the default profile): format word fn-store-8, thirteen u64 fields.
  Pinned: `(equal (fn-spo-layout-frame 13 *spot-pre-as*) *spot-pre-as-octets*)`;
  the open answers (:refused :profile-layout 13)
  (books/store-profile-open.lisp fn-spo-open-of-another-layout-refuses-by-name).
* FORMAT_7_CONFIG: a format-7 store's config.json (word
  fn-store-experiment-7).  Pinned: `(equal (spot-format-7-frame)
  *spot-format-7-octets*)`; the open answers (:refused :store-format)
  (fn-spo-config-open-store-format-is-exactly-a-foreign-frame).
* FORMAT_8_CONFIG: a format-8 store's config.json (the per-file layout,
  word fn-store-8, the development preset: what `init --profile
  development' wrote before the record log; sha256 61802dbb...).  Pinned:
  `(equal (fn-bs-config-encode (spot-as-format-8 *fn-bs-profile-development*))
  *spot-format-8-octets*)'; the open answers (:refused :store-format) on
  every image (fn-spo-open-of-a-format-8-profile-refuses-by-name).

Their trailers are BLAKE3 (store format 10), resealed by lane blake3-digest so
the open's layout and format arms, not the digest arm, are what refuse them;
a real older store is SHA-256-sealed and refused by name by
fn-spo-sha256-sealed-profilep.  The rest of the store is this release's, so the only reason the open can
give is the profile frame's.
"""
import os
from pathlib import Path
import socket
import subprocess

OLDER_RELEASE_CONFIG = bytes.fromhex(
    "464e534d010100000094000a666e2d73746f72652d38001e666e2d73746f7265"
    "2d616c6c6f636174696f6e2d66726f6e746965722d3200000000ffffffff0000"
    "0100000000000000000004000000000000000100000000000000000010000000"
    "0000000001000000000000010000000000000010000000000000001000000000"
    "00000010000000000000001000000000000000100000000000000000000088b0"
    "76905248cc3a6014d430d2025f5367426c5a8b1dbef765568fa27252db94")
FORMAT_7_CONFIG = bytes.fromhex(
    "464e534d0101000000570015666e2d73746f72652d6578706572696d656e742d"
    "3700000000001000000000000000008000000000000180000000000000000000"
    "80001e666e2d73746f72652d616c6c6f636174696f6e2d66726f6e746965722d"
    "3266b19deaacbfb100038199423de016146b9c8a76d8f68d2a991849fe921451"
    "19")
FORMAT_8_CONFIG = bytes.fromhex(
    "464e534d0101000000ac000a666e2d73746f72652d38001e666e2d73746f7265"
    "2d616c6c6f636174696f6e2d66726f6e746965722d3200000000000000800000"
    "00000180000000000000010583360000000000008000000000000000ffff0000"
    "0000000001000000000000000080000000000010000000000000001000000000"
    "0000001000000000000000100000000000000010000000000000000000000000"
    "000000000040000000000000010000000000000040007b1f806a23547ae0234a"
    "a6509d1a36381dc1aa5365c197451ff52f81f97eb9ee")
FRAMES = {"older-release": OLDER_RELEASE_CONFIG, "format-7": FORMAT_7_CONFIG,
          "format-8": FORMAT_8_CONFIG}

# The lines ACL2 renders for the two refusals (fn-spo-refusal-text).
OLDER_RELEASE_LINE = ("open refused reason=older-release: store made by an older release "
                      "(profile layout 13 fields, this release expects 16): export it with "
                      "the release that made it, then import it here")
FORMAT_7_LINE = "open refused reason=store-format: reinstall from the release and import"
LINES = {"older-release": OLDER_RELEASE_LINE, "format-7": FORMAT_7_LINE,
         "format-8": FORMAT_7_LINE}


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


def make_store(kind, image, root, env=None, argv=None):
    """A store under ROOT/KIND/store whose config.json another release wrote.

    Returns (store, config, own): OWN is the config.json octets this
    release wrote, which the control case puts back.  KIND is a key of
    FRAMES.  IMAGE is a native launcher (run as IMAGE --fn ...); ARGV, when
    given, replaces [IMAGE, "--fn"] (a release's bin/fn)."""
    frame = FRAMES[kind]
    base = Path(root) / kind
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
    path.write_bytes(frame)
    path.chmod(mode)
    return store, config, own
