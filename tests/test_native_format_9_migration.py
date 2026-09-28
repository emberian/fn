"""Format 9 -> 10 across a reinstall (D34, lane format-bump-10): the release
before exports, this release imports, and the history is the same.

Opt-in: FN_FORMAT9_HOST names a format-9 image (a developer launcher of the
release before format 10) and FN_FORMAT9_STORE a format-9 store to copy
(hbox: /tank/fn/scratch/fixtures/n1k-2k/store, 1,000 POSTed 2 KiB articles);
FN_NATIVE_DEVELOPER_HOST (or build/fn-host-developer) is the format-10 image
under test.

The case:

* this image refuses the format-9 store at its open by name
  (`reason=store-format-9`, with the way out), exit 1, its files unchanged;
* the format-9 image exports it (its MANIFEST: SHA-256 lines);
* this image imports the archive (books/store-export.lisp fn-sxp-import-plan:
  the MANIFEST checked under SHA-256, the profile translated by
  books/store-format-9.lisp, the records by books/store-format-9-records.lisp)
  and the new store opens: journal/000000.log (its own genesis) and segment 1
  chained from it, the record count unchanged;
* "identical" (specs/storage.md STO-028): this image exports the imported
  store and the two archives hold the same records in the same order, each
  record's octets equal except the two identity fields of an article record,
  which are the BLAKE3 identities of its own Message-ID and payload (checked
  here by an independent computation, tools/blake3_ref.py and the identity
  profile of books/identity.lisp: label, 0, version 1, algorithm 2, digest);
  every line of the second MANIFEST is the BLAKE3 of its entry.
"""
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import blake3_ref  # noqa: E402

F9 = os.environ.get("FN_FORMAT9_HOST")
F9_STORE = os.environ.get("FN_FORMAT9_STORE")
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
READY = bool(F9 and F9_STORE and Path(F9).is_file() and Path(F9_STORE).is_dir()
             and IMAGE.is_file())

SUBJECT = b"fn/subject/v1"
OBLIGATION = b"fn/obligation/v1"


def cbor_items(b):
    """A record's top-level CBOR items: ('u', n) or ('b', bytes), in order."""
    out, p = [], 0
    while p < len(b):
        ib = b[p]; major, info = ib >> 5, ib & 31; p += 1
        if info < 24:
            n = info
        elif info in (24, 25, 26, 27):
            w = {24: 1, 25: 2, 26: 4, 27: 8}[info]
            n = int.from_bytes(b[p:p + w], "big"); p += w
        else:
            raise ValueError("indefinite item")
        if major == 0:
            out.append(("u", n))
        elif major == 2:
            out.append(("b", b[p:p + n])); p += n
        else:
            raise ValueError("major type %d" % major)
    return out


def identity(label, preimage):
    return (label + b"\x00\x01\x02" + blake3_ref.blake3(preimage)).hex().encode()


def expected_identities(msgid, payload):
    s = identity(SUBJECT, SUBJECT + b"\x00" + struct.pack(">I", len(payload)) + payload)
    sb = bytes.fromhex(s.decode())
    o = identity(OBLIGATION, OBLIGATION + b"\x00" + struct.pack(">I", len(msgid)) + msgid
                 + struct.pack(">I", len(sb)) + sb)
    return o, s


def config(root, store, name, port):
    path = Path(root) / (name + ".toml")
    path.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                    '[control]\npath = "{}"\n'.format(store, port, Path(root) / (name + ".sock")),
                    encoding="ascii")
    return path


@unittest.skipUnless(READY, "set FN_FORMAT9_HOST, FN_FORMAT9_STORE and a format-10 image")
class FormatNineMigrationTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-f9-migration-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
        self.env.pop("ACL2_SYSTEM_BOOKS", None)

    def run_image(self, image, *args):
        r = subprocess.run([str(image), "--fn", *map(str, args)], cwd=ROOT, env=self.env,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=3600)
        out = (r.stdout + r.stderr).decode("utf-8", "replace")
        print("$", Path(image).name, *args, "->", r.returncode, "\n" + out.strip()[-1500:], flush=True)
        return r.returncode, out

    def archive_records(self, archive):
        names = sorted(p.name for p in (archive / "records").iterdir())
        return names, [(archive / "records" / n).read_bytes() for n in names]

    def test_a_format_9_store_exports_there_and_imports_here_with_the_same_history(self):
        src = self.tmp / "src"
        shutil.copytree(F9_STORE, src, symlinks=True)
        (src / "writer.lock").touch(mode=0o600)
        # This image refuses it by name, with the way out, and writes nothing.
        before = sorted(str(p) for p in src.rglob("*"))
        rc, out = self.run_image(IMAGE, "store", src, "status")
        self.assertEqual(rc, 1, out)
        self.assertIn("reason=store-format-9", out)
        self.assertIn("export it with that release", out)
        self.assertEqual(sorted(str(p) for p in src.rglob("*")), before)
        # The release before exports it.
        rc, out = self.run_image(F9, "store", src, "rebind-filesystem")
        self.assertEqual(rc, 0, out)
        a9 = self.tmp / "archive-9"
        rc, out = self.run_image(F9, "operator", config(self.tmp, src, "f9", 18231),
                                 "store", "export", a9)
        self.assertEqual(rc, 0, out)
        # This image imports it: a new store with its own genesis.
        dst = self.tmp / "dst"
        rc, out = self.run_image(IMAGE, "operator", config(self.tmp, dst, "f10", 18232),
                                 "store", "import", a9)
        self.assertEqual(rc, 0, out)
        self.assertTrue((dst / "journal" / "000000.log").is_file())
        names9, records9 = self.archive_records(a9)
        rc, out = self.run_image(IMAGE, "store", dst, "digest")
        self.assertEqual(rc, 0, out)
        self.assertIn("digest history records={} ".format(len(records9)), out)
        self.assertIn("digest genesis ", out)
        # And exports it again: the same records, identities re-derived.
        a10 = self.tmp / "archive-10"
        rc, out = self.run_image(IMAGE, "operator", config(self.tmp, dst, "f10b", 18233),
                                 "store", "export", a10)
        self.assertEqual(rc, 0, out)
        names10, records10 = self.archive_records(a10)
        self.assertEqual(names10, names9)
        articles, retention, mapping = 0, 0, {}
        for old, new in zip(records9, records10):
            it9, it10 = cbor_items(old), cbor_items(new)
            self.assertEqual(len(it9), len(it10))
            if it9[0] == ("b", b"fn-r"):
                articles += 1
                ng = it9[7][1]
                end = 8 + ng
                msgid, payload = it9[5][1], it9[6][1]
                o, s = expected_identities(msgid, payload)
                self.assertEqual(it10[end], ("b", o))
                self.assertEqual(it10[end + 1], ("b", s))
                mapping[it9[end][1]], mapping[it9[end + 1][1]] = o, s
                keep = [i for i in range(len(it9)) if i not in (end, end + 1)]
                self.assertEqual([it9[i] for i in keep], [it10[i] for i in keep])
            elif it9[0] == ("b", b"fn-e") and len(it9) == 10:
                # A retention event: its obligation (6) and subject (7) through
                # the articles' map; every other item kept.
                retention += 1
                for i in (6, 7):
                    self.assertEqual(it10[i], ("b", mapping.get(it9[i][1], it9[i][1])))
                keep = [i for i in range(10) if i not in (6, 7)]
                self.assertEqual([it9[i] for i in keep], [it10[i] for i in keep])
            else:
                self.assertEqual(old, new)
        self.assertGreater(articles, 0)
        print("articles={} retention={} records={}".format(articles, retention, len(records9)),
              flush=True)
        # Every line of the format-10 MANIFEST is BLAKE3 (b3sum's format).
        for line in (a10 / "MANIFEST").read_bytes().splitlines():
            hexd, name = line.split(b"  ", 1)
            self.assertEqual(blake3_ref.blake3((a10 / name.decode()).read_bytes()).hex(),
                             hexd.decode())


if __name__ == "__main__":
    unittest.main()
