"""D27, PRF-171, SCN-101: checkpoint generations past the old 4,096.

Until PRF-171 `fn-cpp-next-generation-from` answered :exhausted at 4,096 and
nothing reclaims a number, so a store got 4,096 checkpoint publications in
its lifetime.  Now a generation number is a uint32 and the names a store
retains are the profile's capacity, max-transactions + 1
(books/checkpoint-publish.lisp
`fn-cpp-next-generation-refuses-exactly-at-the-profile-capacity`, called by
host/native/checkpoint.lisp `fnn-checkpoint-publish` through
host/checkpoint-host.lisp `fn-store-checkpoint-next-generation` with the
opened profile).

The fixture is the test's own: one real published generation, hard-linked
under the next names so the namespace holds 4,097 retained generations
without 4,097 publications (the allocator reads names; the opened store
restores only a selected generation, and none is selected).  Under
max-transactions 8191 the next publication is generation 4097; under
max-transactions 4095 (the old figure as an instance: capacity 4,096) the
4,097th is refused by name and nothing is written.
"""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host-developer is required for raw Store fixtures")
class NativeCheckpointGenerationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-generations-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.payload = self.base / "payload"
        self.payload.write_bytes(b"generation payload\r\n")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)

    def native(self, *args, expected=0):
        result = subprocess.run(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180,
            check=False, text=True)
        self.assertEqual(result.returncode, expected,
                         f"native {args} returned {result.returncode}\n"
                         f"stdout={result.stdout}\nstderr={result.stderr}")
        return result

    def store_with_names(self, name, max_transactions, count):
        store = self.base / name
        self.native("store", store, "init", "--max-transactions", max_transactions,
                    "fn.letters")
        self.native("store", store, "post", "<generations@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        first = self.native("checkpoint", "publish", store)
        self.assertIn("generation=0", first.stdout)
        directory = store / "checkpoints"
        source = directory / "generation-0.fncp"
        self.assertTrue(source.is_file())
        for k in range(1, count):
            os.link(source, directory / "generation-{}.fncp".format(k))
        return store, directory

    def test_publication_past_4096_under_the_profile(self):
        store, directory = self.store_with_names("wide", 8191, 4097)
        published = self.native("checkpoint", "publish", store)
        self.assertIn("generation=4097", published.stdout)
        self.assertTrue((directory / "generation-4097.fncp").is_file())
        status = self.native("checkpoint", "status", store)
        self.assertIn(" 4096 4097 ", status.stdout + " ")

    def test_the_old_figure_is_the_instance_of_max_transactions_4095(self):
        store, directory = self.store_with_names("narrow", 4095, 4096)
        before = sorted(p.name for p in directory.iterdir())
        refused = self.native("checkpoint", "publish", store, expected=1)
        self.assertIn("profile's capacity", refused.stderr)
        self.assertEqual(sorted(p.name for p in directory.iterdir()), before)


if __name__ == "__main__":
    unittest.main()
