"""The delegating POST-step theorems state the env the served step uses (X07b)."""
import unittest
from pathlib import Path

BOOKS = Path(__file__).resolve().parents[1] / "books"


def form(book, name):
    text = (BOOKS / book).read_text()
    start = text.index("(defthm " + name)
    return text[start:text.index("\n(", start + 1)]


class PostDelegatesEnvTests(unittest.TestCase):
    def test_the_delegating_theorems_use_the_command_env(self):
        for book, name in (
                ("productive-read-chain.lisp", "fn-pcr-post-delegates-a-read-without-offer-by-definition"),
                ("served-head-bridge.lisp", "fn-shd-post-delegates-a-read-without-offer-by-definition")):
            self.assertTrue("fn-post-command-env" in form(book, name),
                            name + " must be stated over fn-post-command-env")


if __name__ == "__main__":
    unittest.main()
