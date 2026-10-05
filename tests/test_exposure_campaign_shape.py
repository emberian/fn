"""The public_exposure credential-guessing campaign must reconnect.

One connection is closed at its third failed authentication (specs/nntp.md
"Authentication failures", fn-auth-failure-limit 3); the per-address budget
(exposure-auth-failures) refuses the address at the NEXT greeting.  A
campaign that guesses on one connection can therefore never see the address
refusal (ledger SCEN-EXPOSURE-LOCKOUT).  This is the source-level witness of
that shape; the behaviour is tests.test_native_public_exposure on an image.
"""
import ast
import pathlib
import unittest

SOURCE = pathlib.Path(__file__).with_name("test_native_public_exposure.py")


def connects_to(node, address):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "connect" and len(node.args) == 1
            and isinstance(node.args[0], ast.Constant) and node.args[0].value == address)


class CampaignShape(unittest.TestCase):
    def test_guessing_campaign_reconnects(self):
        tree = ast.parse(SOURCE.read_text())
        loops = [n for n in ast.walk(tree) if isinstance(n, ast.For)
                 and any(connects_to(m, "127.0.0.7") for m in ast.walk(n))]
        if not loops:
            self.fail("SCEN-EXPOSURE-LOCKOUT: the guessing campaign does not reconnect")


if __name__ == "__main__":
    unittest.main()
