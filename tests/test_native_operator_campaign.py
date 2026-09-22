"""The operator-verb campaign driver's pure parts (no image, no ACL2)."""
import unittest

from tests.campaign import native_operator_campaign as driver


class OperatorCampaignParsingTests(unittest.TestCase):
    def test_recover_line_counts_are_read_exactly(self):
        line = (b"recovered transactions=2 articles=1 staging-orphans=0 "
                b"anchor=none checkpoint=none\n")
        self.assertEqual(driver.parse_recover(line),
                         {"transactions": 2, "articles": 1, "staging_orphans": 0})

    def test_recover_line_with_named_orphans_keeps_the_count(self):
        line = b"recovered transactions=1 articles=1 staging-orphans=1 [.stage-1] anchor=none"
        self.assertEqual(driver.parse_recover(line)["staging_orphans"], 1)

    def test_a_missing_report_is_none_not_zero(self):
        self.assertIsNone(driver.parse_recover(b"fault operator recover\n"))

    def test_undot_removes_only_the_stuffed_dot(self):
        self.assertEqual(driver.undot([b"..x\r\n", b".y\r\n", b"z\r\n"]),
                         b".x\r\n.y\r\nz\r\n")

    def test_articles_are_crlf_and_name_their_message_id(self):
        octets = driver.article("<a@b.invalid>", "s", "body")
        self.assertIn(b"Message-ID: <a@b.invalid>\r\n", octets)
        self.assertTrue(octets.endswith(b"\r\n\r\nbody\r\n"))
        self.assertNotIn(b"\n", octets.replace(b"\r\n", b""))


if __name__ == "__main__":
    unittest.main()
