"""Native witness for control authority (packet C2, D29).

`operator CONFIG control grant PRINCIPAL VERB NAMESPACE` and `control revoke`
on a running owner go over its control socket to
`fnn-owner-live-admin-serialized` (host/native/admin.lisp), which stages
`fn-native-admin-plan-deltas` (books/native-admin.lisp: `(:grant-control ...)`
code 11, `(:revoke-control ...)` code 12) through `fn-ocfg-step`; admission is
`fn-cfg-delta-reason` (books/config.lisp), whose grant arm is
`fn-cfg-grant-control-admissible-iff`.  A refused request is refused by name
and stages nothing.  `control list` is the read side over the replayed
configuration (`fn-native-admin-query-report`): what a restart reads is
the durable history.

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest -v tests.test_native_control_authority
"""

import unittest

from tests import test_native_live_reconfiguration as live

EXIT_OK, EXIT_REFUSED, IMAGE = live.EXIT_OK, live.EXIT_REFUSED, live.IMAGE

P = "11" * 32
Q = "22" * 32


@unittest.skipUnless(live.executable(IMAGE), "set FN_NATIVE_HOST to a native launcher")
class NativeControlAuthorityTests(live.LiveReconfigurationImageTests):
    """The live-reconfiguration harness (owner, reader, operator); only the
    cases below run here, the inherited ones in their own module."""

    def refused_by_name(self, result, reason):
        self.assertEqual(result.returncode, EXIT_REFUSED, result)
        self.assertIn(reason.upper().encode(), (result.stderr + result.stdout).upper())

    def listed(self):
        result = self.operator("control", "list")
        self.assertEqual(result.returncode, EXIT_OK, result.stderr.decode())
        return result.stdout.decode("ascii").splitlines()

    def test_grant_and_revoke_through_the_live_path_are_durable(self):
        owner = self.start_owner()
        granted = self.operator("control", "grant", P, "cancel", "fn.mod.*")
        self.assertEqual(granted.returncode, EXIT_OK, granted.stderr.decode())
        second = self.operator("control", "grant", Q, "cancel", "fn.test")
        self.assertEqual(second.returncode, EXIT_OK, second.stderr.decode())
        # Refused by name at the plan: reserved namespace, bad principal,
        # an ungrantable verb (C4 is deferred), a malformed pattern.
        self.refused_by_name(self.operator("control", "grant", P, "cancel", "example.*"),
                             "reserved-group-name")
        self.refused_by_name(self.operator("control", "grant", "AB" * 32, "cancel", "fn.x"),
                             "principal")
        self.refused_by_name(self.operator("control", "grant", P, "newgroup", "fn.x"),
                             "verb-not-grantable")
        self.refused_by_name(self.operator("control", "grant", P, "cancel", "fn..*"),
                             "namespace-pattern")
        # The owner keeps serving after every refusal.
        connection, stream = self.reader()
        status, _ = self.command(connection, stream, "GROUP fn.test", False)
        self.assertTrue(status.startswith(b"211"), status)
        self.stop_owner(owner)
        print("NATIVE-CONTROL-AUTHORITY-WITNESS after grants:", self.listed())
        self.assertEqual(self.listed(), ["grant {} cancel fn.mod.*".format(P),
                                         "grant {} cancel fn.test".format(Q)])

        # Revoke on a restarted owner; revoking again is refused at admission
        # (no-such-grant) by the live owner, which stages nothing.
        owner = self.start_owner()
        revoked = self.operator("control", "revoke", P, "cancel", "fn.mod.*")
        self.assertEqual(revoked.returncode, EXIT_OK, revoked.stderr.decode())
        again = self.operator("control", "revoke", P, "cancel", "fn.mod.*")
        self.assertEqual(again.returncode, EXIT_REFUSED, again)
        self.stop_owner(owner)
        print("NATIVE-CONTROL-AUTHORITY-WITNESS after revoke:", self.listed(),
              "second revoke stderr:", again.stderr.decode("utf-8", "replace").strip())
        self.assertEqual(self.listed(), ["grant {} cancel fn.test".format(Q)])


for _name in dir(live.LiveReconfigurationImageTests):
    if _name.startswith("test_") and _name not in vars(NativeControlAuthorityTests):
        setattr(NativeControlAuthorityTests, _name, None)


if __name__ == "__main__":
    unittest.main()
