"""PRF-171, STO-023, SCN-115: field 7 (max-group-name-octets) governs group names.

Before this the profile's field 7 had no reader: `group create' and `init'
checked only the record codec's width (256 octets), so a store whose
profile says 100 still created a 256-octet name.  Now `init' refuses by name
(books/native-operator.lisp `fn-nop-parse-init-plain',
`fn-nop-init-plain-groups-are-within-the-profile') and every configuration
record is authorized against it (books/store-capacity-config.lisp
`fn-cvec-native-admin-authorize', called by host/store-node-host.lisp
`fn-store-cfg-native-admin-authorize' from host/native/admin.lisp
`fnn-admin-authorize').

On the developer image, offline: `init --max-group-name-octets 100 fn.test`;
`group create` of a 100-octet name exits 0; of a 101-octet name exits 1
naming max-group-name-octets and publishes nothing; `init` of a 101-octet
name under field 7 = 100 is refused by name and writes nothing; under the
default profile (field 7 = 256) the 101-octet name is created.
"""
import unittest

from tests import test_native_operator_verbs as verbs

NAME_100 = "fn." + "a" * 97
NAME_101 = "fn." + "a" * 98


@unittest.skipUnless(verbs.executable(verbs.DEVELOPER), "the developer image is required")
class NativeGroupNameBoundTests(verbs.NativeOperatorVerbFixture):
    def operator(self, *words, **kwargs):
        return super().operator(*words, image=verbs.DEVELOPER, **kwargs)

    def config_names(self):
        return sorted(p.name for p in (self.store / "config").iterdir())

    def test_group_create_is_bounded_by_field_7(self):
        made = self.operator("init", "--max-group-name-octets", "100", "fn.test")
        self.assertEqual(made.returncode, verbs.EXIT_OK, made.stderr.decode())
        created = self.operator("group", "create", NAME_100)
        self.assertEqual(created.returncode, verbs.EXIT_OK, created.stderr.decode())
        before = self.config_names()
        refused = self.operator("group", "create", NAME_101)
        self.assertEqual(refused.returncode, verbs.EXIT_REFUSED, refused.stderr.decode())
        self.assertIn(b"MAX-GROUP-NAME-OCTETS", refused.stderr.upper())
        self.assertEqual(self.config_names(), before)

    def test_init_is_bounded_by_field_7(self):
        refused = self.operator("init", "--max-group-name-octets", "100", NAME_101)
        self.assertEqual(refused.returncode, verbs.EXIT_REFUSED, refused.stderr.decode())
        self.assertIn(b"MAX-GROUP-NAME-OCTETS", refused.stderr.upper())
        self.assertFalse(self.store.exists())

    def test_the_default_profile_admits_the_longer_name(self):
        made = self.operator("init", "fn.test")
        self.assertEqual(made.returncode, verbs.EXIT_OK, made.stderr.decode())
        created = self.operator("group", "create", NAME_101)
        self.assertEqual(created.returncode, verbs.EXIT_OK, created.stderr.decode())


if __name__ == "__main__":
    unittest.main()
