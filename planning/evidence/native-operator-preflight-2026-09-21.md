# Native operator explicit preflight

Source: `w15/native-operator-integrated` commit `0f82b6e`. The hbox source was
`/tank/fn/gates/w15-native-operator-integrated`; the grammar source digest is
`a28a78bc752e94e157b74697944aa320135421d9a90bb0738b9302728560f8ae`.

`fn-native-operator-command-preflight` is now the ACL2-only decision before a
configuration read. It returns `(:needs-config)` for every non-help argv that
requires the normalized profile; config-free `help [COMMAND]` returns its
ordinary accepted plan; malformed argv and invalid help syntax return the
ordinary usage result. The raw adapter calls only the matching host projection,
then reads configuration only for `:needs-config`; it no longer supplies an
out-of-domain octet sentinel. Full `fn-native-operator-run` calls the same
preflight, preserving argv usage before malformed-config usage.

Tests cover help with absent and malformed configuration, `:needs-config` for
status/recover, malformed argv precedence over malformed config, and the host
preflight projection. The seven-book ACL2 8.7 / SBCL 2.6.8 closure passed in
5.196 seconds; exact results are in [the manifest](manifests/certify-20260921T093533Z-1966187.json).

The direct default-image boundary test `tests.test_native_operator_cli` passed
three cases on hbox after this change. As in the prior packet, the isolated
rsync gate lacks the full default-image `.cert` set, so its saved image is a
runtime diagnostic and not a certified deployment image.
