# Distinct-identity protected peering projection audit

The previous two-host protected gate compared the source-served article to
the target-served article byte for byte, but configured neither owner's
`path-identity` and used an operator article without Xref. Under
`fn-peer-relayed-octets`, an unset identity leaves Path untouched. Thus a
passing equality did not witness the target's RFC 5537 Path update.

The revised driver sets durable, distinct
`a.gate.example.invalid`/`b.gate.example.invalid` identities and names the
opposite identity in each peer record. Each local operator post must serve
the complete supplied proto-article as an exact suffix and must have the
expected injected `Path: <source>!not-for-mail` first line. The protected
target must serve the complete source-served article with exactly its
`Path: <target>!!<source>!not-for-mail` first line in place. The rest of the
article, including an `X-Authored-Canary` header and body, is compared byte
for byte. This concrete fixture oracle agrees with the `:match` case of
`fn-path-diagnostic`; it is not a host implementation of general Path policy.

The final driver SHA-256 was
`62d42c5905572c888b6023d82b84aa3cf67d907c683e896471b4f52b0bdb360a`.
`python3 -m py_compile tools/native_two_host_protected_gate.py` passed. The
driver then returned `PASS` against source
`1836ed01cba287bea1633c6cd0c231443302de3f` with pinned production
images on hbox and persvati. The launcher, core, runtime, and build-source
manifest SHA-256 inputs on both hosts were respectively
`432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505`,
`d754a540c3a143caed67ffa1af6525565cf05b25f492d0aaeef60c547aa43281`,
`b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`,
and `2024599ca9c32ce3aec40fea27cdcc44d4a57e3b288467dce5482dd7567d579a`.
The images were
`/tank/fn/gates/relocated-native-1836ed01/build/images/1836ed01-production-pair/fn-host`
and `/home/ember/fn-gates/relocated-native-1836ed01/image/fn-host`.
The invocation was:

```sh
python3 tools/native_two_host_protected_gate.py \
  --host-a hbox --host-b persvati \
  --image-a /tank/fn/gates/relocated-native-1836ed01/build/images/1836ed01-production-pair/fn-host \
  --image-b /home/ember/fn-gates/relocated-native-1836ed01/image/fn-host \
  --launcher-sha-a 432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505 \
  --launcher-sha-b 432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505 \
  --core-sha-a d754a540c3a143caed67ffa1af6525565cf05b25f492d0aaeef60c547aa43281 \
  --core-sha-b d754a540c3a143caed67ffa1af6525565cf05b25f492d0aaeef60c547aa43281 \
  --runtime-sha-a b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5 \
  --runtime-sha-b b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5 \
  --source-manifest-sha-a 2024599ca9c32ce3aec40fea27cdcc44d4a57e3b288467dce5482dd7567d579a \
  --source-manifest-sha-b 2024599ca9c32ce3aec40fea27cdcc44d4a57e3b288467dce5482dd7567d579a \
  --source 1836ed01cba287bea1633c6cd0c231443302de3f \
  --evidence-dir build/protected-path-audit-final --timeout 180
```

The driver itself checked image manifests and live `/proc` runtime/core
identities. [Observed events](native-two-host-path-1836ed01-observations.json)
record four full-article transfer comparisons with equal expected/observed
SHA-256, both directions of successful protected feed, a wrong-password
queue/refusal/recovery, and a wrong-CA queue/refusal/recovery. The observations
file SHA-256 is
`12e5daea427645e30fe56741ed4206ef21886a6f05ff36badc533e8617c97e61`.

This is a native peering witness for ordinary operator-injected articles.
Injection refuses a proto-article carrying Xref, so this run does not
exercise transit Xref stripping. It also does not exercise a signed hybrid
carrier or prove that mutable Path/Xref leave the exact signed source intact;
the T10 combined-image carrier run remains separate. The native library,
TLS, filesystem, and remote-host observations are trusted at their stated
boundaries.
