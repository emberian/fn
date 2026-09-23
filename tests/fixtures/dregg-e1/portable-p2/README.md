# Portable fn authorship to Mini E1

The sibling `signed.eml` is the exact public carrier. The frozen fn developer
image at `/tank/fn/gates/integrate-reader-repair-20260923/build/fn-host-developer`
ran `hybrid-verify-source` with the sibling `fn-ml-public.pem` and returned
`portable-verifier-line.txt`: exact source, ACL2-derived 48-octet source ID,
principal and both verified public keys. `fn-ml-public.raw` is the same
1952-octet key independently extracted from the public PEM's OpenSSL SPKI
representation for Mini's pin. `source-claim.json` supplies only the identity,
Message-ID and group text to compare. Mini derived the sibling `package.bin`
byte-for-byte from the authenticated source, and its independent P0 verifier
re-admitted the origin prefix. `verified-result.json` explicitly records
`storeAdmission: unestablished`.

`probe.py` runs the compiled Mini host and fn image against this fixture with
one positive and ten hostile inputs. It only orchestrates processes and
compares exact public bytes and exit outcomes; fn and Mini retain their own
semantic decisions. `hbox-transport-only.sh` is the exact transport shim used
for the Mac Mini host to invoke the Linux fn image on hbox. It copies the
carrier and public PEM to temporary remote files, forwards the native result
and removes the temporary files. It does no parsing or verification. The
result table is `native-results.json`; the command, source/tool hashes and
limits are in [the P2 evidence record](../../../../planning/evidence/dregg-e1-portable-p2.md).

The image and files here prove no local fn Store admission, historical T10
verdict, E2 cursor progress or current Mini operation grant. No private key,
live fn Store, live Mini database or consumer ack was used.
