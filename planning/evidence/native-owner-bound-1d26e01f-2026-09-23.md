# Bound owner callback settlement on the 1d26 native image

The shared hbox developer image was built from frozen source
`1d26e01f558e3cc15e43f80dad630255449f0742` at
`/tank/fn/gates/poll-live-group-native-1d26-20260923/build/fn-host-developer`.
Its launcher SHA-256 was
`177c47f453e9d65c126a62bee664fe77a80a624fcdd0c4c2fe0a0a82810a48a7`;
the exact core named by that launcher was
`12e223e3207341f8456a8d8d09d1a281b8efed56a5159f4cff9c223f9fd4d75f`.
The named `/tank/fn/sbcl/bin/sbcl` runtime SHA-256 was
`b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`.
The shared image lane reported full certificate validation before this test;
this run did not build an image or certify books.

The frozen source contains the bound-callback fix `5309debd` and the ordinary
attempt repair from the shared integration. It predates a *test-only* fixture
correction, `adec5a42159c619c7627da7841a2c6a2770f3fd7`: the first
fixture's signed unknown group was refused before owner `:take`, so it could
not demonstrate post-take settlement. The corrected driver signs two
different authored sources under one Message-ID. The first is accepted, the
second reaches Store and logs `refused post path=control` for that Message-ID,
and a fresh signed Message-ID is then accepted on the same owner. The test
also restarts the owner and reads back the accepted carrier. The driver was
staged separately at `/tank/fn/labs/owner-bound-driver-adec`; its
`tests/test_native_hybrid_author.py` SHA-256 was
`4ab18a51fd9f64730ed146e23ffae71af9cea8d0467bbfede56336c2b041ba22`.

On hbox, with `FN_NATIVE_HOST` set to that developer image,
`FN_RUN_HYBRID_E2E=1`, `FN_OPENSSL_PREFIX` and `LD_LIBRARY_PATH` set to
`/tank/fn/toolchains/openssl-3.5.8` and its `lib`, and `FN_TEST_OPENSSL` set
to its `bin/openssl`, the command was:

```
timeout 180s python3 -m unittest \
  tests.test_native_hybrid_author.NativeHybridAuthorTest.test_enroll_author_refuse_tamper_and_restart_query -v
```

It passed in 1.687 seconds. The [raw result](native-owner-bound-1d26e01f.log)
SHA-256 is `f34aef7070a8981c726736266c32968320fc32143a06eca6f7b659464bc632a8`.
The shipped-defun raw test of a callback *signalling* `fnn-store-error` after
`:take`, followed by a durable request, also passed locally; it additionally
checks that indeterminate, Store fault and OS error classes are not silently
turned into known refusal.

This is a bounded saved-image test of one signed-author conflict and recovery
of the control slot, not a physical persistence fault or a proof of every
callback failure. It does not test the native ambiguous-publication arm.
The store was a test-local temporary directory; the live node was untouched.
