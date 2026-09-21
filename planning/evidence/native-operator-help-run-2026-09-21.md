# Native operator help and normalized-run packet

Source: `w15/native-operator` commit `241a624` (following `68635e1`); the
hbox source was an isolated `rsync --exclude .git` copy at
`/tank/fn/gates/w15-native-operator`. `books/native-operator.lisp` SHA-256 is
`b7cbd65759de565ea84cde99917fff02905efe93ccd0a11e25451b1c9012acd9`.

`fn-native-operator-run` now validates bounded argv first. An ACL2-normalized
`help [COMMAND]` plan therefore succeeds with absent or malformed configuration
bytes and supplies the bounded output string as a result argument. The raw
adapter emits that exact ACL2-selected string only after the help action has
completed. Other commands still require a valid native-config result; missing,
non-regular, or overlong configuration files are host I/O boundary usage (exit
5), while configuration syntax, type, range, and repetition failures are ACL2
operator usage (exit 5).

The ACL2 result projects run's normalized store and listener octets, port,
`--once` boolean, and max-connections nat. `host/native/operator.lisp` invokes
only `fnn-owner-run-normalized` with those projections when an accepted `:run`
plan is returned. It has no source-article submission callback yet, so `post`
remains `usage :shared-submission-unavailable`. Status/recover remain the only
current direct store actions. The raw module is still unregistered and no saved
image or deployed command is claimed; owner convergence must supply the frozen
callback and build registration before an installed-image exercise.

The adapter has one status renderer and one exit-code-to-tag conversion for
underlying native actions. It logs accepted only after help, run, status, or
recover returns successfully; it preserves owner return 0/3/4 unchanged and
uses 5 for grammar/configuration usage.

Hbox ACL2 8.7 / SBCL 2.6.8 closure:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 FN_CERT_CACHE=/tank/fn/certcache \
python3 tools/certify_books.py --jobs 1 --closure \
  tests/acl2/native-operator-host-tests
```

The seven-book closure passed in 5.497 seconds. It exercises config-free help,
normalized run projections, quoted nonnumeric port and slots, out-of-range and
repeated ports, repeated `--once`, unsupported verbs, posting-disabled, and
explicit unavailable post. Exact inputs and tool versions are in [the
manifest](manifests/certify-20260921T090343Z-1905874.json). `make check` also
passed after regenerating the ledger; its existing repository lint warnings are
not a native-operator verdict.
