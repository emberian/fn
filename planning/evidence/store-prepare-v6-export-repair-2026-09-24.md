# Store prepare after the Store-v6 export, 2026-09-24

The 67d combined gate stopped in
`fn-spc-set-keyring-keeps-store-components` (`books/store-prepare-correspondence`)
after the Store-v6 constructor definition was withdrawn at export. The old
hint explicitly enabled seven raw selectors. Its checkpoint was
`(car (fn-sn-make-v6 ...)) = (car s)`: opening a selector before the exported
constructor field theorem could match left the constructor opaque. The
dependent `owner-prepare-correspondence` then lacked this certificate; its
book did not report an independent theorem failure.

The repair changes only that theorem's hint. It opens `fn-sn-set-keyring`
and keeps `fn-sn-make-v6` and the projected selectors closed. The existing
`fn-sn-fields-of-fn-sn-make-v6` law proves all seven equations. No function,
theorem statement, guard, or runtime behavior changed. A bounded hbox REPL
loaded the repaired theorem and then all 31 forms of the book without
refusal.

The scoped hbox run `run-20260924T050523Z-a126`
([manifest](manifests/certify-20260924T050530Z-924925.json)) passed
`books/store-prepare-correspondence`, its test book,
`books/owner-prepare-correspondence`, and its test book. It installed 128
matching dependencies from the shared certificate cache, certified four
roots with two jobs and a 120-second per-book cap, and used ACL2 8.7 / SBCL
2.6.8 pinned toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
The four book wall times were 6.878, 2.819, 3.924, and 4.074 seconds
respectively. `green_check --changed-since 694d9e84 --strict` reports one
changed book, three dependents, and zero not green at this lane's bytes.
This packet repairs the Store-prepare/owner-prepare slice; the other direct
reds from the combined gate have separate owners.
