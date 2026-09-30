# Native suffix carry forwarding recordings

Run `python3 tests/recording/snapshot-suffix-carries/generate.py`.
The generator extracts the two current production forms from
`host/native/io.lisp`, then checks five schedules with explicit decoder, SSR,
STATE, arena and chunk-quantum doubles. It never substitutes the prepared patch.
The tests assert one decoder call per chunk, unchanged wire/carry objects at the
one intern call, lexical token successor handling, empty suffix, NIL child carry,
bad chunk cutoff and propagated decoder failure. This records the native
scheduler boundary; actual parser guarantees come from the distinct sized SRS
component, and full loader/installation/funding/FFI fidelity remains open.
