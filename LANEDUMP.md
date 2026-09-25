# LANEDUMP bounds-blob (Opus 5.5) -- live

PRF-091. Packets PKT-008..011 (backlog-2026-09-25). Record:
planning/evidence/bounds-blob-2026-09-25.md.

## Intent (announced before editing)

- frame-octets / frame-fields / frame-invariants / frame.lisp: ADDITIVE spec form
  `(:blob . W)` (1 <= W <= u32).  Existing `:blob` keeps its width (131072) and
  every existing statement about it; the new form gets its own branch in
  `fn-frame-specp`, `-field-okp`, `-field-octets`, `-field-parse` and its round
  trips.  New `fn-frame-field-width` / `fn-frame-specs-width` (a schema's payload
  width as the sum of its field widths).
- frame-journal: the local length lemma becomes `<= (fn-frame-specs-width specs)`;
  workflow payload classified (node-generated fields) with a width theorem.
  NOT touching the FNRJ receipt field widths (deferral: its store-record blob is a
  data cap; needs the profile in the FNRJ codec and the Python bridge).
- transfer-journal: `*fn-tj-max-payload*` derived from the chunk spec width,
  classified as a per-record work bound.
- native-control: FNCT request spec `((:blob . *fn-record-max-payload*) :text
  (:blob . groups-width))`; `*fn-nctrl-max-payload*` = its width (codec);
  new `fn-nctrl-max-frame-for A G` and `fn-nctrl-read-bound-for A G`.
- native-hybrid-control: exact per-field widths; `*fn-nhctrl-max-payload*`
  derived; `fn-nhctrl-read-bound-for A G`.
- host: native-control-host, native-hybrid-control-host, owner-host
  (`fn-owner-control-profile-bounds`), host/native/control.lisp (read bound
  computed once at control start from the carried profile).
- store-events (a new function next to `fn-store-publication-ceiling`, not near
  `fn-store-event-sequence` -- carry-kind) and store-budget: PKT-011, the
  history pre-check figure from the profile's A, G (article) and R (kind 4).
- NOT touching: cbor, records-*, byte-store-frame (bounds-p6), packs,
  checkpoint (bounds-p5).
