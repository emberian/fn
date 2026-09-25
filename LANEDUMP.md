# LANEDUMP bounds-blob (Opus 5.5) -- done, ready to merge

PRF-091. Packets PKT-008..011. Record: planning/evidence/bounds-blob-2026-09-25.md.
Commits: f5d0c571 (frame + control + host), d9203155 (keystone fix, native
test, registry rows; the image rev), and the evidence commit on top.

## Summary

- PKT-008 DONE. `(:blob . W)` frame spec form; schema widths
  (`fn-frame-specs-width`); FNCT article field = record payload ceiling;
  KEYSTONE `fn-native-control-request-within-profile-frame` (+ read-bound form);
  owner reads control under `fn-nctrl-read-bound-for A G` of the carried profile
  (computed at `fnn-control-start`); client reads up to the FNCT article width.
- PKT-009 DONE. Hybrid widths exact, `*fn-nhctrl-max-payload*` derived (69 438);
  hybrid no longer replaces the FNCT read bound (was: operator post capped ~65 KB
  when hybrid built in). `*fn-nctrl-max-payload*` is the spec width (codec).
- PKT-010 PARTIAL. transfer-journal payload = chunk spec width (work bound);
  FNWF/FNRJ caps proved >= table widths. OPEN (data caps, not work): FNRJ
  request-context blobs (Store record, request ADU at 131 072) and app-journal
  record count / aggregates -- need the profile threaded into FNRJ + Python
  bridge and `fn-aj-statep`.
- PKT-011 BLOCKED. Profile-derived figures make `fn-profile-upgrade-keeps-verdict`
  (PRF-072) false when A/R rise without H; needs a decision (hypothesis on the
  theorem, or a new relation in `fn-profile-upgradep`). Not done.
- Certified: persvati run-20260925T085910Z-22ae (538 pass, native-control chain
  red) then run-20260925T093314Z-2f56 (exit 0, whole affected set); hbox image
  closure run-20260925T093714Z-e8e4 (198/198). No lane book over 10 s.
- Native (hbox, image d9203155): operator post 131 073 and 290 000 accepted and
  re-read, 300 001 refused ARTICLE-EXCEEDS-PROFILE-BOUND under A = 300 000;
  before image 0e2173ab: all three exit 4 (client 131 072 read).
- make check: only the generated ledger is stale (deputy regenerates).

## Findings for others

- `*fn-bpn-machine-max-job-octets*` = `*fn-frame-max-blob*`: BP held-image data
  cap at 131 072; `(:blob . W)` now exists for it.
- Native suite reds that are not this lane's (same on the before image):
  SOCKOPT-ERROR reading host/native/io.lisp in the raw-stub harness; the
  peer-list structural test pins a moved defun; the body-limit wording test.
