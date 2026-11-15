# Bounded full decode source packet

This packet targets qualified layout2060684e at rootad7229772. It does not
integrate quarantined3fc or activate a runtime. ACL2 controls and guards below
remain unexecuted unless a separate current-key receipt says otherwise.

The three independent projections are:

1. `layout_payload_span_rewrite.rewrite`: same byte fuel, code/NEXT and
   continuation. A typed opaque chunk is min(payload remainder, input remainder,
   fuel), consumes that many fuel units, and retains the initial read/error
   check. Its logical untyped fallback reads one byte. There is one scanner.
2. `layout_bounded_full_rewrite.model_error`: the reference wrapper returns the
   actual scanner fault NEXT instead of OFF. The original typed malformed
   mismatch remains in `tests/layout-model-error-boundary-unit.lisp`; it is not
   silently changed into the repaired expectation.
3. `layout_bounded_full_rewrite.full`: full fuel is
   `1 + min(actual supplied span, declared MAX) + empty-field count`. The final
   sentinel allows the existing truncation check when input ends at the byte
   budget. MAX prevents a malformed tiny-schema scalar prefix from consuming an
   entire enclosing page or overlay window. Range/owner/bounds checks precede
   START, giving an actual no-mutation refusal. Generated STEP and G1 formulas
   are unchanged. The sole empty-field counter moves before its new use; its
   structural guard and natural-result fact are explicit.

Declared MAX+FIELDS+1 bounds full fuel. Encoder work remains per octet; no
opaque-payload credit is applied to encode. The actual per-call bound uses the
supplied span, so the FNCT article declaration alone grants no multi-GiB call.
This is a work bound, not an extra data ceiling.

The current source caller audit has these distinct admission obligations:

| Actual consumer | Relevant bound and remaining obligation |
| --- | --- |
| `fn2-ov-entry`, generated run NTH/search/read and run-add-write | END can be the whole overlay/page. MAX must cap each entry; the existing entry/restart byte charge derives from schema MAX, while the cost owner is connecting parser/table steps. Internal20 reader work remains separate from public successor admission. |
| `fn2-journal-body-decode`, recovery/member scanners | The original records payload and owned frame delimit input. Shared generated body codecs keep exact end checks. Budget-taking outer callers still need their own continuation/charge contract. |
| Frame/page/seal/anchor/map/arena/descriptor decoders | Generated maxima and physical framing bound work; a 64KiB enclosing page does not grant a small header a page scan. The new truncation sentinel must be admitted as a step, not hidden as a payload byte. |
| Source-manifest entry/header, ribbon and compression decoders | Finite typed layout bounds apply to each call. Enclosing iteration remains its own bounded caller obligation. |
| Native FNCT/CNS and authority request decoders | Current CTL receive admission is4096 including framing; this does not establish future streaming admission. Q1 owns actual CNS continuation/profile composition. Large APPEND full-codec success alone does not establish a native served request. |

The actual generated six-KiB control compares full/model results, exact Ref/end,
typed malformed padding rollback, preflight owner refusal with a complete fields
snapshot, and truncation. A real tiny-schema scalar over a64KiB input must stop
at NEXT10, while its nine-byte unterminated input must return TRUNCATED/NEXT9.
It is in `tools/fixtures/layout-bounded-full-unit.lisp` because it requires the
named projections; it is not registered as a runnable current-source root before
that projection. The source fixture uses the existing real model and generated
codec, rather than a parser implemented in Python.

Four full-packet and three span-projection source controls pass. They preserve
the qualified hints/rune boundary and original G1 forms, and verify projection
commutation. The transformed whole layout has the same single pre-existing B*
ignore-binding finding as the qualified baseline. No whole-guard, scan/effect
refinement, native admission or actual caller cost qualification is claimed.
