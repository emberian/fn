# fn-xc-span-at walks the candidates in one call (lane p-xc-span round 4)

Present state, certified on persvati (run-20261008T170104Z-4746). The statements below are in books/extent-cache-span.lisp; the teeth are in tests/acl2/extent-cache-span-tests.lisp.

## Stobj shape

    (defstobj fn-xcw-win (fn-xcw-win-bytes (array (unsigned-byte 8) (262144)) :initially 0) :inline t :congruent-to fn-ew-buffer)
    (defstobj fn-xcw (fn-xcw-plans (array t (8))) (fn-xcw-wins (array fn-xcw-win (8))))

Sizes are the profile figures (:read-window-octets, :extent-cache-windows). Row of slot s is (fn-xc-row s cells) = s - NE. fn-xcs and every earlier fn-xc statement are unchanged.

## Exports

    (fn-xc-span-at from ledger file eoff elen poff plen trailer p end fn-xcs fn-xcc fn-xcw fn-ew-span)
      -> (mv word count slot fn-ew-span fn-xcs fn-xcc)       ; :span or :miss
    (fn-xc-install-window-bytes token plan fn-xcs fn-xcc fn-xcw fn-ew-buffer)
      -> (mv word slot evicted fn-xcs fn-xcc fn-xcw)         ; the table decision of fn-xc-install-window, then plan and staged window stored with the slot
    (fn-xc-init-windows ne nw fn-xcs fn-xcc) -> (mv word fn-xcs fn-xcc)   ; :refused-window-rows when nw exceeds the fn-xcw row count

The walk: lookup from FROM selects slot s; try s's own plan and window (fn-xc-span-row); on :span touch s and answer; otherwise continue from s+1; :miss with slot nil when no later candidate exists. Measure: slot count - from.

## Keystones

- C1 fn-xc-span-at-answers-a-covered-slot: any live kind-2 slot i >= from matching the descriptor at p, token cached, plan a true list, supplying the octet at p, with p < end and NW within the row count, makes the call answer :span from a slot in [from, i].
- C2 fn-xc-span-at-is-the-returned-bytes: the old statement with plan and window read from the answering slot's row.
- fn-xc-span-at-answers-from-a-matching-slot: :span implies the slot matches the descriptor, is at or after FROM, is cached, and its row plan matches its token.
- fn-xc-span-at-hit-touches-only-the-selected-slot: stamps and clock are those of touching the answered slot (a miss names no slot and touches none); fn-xc-span-at-miss-changes-nothing.
- fn-xc-span-at-answers-an-owed-hit: the first-candidate case of C1, answered slot equal to the first candidate.
- fn-xc-span-at-never-answers-a-freed-slot.
- fn-xc-install-window-bytes-installs-the-table-decision, -stores-the-pair, -leaves-other-rows, -keeps-the-rows-unless-it-installs.
- fn-xc-init-windows-refuses-more-windows-than-rows, fn-xc-init-windows-readies-the-rows (its admitted state implies C1's NW bound).

Premises the host path discharges: readiness and the NW bound by fn-xc-init-windows; the stored plan by fn-xc-install-window-bytes; the installed slot lies in the window region (fn-xc-install-placement).
