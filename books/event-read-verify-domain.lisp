; Output types, invariants and row frames for the actual retained formatter.
(in-package "ACL2")
(include-book "event-read-verify")
(fn2-book-layer :c)
(local (in-theory (disable fn2-event-readp fn2-event-read-wfp fn2-event-read-rows
 fn2-fcp fn2-fc-wfp fn2-fc-rows
 fn2-fc-contextp fn2-fc-context-wfp fn2-fc-context-rows
 fn2-fieldsp fn2-fields-wfp fn2-fields-rows
 fn2-poolp fn2-pool-wfp fn2-pool-rows
 fn2-b3p fn2-b3-wfp fn2-b3-rows
 fn2-digestsp fn2-digests-wfp fn2-digests-rows
 fn2-journal-membersp fn2-journal-members-wfp fn2-journal-members-rows)))


(local (in-theory (disable fn2-event-read-allocation
 fn2-event-read-body-len
 fn2-event-read-body-off
 fn2-event-read-checker
 fn2-event-read-commit
 fn2-event-read-epoch
 fn2-event-read-extent
 fn2-event-read-field-base
 fn2-event-read-first
 fn2-event-read-gen
 fn2-event-read-journal-history
 fn2-event-read-journal-incarnation
 fn2-event-read-members
 fn2-event-read-owner-gen
 fn2-event-read-owner-kind
 fn2-event-read-owner-slot
 fn2-event-read-pending
 fn2-event-read-phase
 fn2-event-read-record-fetch-acc
 fn2-event-read-record-fetch-next
 fn2-event-read-record-fetch-off
 fn2-event-read-seal-span-length
 fn2-event-read-seal-span-next
 fn2-event-read-seal-span-started
 fn2-event-read-slot
 fn2-fc-phase
 fn2-fields-ref-gen
 fn2-fields-ref-len
 fn2-fields-ref-off
 fn2-fields-ref-slot
 fn2-fields-value
 nth update-nth fn2-layout-range-code fn2-journal-members-begin)))


(local (in-theory (disable fn2-digest-equal fn2-b3-ready fn2-b-event-row
 fn2-fc-context-hash fn2-fc-context-geometry fn2-fc-context-previous-seal
 fn2-event-read-record-digest-current-p fn2-digest-rowp)))

(fn2-event-read-preserves fn2-event-read-checked-unit
 (expected fn2-event-read fn2-journal-members fn2-fields fn2-pool fn2-digests)
 :hyps ((fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read)
        (fn2-journal-membersp fn2-journal-members) (fn2-journal-members-wfp fn2-journal-members)
        (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
        (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
        (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-EVENT-READ-DOMAIN-TYPE" fn2-event-readp 1)
         ("-EVENT-READ-DOMAIN-WFP" fn2-event-read-wfp 1)
         ("-EVENT-READ-DOMAIN-ROWS" fn2-event-read-rows 1 :frame fn2-event-read)
         ("-JOURNAL-MEMBERS-DOMAIN-TYPE" fn2-journal-membersp 2)
         ("-JOURNAL-MEMBERS-DOMAIN-WFP" fn2-journal-members-wfp 2)
         ("-JOURNAL-MEMBERS-DOMAIN-ROWS" fn2-journal-members-rows 2 :frame fn2-journal-members)
         ("-FIELDS-DOMAIN-TYPE" fn2-fieldsp 3)
         ("-FIELDS-DOMAIN-WFP" fn2-fields-wfp 3)
         ("-FIELDS-DOMAIN-ROWS" fn2-fields-rows 3 :frame fn2-fields))
 :hints (("Goal" :in-theory (enable fn2-event-read-checked-unit))))

(fn2-event-read-preserves fn2-event-read-format-core
 (budget expected previous fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 :hyps ((fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read)
        (fn2-journal-membersp fn2-journal-members) (fn2-journal-members-wfp fn2-journal-members)
        (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc)
        (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context)
        (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
        (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
        (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
        (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-EVENT-READ-DOMAIN-TYPE" fn2-event-readp 1)
         ("-EVENT-READ-DOMAIN-WFP" fn2-event-read-wfp 1)
         ("-EVENT-READ-DOMAIN-ROWS" fn2-event-read-rows 1 :frame fn2-event-read)
         ("-JOURNAL-MEMBERS-DOMAIN-TYPE" fn2-journal-membersp 2)
         ("-JOURNAL-MEMBERS-DOMAIN-WFP" fn2-journal-members-wfp 2)
         ("-JOURNAL-MEMBERS-DOMAIN-ROWS" fn2-journal-members-rows 2 :frame fn2-journal-members)
         ("-FC-DOMAIN-TYPE" fn2-fcp 3)
         ("-FC-DOMAIN-WFP" fn2-fc-wfp 3)
         ("-FC-DOMAIN-ROWS" fn2-fc-rows 3 :frame fn2-fc)
         ("-FC-CONTEXT-DOMAIN-TYPE" fn2-fc-contextp 4)
         ("-FC-CONTEXT-DOMAIN-WFP" fn2-fc-context-wfp 4)
         ("-FC-CONTEXT-DOMAIN-ROWS" fn2-fc-context-rows 4 :frame fn2-fc-context)
         ("-B3-DOMAIN-TYPE" fn2-b3p 5)
         ("-B3-DOMAIN-WFP" fn2-b3-wfp 5)
         ("-B3-DOMAIN-ROWS" fn2-b3-rows 5 :frame fn2-b3)
         ("-FIELDS-DOMAIN-TYPE" fn2-fieldsp 6)
         ("-FIELDS-DOMAIN-WFP" fn2-fields-wfp 6)
         ("-FIELDS-DOMAIN-ROWS" fn2-fields-rows 6 :frame fn2-fields)
         ("-POOL-DOMAIN-TYPE" fn2-poolp 7)
         ("-POOL-DOMAIN-WFP" fn2-pool-wfp 7)
         ("-POOL-DOMAIN-ROWS" fn2-pool-rows 7 :frame fn2-pool)
         ("-DIGESTS-DOMAIN-TYPE" fn2-digestsp 8)
         ("-DIGESTS-DOMAIN-WFP" fn2-digests-wfp 8)
         ("-DIGESTS-DOMAIN-ROWS" fn2-digests-rows 8 :frame fn2-digests))
 :hints (("Goal" :in-theory (enable fn2-event-read-format-core))))
