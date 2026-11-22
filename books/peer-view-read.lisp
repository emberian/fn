; Project from the live leased reader. The caller obtains PRINCIPAL/STREAM
; and AUTHORITY from its grant check and must revalidate that revision before
; publishing the typed spans. This stage never returns the raw member.
(in-package "ACL2")
(include-book "peer-view-member")
(include-book "event-read-members")
(fn2-book-layer :e)
(local (in-theory (disable fn2-event-readp fn2-event-read-wfp fn2-event-read-rows
 fn2-journal-membersp fn2-journal-members-wfp fn2-journal-members-rows
 fn2-journal-leasep fn2-journal-lease-wfp fn2-peer-view-record fn2-peer-view-pair
 fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-poolp fn2-pool-wfp fn2-event-read-ownerp)))

(local (in-theory (disable fn2-event-read-field-base
 fn2-event-read-gen
 fn2-event-read-owner-gen
 fn2-event-read-owner-kind
 fn2-event-read-owner-slot
 fn2-event-read-phase
 fn2-event-read-slot
 fn2-event-read-token
 fn2-event-read-view-authority
 fn2-event-read-view-ee
 fn2-event-read-view-end
 fn2-event-read-view-es
 fn2-event-read-view-event
 fn2-event-read-view-first
 fn2-event-read-view-gen
 fn2-event-read-view-he
 fn2-event-read-view-hs
 fn2-event-read-view-member
 fn2-event-read-view-off
 fn2-event-read-view-other
 fn2-event-read-view-principal
 fn2-event-read-view-slot
 fn2-event-read-view-stream
 fn2-event-read-view-token
 fn2-journal-members-event
 fn2-journal-members-gen
 fn2-journal-members-hash-phase
 fn2-journal-members-leaf-end
 fn2-journal-members-owner-gen
 fn2-journal-members-owner-kind
 fn2-journal-members-owner-slot
 fn2-journal-members-phase
 fn2-journal-members-slot
 fn2-journal-members-start
 fn2-layout-range-code fn2-pool-rows nth update-nth)))

(defun fn2-peer-view-read-step (token principal stream authority kind owner generation
 fn2-event-read fn2-journal-lease fn2-journal-members fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-event-read fn2-journal-lease fn2-journal-members fn2-fields fn2-pool)
 :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-journal-lease-wfp fn2-journal-lease)
             (fn2-journal-members-wfp fn2-journal-members) (fn2-fields-wfp fn2-fields)
             (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (mbt (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)))
                    (< 0 (fn2-event-read-rows fn2-event-read)) (< 0 (fn2-journal-members-rows fn2-journal-members))
                    (fn2-event-read-ownerp fn2-event-read fn2-journal-lease)
                    (equal token (fn2-event-read-token 0 fn2-event-read))
                    (equal kind (fn2-event-read-owner-kind 0 fn2-event-read))
                    (equal owner (fn2-event-read-owner-slot 0 fn2-event-read))
                    (equal generation (fn2-event-read-owner-gen 0 fn2-event-read))
                    (posp principal) (unsigned-byte-p 60 principal) (posp stream) (unsigned-byte-p 60 stream)
                    (posp authority) (unsigned-byte-p 60 authority)))
       (mv :source 0 0 0 0 fn2-event-read fn2-fields))
      ((unless (and (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-members*)
                    (equal (fn2-journal-members-phase 0 fn2-journal-members) *fn2-journal-members-phase-leaf*)
                    (equal (fn2-journal-members-hash-phase 0 fn2-journal-members) 3)))
       (mv :pending 0 0 0 0 fn2-event-read fn2-fields))
      (slot (fn2-journal-members-slot 0 fn2-journal-members)) (gen (fn2-journal-members-gen 0 fn2-journal-members))
      (event (fn2-journal-members-event 0 fn2-journal-members))
      (first (fn2-journal-members-start 0 fn2-journal-members)) (end (fn2-journal-members-leaf-end 0 fn2-journal-members))
      (base (fn2-event-read-field-base 0 fn2-event-read))
      ((unless (and (posp event) (< first end) (<= end *fn2-commit-unit-bytes*)
                    (equal slot (fn2-event-read-slot 0 fn2-event-read)) (equal gen (fn2-event-read-gen 0 fn2-event-read))
                    (equal kind (fn2-journal-members-owner-kind 0 fn2-journal-members))
                    (equal owner (fn2-journal-members-owner-slot 0 fn2-journal-members))
                    (equal generation (fn2-journal-members-owner-gen 0 fn2-journal-members))
                    (eq :ok (fn2-layout-range-code slot gen first end nil kind owner generation fn2-pool))))
       (mv :source 0 0 0 0 fn2-event-read fn2-fields))
      (current (and (equal token (fn2-event-read-view-token 0 fn2-event-read))
                    (equal principal (fn2-event-read-view-principal 0 fn2-event-read))
                    (equal stream (fn2-event-read-view-stream 0 fn2-event-read))
                    (equal authority (fn2-event-read-view-authority 0 fn2-event-read))
                    (equal event (fn2-event-read-view-event 0 fn2-event-read))
                    (equal slot (fn2-event-read-view-slot 0 fn2-event-read))
                    (equal gen (fn2-event-read-view-gen 0 fn2-event-read))
                    (equal first (fn2-event-read-view-first 0 fn2-event-read))
                    (equal end (fn2-event-read-view-end 0 fn2-event-read))))
      ((unless current)
       (let ((fn2-event-read (fn2-event-read-put 0 (view-token token) (view-principal principal)
        (view-stream stream) (view-authority authority) (view-event event) (view-slot slot) (view-gen gen)
        (view-first first) (view-end end) (view-off first) (view-hs 0) (view-he 0) (view-es 0) (view-ee 0)
        (view-member 0) (view-other 0))))
        (mv :more 0 0 0 0 fn2-event-read fn2-fields)))
      (off (fn2-event-read-view-off 0 fn2-event-read))
      (hs (fn2-event-read-view-hs 0 fn2-event-read)) (he (fn2-event-read-view-he 0 fn2-event-read))
      (es (fn2-event-read-view-es 0 fn2-event-read)) (ee (fn2-event-read-view-ee 0 fn2-event-read))
      ((unless (and (<= first off) (<= off end))) (mv :source 0 0 0 0 fn2-event-read fn2-fields))
      ((when (equal off end))
       (b* (((when (equal (fn2-event-read-view-member 0 fn2-event-read) 0))
             (mv :hidden 0 0 0 0 fn2-event-read fn2-fields))
            ((unless (and (equal (fn2-event-read-view-other 0 fn2-event-read) 0)
                          (<= first hs) (< hs he) (<= he end) (<= first es) (< es ee) (<= ee end)))
             (mv :dependency 0 0 0 0 fn2-event-read fn2-fields))
            ((mv code fn2-fields) (fn2-peer-view-pair event hs he es ee slot gen base kind owner generation fn2-fields fn2-pool)))
        (if (eq code :ok) (mv :item hs he es ee fn2-event-read fn2-fields)
          (mv code 0 0 0 0 fn2-event-read fn2-fields))))
      ((mv code next body fn2-fields)
       (fn2-peer-view-record stream event off end slot gen base kind owner generation fn2-fields fn2-pool))
      ((unless (and (member-eq code '(:history :evidence :membership :private :other-identity))
                    (unsigned-byte-p 32 next) (< off next) (<= next end)
                    (unsigned-byte-p 32 body)))
       (mv :invalid 0 0 0 0 fn2-event-read fn2-fields))
      (h (eq code :history)) (e (eq code :evidence))
      (other (or (eq code :other-identity) (and h (posp he)) (and e (posp ee))
                 (equal (fn2-event-read-view-other 0 fn2-event-read) 1)))
      (memberp (or (eq code :membership) (equal (fn2-event-read-view-member 0 fn2-event-read) 1)))
      (fn2-event-read (fn2-event-read-put 0 (view-off next) (view-hs (if h body hs)) (view-he (if h next he))
               (view-es (if e body es)) (view-ee (if e next ee)) (view-member (if memberp 1 0)) (view-other (if other 1 0)))))
  (mv :more 0 0 0 0 fn2-event-read fn2-fields)))

(fn2-event-read-preserves fn2-peer-view-read-step
 (token principal stream authority kind owner generation fn2-event-read fn2-journal-lease fn2-journal-members fn2-fields fn2-pool)
 :hyps ((fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read)
        (fn2-journal-leasep fn2-journal-lease) (fn2-journal-lease-wfp fn2-journal-lease)
        (fn2-journal-membersp fn2-journal-members) (fn2-journal-members-wfp fn2-journal-members)
        (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 :specs (("-EVENT-READ-TYPE" fn2-event-readp 5)
         ("-EVENT-READ-WFP" fn2-event-read-wfp 5)
         ("-EVENT-READ-ROWS" fn2-event-read-rows 5 :frame fn2-event-read)
         ("-FIELDS-TYPE" fn2-fieldsp 6)
         ("-FIELDS-WFP" fn2-fields-wfp 6)
         ("-FIELDS-ROWS" fn2-fields-rows 6 :frame fn2-fields)))
