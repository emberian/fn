; Teeth for books/store-budget-naming: the staged record's transaction name
; over an owner state reached by the owner's own transitions, the counterexample
; each hypothesis of the name keystone excludes, and the POST payload bound at
; bound-1, bound and bound+1 with one counterexample per boundary hypothesis.
(in-package "ACL2")
(include-book "../../books/store-budget-naming")
(include-book "../../books/owner-store-budget")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable owner: one committed record, a second staged
; (the construction of tests/acl2/owner-store-budget-tests.lisp).

(defconst *sbnt-groups* '("fn.letters" "fn.test"))
(defconst *sbnt-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record*)))
(defconst *sbnt-post-config*
  (fn-inj-make-config
   t '(102 110 46 111 112 99 46 105 110 118 97 108 105 100)
   (list (fn-nntp-string-octets "fn.letters")
         (fn-nntp-string-octets "fn.test"))
   32768))
(defconst *sbnt-first*
  (fn-record-make 0 0 0 "<sbnt-first@example.invalid>" '(65 66)
                  *sbnt-groups* "sbnt-pin-1" "sbnt-subject-1"
                  "sbnt-release-1" 2 841000000))
(defconst *sbnt-second*
  (fn-record-make 1 1 1 "<sbnt-second@example.invalid>" '(67 68)
                  '("fn.test") "sbnt-pin-2" "sbnt-subject-2"
                  "sbnt-release-2" 1 841000000))

(defun sbnt-run (oc events)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (if (consp events)
      (sbnt-run (fn-ocfg-step oc (car events)) (cdr events))
    oc))

(defconst *sbnt-reserve-events*
  '((:store (:io :start-frontier nil))
    (:store (:io :frontier-file :ok))
    (:store (:io :frontier-replace :ok))
    (:store (:io :frontier-directory :ok))))
(defconst *sbnt-0*
  (fn-ocfg-make
   (fn-own-configure (fn-own-start (fn-sn-initial *sbnt-groups* 10) 3)
                     *sbnt-post-config*)
   *sbnt-config* nil nil))
(defconst *sbnt-ready-one*
  (fn-ocfg-step
   (sbnt-run (fn-opc-prepare (sbnt-run *sbnt-0* *sbnt-reserve-events*)
                             *sbnt-first*)
             '((:store (:io :record-file :ok))
               (:store (:io :record-link :ok))
               (:store (:io :record-directory :ok))))
   '(:complete)))
(defconst *sbnt-reserved* (sbnt-run *sbnt-ready-one* *sbnt-reserve-events*))
(defconst *sbnt-staged*
  (fn-sbud-oc-store (fn-opc-prepare *sbnt-reserved* *sbnt-second*)))
(defconst *sbnt-reserved-store* (fn-sbud-oc-store *sbnt-reserved*))

(defun sbnt-name-conclusion (s)
  (declare (xargs :verify-guards nil))
  (equal (fn-bs-txn-observation-pairs
          (append (fn-sbud-names 0 (fn-sbud-used s))
                  (list (fn-sbud-txn-name (fn-sbud-pending-sequence s))))
          0)
         (fn-sbud-name-pairs 0 (1+ (fn-sbud-used s)))))

; fn-sbud-pending-sequence-is-used
; The witness is reached and not degenerate: one committed record, the second
; staged, both hypotheses hold, and the staged sequence is 1.
(assert-event (equal (fn-sf-phase (fn-sn-files *sbnt-staged*)) :record-staged))
(assert-event (fn-sf-statep (fn-sn-files *sbnt-staged*)))
(assert-event (equal (fn-sbud-used *sbnt-staged*) 1))
(assert-event (equal (fn-sbud-pending-sequence *sbnt-staged*) 1))
; Without the record phase: the reserved owner's kernel is well formed, has
; one committed record and no candidate.
(assert-event (not (equal (fn-sbud-pending-sequence *sbnt-reserved-store*)
                          (fn-sbud-used *sbnt-reserved-store*))))
(must-fail
 (defthm sbnt-sequence-without-record-phase
   (implies (fn-sf-statep (fn-sn-files s))
            (equal (fn-sbud-pending-sequence s) (fn-sbud-used s)))))
; Without the kernel invariant: the misnumbered candidate below (5 over no
; committed record) is the other counterexample.
(must-fail
 (defthm sbnt-sequence-without-kernel-invariant
   (implies (fn-sf-record-phasep (fn-sf-phase (fn-sn-files s)))
            (equal (fn-sbud-pending-sequence s) (fn-sbud-used s)))))

; fn-sbud-pending-name-is-the-scans-next-name
; The same witness: the name is the second file's and the scan binds it.
(assert-event (equal (fn-sbud-txn-name (fn-sbud-pending-sequence *sbnt-staged*))
                     "00000000000000000001.txn"))
(assert-event (sbnt-name-conclusion *sbnt-staged*))
(assert-event (equal (fn-sbud-name-pairs 0 2)
                     '((0 "00000000000000000000.txn")
                       (1 "00000000000000000001.txn"))))

; Hypothesis `fn-sf-record-phasep': the reserved owner (a well-formed kernel,
; no candidate) has no pending sequence, its name is "", and the scan refuses
; the namespace it would make.
(assert-event (fn-sf-statep (fn-sn-files *sbnt-reserved-store*)))
(assert-event (not (fn-sf-record-phasep
                    (fn-sf-phase (fn-sn-files *sbnt-reserved-store*)))))
(assert-event (equal (fn-sbud-pending-sequence *sbnt-reserved-store*) nil))
(assert-event (not (sbnt-name-conclusion *sbnt-reserved-store*)))
(must-fail
 (defthm sbnt-name-without-record-phase
   (implies (fn-sf-statep (fn-sn-files s))
            (sbnt-name-conclusion s))))

; Hypothesis `fn-sf-statep': a record phase whose candidate is numbered 5 over
; an empty record list.  Its name is the sixth file's, which the scan does not
; accept after zero committed names.
(defconst *sbnt-misnumbered*
  (list nil nil
        (list :store-files :record-staged 6 nil nil
              (fn-record-make 5 5 5 "<sbnt-five@example.invalid>" '(69)
                              '("fn.test") "p" "s" "r" 1 841000000)
              nil nil 0)))
(assert-event (fn-sf-record-phasep (fn-sf-phase (fn-sn-files *sbnt-misnumbered*))))
(assert-event (not (fn-sf-statep (fn-sn-files *sbnt-misnumbered*))))
(assert-event (equal (fn-sbud-pending-sequence *sbnt-misnumbered*) 5))
(assert-event (not (equal (fn-sbud-pending-sequence *sbnt-misnumbered*)
                          (fn-sbud-used *sbnt-misnumbered*))))
(assert-event (not (sbnt-name-conclusion *sbnt-misnumbered*)))
(must-fail
 (defthm sbnt-name-without-kernel-invariant
   (implies (fn-sf-record-phasep (fn-sf-phase (fn-sn-files s)))
            (sbnt-name-conclusion s))))

; -----------------------------------------------------------------------------
; The POST payload bound

(defun sbnt-codes (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars) (cons (char-code (car chars)) (sbnt-codes (cdr chars))) nil))
(defconst *sbnt-msgid* (sbnt-codes (coerce "<sbnt@example.invalid>" 'list)))
(defconst *sbnt-dev* (fn-bs-config-for-profile :development))
(defconst *sbnt-scale* (fn-bs-config-for-profile :scale))

(assert-event (fn-af-message-idp *sbnt-msgid*))
; fn-sbud-post-boundary-refuses-exactly-past-the-profile-bound
; bound-1, bound, bound+1 under both named profiles.
(assert-event (equal (fn-sbud-post-boundary *sbnt-dev* *sbnt-msgid* 32767 1 9) :ok))
(assert-event (equal (fn-sbud-post-boundary *sbnt-dev* *sbnt-msgid* 32768 1 9) :ok))
(assert-event (equal (fn-sbud-post-boundary *sbnt-dev* *sbnt-msgid* 32769 1 9)
                     :payload-bound))
(assert-event (equal (fn-sbud-post-boundary *sbnt-scale* *sbnt-msgid* 32768 16 9) :ok))
(assert-event (equal (fn-sbud-post-boundary *sbnt-scale* *sbnt-msgid* 32769 16 9)
                     :payload-bound))
; An operator's profile (`init --max-article-octets 20000'): its A is the
; bound, P-1 and P admitted and P+1 refused, whatever the codec could carry.
(defconst *sbnt-operator* (fn-bs-profile-set-fields *sbnt-dev* '((5 . 20000))))
(assert-event (fn-bs-profile-validp *sbnt-operator*))
(assert-event (equal (fn-sbud-post-boundary *sbnt-operator* *sbnt-msgid* 19999 1 9) :ok))
(assert-event (equal (fn-sbud-post-boundary *sbnt-operator* *sbnt-msgid* 20000 1 9) :ok))
(assert-event (equal (fn-sbud-post-boundary *sbnt-operator* *sbnt-msgid* 20001 1 9)
                     :payload-bound))
; Its G: a profile with 4 groups per article refuses a fifth group.
(defconst *sbnt-four* (fn-bs-profile-set-fields *sbnt-dev* '((6 . 4))))
(assert-event (equal (fn-sbud-post-boundary *sbnt-four* *sbnt-msgid* 10 4 9) :ok))
(assert-event (equal (fn-sbud-post-boundary *sbnt-four* *sbnt-msgid* 10 5 9)
                     :group-bound))
; A value that is not a named profile admits no payload at all.
(assert-event (equal (fn-sbud-payload-bound '(1 2 3 4 5 6)) 0))
(assert-event (equal (fn-sbud-post-boundary '(1 2 3 4 5 6) *sbnt-msgid* 1 1 9)
                     :payload-bound))
; The served owner relays the refusal as `:refused', and that is its line.
(assert-event (equal (fn-post-store-refusal-line :refused)
                     "441 posting failed; the article was refused"))

(defun sbnt-bound-conclusion (profile msgid n groups charge)
  (declare (xargs :verify-guards nil))
  (equal (fn-sbud-post-boundary profile msgid n groups charge)
         (if (<= n (fn-sbud-payload-bound profile)) :ok :payload-bound)))

; One counterexample per hypothesis, every other hypothesis holding.
(assert-event (not (sbnt-bound-conclusion *sbnt-dev* '(97) 10 1 9)))
(assert-event (not (sbnt-bound-conclusion *sbnt-dev* *sbnt-msgid* -1 1 9)))
(assert-event (not (sbnt-bound-conclusion *sbnt-dev* *sbnt-msgid* 10 0 9)))
(assert-event (not (sbnt-bound-conclusion *sbnt-dev* *sbnt-msgid* 10
                                           (1+ *fn-record-max-groups*) 9)))
(assert-event (not (sbnt-bound-conclusion *sbnt-dev* *sbnt-msgid* 10 1 0)))
(assert-event (not (sbnt-bound-conclusion *sbnt-dev* *sbnt-msgid* 10 1 4294967296)))

(must-fail
 (defthm sbnt-bound-without-message-id
   (implies (and (natp n) (posp g) (<= g *fn-record-max-groups*)
                 (posp c) (<= c *fn-cbor-max-uint*))
            (sbnt-bound-conclusion p m n g c))))
(must-fail
 (defthm sbnt-bound-without-natural-length
   (implies (and (fn-af-message-idp m) (posp g) (<= g *fn-record-max-groups*)
                 (posp c) (<= c *fn-cbor-max-uint*))
            (sbnt-bound-conclusion p m n g c))))
(must-fail
 (defthm sbnt-bound-without-positive-groups
   (implies (and (fn-af-message-idp m) (natp n) (<= g *fn-record-max-groups*)
                 (posp c) (<= c *fn-cbor-max-uint*))
            (sbnt-bound-conclusion p m n g c))))
(must-fail
 (defthm sbnt-bound-without-group-ceiling
   (implies (and (fn-af-message-idp m) (natp n) (posp g)
                 (posp c) (<= c *fn-cbor-max-uint*))
            (sbnt-bound-conclusion p m n g c))))
(must-fail
 (defthm sbnt-bound-without-positive-charge
   (implies (and (fn-af-message-idp m) (natp n) (posp g)
                 (<= g *fn-record-max-groups*) (<= c *fn-cbor-max-uint*))
            (sbnt-bound-conclusion p m n g c))))
(must-fail
 (defthm sbnt-bound-without-charge-ceiling
   (implies (and (fn-af-message-idp m) (natp n) (posp g)
                 (<= g *fn-record-max-groups*) (posp c))
            (sbnt-bound-conclusion p m n g c))))

; -----------------------------------------------------------------------------
; The signed composite's record bound (D27, signed-path 2026-09-25):
; fn-sbud-signed-event-boundary-refuses-exactly-past-the-record-field and
; fn-sbud-signed-event-boundary-ok-is-publishable.

; A composite past every old data cap: its article record (300,000) is past
; 65,538, its source (220,000) past 32,768, its encoding past 196,608.
(defconst *sbnt-composite*
  (fn-stxa-make-carried 4 9 12 3 '(112) '(115)
                        (make-list 300000 :initial-element 1)
                        (make-list *fn-stxe-max-octets* :initial-element 2)
                        (make-list 220000 :initial-element 5)
                        '(115 1 2 3)))
(defconst *sbnt-composite-octets* (len (fn-stxa-encode *sbnt-composite*)))
(assert-event (fn-stxa-p *sbnt-composite*))
(assert-event (< 196608 *sbnt-composite-octets*))
; The operator's R decides, one octet either side of the composite.
(defconst *sbnt-r-at* (fn-bs-profile-set-fields
                       *fn-bs-profile-defaults*
                       (list (cons 4 *sbnt-composite-octets*)
                             (cons 5 65536) (cons 6 1) (cons 7 64))))
(defconst *sbnt-r-below* (fn-bs-profile-set-fields
                          *fn-bs-profile-defaults*
                          (list (cons 4 (1- *sbnt-composite-octets*))
                                (cons 5 65536) (cons 6 1) (cons 7 64))))
(assert-event (fn-bs-profile-admittedp *sbnt-r-at*))
(assert-event (fn-bs-profile-admittedp *sbnt-r-below*))
(assert-event (equal (fn-sbud-signed-event-boundary *sbnt-r-at* *sbnt-composite*)
                     :ok))
(assert-event (equal (fn-sbud-signed-event-boundary *sbnt-r-below* *sbnt-composite*)
                     :signed-record))
(assert-event (equal (fn-sbud-signed-event-boundary *fn-bs-profile-defaults*
                                                    *sbnt-composite*)
                     :ok))
; No composite: nil, as a builder returns when a binding fails.
(assert-event (equal (fn-sbud-signed-event-boundary *sbnt-r-at* nil) :event))
; Both words are named on the wire, and differently.
(assert-event (equal (fn-post-store-refusal-line :signed-record)
                     "441 posting failed; the signed article with its authored source exceeds the configured record size (signed-record)"))
(assert-event (equal (fn-post-store-refusal-line :event)
                     "441 posting failed; the signed article did not form a Store event (event)"))
; The publish gate admits the :ok composite at its framed length.
(assert-event (fn-bs-publication-admissiblep
               *sbnt-r-at* 0 (len (fn-store-event-encode *sbnt-composite*))))
(assert-event (not (fn-bs-publication-admissiblep
                    *sbnt-r-below* 0
                    (len (fn-store-event-encode *sbnt-composite*)))))

(must-fail
 (defthm sbnt-exactly-without-a-composite
   (equal (fn-sbud-signed-event-boundary profile event)
          (if (<= (len (fn-store-event-encode event))
                  (fn-bs-profile-max-record-octets profile))
              :ok :signed-record))
   :hints (("Goal" :in-theory (disable fn-store-event-encode fn-stxa-encode
                                       fn-stxa-p fn-bs-profile-max-record-octets
                                       fn-bs-profile-max-transactions
                                       fn-bs-profile-admittedp)))))
(must-fail
 (defthm sbnt-publishable-without-ok
   (implies (and (fn-bs-profile-admittedp profile) (natp count)
                 (< count (fn-bs-profile-max-transactions profile)))
            (fn-bs-publication-admissiblep
             profile count (len (fn-store-event-encode event))))
   :hints (("Goal" :in-theory (disable fn-store-event-encode fn-stxa-encode
                                       fn-stxa-p fn-bs-profile-max-record-octets
                                       fn-bs-profile-max-transactions
                                       fn-bs-profile-admittedp)))))
(must-fail
 (defthm sbnt-publishable-without-admitted-profile
   (implies (and (equal (fn-sbud-signed-event-boundary profile event) :ok)
                 (natp count)
                 (< count (fn-bs-profile-max-transactions profile)))
            (fn-bs-publication-admissiblep
             profile count (len (fn-store-event-encode event))))
   :hints (("Goal" :in-theory (disable fn-store-event-encode fn-stxa-encode
                                       fn-stxa-p fn-bs-profile-max-record-octets
                                       fn-bs-profile-max-transactions
                                       fn-bs-profile-admittedp)))))
(must-fail
 (defthm sbnt-publishable-without-natural-count
   (implies (and (equal (fn-sbud-signed-event-boundary profile event) :ok)
                 (fn-bs-profile-admittedp profile)
                 (< count (fn-bs-profile-max-transactions profile)))
            (fn-bs-publication-admissiblep
             profile count (len (fn-store-event-encode event))))
   :hints (("Goal" :in-theory (disable fn-store-event-encode fn-stxa-encode
                                       fn-stxa-p fn-bs-profile-max-record-octets
                                       fn-bs-profile-max-transactions
                                       fn-bs-profile-admittedp)))))
(must-fail
 (defthm sbnt-publishable-without-a-transaction-left
   (implies (and (equal (fn-sbud-signed-event-boundary profile event) :ok)
                 (fn-bs-profile-admittedp profile)
                 (natp count))
            (fn-bs-publication-admissiblep
             profile count (len (fn-store-event-encode event))))
   :hints (("Goal" :in-theory (disable fn-store-event-encode fn-stxa-encode
                                       fn-stxa-p fn-bs-profile-max-record-octets
                                       fn-bs-profile-max-transactions
                                       fn-bs-profile-admittedp)))))
; Evaluated counterexamples for the same hypotheses.
(assert-event (not (equal (fn-sbud-signed-event-boundary *sbnt-r-at* nil) :ok)))
(assert-event (not (fn-bs-publication-admissiblep
                    '(1 2 3) 0 (len (fn-store-event-encode *sbnt-composite*)))))
(assert-event (not (fn-bs-publication-admissiblep
                    *sbnt-r-at* -1 (len (fn-store-event-encode *sbnt-composite*)))))
(assert-event (not (fn-bs-publication-admissiblep
                    *sbnt-r-at* (fn-bs-profile-max-transactions *sbnt-r-at*)
                    (len (fn-store-event-encode *sbnt-composite*)))))

; -----------------------------------------------------------------------------
; PKT-091: the POST boundary's refusal text is ACL2's.
; fn-sbud-post-boundary-refusal-is-nil-exactly-when-admitted (no hypothesis):
; an admitted post renders nothing; each refused post renders its own line,
; the octets host/native/io.lisp fnn-validate-post-boundary prints.
(assert-event (equal (fn-sbud-post-boundary-refusal
                      (fn-sbud-post-boundary *sbnt-dev* *sbnt-msgid* 32768 1 9))
                     nil))
(assert-event (equal (fn-sbud-post-boundary-refusal
                      (fn-sbud-post-boundary *sbnt-dev* *sbnt-msgid* 32769 1 9))
                     (sbnt-codes (coerce "payload exceeds the modelled bound" 'list))))
(assert-event (equal (fn-sbud-post-boundary-refusal
                      (fn-sbud-post-boundary *sbnt-dev* '(97) 10 1 9))
                     (sbnt-codes (coerce "Message-ID is not a valid RFC 5536 message identifier"
                                         'list))))
(assert-event (equal (fn-sbud-post-boundary-refusal
                      (fn-sbud-post-boundary *sbnt-four* *sbnt-msgid* 10 5 9))
                     (sbnt-codes (coerce "group count exceeds codec bound" 'list))))
(assert-event (equal (fn-sbud-post-boundary-refusal
                      (fn-sbud-post-boundary *sbnt-dev* *sbnt-msgid* 10 1 0))
                     (sbnt-codes (coerce "charge must be a positive uint32" 'list))))
; A word the boundary never returns still refuses (the unreachable branch
; fails closed); it is not evidence for the keystone.
(assert-event (equal (fn-sbud-post-boundary-refusal :something-else)
                     *fn-sbud-refusal-unnamed*))
; fn-sbud-post-boundary-refusals-are-distinct: each hypothesis is needed.
; Without the named-word hypothesis two unnamed words share the unnamed text.
(assert-event (equal (fn-sbud-post-boundary-refusal :x)
                     (fn-sbud-post-boundary-refusal :y)))
(must-fail
 (defthm sbnt-refusals-distinct-without-a-named-word
   (implies (not (equal v1 v2))
            (not (equal (fn-sbud-post-boundary-refusal v1)
                        (fn-sbud-post-boundary-refusal v2))))))
(must-fail
 (defthm sbnt-refusals-distinct-without-distinct-words
   (implies (or (fn-sbud-post-boundary-verdictp v1)
                (fn-sbud-post-boundary-verdictp v2))
            (not (equal (fn-sbud-post-boundary-refusal v1)
                        (fn-sbud-post-boundary-refusal v2))))))
