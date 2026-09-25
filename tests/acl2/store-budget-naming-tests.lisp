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
