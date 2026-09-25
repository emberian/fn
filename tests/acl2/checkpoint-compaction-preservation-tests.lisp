; Witnesses and teeth for books/checkpoint-compaction-preservation.
(in-package "ACL2")
(include-book "../../books/checkpoint-compaction-preservation")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

; Five committed events: a record, an undertaking, its release, an identity
; event and an enrollment (the retention and identity history a pack must
; keep, not only articles).
(defconst *ccpt-a0*
  (fn-record-make 0 0 0 "<compact@example.invalid>" '(65 13 10)
                  '("fn.letters") "archive-0" "subject-0" "evidence-0" 3 841000000))
(defconst *ccpt-e1*
  (fn-store-retention-event-make :undertake 1 1 1
                                 "forward-1" "subject-1" "evidence-1" 2))
(defconst *ccpt-e2*
  (fn-store-retention-event-make :release 2 2 2
                                 "forward-1" "subject-1" "receipt-1" 0))
(defconst *ccpt-i3*
  (fn-stxe-make 3 3 3 "<compact@example.invalid>" :unverified
                '(117 110 118 101 114 105 102 105 101 100) 7 '(116 101 115 116)))
(defconst *ccpt-k4*
  (fn-stxk-make 4 4 4 7 '(116 101 115 116) '(1 2 3 4)))
(make-event `(defconst *ccpt-b0* ',(fn-store-event-encode *ccpt-a0*)))
(make-event `(defconst *ccpt-b1* ',(fn-store-event-encode *ccpt-e1*)))
(make-event `(defconst *ccpt-b2* ',(fn-store-event-encode *ccpt-e2*)))
(make-event `(defconst *ccpt-b3* ',(fn-store-event-encode *ccpt-i3*)))
(make-event `(defconst *ccpt-b4* ',(fn-store-event-encode *ccpt-k4*)))

; The selected pack covers sequences 0..3; sequence 4 is the suffix.
(defconst *ccpt-digest* (make-list 32 :initial-element 7))
(make-event `(defconst *ccpt-framed* ',(append (fn-cc-encode (fn-cc-make 4 4 (list *ccpt-b0* *ccpt-b1*
                                              *ccpt-b2* *ccpt-b3*)))
          *ccpt-digest*)))
(make-event `(defconst *ccpt-names* ',(list (fn-bs-txn-name 0) (fn-bs-txn-name 1) (fn-bs-txn-name 2)
        (fn-bs-txn-name 3) (fn-bs-txn-name 4))))
(make-event `(defconst *ccpt-contents* ',(list (cons (fn-bs-txn-name 0) *ccpt-b0*) (cons (fn-bs-txn-name 1) *ccpt-b1*)
        (cons (fn-bs-txn-name 2) *ccpt-b2*) (cons (fn-bs-txn-name 3) *ccpt-b3*)
        (cons (fn-bs-txn-name 4) *ccpt-b4*))))
(defconst *ccpt-all*
  (list *ccpt-b0* *ccpt-b1* *ccpt-b2* *ccpt-b3* *ccpt-b4*))

(defun ccpt-open (names lower contents)
  ; The open path: the namespace gate at the profile bound 8, the host's
  ; read of each issued pair, the framed pack's reconstruction.
  (declare (xargs :guard t :verify-guards nil))
  (let ((obs (fn-profile-txn-observation names 8 lower)))
    (if (equal obs :invalid) :invalid
      (fn-ccp-observe-framed *ccpt-framed* *ccpt-digest*
                             (fn-ccp-read (third obs) contents) 6))))

(assert-event (equal (fn-ccp-framed-boundary *ccpt-framed* *ccpt-digest*) 4))
(assert-event
 (equal (fn-ccp-coverage-framed *ccpt-framed* *ccpt-digest* 8 6) '(:ok 4 4)))

; Reachable, non-degenerate: the plan is the four covered names; before the
; reclaim, after a cut that lost names 1 and 3, and after the whole plan,
; the open reconstructs the same five records.
(assert-event
 (equal (fn-bs-pack-reclaim-plan *ccpt-names* 8 4)
        (list (fn-bs-txn-name 0) (fn-bs-txn-name 1)
              (fn-bs-txn-name 2) (fn-bs-txn-name 3))))
(assert-event (equal (ccpt-open *ccpt-names* 4 *ccpt-contents*)
                     (list :ok *ccpt-all* 6)))
(assert-event
 (equal (ccpt-open (fn-ccp-remove-names
                    *ccpt-names* (list (fn-bs-txn-name 1) (fn-bs-txn-name 3)))
                   4 *ccpt-contents*)
        (list :ok *ccpt-all* 6)))
(assert-event
 (equal (ccpt-open (fn-ccp-remove-names
                    *ccpt-names* (fn-bs-pack-reclaim-plan *ccpt-names* 8 4))
                   4 *ccpt-contents*)
        (list :ok *ccpt-all* 6)))
; ... and that list is the records the store had with no pack at all.
(assert-event
 (equal (fn-ccp-records
         (fn-ccp-read (third (fn-profile-txn-observation *ccpt-names* 8 0))
                      *ccpt-contents*))
        *ccpt-all*))

; -----------------------------------------------------------------------------
; Teeth: each hypothesis of the composition, by a concrete counterexample
; and by the prover's refusal.

; Without a valid observation before: a gap in the suffix (4 missing, 5
; present) is refused before and after, whatever the plan.
(assert-event
 (equal (ccpt-open (list (fn-bs-txn-name 0) (fn-bs-txn-name 5)) 4
                   *ccpt-contents*)
        :invalid))
; Without GONE within the plan: losing the newest suffix name 4 leaves a
; namespace the gate accepts (a missing tail is not a gap), and the open
; silently loses record 4.  The plan never issues it
; (fn-bs-selected-suffix-is-not-in-reclaim-plan) and no cut loses it
; (fn-bs-selected-reclaim-crash-preserves-suffix-payload).
(assert-event
 (equal (ccpt-open (fn-ccp-remove-names *ccpt-names* (list (fn-bs-txn-name 4)))
                   4 *ccpt-contents*)
        (list :ok (list *ccpt-b0* *ccpt-b1* *ccpt-b2* *ccpt-b3*) 6)))
; Without LOWER = the pack's boundary: a plan computed at 5 deletes name 4,
; which the pack does not hold, and the open silently loses record 4.
(assert-event
 (member-equal (fn-bs-txn-name 4) (fn-bs-pack-reclaim-plan *ccpt-names* 8 5)))
(assert-event
 (equal (ccpt-open (fn-ccp-remove-names *ccpt-names* (list (fn-bs-txn-name 4)))
                   5 *ccpt-contents*)
        (list :ok (list *ccpt-b0* *ccpt-b1* *ccpt-b2* *ccpt-b3*) 6)))
; Without the open before succeeding: a surviving covered file that
; disagrees with the pack is refused before, and reclaiming it would have
; changed the answer.
(make-event `(defconst *ccpt-bad-contents* ',(put-assoc-equal (fn-bs-txn-name 1) *ccpt-b2* *ccpt-contents*)))
(assert-event (equal (ccpt-open *ccpt-names* 4 *ccpt-bad-contents*)
                     '(:error :conflict)))
(assert-event
 (equal (ccpt-open (fn-ccp-remove-names *ccpt-names* (list (fn-bs-txn-name 1)))
                   4 *ccpt-bad-contents*)
        (list :ok *ccpt-all* 6)))

;; The same four, as the conclusion the prover refuses at those constants.
(make-event `(defconst *ccpt-gap-names* ',(list (fn-bs-txn-name 0) (fn-bs-txn-name 5))))
(local
 (must-fail
  (defthm ccpt-composition-without-valid-before
    (not (equal (ccpt-open (fn-ccp-remove-names *ccpt-gap-names* nil) 4
                           *ccpt-contents*)
                :invalid)))))
(local
 (must-fail
  (defthm ccpt-composition-without-gone-in-plan
    (equal (ccpt-open (fn-ccp-remove-names *ccpt-names* (list (fn-bs-txn-name 4)))
                      4 *ccpt-contents*)
           (ccpt-open *ccpt-names* 4 *ccpt-contents*)))))
(local
 (must-fail
  (defthm ccpt-composition-without-pack-boundary
    (equal (ccpt-open (fn-ccp-remove-names *ccpt-names* (list (fn-bs-txn-name 4)))
                      5 *ccpt-contents*)
           (ccpt-open *ccpt-names* 5 *ccpt-contents*)))))
(local
 (must-fail
  (defthm ccpt-composition-without-open-before
    (equal (ccpt-open (fn-ccp-remove-names *ccpt-names* (list (fn-bs-txn-name 1)))
                      4 *ccpt-bad-contents*)
           (ccpt-open *ccpt-names* 4 *ccpt-bad-contents*)))))

; Record-level keystones.
(make-event `(defconst *ccpt-observed* ',(fn-ccp-read (third (fn-profile-txn-observation
                                                *ccpt-names* 8 4))
                                       *ccpt-contents*)))
(assert-event
 (fn-ccp-covered-sublistp (list (list 0 *ccpt-b0*) (list 4 *ccpt-b4*))
                          *ccpt-observed* 4))
(assert-event
 (not (fn-ccp-covered-sublistp (list (list 0 *ccpt-b0*)) *ccpt-observed* 4)))
(assert-event
 (equal (fn-ccp-observe-framed *ccpt-framed* *ccpt-digest*
                               (list (list 0 *ccpt-b0*)) 6)
        (list :ok (list *ccpt-b0* *ccpt-b1* *ccpt-b2* *ccpt-b3*) 6)))
(local
 (must-fail
  (defthm ccpt-deletion-without-sublist
    (implies (equal (car (fn-ccp-observe-framed framed digest observed frontier))
                    :ok)
             (equal (fn-ccp-observe-framed framed digest after frontier)
                    (fn-ccp-observe-framed framed digest observed frontier))))))
(local
 (must-fail
  (defthm ccpt-deletion-without-ok-before
    (implies (fn-ccp-covered-sublistp after observed
                                      (fn-ccp-framed-boundary framed digest))
             (equal (fn-ccp-observe-framed framed digest after frontier)
                    (fn-ccp-observe-framed framed digest observed frontier))))))

; A complete observation: its records, and why each hypothesis is needed.
(assert-event (fn-ccp-contiguousp *ccpt-observed* 0))
(assert-event
 (equal (fn-ccp-observe-framed *ccpt-framed* *ccpt-digest* *ccpt-observed* 6)
        (list :ok (fn-ccp-records *ccpt-observed*) 6)))
; Not contiguous: sequence 1 missing, the pack supplies it.
(assert-event
 (not (equal (fn-ccp-observe-framed *ccpt-framed* *ccpt-digest*
                                    (list (list 0 *ccpt-b0*) (list 2 *ccpt-b2*)
                                          (list 3 *ccpt-b3*) (list 4 *ccpt-b4*))
                                    6)
             (list :ok (list *ccpt-b0* *ccpt-b2* *ccpt-b3* *ccpt-b4*) 6))))
; Shorter than the boundary: the pack supplies records 2 and 3.
(assert-event
 (equal (fn-ccp-observe-framed *ccpt-framed* *ccpt-digest*
                               (list (list 0 *ccpt-b0*) (list 1 *ccpt-b1*)) 6)
        (list :ok (list *ccpt-b0* *ccpt-b1* *ccpt-b2* *ccpt-b3*) 6)))
(local
 (must-fail
  (defthm ccpt-complete-without-ok
    (implies (and (fn-ccp-contiguousp observed 0)
                  (<= (fn-ccp-framed-boundary framed digest) (len observed)))
             (equal (fn-ccp-observe-framed framed digest observed frontier)
                    (list :ok (fn-ccp-records observed) frontier))))))
(local
 (must-fail
  (defthm ccpt-complete-without-contiguity
    (implies (and (equal (car (fn-ccp-observe-framed framed digest observed
                                                     frontier))
                         :ok)
                  (<= (fn-ccp-framed-boundary framed digest) (len observed)))
             (equal (fn-ccp-observe-framed framed digest observed frontier)
                    (list :ok (fn-ccp-records observed) frontier))))))
(local
 (must-fail
  (defthm ccpt-complete-without-length
    (equal (fn-ccp-observe-framed *ccpt-framed* *ccpt-digest*
                                  (list (list 0 *ccpt-b0*) (list 1 *ccpt-b1*)) 6)
           (list :ok (list *ccpt-b0* *ccpt-b1*) 6)))))

; Namespace keystone.
(assert-event
 (equal (fn-profile-txn-observation
         (fn-ccp-remove-names *ccpt-names* (list (fn-bs-txn-name 2))) 8 4)
        (list :ok 4 (list (list 0 (fn-bs-txn-name 0)) (list 1 (fn-bs-txn-name 1))
                          (list 3 (fn-bs-txn-name 3)) (list 4 (fn-bs-txn-name 4))))))
(local
 (must-fail
  (defthm ccpt-namespace-without-plan
    (let ((before (fn-profile-txn-observation names maximum lower)))
      (implies (not (equal before :invalid))
               (equal (fn-profile-txn-observation
                       (fn-ccp-remove-names names gone) maximum lower)
                      (list :ok lower
                            (fn-ccp-remove-pairs (third before) gone))))))))
(local
 (must-fail
  (defthm ccpt-namespace-without-valid-before
    (let ((before (fn-profile-txn-observation names maximum lower)))
      (implies (subsetp-equal gone (fn-bs-pack-reclaim-plan names maximum lower))
               (equal (fn-profile-txn-observation
                       (fn-ccp-remove-names names gone) maximum lower)
                      (list :ok lower
                            (fn-ccp-remove-pairs (third before) gone))))))))

; One owner of field 4: the reclaim plan under a profile upgrade.
(assert-event
 (fn-profile-upgradep *fn-bs-profile-development* *fn-bs-profile-scale*))
(assert-event
 (equal (fn-bs-pack-reclaim-plan *ccpt-names* 3 4) :invalid))
(assert-event
 (not (equal (fn-bs-pack-reclaim-plan *ccpt-names* 8 4) :invalid)))
(local
 (must-fail
  (defthm ccpt-plan-without-upgrade
    (implies (not (equal (fn-bs-pack-reclaim-plan
                          names (fn-bs-profile-max-transactions old) lower)
                         :invalid))
             (equal (fn-bs-pack-reclaim-plan names (fn-bs-profile-max-transactions new) lower)
                    (fn-bs-pack-reclaim-plan names (fn-bs-profile-max-transactions old)
                                             lower)))
    :hints (("Goal" :in-theory (disable fn-bs-profile-max-transactions
                                        fn-bs-pack-reclaim-plan))))))
; Its counterexample: scale's plan over 129 names is not development's.
; Without the old plan being valid: 129 names are :invalid under development
; (T = 128) and a plan under scale, across an upgrade.
(defun ccpt-names (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (fn-bs-txn-name-impl i) (ccpt-names (1+ i) n))
    nil))
(assert-event
 (let ((names (ccpt-names 0 129)))
   (and (fn-profile-upgradep *fn-bs-profile-development* *fn-bs-profile-scale*)
        (equal (fn-bs-pack-reclaim-plan
                names (fn-bs-profile-max-transactions *fn-bs-profile-development*) 0)
               :invalid)
        (not (equal (fn-bs-pack-reclaim-plan
                     names (fn-bs-profile-max-transactions *fn-bs-profile-scale*) 0)
                    :invalid)))))
(local
 (must-fail
  (defthm ccpt-plan-without-valid-old
    (implies (fn-profile-upgradep old new)
             (equal (fn-bs-pack-reclaim-plan names (fn-bs-profile-max-transactions new) lower)
                    (fn-bs-pack-reclaim-plan names (fn-bs-profile-max-transactions old)
                                             lower)))
    :hints (("Goal" :in-theory (disable fn-profile-upgradep
                                        fn-bs-profile-max-transactions
                                        fn-bs-pack-reclaim-plan))))))
(assert-event
 (equal (fn-ccp-coverage-framed *ccpt-framed* *ccpt-digest* 3 6)
        '(:error :coverage)))
(local
 (must-fail
  (defthm ccpt-coverage-without-ok
    (implies (and (rationalp old) (rationalp new) (<= old new))
             (equal (fn-ccp-coverage-framed framed digest new frontier)
                    (fn-ccp-coverage-framed framed digest old frontier))))))
(local
 (must-fail
  (defthm ccpt-coverage-without-order
    (equal (fn-ccp-coverage-framed *ccpt-framed* *ccpt-digest* 3 6)
           (fn-ccp-coverage-framed *ccpt-framed* *ccpt-digest* 8 6)))))
