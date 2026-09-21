(in-package "ACL2")
(include-book "../../books/checkpoint-compaction")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cc-a0*
  (fn-record-make 0 0 0 "<compact@example.invalid>" '(65 13 10)
                  '("fn.letters") "archive-0" "subject-0" "evidence-0" 3))
(defconst *cc-e1*
  (fn-store-retention-event-make :undertake 1 1 1
                                 "forward-1" "subject-1" "evidence-1" 2))
(defconst *cc-e2*
  (fn-store-retention-event-make :release 2 2 2
                                 "forward-1" "subject-1" "receipt-1" 0))
(defconst *cc-b0* (fn-store-event-encode *cc-a0*))
(defconst *cc-b1* (fn-store-event-encode *cc-e1*))
(defconst *cc-b2* (fn-store-event-encode *cc-e2*))
(defconst *cc-i3*
  (fn-stxe-make 3 3 3 "<compact@example.invalid>" :unverified
                '(117 110 118 101 114 105 102 105 101 100) 7 '(116 101 115 116)))
(defconst *cc-k4*
  (fn-stxk-make 4 4 4 7 '(116 101 115 116) '(1 2 3 4)))
(defconst *cc-b3* (fn-store-event-encode *cc-i3*))
(defconst *cc-b4* (fn-store-event-encode *cc-k4*))

(defun cc-repeat-octet (n)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) nil (cons 65 (cc-repeat-octet (1- n)))))
(defconst *cc-large-payload* (cc-repeat-octet 24000))
(defconst *cc-large-b0*
  (fn-store-event-encode
   (fn-record-make 0 0 0 "<large-0@example.invalid>" *cc-large-payload*
                   '("fn.letters") "archive-0" "subject-0" "evidence-0" 1)))
(defconst *cc-large-b1*
  (fn-store-event-encode
   (fn-record-make 1 1 1 "<large-1@example.invalid>" *cc-large-payload*
                   '("fn.letters") "archive-1" "subject-1" "evidence-1" 1)))
(defconst *cc-large-b2*
  (fn-store-event-encode
   (fn-record-make 2 2 2 "<large-2@example.invalid>" *cc-large-payload*
                   '("fn.letters") "archive-2" "subject-2" "evidence-2" 1)))
(defconst *cc-large-summary*
  (fn-cc-make 3 3 (list *cc-large-b0* *cc-large-b1* *cc-large-b2*)))
(assert-event (< *fn-cbor-max-input* (len (fn-cc-encode *cc-large-summary*))))
(assert-event
 (equal (fn-cc-decode-exact (fn-cc-encode *cc-large-summary*))
        (list :ok *cc-large-summary*)))

; One canonical kind-3 Store event crosses the legacy CBOR byte-string cap.
; This exercises the per-item bound, independently of the aggregate witness.
(defconst *cc-single-large-event*
  (fn-store-event-encode
   (fn-stxk-make 0 0 0 1 '(116 101 115 116) (cc-repeat-octet 65536))))
(defconst *cc-single-large-summary*
  (fn-cc-make 1 1 (list *cc-single-large-event*)))
(assert-event (< *fn-cbor-max-bytes* (len *cc-single-large-event*)))
(assert-event
 (equal (fn-cc-decode-exact (fn-cc-encode *cc-single-large-summary*))
        (list :ok *cc-single-large-summary*)))
(local
 (must-fail
  (defthm fn-cc-decode-always-rejects-before-header
    (equal (fn-cc-decode-exact octets) (list :error :octets)))))

(assert-event
 (equal (fn-cc-expand (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))
                      (list *cc-b2*) 4)
        (list :ok (list *cc-b0* *cc-b1* *cc-b2*) 4)))
(assert-event
 (equal (fn-cc-expand
         (fn-cc-make 4 4 (list *cc-b0* *cc-b1* *cc-b2* *cc-b3*))
         (list *cc-b4*) 6)
        (list :ok (list *cc-b0* *cc-b1* *cc-b2* *cc-b3* *cc-b4*) 6)))
(assert-event
 (fn-cc-observation-agrees
  (list (list 1 *cc-b1*) (list 2 *cc-b2*) (list 3 *cc-b3*) (list 4 *cc-b4*))
  (list *cc-b0* *cc-b1* *cc-b2* *cc-b3*) 4))
(assert-event
 (not (fn-cc-observation-agrees
       (list (list 1 *cc-b0*) (list 4 *cc-b4*))
       (list *cc-b0* *cc-b1* *cc-b2* *cc-b3*) 4)))

; A non-degenerate partial deletion: sequence 0 survives, sequence 1 is gone,
; and sequence 2 is the complete suffix.  Recovery retains both packed prefix
; records exactly once and then the suffix.
(defconst *cc-partial-summary* (fn-cc-make 2 2 (list *cc-b0* *cc-b1*)))
(defconst *cc-partial-observed* (list (list 0 *cc-b0*) (list 2 *cc-b2*)))
(assert-event
 (equal (fn-cc-recover-observation *cc-partial-summary*
                                   *cc-partial-observed* 4)
        (list :ok (list *cc-b0* *cc-b1* *cc-b2*) 4)))

; Each theorem hypothesis is load-bearing.
(local
 (must-fail
  (defthm fn-cc-partial-without-summary-shape
    (implies (and (fn-cc-valid-suffixp summary suffix final-frontier)
                  (fn-cc-partial-observationp
                   observed (fn-cc-events summary) suffix
                   (fn-cc-sequence summary)))
             (equal (fn-cc-recover-observation summary observed final-frontier)
                    (list :ok (append (fn-cc-events summary) suffix)
                          final-frontier))))))
(local
 (must-fail
  (defthm fn-cc-partial-without-valid-suffix
    (implies (and (fn-cc-summaryp summary)
                  (fn-cc-partial-observationp
                   observed (fn-cc-events summary) suffix
                   (fn-cc-sequence summary)))
             (equal (fn-cc-recover-observation summary observed final-frontier)
                    (list :ok (append (fn-cc-events summary) suffix)
                          final-frontier))))))
(local
 (must-fail
  (defthm fn-cc-partial-without-exact-observation
    (implies (and (fn-cc-summaryp summary)
                  (fn-cc-valid-suffixp summary suffix final-frontier))
             (equal (fn-cc-recover-observation summary observed final-frontier)
                    (list :ok (append (fn-cc-events summary) suffix)
                          final-frontier))))))
(assert-event
 (equal (fn-cc-decode-exact
         (fn-cc-encode (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))))
        (list :ok (fn-cc-make 2 2 (list *cc-b0* *cc-b1*)))))
(assert-event
 (equal (fn-cc-decode-exact
         (append (fn-cc-encode (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))) '(0)))
        '(:error :summary)))
(assert-event
 (member-equal *cc-b0*
               (fn-cc-events
                (fn-cc-nth 1 (fn-cc-capture (list *cc-b0* *cc-b1*) 2)))))
(assert-event
 (equal (fn-cc-expand (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))
                      (list *cc-b1*) 6)
        '(:error :suffix)))
(assert-event
 (equal (fn-cc-expand (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))
                      (list *cc-b2*) 1)
        '(:error :frontier)))
(assert-event
 (equal (fn-cc-expand (fn-cc-make 2 2 (list *cc-b0* '(999)))
                      (list *cc-b2*) 6)
        '(:error :summary)))
