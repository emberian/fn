; Tests for books/payload-commit-extent.lisp (lane arena-offheap-3, PRF-309).
;
; 1. The functions the host calls are guard-verified.
; 2. The place search on a live arena: a record holding handle 0's payload
;    gives the extent at that place; a record without it, a frame length
;    that is not the record's, and a handle past the count give nil (no
;    reseat).
; 3. Teeth for the keystones.

(in-package "ACL2")
(include-book "../../books/payload-commit-extent")
(include-book "must-fail-checked")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-arn-extent-guardp))))

(assert-event
 (and (eq (symbol-class 'fn-arx-arena-prefixp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-arena-find (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-commit-place (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-commit-extent (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-commit-reseat (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-commit-reseats (w state)) :common-lisp-compliant)))

; Handle 0 holds (1 2 3); the record the log wrote is (9 9 1 2 3 7), placed
; (fn-arx-list-places) in the one-record entry at start 100 of file 5: frame
; 42 + 6 + 32 = 80 octets, the record at 142, 6 octets.
(defconst *pcx-r* '(9 9 1 2 3 7))
(defconst *pcx-pos* '(100 80 142 6))

(assert-event
 (let ((fn-arena (fn-arena-clear fn-arena)))
   (let ((fn-arena (fn-arena-seal-list '(1 2 3) fn-arena)))
     (mv (and (equal (fn-arx-commit-extent 0 5 *pcx-pos* *pcx-r* fn-arena)
                     '(5 100 48 144 3 0))
              ; the payload is not in the record
              (null (fn-arx-commit-extent 0 5 *pcx-pos* '(9 9 1 2 4 7) fn-arena))
              ; the place is not the record's (its length)
              (null (fn-arx-commit-extent 0 5 '(100 80 142 7) *pcx-r* fn-arena))
              ; the record is not inside the entry's protected prefix
              (null (fn-arx-commit-extent 0 5 '(100 79 142 6) *pcx-r* fn-arena))
              ; the payload is longer than the record
              (null (fn-arx-commit-extent 0 5 '(100 76 142 2) '(1 2) fn-arena)))
         fn-arena)))
 :stobjs-out '(nil fn-arena))

; A reseat the ACL2 check refuses leaves the arena as it is (a handle past
; the count, a record that does not hold the payload).
(assert-event
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list '(1 2 3) fn-arena))
        (fn-arena (fn-arx-commit-reseat 1 5 *pcx-pos* *pcx-r* fn-arena))
        (fn-arena (fn-arx-commit-reseat 0 5 *pcx-pos* '(9 9 9) fn-arena)))
   (mv (and (equal (fn-arena-count fn-arena) 1)
            (equal (fn-arena-payload 0 fn-arena) '(1 2 3)))
       fn-arena))
 :stobjs-out '(nil fn-arena))

; --- Teeth.
; fn-arx-commit-reseat-keeps-the-arena: positive witness at the ground arena
; and record above, the faithful write as the hypothesis; the extent is
; found (so the reseat branch is the one taken) and the arena is unchanged.
(defthm pcx-keeps-witness
  (implies (equal (fn-durable-octets 5 142 6) *pcx-r*)
           (and (fn-arena-p '((1 2 3)))
                (true-listp *pcx-r*)
                (equal (fn-arx-commit-extent 0 5 *pcx-pos* *pcx-r* '((1 2 3)))
                       '(5 100 48 144 3 0))
                (equal (fn-arx-commit-reseat 0 5 *pcx-pos* *pcx-r* '((1 2 3)))
                       '((1 2 3)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arx-commit-reseat-keeps-the-arena
                                   (h 0) (file 5) (position *pcx-pos*) (r *pcx-r*)
                                   (fn-arena '((1 2 3)))))
           :in-theory (disable (:e fn-arx-commit-reseat) fn-arx-commit-reseat-keeps-the-arena))))

; Without the faithful write the reseat is not provably the identity.
(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pcx-keeps-without-faithful
    (implies (and (fn-arena-p fn-arena) (true-listp r))
             (equal (fn-arx-commit-reseat h file position r fn-arena) fn-arena))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pcx-keeps-without-arena-p
    (implies (and (true-listp r)
                  (equal (fn-durable-octets (nfix file) (nfix (nth 2 position)) (len r)) r))
             (equal (fn-arx-commit-reseat h file position r fn-arena) fn-arena))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pcx-keeps-without-true-listp
    (implies (and (fn-arena-p fn-arena)
                  (equal (fn-durable-octets (nfix file) (nfix (nth 2 position)) (len r)) r))
             (equal (fn-arx-commit-reseat h file position r fn-arena) fn-arena))))))

; fn-arx-commit-reseats-keep-the-arena: the ground batch of the witness.
(defthm pcx-reseats-witness
  (implies (equal (fn-durable-octets 5 142 6) *pcx-r*)
           (and (fn-arx-commit-faithful-p (list (list 0 5 *pcx-pos* *pcx-r*)))
                (equal (fn-arx-commit-reseats (list (list 0 5 *pcx-pos* *pcx-r*)) '((1 2 3)))
                       '((1 2 3)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arx-commit-reseats-keep-the-arena
                                   (members (list (list 0 5 *pcx-pos* *pcx-r*)))
                                   (fn-arena '((1 2 3)))))
           :in-theory (disable (:e fn-arx-commit-reseats) fn-arx-commit-reseats-keep-the-arena))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pcx-reseats-without-faithful
    (implies (fn-arena-p fn-arena)
             (equal (fn-arx-commit-reseats members fn-arena) fn-arena))))))
