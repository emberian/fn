; Layer C2 unit: exact Message-ID identity over the overlay and sealed runs.
(in-package "ACL2")
(include-book "runs-assembly")

; Offer fixtures: Message-ID j ("<i" five digits "@t>"), content all byte b.
(defun fn2-it-digits (n k)
 (declare (xargs :verify-guards nil :measure (nfix k)))
 (if (zp k) nil (append (fn2-it-digits (floor n 10) (- k 1)) (list (+ 48 (mod n 10))))))
(defun fn2-it-mid (j) (declare (xargs :verify-guards nil)) (append (list 60 105) (fn2-it-digits j 5) (list 64 116 62)))
(defun fn2-it-offer (j b) (declare (xargs :verify-guards nil)) (list (fn2-it-mid j) (make-list 32 :initial-element b)))

; The M3-shaped scenario: ten Message-IDs accepted; a conflicting content for
; m3; a duplicate re-offer of m5; m7 offered with five contents, of which the
; bound retains four. Sealed every four offers, so facts sit in three runs
; and the overlay. The staging workspace holding every offer's octets is
; released before the queries.
(defconst *fn2-it-offers*
 (append (list (fn2-it-offer 0 1) (fn2-it-offer 1 1) (fn2-it-offer 2 1) (fn2-it-offer 3 1) (fn2-it-offer 4 1))
         (list (fn2-it-offer 3 2) (fn2-it-offer 5 1) (fn2-it-offer 5 1) (fn2-it-offer 6 1))
         (list (fn2-it-offer 7 1) (fn2-it-offer 7 2) (fn2-it-offer 7 3) (fn2-it-offer 7 4) (fn2-it-offer 7 5))
         (list (fn2-it-offer 8 1) (fn2-it-offer 9 1))))
(defconst *fn2-it-queries*
 (list (fn2-it-offer 0 1) (fn2-it-offer 3 2) (fn2-it-offer 3 9) (fn2-it-offer 11 1) (fn2-it-offer 7 5)
       (fn2-it-offer 7 4) (fn2-it-offer 5 1) (fn2-it-offer 9 2) (list nil (make-list 32 :initial-element 1))))
(assert-event
 (equal (fn2-identity-decide-image *fn2-it-offers* 4 nil *fn2-it-queries*)
        '(((:stored :ok) (:stored :ok) (:stored :ok) (:stored :ok) (:stored :ok) (:conflict :ok) (:stored :ok)
           (:duplicate :none) (:stored :ok) (:stored :ok) (:conflict :ok) (:conflict :ok) (:conflict :ok)
           (:conflict :identity-conflict-bound) (:stored :ok) (:stored :ok))
          :ok
          (:duplicate :duplicate :conflict :stored :conflict :duplicate :duplicate :conflict :stored))))

;; Teeth for fn2-exact-identity. Positive: the scenario above at three
;; splits (all in the overlay, sealed every four, sealed after each offer).
;; Negative: a node whose summary dropped the Message-ID octets (offers
;; recorded under the empty Message-ID) answers :stored to the re-offer of m1
;; with a different content, where the statement requires :conflict.
(defun fn2-it-drop-mids (offers)
 (declare (xargs :verify-guards nil))
 (if (atom offers) nil (cons (list nil (fn2-id-content (car offers))) (fn2-it-drop-mids (cdr offers)))))
(defun fn2-exact-identity-positive ()
 (declare (xargs :verify-guards nil))
 (and (fn2-id-offersp *fn2-it-offers*) (fn2-id-offersp *fn2-it-queries*)
      (equal (caddr (fn2-identity-decide-image *fn2-it-offers* 0 nil *fn2-it-queries*)) (fn2-id-answers-spec *fn2-it-offers* *fn2-it-queries*))
      (equal (caddr (fn2-identity-decide-image *fn2-it-offers* 4 nil *fn2-it-queries*)) (fn2-id-answers-spec *fn2-it-offers* *fn2-it-queries*))
      (equal (caddr (fn2-identity-decide-image *fn2-it-offers* 1 nil *fn2-it-queries*)) (fn2-id-answers-spec *fn2-it-offers* *fn2-it-queries*))))
(defun fn2-exact-identity-negative ()
 (declare (xargs :verify-guards nil))
 (let ((q (list (fn2-it-offer 1 2))))
  (and (equal (fn2-id-answers-spec *fn2-it-offers* q) '(:conflict))
       (not (equal (caddr (fn2-identity-decide-image (fn2-it-drop-mids *fn2-it-offers*) 4 nil q))
                   (fn2-id-answers-spec *fn2-it-offers* q))))))
(fn2-assert-owed-teeth fn2-exact-identity)

;; Teeth for fn2-identity-binding-converges. Positive: one fact set within
;; the bound, delivered in two orders (the second with a duplicate) under two
;; sealing schedules, gives one Binding. Negative: nodes that refuse a
;; conflicting offer and record nothing hold different Bindings for the two
;; orders, and neither learns of the conflict.
(defconst *fn2-it-bind*
 (list (fn2-it-offer 1 1) (fn2-it-offer 2 1) (fn2-it-offer 1 2) (fn2-it-offer 3 1) (fn2-it-offer 2 3) (fn2-it-offer 4 1)))
(defconst *fn2-it-bind-2*
 (append (reverse *fn2-it-bind*) (list (fn2-it-offer 2 1))))
(defun fn2-identity-binding-converges-positive ()
 (declare (xargs :verify-guards nil))
 (and (fn2-id-offersp *fn2-it-bind*) (fn2-id-offersp *fn2-it-bind-2*)
      (equal (fn2-id-binding-spec *fn2-it-bind*) (fn2-id-binding-spec *fn2-it-bind-2*))
      (fn2-id-within-bound *fn2-it-bind*)
      (equal (fn2-identity-binding-image *fn2-it-bind* 2 nil) (fn2-identity-binding-image *fn2-it-bind-2* 3 nil))
      (equal (fn2-identity-binding-image *fn2-it-bind* 2 nil) (fn2-id-binding-spec *fn2-it-bind*))))
(defun fn2-identity-binding-converges-negative ()
 (declare (xargs :verify-guards nil))
 (not (equal (fn2-identity-binding-image *fn2-it-bind* 2 t) (fn2-identity-binding-image *fn2-it-bind-2* 3 t))))
(fn2-assert-owed-teeth fn2-identity-binding-converges)

;; The identity schema's generated keystones (page, seek, run lookup, scan,
;; overlay), with the run units' teeth makers over identity entries: Message-ID
;; j with contents all-0 (accepted) and all-1 (conflict evidence).
(defconst *fn2-it-meta* '(0 1 1 6 2 4 1 1 8 0 0))
(defun fn2-it-entries (i n)
 (declare (xargs :verify-guards nil :measure (nfix (- n i))))
 (if (zp (- n i)) nil
  (cons (list (fn2-it-mid (floor i 2)) (cons 1 (make-list 32 :initial-element (mod i 2))) (mod i 2) (+ 100 i) (+ 1 i) 7)
        (fn2-it-entries (+ 1 i) n))))
(defconst *fn2-it-good* (fn2-it-entries 0 40))
(defconst *fn2-it-bad* (append (list (nth 5 *fn2-it-good*)) (take 5 *fn2-it-good*) (nthcdr 6 *fn2-it-good*)))
(defconst *fn2-it-key* '((message-id (:octets 250)) (content :digest)))
(defun fn2-it-q (j c) (declare (xargs :verify-guards nil)) (list (fn2-it-mid j) (cons 1 (make-list 32 :initial-element c)) 0 0 0 0))
(fn2-rt-teeth fn2-identity 1 ((message-id (:octets 250)) (content :digest))
 *fn2-it-meta* *fn2-it-good* *fn2-it-bad*
 (list (fn2-it-q 0 0) (fn2-it-q 7 1) (fn2-it-q 7 2) (fn2-it-q 19 1) (fn2-it-q 20 0) (list nil (cons 1 (make-list 32 :initial-element 0)) 0 0 0 0))
 (nth 10 *fn2-it-good*))
(fn2-rt-run-teeth fn2-identity 1 ((message-id (:octets 250)) (content :digest))
 *fn2-it-good* *fn2-it-bad* 1024
 (list (nth 0 *fn2-it-good*) (nth 17 *fn2-it-good*) (nth 39 *fn2-it-good*) (fn2-it-q 7 2) (fn2-it-q 25 0))
 (nth 10 *fn2-it-good*))
(fn2-rt-scan-teeth fn2-identity 1 ((message-id (:octets 250)) (content :digest))
 *fn2-it-good* *fn2-it-bad* 1024
 (list (list (list nil (cons 1 (make-list 32 :initial-element 0)) 0 0 0 0) 50)
       (list (fn2-it-q 7 0) 3) (list (fn2-it-q 7 2) 4) (list (nth 39 *fn2-it-good*) 2))
 (list nil (cons 1 (make-list 32 :initial-element 0)) 0 0 0 0))
(fn2-rt-overlay-teeth fn2-identity 1 ((message-id (:octets 250)) (content :digest))
 (fn2-rt-shuffle *fn2-it-good* 0 40) (cons (nth 3 *fn2-it-good*) (fn2-rt-shuffle *fn2-it-good* 0 40)))

;; Read amplification with the per-run Ribbon filters (C2c): each query of
;; the M3-shaped scenario reads only the runs that hold its Message-ID; the
;; filters skip the rest, and an absent Message-ID reads no run. Sealed after
;; every offer (14 runs) and every four (4 runs): (answer runs-read runs-skipped).
(assert-event
 (equal (fn2-identity-cost-image *fn2-it-offers* 1 *fn2-it-queries*)
        '((:duplicate 1 13) (:duplicate 2 12) (:conflict 2 12) (:stored 0 14) (:conflict 4 10)
          (:duplicate 4 10) (:duplicate 1 13) (:conflict 1 13) (:stored 0 14))))
(assert-event
 (equal (fn2-identity-cost-image *fn2-it-offers* 4 *fn2-it-queries*)
        '((:duplicate 1 3) (:duplicate 2 2) (:conflict 2 2) (:stored 0 4) (:conflict 2 2)
          (:duplicate 2 2) (:duplicate 1 3) (:conflict 1 3) (:stored 0 4))))
