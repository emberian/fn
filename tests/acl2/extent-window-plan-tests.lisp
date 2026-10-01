(in-package "ACL2")
(include-book "../../books/extent-window-plan")

(defun ewpt-consume (s)
  (declare (xargs :guard (true-listp s)))
  (mv-let (verdict next)
    (fn-ewp-complete-read (fn-ewp-effect s) (fn-ewp-demand s) :ok s)
    (declare (ignore verdict)) next))
(defun ewpt-finish (read digest s)
  (declare (xargs :guard (true-listp s)))
  (mv-let (verdict next) (fn-ewp-finish read digest s)
    (declare (ignore verdict)) next))
(defun ewpt-completion (effect got verdict s)
  (declare (xargs :guard (and (natp got) (true-listp s))))
  (mv-let (answer next) (fn-ewp-complete-read effect got verdict s)
    (declare (ignore answer)) next))
(defconst *ewpt-trailer* (make-list 32 :initial-element 0))
(defconst *ewpt-begin*
  (fn-ewp-begin 5 100 70 160 10 0 21 '(generation 8) '(lease 4)
                (fn-bch-pack *ewpt-trailer*)))
(defconst *ewpt-last* (ewpt-consume *ewpt-begin*))
(defconst *ewpt-trailer-state* (ewpt-consume *ewpt-last*))
(defconst *ewpt-digest* (ewpt-consume *ewpt-trailer-state*))
(defconst *ewpt-verified*
  (ewpt-finish *ewpt-trailer* *ewpt-trailer* *ewpt-digest*))

; Nonempty requested window crosses two protected-prefix reads.
(assert-event
 (and (equal (fn-ewp-demand *ewpt-begin*) 64)
      (equal (fn-ewp-demand *ewpt-last*) 6)
      (equal (fn-ewp-window-span *ewpt-begin*) '(60 4 0))
      (equal (fn-ewp-window-span *ewpt-last*) '(0 6 4))
      (equal (fn-ewp-payload-span 160 10 *ewpt-begin*) '(60 4))
      (equal (fn-ewp-payload-span 160 10 *ewpt-last*) '(0 6))
      (equal (fn-ewp-demand *ewpt-trailer-state*) 32)
      (equal (nth 4 (fn-ewp-effect *ewpt-trailer-state*)) 170)
      (not (fn-ewp-publication *ewpt-begin*))
      (not (fn-ewp-publication *ewpt-last*))
      (not (fn-ewp-publication *ewpt-trailer-state*))
      (not (fn-ewp-publication *ewpt-digest*))
      (equal (fn-ewp-publication *ewpt-verified*)
             '(21 (generation 8) (lease 4) 5 160 10))))

; Full antecedent and conclusion of the integrity publication keystone.
; The digest value is an input here; this is not a hash correctness witness.
(assert-event
 (let ((s *ewpt-digest*) (read *ewpt-trailer*) (digest *ewpt-trailer*))
   (and (not (fn-ewp-publication s))
        (fn-ewp-publication (ewpt-finish read digest s))
        (equal (nth 0 s) :digest) (equal (nth 7 s) (nth 3 s))
        (fn-bch-octetsp read) (equal (len read) 32)
        (equal (fn-bch-pack read) (nth 6 s)) (equal digest read))))

; Hypothesis-removal: preexisting publication is not a new verified result.
(assert-event
 (let ((s *ewpt-verified*) (read '(1)) (digest '(2)))
   (and (fn-ewp-publication s)
        (fn-ewp-publication (ewpt-finish read digest s))
        (not (and (equal (nth 0 s) :digest) (equal (nth 7 s) (nth 3 s))
                  (fn-bch-octetsp read) (equal (len read) 32)
                  (equal (fn-bch-pack read) (nth 6 s)) (equal digest read))))))

; Hypothesis-removal: no resulting publication, all other hypotheses retained.
(assert-event
 (let ((s *ewpt-digest*) (read *ewpt-trailer*) (digest '(9)))
   (and (not (fn-ewp-publication s))
        (not (fn-ewp-publication (ewpt-finish read digest s)))
        (not (and (equal (nth 0 s) :digest) (equal (nth 7 s) (nth 3 s))
                  (fn-bch-octetsp read) (equal (len read) 32)
                  (equal (fn-bch-pack read) (nth 6 s)) (equal digest read))))))

; Corruption and stale incarnation/lease are distinct from success.
(assert-event
 (and (equal (nth 0 (ewpt-finish '(9) '(9) *ewpt-digest*)) :commitment)
      (equal (nth 0 (ewpt-finish *ewpt-trailer* '(9) *ewpt-digest*)) :digest)
      (equal (ewpt-completion
                        '(21 (generation 9) (lease 4) 5 100 64 :scan)
                        64 :ok *ewpt-begin*) *ewpt-begin*)
      (equal (nth 0 (ewpt-completion
                               (fn-ewp-effect *ewpt-begin*) 63 :ok *ewpt-begin*)) :read)))

; An extent far larger than the window does not change scratch demand or
; reject the data; the next requested payload window is simply another step.
(assert-event
 (let ((s (fn-ewp-begin 5 0 1000000000 100 999999000 17000 21 8 4 0)))
   (and (eq (nth 0 s) :scan) (equal (nth 5 s) 16384)
        (equal (fn-ewp-demand s) 64) (equal (nth 4 s) 17100))))
