(in-package "ACL2")
(include-book "../../books/extent-window-stream")

; Test-only archive adapter. Runtime reads exactly the core-issued effect.
(defun ewst-run (fuel archive s pgs-digest-state fn-ew-buffer fn-octets reads)
  (declare (xargs :stobjs (pgs-digest-state fn-ew-buffer fn-octets)
                  :measure (nfix fuel) :verify-guards nil))
  (cond ((zp fuel) (mv :fuel s pgs-digest-state fn-ew-buffer fn-octets reads))
        ((not (member-eq (nth 0 s) '(:scan :trailer)))
         (mv (nth 0 s) s pgs-digest-state fn-ew-buffer fn-octets reads))
        (t (let ((effect (fn-ews-effect s pgs-digest-state)))
             (if effect
                 (let* ((bytes (fn-b3-firstn (nth 5 effect)
                                   (fn-b3-nthcdrx (- (nth 4 effect) (nth 2 s)) archive)))
                        (fn-octets (fn-octets-from-list bytes fn-octets)))
                   (mv-let (status s pgs-digest-state fn-ew-buffer)
                     (fn-ews-read effect :ok s fn-octets pgs-digest-state fn-ew-buffer)
                     (declare (ignore status))
                     (ewst-run (1- fuel) archive s pgs-digest-state fn-ew-buffer fn-octets
                               (+ reads (len bytes)))))
               (mv-let (status s pgs-digest-state)
                 (fn-ews-tick s pgs-digest-state)
                 (declare (ignore status))
                 (ewst-run (1- fuel) archive s pgs-digest-state fn-ew-buffer fn-octets reads)))))))

(defun ewst-output (n i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer :measure (nfix n) :verify-guards nil))
  (if (zp n) nil
    (cons (fn-ew-bytesi i fn-ew-buffer) (ewst-output (1- n) (1+ i) fn-ew-buffer))))

(defun ewst-example (msg archive payload-start payload-length offset expected)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (answer pgs-digest-state)
      (with-local-stobj fn-octets
        (mv-let (answer pgs-digest-state fn-octets)
          (with-local-stobj fn-ew-buffer
            (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer)
              (mv-let (s pgs-digest-state)
                (fn-ews-begin 7 100 (len msg) (+ 100 payload-start) payload-length offset
                              23 47 59 expected pgs-digest-state)
                (mv-let (status s pgs-digest-state fn-ew-buffer fn-octets reads)
                  (ewst-run 10000 archive s pgs-digest-state fn-ew-buffer fn-octets 0)
                  (mv (list status (fn-ewp-publication s) reads
                            (ewst-output (nth 5 s) 0 fn-ew-buffer))
                      pgs-digest-state fn-octets fn-ew-buffer)))
              (mv answer pgs-digest-state fn-octets)))
          (mv answer pgs-digest-state)))
      answer)))

; Actual local concrete buffers/cursor, arbitrary tail lengths, tree boundaries.
(assert-event
 (let* ((msg '(0 1 2 3 4 5 6 7 8 9)) (digest (fn-blake3 msg)))
   (equal (ewst-example msg (append msg digest) 2 6 1 (fn-bch-pack digest))
          '(:verified (23 47 59 7 103 5) 42 (3 4 5 6 7)))))
(assert-event
 (let ((digest (fn-blake3 nil)))
   (equal (ewst-example nil digest 0 0 0 (fn-bch-pack digest))
          '(:verified (23 47 59 7 100 0) 32 nil))))
(assert-event
 (let* ((msg (append (make-list 1024 :initial-element 9) '(3 4 5)))
        (digest (fn-blake3 msg)))
   (equal (ewst-example msg (append msg digest) 1022 5 0 (fn-bch-pack digest))
          '(:verified (23 47 59 7 1122 5) 1059 (9 9 3 4 5)))))
(assert-event
 (let* ((msg (make-list 16449 :initial-element 7)) (digest (fn-blake3 msg))
        (answer (ewst-example msg (append msg digest) 1 16448 0 (fn-bch-pack digest))))
   (and (equal (car answer) :verified)
        (equal (cadr answer) '(23 47 59 7 101 16384))
        (equal (caddr answer) 16481)
        (equal (cadddr answer) (make-list 16384 :initial-element 7)))))

; Distinct damaged-prefix / wrong commitment / short read failures.
(assert-event
 (let* ((msg '(1 2 3)) (digest (fn-blake3 msg)))
   (and (equal (car (ewst-example msg (append '(1 2 4) digest) 0 3 0 (fn-bch-pack digest))) :digest)
        (not (cadr (ewst-example msg (append '(1 2 4) digest) 0 3 0 (fn-bch-pack digest))))
        (equal (car (ewst-example msg (append msg digest) 0 3 0 0)) :commitment)
        (equal (car (ewst-example msg '(1 2) 0 3 0 (fn-bch-pack digest))) :read))))

(defun-nx ewst-three-ready ()
  (let* ((msg '(1 2 3)) (digest (fn-blake3 msg))
         (begin (fn-ews-begin 7 100 3 100 3 0 23 47 59 (fn-bch-pack digest) (create-pgs-digest-state))))
    (ewst-run 4 (append msg digest) (car begin) (cadr begin) (create-fn-ew-buffer) nil 0)))

; Full literal antecedent and conclusion of actual-core integrity theorem.
(defthm ewst-core-integrity-positive
  (let* ((ready (ewst-three-ready)) (s (nth 1 ready)) (cursor (nth 2 ready))
         (buffer (nth 3 ready)) (input (fn-blake3 '(1 2 3)))
         (effect (fn-ews-effect s cursor))
         (next (fn-ews-read effect :ok s input cursor buffer)))
    (and (not (fn-ewp-publication s)) (fn-ewp-publication (nth 1 next))
         (equal (nth 0 s) :trailer) (equal (pgs-dc-mode cursor) :done)
         (equal (nth 7 s) (nth 3 s))
         (equal effect (fn-ews-effect s cursor))
         (equal :ok :ok) (equal (fn-octets-len input) 32)
         (equal (fn-bch-pack (fn-ews-read-trailer 32 0 input)) (nth 6 s))
         (equal (pgs-dcb-result-octets cursor) (fn-ews-read-trailer 32 0 input))))
  :rule-classes nil)

; Remove only 'not previously published': a later stale read preserves an
; already published result. It need not be a new successful trailer read.
(defthm ewst-core-integrity-prior-publication-removal
  (let* ((ready (ewst-three-ready)) (s0 (nth 1 ready)) (cursor (nth 2 ready))
         (buffer (nth 3 ready)) (input (fn-blake3 '(1 2 3)))
         (s (nth 1 (fn-ews-read (fn-ews-effect s0 cursor) :ok s0 input cursor buffer)))
         (next (fn-ews-read nil :ok s input cursor buffer)))
    (and (fn-ewp-publication s) (fn-ewp-publication (nth 1 next))
         (not (and (equal (nth 0 s) :trailer) (equal (pgs-dc-mode cursor) :done)
                   (equal (nth 7 s) (nth 3 s))
                   (equal nil (fn-ews-effect s cursor))
                   (equal :ok :ok) (equal (fn-octets-len input) 32)
                   (equal (fn-bch-pack (fn-ews-read-trailer 32 0 input)) (nth 6 s))
                   (equal (pgs-dcb-result-octets cursor) (fn-ews-read-trailer 32 0 input))))))
  :rule-classes nil)

; Stale physical incarnation preserves all concrete state, not just status.
(defthm ewst-stale-all-effects-positive
  (let* ((ready (ewst-three-ready)) (s (nth 1 ready)) (cursor (nth 2 ready))
         (buffer (nth 3 ready)) (input (fn-blake3 '(1 2 3)))
         (effect (update-nth 1 48 (fn-ews-effect s cursor))))
    (and (not (equal effect (fn-ews-effect s cursor)))
         (equal (fn-ews-read effect :ok s input cursor buffer)
                (list :stale s cursor buffer))))
  :rule-classes nil)

; Omit the complete stale disjunction: an exact live completion changes state.
(defthm ewst-stale-all-effects-removal
  (let* ((ready (ewst-three-ready)) (s (nth 1 ready)) (cursor (nth 2 ready))
         (buffer (nth 3 ready)) (input (fn-blake3 '(1 2 3)))
         (effect (fn-ews-effect s cursor)))
    (and effect (equal effect (fn-ews-effect s cursor))
         (not (equal (fn-ews-read effect :ok s input cursor buffer)
                     (list :stale s cursor buffer)))))
  :rule-classes nil)
