; Incremental operator replay of the decision journal (S011).
; Keep the parser continuation and the replay state, never prior entries.
; A malformed long line retains only its first eight fields: replay rejects
; every entry longer than seven, and reporting uses only its first two.
; Natural fields retain their exact width; this introduces no numeric ceiling.
(in-package "ACL2")
(include-book "owner-time-journal")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

(local (defthm otjs-tlf-type (true-listp (true-list-fix x))))
(local (defthm otjs-tlf-id
         (implies (true-listp x) (equal (true-list-fix x) x))
         :hints (("Goal" :in-theory (enable true-list-fix)))))
(local (defthm otjs-len-tlf (equal (len (true-list-fix x)) (len x))
         :hints (("Goal" :in-theory (enable true-list-fix)))))
(local (defthm otjs-car-tlf (equal (car (true-list-fix x)) (car x))
         :hints (("Goal" :in-theory (enable true-list-fix)))))
(local (defthm otjs-cdr-tlf
         (equal (cdr (true-list-fix x)) (true-list-fix (cdr x)))
         :hints (("Goal" :in-theory (enable true-list-fix)))))

; State: syntax, unfinished number, reversed fields, complete-entry count,
; segment count, first replay verdict, current replay state.
(defun fn-otjs-init ()
  (declare (xargs :guard t))
  (list :whole nil nil 0 0 :agrees (fn-otm-init)))

(defun fn-otjs-field (n st)
  (declare (xargs :guard (natp n)))
  (nth n (true-list-fix st)))

(defun fn-otjs-fields (st)
  (declare (xargs :guard t))
  (true-list-fix (fn-otjs-field 2 st)))

(defun fn-otjs-entry (st value)
  (declare (xargs :guard t))
  (let* ((entry (fn-otm-revonto (fn-otjs-fields st) (list value)))
         (old (fn-otjs-field 5 st))
         (prior (fn-otjs-field 6 st)))
    (mv-let (verdict next)
      (if (eq old :agrees)
          (fn-otm-replay prior (list entry))
        (mv old prior))
      (list :whole nil nil
            (+ 1 (nfix (fn-otjs-field 3 st)))
            (+ (nfix (fn-otjs-field 4 st))
               (if (and (consp entry) (consp (cdr entry))
                        (equal (cadr entry) 0)) 1 0))
            verdict next))))

(defun fn-otjs-octet (o st)
  (declare (xargs :guard t))
  (let* ((st (true-list-fix st))
         (acc (fn-otjs-field 1 st))
         (fields (fn-otjs-fields st)))
    (cond ((eq (fn-otjs-field 0 st) :malformed) st)
          ((and (natp o) (<= 48 o) (<= o 57))
           (update-nth 1 (if (< (len fields) 8)
                             (+ (* 10 (nfix acc)) (- o 48))
                           0) st))
          ((and (equal o 32) acc)
           (update-nth 1 nil
             (update-nth 2 (if (< (len fields) 8)
                               (cons acc fields) fields) st)))
          ((and (equal o 10) acc) (fn-otjs-entry st acc))
          (t (update-nth 0 :malformed st)))))

(defun fn-otjs-consume (octets st)
  (declare (xargs :guard t :measure (len octets)))
  (if (consp octets)
      (fn-otjs-consume (cdr octets) (fn-otjs-octet (car octets) st))
    st))

(defun fn-otjs-status (st)
  (declare (xargs :guard t))
  (cond ((eq (fn-otjs-field 0 st) :malformed) :malformed)
        ((or (fn-otjs-field 1 st) (fn-otjs-field 2 st)) :torn)
        (t :whole)))

(defun fn-otjs-report (st)
  (declare (xargs :guard t))
  (append (fn-osch-text "journal:")
          (fn-osch-kv "entries" (nfix (fn-otjs-field 3 st)))
          (fn-osch-kv "segments" (nfix (fn-otjs-field 4 st)))
          (fn-osch-text (case (fn-otjs-status st)
                          (:whole " status=whole")
                          (:torn " status=torn")
                          (otherwise " status=malformed")))
          (fn-osch-text " replay=")
          (fn-otm-verdict-text (fn-otjs-field 5 st))
          (list 10)))

(defun fn-otjs-exit (st)
  (declare (xargs :guard t))
  (if (eq (fn-otjs-field 5 st) :agrees) 0 1))

; A scheduling quantum, not a file-size or numeric-field ceiling.
(defun fn-otjs-read-count (remaining)
  (declare (xargs :guard t))
  (min 65536 (nfix remaining)))

; Chunk boundaries cannot change the parser/replay outcome.
(defthm fn-otjs-consume-of-append
  (equal (fn-otjs-consume (append a b) st)
         (fn-otjs-consume b (fn-otjs-consume a st)))
  :hints (("Goal" :induct (fn-otjs-consume a st)
           :in-theory (disable fn-otjs-octet))))

(defthm fn-otjs-read-count-bounded
  (and (natp (fn-otjs-read-count remaining))
       (<= (fn-otjs-read-count remaining) 65536)
       (<= (fn-otjs-read-count remaining) (nfix remaining))))

(defthm fn-otjs-fields-bounded
  (implies (<= (len (fn-otjs-fields st)) 8)
           (<= (len (fn-otjs-fields (fn-otjs-octet o st))) 8))
  :hints (("Goal" :in-theory
           (e/d (fn-otjs-octet fn-otjs-entry fn-otjs-fields fn-otjs-field
                 nth update-nth true-list-fix) (fn-otm-replay)))))

(defthm fn-otjs-consume-fields-bounded
  (implies (<= (len (fn-otjs-fields st)) 8)
           (<= (len (fn-otjs-fields (fn-otjs-consume octets st))) 8))
  :hints (("Goal" :induct (fn-otjs-consume octets st)
           :in-theory (disable fn-otjs-fields fn-otjs-octet))))
