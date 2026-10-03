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

; A replay folds complete entries in order. Once a verdict fails, a suffix
; must not reset it, even when the suffix begins a new journal segment.
(defthm fn-otjs-replay-of-append
  (equal (fn-otm-replay s (append a b))
         (mv-let (verdict next) (fn-otm-replay s a)
           (if (eq verdict :agrees)
               (fn-otm-replay next b)
             (mv verdict next))))
  :hints (("Goal" :induct (fn-otm-replay s a)
           :in-theory (e/d (fn-otm-replay)
                           (fn-otm-disk-event fn-otm-note fn-otm-init
                            fn-otm-jseq fn-otm-word-code fn-otm-kind-of-op)))))

; The retained projection of an overlong entry preserves its sequence and
; operation, and remains overlong. The ninth dummy field cannot accidentally
; make a rejected entry valid; its arbitrary numeric width is irrelevant.
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(defun fn-otjs-cap-entry (entry)
  (declare (xargs :guard (true-listp entry)))
  (if (< 8 (len entry)) (append (take 8 entry) (list 0))
    entry))

(defthm fn-otjs-replay-of-cap-entry
  (equal (fn-otm-replay s (cons (fn-otjs-cap-entry entry) rest))
         (fn-otm-replay s (cons entry rest)))
  :hints (("Goal" :in-theory (e/d (fn-otjs-cap-entry fn-otm-replay)
                           (fn-otm-disk-event fn-otm-note fn-otm-init
                            fn-otm-jseq fn-otm-word-code fn-otm-kind-of-op)))))

(defthm fn-otjs-starts-of-cap-entry
  (equal (fn-otm-journal-starts (cons (fn-otjs-cap-entry entry) rest))
         (fn-otm-journal-starts (cons entry rest)))
  :hints (("Goal" :in-theory (enable fn-otjs-cap-entry
                                      fn-otm-journal-starts))))

(local
 (defun otjs-cap-fields (fields)
   (if (and (consp fields) (< 8 (len fields)))
       (otjs-cap-fields (cdr fields))
     (true-list-fix fields))))

(local
 (defthm otjs-cap-fields-length
   (equal (len (otjs-cap-fields fields)) (min 8 (len fields)))))

(local
 (defthm otjs-cap-fields-cons
   (equal (otjs-cap-fields (cons acc fields))
          (if (< (len fields) 8)
              (cons acc (true-list-fix fields))
            (otjs-cap-fields fields)))
   :hints (("Goal" :expand ((otjs-cap-fields (cons acc fields)))))))

(local
 (defthm otjs-revonto-append
   (equal (fn-otm-revonto fields (append a b))
          (append (fn-otm-revonto fields a) b))))

(local
 (defthm otjs-revonto-length
   (equal (len (fn-otm-revonto fields tail))
          (+ (len fields) (len tail)))))

(local
 (defthm otjs-revonto-is-append
   (equal (fn-otm-revonto fields tail)
          (append (fn-otm-revonto fields nil) tail))
   :rule-classes nil
   :hints (("Goal" :use ((:instance otjs-revonto-append (a nil) (b tail)))
            :in-theory (disable fn-otm-revonto otjs-revonto-append)))))

(local
 (defthm otjs-revonto-true-list
   (implies (true-listp tail)
            (true-listp (fn-otm-revonto fields tail)))))

(local
 (defthm otjs-revonto-singleton
   (equal (fn-otm-revonto fields (list acc))
          (append (fn-otm-revonto fields nil) (list acc)))
   :hints (("Goal" :use ((:instance otjs-revonto-is-append (tail (list acc))))
            :in-theory (disable fn-otm-revonto)))))

(local
 (defthm otjs-revonto-cons-prefix
   (implies (<= 8 (len fields))
            (equal (take 8 (fn-otm-revonto (cons n fields) tail))
                   (take 8 (fn-otm-revonto fields tail))))
   :hints (("Goal" :expand ((fn-otm-revonto (cons n fields) tail))
            :use ((:instance otjs-revonto-is-append (tail (cons n tail)))
                  (:instance otjs-revonto-is-append))
            :in-theory (disable fn-otm-revonto)))))

(local
 (defthm otjs-capped-entry
   (implies (true-listp fields)
            (equal (fn-otm-revonto (otjs-cap-fields fields)
                     (list (if (< (len fields) 8) acc 0)))
                   (fn-otjs-cap-entry
                     (fn-otm-revonto fields (list acc)))))
   :hints (("Goal" :induct (otjs-cap-fields fields)
            :in-theory (enable fn-otjs-cap-entry)))))

(local
 (defun otjs-prefix-state (acc fields entries)
   (mv-let (verdict prior) (fn-otm-replay (fn-otm-init)
                              (fn-otm-revonto entries nil))
     (list :whole (if (< (len fields) 8) acc (if acc 0 nil))
           (otjs-cap-fields fields) (len entries)
           (fn-otm-journal-starts entries) verdict prior))))

(local
 (defun otjs-observable (st)
   (list (fn-otjs-status st) (fn-otjs-field 3 st) (fn-otjs-field 4 st)
         (fn-otjs-field 5 st) (fn-otjs-field 6 st))))

(local
 (defun otjs-reference (xs acc fields entries)
   (mv-let (status complete) (fn-otm-jparse xs acc fields entries)
     (mv-let (verdict prior) (fn-otm-replay (fn-otm-init) complete)
       (list status (len complete) (fn-otm-journal-starts complete)
             verdict prior)))))

(local
 (defthm otjs-starts-revonto
   (equal (fn-otm-journal-starts (fn-otm-revonto entries tail))
          (+ (fn-otm-journal-starts entries)
             (fn-otm-journal-starts tail)))
   :hints (("Goal" :induct (fn-otm-revonto entries tail)
            :in-theory (enable fn-otm-journal-starts)))))

(local
 (defthm otjs-revonto-cons
   (equal (fn-otm-revonto (cons entry entries) nil)
          (append (fn-otm-revonto entries nil) (list entry)))
   :hints (("Goal" :expand ((fn-otm-revonto (cons entry entries) nil))))))

(local
 (defthm otjs-cap-fields-true-list
   (true-listp (otjs-cap-fields fields))))

(local
 (defthm otjs-starts-cons
   (equal (fn-otm-journal-starts (cons entry entries))
          (+ (if (and (consp entry) (consp (cdr entry))
                      (equal (cadr entry) 0)) 1 0)
             (fn-otm-journal-starts entries)))
   :hints (("Goal" :expand ((fn-otm-journal-starts (cons entry entries)))))))

(local
 (defthm otjs-starts-natural
   (natp (fn-otm-journal-starts entries))
   :rule-classes :type-prescription))

(local
 (defthm otjs-cap-fields-short
   (implies (<= (len fields) 8)
            (equal (otjs-cap-fields fields) (true-list-fix fields)))
   :hints (("Goal" :expand ((otjs-cap-fields fields))))))

(local
 (defthm otjs-capped-entry-long
   (implies (and (true-listp fields) (<= 8 (len fields)))
            (equal (fn-otm-revonto (otjs-cap-fields fields) '(0))
                   (fn-otjs-cap-entry (fn-otm-revonto fields (list acc)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance otjs-capped-entry))
            :in-theory (disable fn-otm-revonto otjs-cap-fields
                                fn-otjs-cap-entry otjs-revonto-singleton)))))

(local
 (defthm otjs-cap-entry-operation
   (and (equal (consp (fn-otjs-cap-entry entry)) (consp entry))
        (equal (consp (cdr (fn-otjs-cap-entry entry))) (consp (cdr entry)))
        (equal (cadr (fn-otjs-cap-entry entry)) (cadr entry)))
   :hints (("Goal" :in-theory (enable fn-otjs-cap-entry)))))

(local
 (defthm otjs-prefix-entry
   (implies (true-listp fields)
            (equal (fn-otjs-entry (otjs-prefix-state acc fields entries)
                       (if (< (len fields) 8) acc 0))
                   (otjs-prefix-state nil nil
                     (cons (fn-otm-revonto fields (list acc)) entries))))
   :hints (("Goal" :do-not-induct t :in-theory
            (e/d (otjs-prefix-state fn-otjs-entry fn-otjs-fields
                  fn-otjs-field)
                 (fn-otm-replay fn-otm-init fn-otjs-cap-entry
                  fn-otm-revonto otjs-cap-fields fn-otm-journal-starts
                  otjs-revonto-singleton otjs-capped-entry))
            :expand ((fn-otm-journal-starts
                        (cons (fn-otm-revonto fields (list acc)) entries)))
            :use ((:instance otjs-capped-entry-long))))))

(local
 (defthm otjs-cap-fields-empty
   (equal (consp (otjs-cap-fields fields)) (consp fields))))

(local
 (defthm otjs-malformed-consume
   (implies (and (true-listp st) (eq (fn-otjs-field 0 st) :malformed))
            (equal (fn-otjs-consume xs st) st))
   :hints (("Goal" :induct (fn-otjs-consume xs st)
            :in-theory (enable fn-otjs-octet fn-otjs-field)))))

(local
 (defthm otjs-prefix-digit
   (implies (and (true-listp fields) (natp o) (<= 48 o) (<= o 57))
            (equal (fn-otjs-octet o (otjs-prefix-state acc fields entries))
                   (otjs-prefix-state (+ (* 10 (nfix acc)) (- o 48))
                                      fields entries)))
   :hints (("Goal" :do-not-induct t :in-theory
            (e/d (fn-otjs-octet fn-otjs-field fn-otjs-fields otjs-prefix-state)
                 (fn-otm-replay fn-otm-init otjs-cap-fields))))))

(local
 (defthm otjs-prefix-space
   (implies (and (true-listp fields) acc)
            (equal (fn-otjs-octet 32 (otjs-prefix-state acc fields entries))
                   (otjs-prefix-state nil (cons acc fields) entries)))
   :hints (("Goal" :do-not-induct t :in-theory
            (e/d (fn-otjs-octet fn-otjs-field fn-otjs-fields otjs-prefix-state)
                 (fn-otm-replay fn-otm-init otjs-cap-fields))))))

(local
 (defthm otjs-prefix-line
   (implies (and (true-listp fields) acc)
            (equal (fn-otjs-octet 10 (otjs-prefix-state acc fields entries))
                   (otjs-prefix-state nil nil
                     (cons (fn-otm-revonto fields (list acc)) entries))))
   :hints (("Goal" :do-not-induct t :in-theory
            (e/d (fn-otjs-octet fn-otjs-field fn-otjs-fields)
                 (fn-otm-replay fn-otm-init fn-otjs-entry otjs-cap-fields
                  otjs-prefix-state otjs-prefix-entry))
            :expand ((otjs-prefix-state acc fields entries))
            :use ((:instance otjs-prefix-entry))))))

(local
 (defthm otjs-reference-step
   (equal (otjs-reference (cons o xs) acc fields entries)
          (cond ((and (natp o) (<= 48 o) (<= o 57))
                 (otjs-reference xs (+ (* 10 (nfix acc)) (- o 48)) fields entries))
                ((and (equal o 32) acc)
                 (otjs-reference xs nil (cons acc fields) entries))
                ((and (equal o 10) acc)
                 (otjs-reference xs nil nil
                   (cons (fn-otm-revonto fields (list acc)) entries)))
                (t (update-nth 0 :malformed
                     (otjs-reference nil nil nil entries)))))
   :hints (("Goal" :in-theory (e/d (otjs-reference)
                                  (fn-otm-jparse fn-otm-replay fn-otm-revonto))
            :expand ((fn-otm-jparse (cons o xs) acc fields entries)
                     (fn-otm-jparse nil nil nil entries))))))

(local
 (defthm otjs-cap-fields-present
   (iff (otjs-cap-fields fields) (consp fields))
   :hints (("Goal" :use ((:instance otjs-cap-fields-empty)
                         (:instance otjs-cap-fields-true-list))
            :in-theory (disable otjs-cap-fields otjs-cap-fields-empty
                                otjs-cap-fields-true-list)))))

(local
 (defthm otjs-prefix-observable
   (implies (true-listp fields)
            (equal (otjs-observable (otjs-prefix-state acc fields entries))
                   (otjs-reference nil acc fields entries)))
   :hints (("Goal" :in-theory
            (e/d (otjs-observable otjs-prefix-state otjs-reference
                  fn-otjs-status fn-otjs-field)
                 (fn-otm-jparse fn-otm-replay fn-otm-revonto otjs-cap-fields
                  fn-otm-journal-starts))
            :expand ((fn-otm-jparse nil acc fields entries))))))

(local
 (defthm otjs-reference-consp
   (implies (consp xs)
            (equal (otjs-reference xs acc fields entries)
                   (let ((o (car xs)) (rest (cdr xs)))
                     (cond ((and (natp o) (<= 48 o) (<= o 57))
                            (otjs-reference rest (+ (* 10 (nfix acc)) (- o 48)) fields entries))
                           ((and (equal o 32) acc)
                            (otjs-reference rest nil (cons acc fields) entries))
                           ((and (equal o 10) acc)
                            (otjs-reference rest nil nil
                              (cons (fn-otm-revonto fields (list acc)) entries)))
                           (t (update-nth 0 :malformed
                                (otjs-reference nil nil nil entries)))))))
   :hints (("Goal" :use ((:instance otjs-reference-step (o (car xs)) (xs (cdr xs))))
            :in-theory (disable otjs-reference otjs-reference-step)))))

(local
 (defthm otjs-prefix-malformed
   (implies (and (true-listp fields)
                 (not (and (natp o) (<= 48 o) (<= o 57)))
                 (not (and (equal o 32) acc))
                 (not (and (equal o 10) acc)))
            (equal (fn-otjs-octet o (otjs-prefix-state acc fields entries))
                   (update-nth 0 :malformed (otjs-prefix-state acc fields entries))))
   :hints (("Goal" :in-theory
            (e/d (fn-otjs-octet fn-otjs-field fn-otjs-fields otjs-prefix-state)
                 (fn-otm-replay fn-otm-init otjs-cap-fields))))))

(local
 (defthm otjs-prefix-state-true-list
   (true-listp (otjs-prefix-state acc fields entries))))

(local
 (defthm otjs-observable-malformed
   (equal (otjs-observable (update-nth 0 :malformed st))
          (update-nth 0 :malformed (otjs-observable st)))
   :hints (("Goal" :in-theory (enable otjs-observable fn-otjs-status
                                      fn-otjs-field nth update-nth true-list-fix)))))

(local
 (defthm otjs-reference-atom
   (implies (not (consp xs))
            (equal (otjs-reference xs acc fields entries)
                   (otjs-reference nil acc fields entries)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (otjs-reference)
                                  (fn-otm-jparse fn-otm-replay fn-otm-revonto))
            :expand ((fn-otm-jparse xs acc fields entries)
                     (fn-otm-jparse nil acc fields entries))))))

(local
 (defthm otjs-reference-leaf
   (implies (not (consp xs))
            (equal (otjs-reference xs acc fields entries)
                   (mv-let (verdict prior)
                     (fn-otm-replay (fn-otm-init) (fn-otm-revonto entries nil))
                     (list (if (or acc fields) :torn :whole) (len entries)
                           (fn-otm-journal-starts entries) verdict prior))))
   :hints (("Goal" :in-theory
            (e/d (otjs-reference)
                 (fn-otm-jparse fn-otm-replay fn-otm-revonto
                  fn-otm-journal-starts))
            :expand ((fn-otm-jparse xs acc fields entries))))))

(local
 (defthm otjs-prefix-malformed-consume
   (equal (fn-otjs-consume xs
             (update-nth 0 :malformed (otjs-prefix-state acc fields entries)))
          (update-nth 0 :malformed (otjs-prefix-state acc fields entries)))
   :hints (("Goal" :use ((:instance otjs-malformed-consume
                         (st (update-nth 0 :malformed
                               (otjs-prefix-state acc fields entries)))))
            :in-theory (e/d (otjs-prefix-state fn-otjs-field)
                            (fn-otjs-consume otjs-malformed-consume
                             fn-otm-replay fn-otm-init otjs-cap-fields))))))

(local
 (defthm otjs-consume-consp
   (implies (consp xs)
            (equal (fn-otjs-consume xs st)
                   (fn-otjs-consume (cdr xs) (fn-otjs-octet (car xs) st))))
   :hints (("Goal" :expand ((fn-otjs-consume xs st))
            :in-theory (disable fn-otjs-consume fn-otjs-octet)))))

(local
 (defthm otjs-consume-atom
   (implies (not (consp xs)) (equal (fn-otjs-consume xs st) st))))

(local
 (defthm otjs-prefix-malformed-observable
   (equal (otjs-observable
            (update-nth 0 :malformed (otjs-prefix-state acc fields entries)))
          (update-nth 0 :malformed (otjs-reference nil nil nil entries)))
   :hints (("Goal" :in-theory
            (e/d (otjs-observable otjs-prefix-state fn-otjs-status fn-otjs-field)
                 (fn-otm-replay fn-otm-init fn-otm-revonto
                  fn-otm-journal-starts otjs-cap-fields))))))

(local
 (defthm otjs-prefix-refines-parser
   (implies (true-listp fields)
            (equal (otjs-observable
                     (fn-otjs-consume xs (otjs-prefix-state acc fields entries)))
                   (otjs-reference xs acc fields entries)))
   :hints (("Goal" :induct (fn-otm-jparse xs acc fields entries)
            :in-theory
            (e/d ((:induction fn-otm-jparse))
                 ((:definition fn-otm-jparse) fn-otjs-consume fn-otjs-octet otjs-reference otjs-observable
                  otjs-prefix-state fn-otjs-status fn-otjs-field fn-otjs-fields
                  fn-otm-replay fn-otm-init fn-otm-revonto
                  fn-otm-journal-starts fn-otjs-entry otjs-cap-fields
                  otjs-revonto-singleton otjs-capped-entry update-nth
                  update-nth-when-zp update-nth-of-cons))))))

; The operator's actual incremental subjects render the reference parser's
; entire report and exit verdict for arbitrary input, not just generated runs.
(defthm fn-otjs-report-refines-journal-report
  (equal (fn-otjs-report (fn-otjs-consume xs (fn-otjs-init)))
         (fn-otm-journal-report xs))
  :hints (("Goal" :use ((:instance otjs-prefix-refines-parser
                         (acc nil) (fields nil) (entries nil)))
           :in-theory
           (e/d (fn-otjs-report fn-otjs-init fn-otm-journal-report
                 fn-otm-journal-read otjs-observable otjs-reference
                 otjs-prefix-state)
                (fn-otjs-consume fn-otjs-status fn-otjs-field
                 fn-otm-jparse fn-otm-replay fn-otm-init
                 fn-osch-text fn-osch-kv fn-otm-verdict-text)))))

(defthm fn-otjs-exit-refines-journal-exit
  (equal (fn-otjs-exit (fn-otjs-consume xs (fn-otjs-init)))
         (fn-otm-journal-exit xs))
  :hints (("Goal" :use ((:instance otjs-prefix-refines-parser
                         (acc nil) (fields nil) (entries nil)))
           :in-theory
           (e/d (fn-otjs-exit fn-otjs-init fn-otm-journal-exit
                 fn-otm-journal-read otjs-observable otjs-reference
                 otjs-prefix-state)
                (fn-otjs-consume fn-otjs-status fn-otjs-field
                 fn-otm-jparse fn-otm-replay fn-otm-init)))))
