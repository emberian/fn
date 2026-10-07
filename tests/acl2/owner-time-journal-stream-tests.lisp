(in-package "ACL2")
(include-book "../../books/owner-time-journal-stream")
(include-book "../../books/defkeystone")

(defun otjs-test-splits (n xs)
  (declare (xargs :measure (nfix n)))
  (let* ((whole (fn-otjs-consume xs (fn-otjs-init)))
         (split (fn-otjs-consume (nthcdr (nfix n) xs)
                   (fn-otjs-consume (take (nfix n) xs) (fn-otjs-init)))))
    (and (equal split whole)
         (or (zp n) (otjs-test-splits (- n 1) xs)))))

(defun otjs-test-cases (cases)
  (if (consp cases)
      (let* ((xs (car cases))
             (st (fn-otjs-consume xs (fn-otjs-init))))
        (and (equal (fn-otjs-report st) (fn-otm-journal-report xs))
             (equal (fn-otjs-exit st) (fn-otm-journal-exit xs))
             (<= (len (fn-otjs-fields st)) 8)
             (otjs-test-splits (len xs) xs)
             (otjs-test-cases (cdr cases))))
    t))

(assert-event
 (let* ((start (fn-otm-start-line 1700000000 t))
        (note (fn-otm-jline '(1 5 0 1 2 0 0)))
        (gap (fn-otm-jline '(3 5 0 1 2 0 0)))
        (unknown (fn-otm-jline '(1 99 0 0 0 0 0)))
        (long (fn-otm-jline '(8 0 2 3 4 5 6 7 8 9 10 11 12)))
        (huge (fn-otm-start-line (expt 10 100) t)))
   (otjs-test-cases
    (list nil start (append start note) (append start note start note)
          (append start gap note) (append start unknown note)
          (append start long note) huge
          '(10) '(48 32 32 49 10) '(48 32 49) '(48 32)
          (append start '(255) note)
          (append start (butlast note 1))
          (fn-otm-jline (make-list 500 :initial-element 0))))))

; Literal chunk-associativity witness (unconditional keystone).
(assert-event
 (let ((a '(48 32 48 32 48)) (b '(32 48 32 48 32 48 32 48 10))
       (st (fn-otjs-init)))
   (equal (fn-otjs-consume (append a b) st)
          (fn-otjs-consume b (fn-otjs-consume a st)))))
; Literal bounded-fields keystone premise and conclusion.
(assert-event
 (let ((st (fn-otjs-init)) (xs (fn-otm-jline (make-list 500 :initial-element 0))))
   (and (<= (len (fn-otjs-fields st)) 8)
        (<= (len (fn-otjs-fields (fn-otjs-consume xs st))) 8))))
; Corrupted state, field-bound premise removed: no retained hypotheses;
; both the omitted premise and conclusion affirmatively fail.
(assert-event
 (let ((st '(:whole nil (0 1 2 3 4 5 6 7 8) 0 0 :agrees nil)))
   (and (not (<= (len (fn-otjs-fields st)) 8))
        (not (<= (len (fn-otjs-fields (fn-otjs-consume '(48) st))) 8)))))
(assert-event
 (and (eq (symbol-class 'fn-otjs-init (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-otjs-consume (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-otjs-read-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-otjs-report (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-otjs-exit (w state)) :common-lisp-compliant)))

; Literal unconditional report keystone: continue counting complete entries
; and segment markers after the first replay gap, including an overlong
; rejected segment. A later restart cannot erase the earlier verdict.
(assert-event
 (let* ((xs (append (fn-otm-start-line (expt 10 100) t)
                    (fn-otm-jline '(1 5 0 1 2 0 0))
                    (fn-otm-jline '(3 5 0 1 2 0 0))
                    (fn-otm-jline '(999 0 0 0 0 0 0 0 0 0 0))
                    (fn-otm-start-line 1700000000 t)
                    (fn-otm-jline '(1 5 0 1 2 0 0)) '(255)))
        (st (fn-otjs-consume xs (fn-otjs-init))))
   (and (equal (fn-otjs-report st) (fn-otm-journal-report xs))
        (equal (fn-otjs-report st)
               (fn-osch-text "journal: entries=6 segments=3 status=malformed replay=gap-at-2
")))))

; Literal unconditional exit keystone, with a torn suffix after the gap.
(assert-event
 (let* ((xs (append (fn-otm-start-line 1 t)
                    (fn-otm-jline '(2 5 0 1 2 0 0)) '(48 32)))
        (st (fn-otjs-consume xs (fn-otjs-init))))
   (and (equal (fn-otjs-exit st) (fn-otm-journal-exit xs))
        (equal (fn-otjs-exit st) 1)
        (equal (fn-otjs-status st) :torn))))

; ---------------------------------------------------------------------------
; PRF-1275 keystones of books/owner-time-journal-stream.lisp with their teeth
; (TEETH CONTRACT v1): a start line, a note, a line of an unknown kind (exit
; 1), a note without its terminator (six fields pending).
(defconst *otjs-start* (fn-otm-start-line 1700000000 t))
(defconst *otjs-note* (fn-otm-jline '(1 5 0 1 2 0 0)))
(defconst *otjs-unknown-journal* (append *otjs-start* (fn-otm-jline '(1 99 0 0 0 0 0))))
(defconst *otjs-partial* (butlast *otjs-note* 1))
; A stream state no consume builds: nine fields pending.
(defconst *otjs-nine-fields* (update-nth 2 '(1 2 3 4 5 6 7 8 9) (fn-otjs-init)))

(defteeth fn-otjs-consume-of-append
  :claim (() (equal (fn-otjs-consume (append a b) st)
                    (fn-otjs-consume b (fn-otjs-consume a st))))
  :subject fn-otjs-consume
  :witness ((a *otjs-start*) (b *otjs-note*) (st (fn-otjs-init)))
  :mutations ((halves-swapped
               (:conclusion (equal (fn-otjs-consume (append a b) st)
                                   (fn-otjs-consume a (fn-otjs-consume b st))))
               ((a *otjs-start*) (b *otjs-note*) (st (fn-otjs-init)))
               :fault "a chunked read that consumes its chunks out of order")))

(defteeth fn-otjs-consume-fields-bounded
  :claim (((bounded (<= (len (fn-otjs-fields st)) 8)))
          (<= (len (fn-otjs-fields (fn-otjs-consume octets st))) 8))
  :subject fn-otjs-consume
  :witness ((octets *otjs-partial*) (st (fn-otjs-init)))
  :breaks ((bounded ((octets '(32)) (st *otjs-nine-fields*))))
  :mutations ((partial-line-fieldless
               (:conclusion (<= (len (fn-otjs-fields (fn-otjs-consume octets st))) 0))
               ((octets *otjs-partial*) (st (fn-otjs-init)))
               :fault "a line's fields dropped before its terminator arrives")))

(defteeth fn-otjs-exit-refines-journal-exit
  :claim (() (equal (fn-otjs-exit (fn-otjs-consume xs (fn-otjs-init)))
                    (fn-otm-journal-exit xs)))
  :subject fn-otjs-exit
  :witness ((xs *otjs-unknown-journal*))
  :mutations ((last-line-unterminated
               (:conclusion (equal (fn-otjs-exit (fn-otjs-consume xs (fn-otjs-init)))
                                   (fn-otm-journal-exit (butlast xs 1))))
               ((xs *otjs-unknown-journal*))
               :fault "the last line judged before its terminator (an unknown kind passes)")))

(defteeth fn-otjs-report-refines-journal-report
  :claim (() (equal (fn-otjs-report (fn-otjs-consume xs (fn-otjs-init)))
                    (fn-otm-journal-report xs)))
  :subject fn-otjs-report
  :witness ((xs (append *otjs-start* *otjs-note*)))
  :mutations ((first-octet-dropped
               (:conclusion (equal (fn-otjs-report (fn-otjs-consume xs (fn-otjs-init)))
                                   (fn-otm-journal-report (cdr xs))))
               ((xs (append *otjs-start* *otjs-note*)))
               :fault "the stream starts one octet into the journal")))
