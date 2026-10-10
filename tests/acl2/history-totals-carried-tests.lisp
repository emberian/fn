; Witnesses for books/history-totals-carried.lisp (K-TOTALS; Builder M, memory
; landing 3+4, 2026-10-09).
;
; One small store: two HELD rows (wire records interned on a local arena) and
; a retention event, the history stobj loaded with them.  The carried totals
; (a cache over the first record, the other two read from the stobj) are the
; fold over all three; the cache is valid after a commit; the fold covers the
; store's totals when the log's lengths are within the charge.
(in-package "ACL2")
(include-book "../../books/history-totals-carried")
(include-book "../../books/records-attach")
(include-book "../../books/catalog-record")
(include-book "../../books/defkeystone")
(include-book "std/testing/assert-bang" :dir :system)

; A wire record from a number: payload length, group count and ids vary.
(defun htct-row (n)
  (declare (xargs :guard t :verify-guards nil))
  (let ((n (nfix n)))
    (fn-record-make (mod n 3) (mod n 5) (mod n 7)
                    (concatenate 'string "<htct-" (coerce (explode-nonnegative-integer n 10 nil) 'string) "@example.invalid>")
                    (make-list (mod n 11) :initial-element (+ 65 (mod n 26)))
                    (if (evenp n) '("fn.test") '("fn.test" "fn.other"))
                    "o0" "s0" "e0" 4 (+ 841000000 n))))

(defun htct-intern-all (ns fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom ns)
      (mv nil fn-arena)
    (mv-let (row fn-arena) (fn-cat-intern-list (htct-row (car ns)) nil 0 fn-arena)
      (mv-let (rest fn-arena) (htct-intern-all (cdr ns) fn-arena)
        (mv (cons row rest) fn-arena)))))

(defun htct-held-rows (ns)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (htct-intern-all ns fn-arena)
      rows)))

(defconst *htct-records*
  (append (htct-held-rows '(11 5))
          (list (fn-store-retention-event-make :undertake 2 2 2 "forward" "fwd-subject" "evidence" 4))))

; The store: only its file kernel's records matter to the statements.
(defconst *htct-s*
  (fn-sn-make nil 0 (fn-sf-make nil nil nil *htct-records* nil nil nil nil) nil nil nil))

(assert-event (and (fn-held-p (car *htct-records*)) (fn-held-p (cadr *htct-records*))
                   (not (fn-held-p (caddr *htct-records*)))
                   (equal (fn-sf-records (fn-sn-files *htct-s*)) *htct-records*)))

(defconst *htct-fold* (fn-ct-charged *htct-records* :resident))
(defconst *htct-cache* (cons 1 (fn-ct-charged (take 1 *htct-records*) :resident)))
; the fold is not vacuous: RECORDS, CHARGE, LOG and HISTORY are all positive
(assert-event (equal *htct-fold* '(3 5 100 4 40 3489 456 45 :resident)))

; ---------------------------------------------------------------------------
; KEYSTONE (1) fn-hist-totals-carried-is-totals-extend, on a live stobj
; holding the store's records (R by construction).

(defun htct-carried (cache records s residency)
  (declare (xargs :guard (true-listp records) :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load records 0 fn-hist)))
        (mv (fn-hist-totals-carried cache s residency fn-hist) fn-hist))
      ans)))

; satisfiable: a valid cache over the first record, the reader walks two rows
(assert-event (equal (htct-carried *htct-cache* *htct-records* *htct-s* :resident)
                     (fn-ct-totals-extend *htct-cache* *htct-records* :resident)))
(assert-event (equal (htct-carried *htct-cache* *htct-records* *htct-s* :resident) *htct-fold*))
; teeth: the cache is read, not ignored.  A cache that is not the fold over
; its prefix is carried forward as given, so the carried totals differ from
; the fold (the extend specification says exactly so).
(defconst *htct-wrong-cache* (cons 1 (cons 7 (cddr *htct-cache*))))
(assert-event (equal (htct-carried *htct-wrong-cache* *htct-records* *htct-s* :resident)
                     (fn-ct-totals-extend *htct-wrong-cache* *htct-records* :resident)))
(assert-event (not (equal (htct-carried *htct-wrong-cache* *htct-records* *htct-s* :resident)
                          *htct-fold*)))
; no cache, a malformed cache, and a cache past the history fall back to the fold
(assert-event (equal (htct-carried nil *htct-records* *htct-s* :resident) *htct-fold*))
(assert-event (equal (htct-carried (cons 1 'junk) *htct-records* *htct-s* :resident) *htct-fold*))
(assert-event (equal (htct-carried (cons 9 (fn-ct-zero-tot :resident)) *htct-records* *htct-s* :resident)
                     *htct-fold*))
; the residency is the caller's
(assert-event (equal (htct-carried nil *htct-records* *htct-s* :paged)
                     (fn-ct-charged *htct-records* :paged)))
; Removal of R: a stobj holding only the first two records, against the store's
; three: the reader walks what the stobj holds, so it is not the extend
; specification over the store.
(assert-event (not (equal (htct-carried *htct-cache* (take 2 *htct-records*) *htct-s* :resident)
                          (fn-ct-totals-extend *htct-cache* *htct-records* :resident))))

; ---------------------------------------------------------------------------
; KEYSTONE (2) fn-ct-totals-extend-of-a-valid-cache.
(defteeth fn-ct-totals-extend-of-a-valid-cache
  :claim (((valid (fn-ct-totals-cache-validp cache records residency)))
          (equal (fn-ct-totals-extend cache records residency)
                 (fn-ct-charged records residency)))
  :subject fn-ct-totals-extend
  :witness ((cache *htct-cache*) (records *htct-records*) (residency :resident))
  :breaks ((valid ((cache *htct-wrong-cache*) (records *htct-records*) (residency :resident))))
  :mutations ((extend-drops-the-cache
               (:conclusion (equal (fn-ct-totals-extend cache records residency)
                                   (fn-ct-charged (nthcdr (car cache) records) residency)))
               ((cache *htct-cache*) (records *htct-records*) (residency :resident))
               :fault "an extend that charges only the records past K and forgets the cached prefix")))

; Not a hypothesis of the keystone but the same cache: it stays valid after a
; commit, and the empty cache is valid.
(assert-event (fn-ct-totals-cache-validp *htct-cache* *htct-records* :resident))
(assert-event (fn-ct-totals-cache-validp *htct-cache*
                                         (append *htct-records* (list (htct-row 3))) :resident))
(assert-event (fn-ct-totals-cache-validp (cons 0 (fn-ct-zero-tot :resident)) *htct-records* :resident))
(assert-event (not (fn-ct-totals-cache-validp *htct-wrong-cache* *htct-records* :resident)))

; ---------------------------------------------------------------------------
; KEYSTONE (3) fn-ct-charged-covers-the-store: the log's lengths within the
; charged LOG.
(defconst *htct-log* (fn-ct-log-of-records *htct-records*))
(defteeth fn-ct-charged-covers-the-store
  :claim (((within (<= (fn-ct-sum-lengths lens) (fn-ct-log-of-records (fn-sf-records (fn-sn-files s))))))
          (fn-mm-tot-le (fn-ct-of-store s lens (fn-sf-records (fn-sn-files s)) residency)
                        (fn-ct-charged (fn-sf-records (fn-sn-files s)) residency)))
  :subject fn-ct-charged
  :witness ((s *htct-s*) (lens (list 3000 (- *htct-log* 3000))) (residency :resident))
  :breaks ((within ((s *htct-s*) (lens (list (1+ *htct-log*))) (residency :resident))))
  :mutations ((cover-as-equality
               (:conclusion (equal (fn-ct-of-store s lens (fn-sf-records (fn-sn-files s)) residency)
                                   (fn-ct-charged (fn-sf-records (fn-sn-files s)) residency)))
               ((s *htct-s*) (lens (list (1- *htct-log*))) (residency :resident))
               :fault "a cover stated as equality: the replayed log is within its charge, not equal to it")))

; fn-ct-charged-is-the-store-but-the-log: every field but LOG is the store's
(assert-event
 (let ((a (fn-ct-of-store *htct-s* (list *htct-log*) *htct-records* :resident)))
   (and (equal (take 5 *htct-fold*) (take 5 a))
        (equal (nth 6 *htct-fold*) (nth 6 a))
        (equal (nth 7 *htct-fold*) (nth 7 a))
        (equal (nth 5 *htct-fold*) *htct-log*))))
