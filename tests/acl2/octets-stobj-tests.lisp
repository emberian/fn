; fn: teeth for books/octets-stobj.lisp and books/poster-bytes-buffer.lisp.
;
; What this book is evidence FOR.  The abstraction theorems of the buffer
; (`fn-octets-get{correspondence}' and the others) say that every export's
; executable step on the array equals the list operation on the abstraction
; whenever the correspondence and the export's guard hold; the consumer
; keystone `fn-pbb-existing-action-is-pb-existing-action' says the
; existing-article test over the buffer is the list test on the buffer's
; logical value whenever the value is an octet list.  Each theorem gets a
; ground positive witness asserting its complete antecedent and conclusion,
; and for each hypothesis a witness on which every retained hypothesis
; holds, the omitted one fails, and the conclusion fails.  The exec path is
; also run on a live local buffer, the way the host runs it.

(in-package "ACL2")
(include-book "../../books/octets-stobj")
(include-book "../../books/poster-bytes-buffer")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-served-invariants-tests")

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it may reach is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-octets$c-len (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-octets$c-get (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-octets$c-put (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-octets$c-append-octet (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-octets$c-clear (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-octets$c-reserve (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-octets$c-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-octets$c-from-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-slice-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-prefix-equalp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-suffix-equalp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-line-end (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pbb-strip-at (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pbb-source-index (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pbb-line (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pbb-path-agent (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pbb-same-articlep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pbb-existing-action (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The executable path on a live local buffer: what the host's fill and reads
; run.  A sequence of exports, and the resize past the first 1024 cells.

(defun ost-exec-run (fn-octets)
  (declare (xargs :stobjs fn-octets))
  (let* ((fn-octets (fn-octets-from-list '(5 6 7) fn-octets))
         (a (list (fn-octets-len fn-octets) (fn-octets-get 1 fn-octets)
                  (fn-octets-list fn-octets)))
         (fn-octets (fn-octets-put 1 9 fn-octets))
         (fn-octets (fn-octets-append-octet 8 fn-octets))
         (b (list (fn-octets-len fn-octets) (fn-octets-get 1 fn-octets)
                  (fn-octets-get 3 fn-octets) (fn-octets-list fn-octets)))
         (fn-octets (fn-octets-clear fn-octets))
         (c (list (fn-octets-len fn-octets) (fn-octets-list fn-octets))))
    (mv (list a b c) fn-octets)))

(defun ost-exec-run-value ()
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (ost-exec-run fn-octets) v)))

(assert-event
 (equal (ost-exec-run-value)
        '((3 6 (5 6 7))
          (4 9 8 (5 9 7 8))
          (0 nil))))

(defun ost-ramp (n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n) acc (ost-ramp (1- n) (cons (mod n 256) acc))))

; Cell k holds (mod (1+ k) 256): 1, 2, ..., 255, 0, 1, ...
(defconst *ost-big* (ost-ramp 3000 nil))
(assert-event (and (fn-cbor-octet-listp *ost-big*) (equal (len *ost-big*) 3000)))

(defun ost-exec-big (fn-octets)
  (declare (xargs :stobjs fn-octets))
  (let* ((fn-octets (fn-octets-reserve 10 fn-octets))
         (fn-octets (fn-octets-from-list *ost-big* fn-octets))
         (r (list (fn-octets-len fn-octets) (fn-octets-get 2999 fn-octets)
                  (equal (fn-octets-list fn-octets) *ost-big*)
                  (fn-oct-slice-list 10 14 fn-octets)
                  (fn-oct-prefix-equalp 0 '(1 2 3) fn-octets)
                  (fn-oct-prefix-equalp 1 '(1 2 3) fn-octets)
                  (fn-oct-suffix-equalp 2997 '(182 183 184) fn-octets)
                  (fn-oct-suffix-equalp 2997 '(182 183) fn-octets)
                  (fn-oct-line-end 0 fn-octets))))
    (mv r fn-octets)))

(defun ost-exec-big-value ()
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (ost-exec-big fn-octets) v)))

(assert-event
 (equal (ost-exec-big-value)
        (list 3000 (mod 3000 256) t '(11 12 13 14) t nil t nil 10)))

; -----------------------------------------------------------------------------
; The abstraction obligations on ground values.  A concrete object is the
; list (array fill); the abstraction is the array's first FILL cells.  A
; concrete-side function takes the stobj variable at the top level, so
; each ground witness is a theorem (ost-w-*), proved by evaluation.

(defconst *ost-c* '((5 6 7 0) 3))
(defconst *ost-a* '(5 6 7))
(defthm ost-w-1 ; a ground witness, proved by evaluation
 (fn-octets$corr *ost-c* *ost-a*)
 :rule-classes nil)

; fn-octets-get{correspondence}: (corr c a), (natp i), (< i (len a)).
(defthm ost-w-2 ; a ground witness, proved by evaluation
 (and (natp 1) (< 1 (fn-octets$a-len *ost-a*))
      (equal (fn-octets$c-get 1 *ost-c*) 6)
      (equal (fn-octets$c-get 1 *ost-c*) (fn-octets$a-get 1 *ost-a*)))
 :rule-classes nil)
; Without the correspondence (the fill count beyond the array): the cell
; past the array is nil, the abstraction's is 0.
(defconst *ost-c-over* '((5 6 7 0) 5))
(defconst *ost-a-over* '(5 6 7 0 0))
(defthm ost-w-3 ; a ground witness, proved by evaluation
 (and (not (fn-octets$corr *ost-c-over* *ost-a-over*))
      (natp 4) (< 4 (fn-octets$a-len *ost-a-over*))
      (not (equal (fn-octets$c-get 4 *ost-c-over*) (fn-octets$a-get 4 *ost-a-over*))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-get-without-corr
   (implies (and (natp 4) (< 4 (fn-octets$a-len *ost-a-over*)))
            (equal (fn-octets$c-get 4 *ost-c-over*) (fn-octets$a-get 4 *ost-a-over*)))))
; Without (natp i): an index below zero reads the array's first cell, which
; an empty abstraction does not have.
(defconst *ost-c-empty* '((5 6 7 0) 0))
(defthm ost-w-4 ; a ground witness, proved by evaluation
 (and (fn-octets$corr *ost-c-empty* nil) (< -1 (fn-octets$a-len nil)) (not (natp -1))
      (not (equal (fn-octets$c-get -1 *ost-c-empty*) (fn-octets$a-get -1 nil))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-get-without-natp
   (implies (and (fn-octets$corr *ost-c-empty* nil) (< -1 (fn-octets$a-len nil)))
            (equal (fn-octets$c-get -1 *ost-c-empty*) (fn-octets$a-get -1 nil)))))
; Without (< i (len a)): the cell at the fill count is the array's spare 0.
(defthm ost-w-5 ; a ground witness, proved by evaluation
 (and (fn-octets$corr *ost-c* *ost-a*) (natp 3) (not (< 3 (fn-octets$a-len *ost-a*)))
      (not (equal (fn-octets$c-get 3 *ost-c*) (fn-octets$a-get 3 *ost-a*))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-get-without-bound
   (implies (and (fn-octets$corr *ost-c* *ost-a*) (natp 3))
            (equal (fn-octets$c-get 3 *ost-c*) (fn-octets$a-get 3 *ost-a*)))))

; fn-octets-put{correspondence}: (corr c a), (natp i), (< i (len a)), (octetp o).
(defthm ost-w-6 ; a ground witness, proved by evaluation
 (and (natp 1) (< 1 (fn-octets$a-len *ost-a*)) (fn-cbor-octetp 9)
      (equal (fn-octets$c-put 1 9 *ost-c*) '((5 9 7 0) 3))
      (fn-octets$corr (fn-octets$c-put 1 9 *ost-c*) (fn-octets$a-put 1 9 *ost-a*)))
 :rule-classes nil)
(defthm ost-w-7 ; a ground witness, proved by evaluation
 ; without corr: the fill count stays beyond the array
 (and (not (fn-octets$corr *ost-c-over* *ost-a-over*))
      (natp 3) (< 3 (fn-octets$a-len *ost-a-over*)) (fn-cbor-octetp 9)
      (not (fn-octets$corr (fn-octets$c-put 3 9 *ost-c-over*)
                           (fn-octets$a-put 3 9 *ost-a-over*))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-put-without-corr
   (implies (and (natp 3) (< 3 (fn-octets$a-len *ost-a-over*)) (fn-cbor-octetp 9))
            (fn-octets$corr (fn-octets$c-put 3 9 *ost-c-over*)
                            (fn-octets$a-put 3 9 *ost-a-over*)))))
(defthm ost-w-8 ; a ground witness, proved by evaluation
 ; without natp: the abstraction grows a cell, the array does not
 (and (fn-octets$corr *ost-c-empty* nil) (not (natp -1)) (< -1 (fn-octets$a-len nil))
      (fn-cbor-octetp 9)
      (not (fn-octets$corr (fn-octets$c-put -1 9 *ost-c-empty*) (fn-octets$a-put -1 9 nil))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-put-without-natp
   (implies (and (fn-octets$corr *ost-c-empty* nil) (< -1 (fn-octets$a-len nil))
                 (fn-cbor-octetp 9))
            (fn-octets$corr (fn-octets$c-put -1 9 *ost-c-empty*) (fn-octets$a-put -1 9 nil)))))
(defthm ost-w-9 ; a ground witness, proved by evaluation
 ; without the bound: the write lands past the fill count
 (and (fn-octets$corr *ost-c* *ost-a*) (natp 3) (not (< 3 (fn-octets$a-len *ost-a*)))
      (fn-cbor-octetp 9)
      (not (fn-octets$corr (fn-octets$c-put 3 9 *ost-c*) (fn-octets$a-put 3 9 *ost-a*))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-put-without-bound
   (implies (and (fn-octets$corr *ost-c* *ost-a*) (natp 3) (fn-cbor-octetp 9))
            (fn-octets$corr (fn-octets$c-put 3 9 *ost-c*) (fn-octets$a-put 3 9 *ost-a*)))))
(defthm ost-w-10 ; a ground witness, proved by evaluation
 ; without the octet: the array is no longer well formed
 (and (fn-octets$corr *ost-c* *ost-a*) (natp 1) (< 1 (fn-octets$a-len *ost-a*))
      (not (fn-cbor-octetp 300))
      (not (fn-octets$corr (fn-octets$c-put 1 300 *ost-c*) (fn-octets$a-put 1 300 *ost-a*))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-put-without-octet
   (implies (and (fn-octets$corr *ost-c* *ost-a*) (natp 1) (< 1 (fn-octets$a-len *ost-a*)))
            (fn-octets$corr (fn-octets$c-put 1 300 *ost-c*) (fn-octets$a-put 1 300 *ost-a*)))))

; fn-octets-append-octet{correspondence}: (corr c a), (octetp o).  The
; array is full at three of four cells; a second append resizes it.
(defthm ost-w-11 ; a ground witness, proved by evaluation
 (and (fn-cbor-octetp 8)
      (equal (fn-octets$c-append-octet 8 *ost-c*) '((5 6 7 8) 4))
      (fn-octets$corr (fn-octets$c-append-octet 8 *ost-c*)
                      (fn-octets$a-append-octet 8 *ost-a*))
      (let ((c2 (fn-octets$c-append-octet 9 (fn-octets$c-append-octet 8 *ost-c*))))
        (and (equal (fn-octets$c-fill c2) 5)
             (equal (fn-octets$c-buf-length c2) 1024)
             (fn-octets$corr c2 (fn-octets$a-append-octet
                                 9 (fn-octets$a-append-octet 8 *ost-a*))))))
 :rule-classes nil)
(defconst *ost-a-other* '(1 2 3))
(defthm ost-w-12 ; a ground witness, proved by evaluation
 ; without corr (an abstraction that is not the array's)
 (and (not (fn-octets$corr *ost-c* *ost-a-other*)) (fn-cbor-octetp 8)
      (not (fn-octets$corr (fn-octets$c-append-octet 8 *ost-c*)
                           (fn-octets$a-append-octet 8 *ost-a-other*))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-append-without-corr
   (implies (fn-cbor-octetp 8)
            (fn-octets$corr (fn-octets$c-append-octet 8 *ost-c*)
                            (fn-octets$a-append-octet 8 *ost-a-other*)))))
(defthm ost-w-13 ; a ground witness, proved by evaluation
 ; without the octet
 (and (fn-octets$corr *ost-c* *ost-a*) (not (fn-cbor-octetp 300))
      (not (fn-octets$corr (fn-octets$c-append-octet 300 *ost-c*)
                           (fn-octets$a-append-octet 300 *ost-a*))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-append-without-octet
   (implies (fn-octets$corr *ost-c* *ost-a*)
            (fn-octets$corr (fn-octets$c-append-octet 300 *ost-c*)
                            (fn-octets$a-append-octet 300 *ost-a*)))))

; fn-octets-list{correspondence}: (corr c a).
(defthm ost-w-14 ; a ground witness, proved by evaluation
 (equal (fn-octets$c-list *ost-c*) (fn-octets$a-list *ost-a*))
 :rule-classes nil)
(defthm ost-w-15 ; a ground witness, proved by evaluation
 (and (not (fn-octets$corr *ost-c-over* *ost-a-over*))
      (not (equal (fn-octets$c-list *ost-c-over*) (fn-octets$a-list *ost-a-over*))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-list-without-corr
   (equal (fn-octets$c-list *ost-c-over*) (fn-octets$a-list *ost-a-over*))))

; fn-octets-from-list{correspondence}: (corr c a), (octet-listp xs).
(defthm ost-w-16 ; a ground witness, proved by evaluation
 (and (fn-cbor-octet-listp '(1 2))
      (fn-octets$corr (fn-octets$c-from-list '(1 2) *ost-c*)
                      (fn-octets$a-from-list '(1 2) *ost-a*)))
 :rule-classes nil)
; The correspondence hypothesis carries nothing beyond the concrete
; recognizer here: writing a list resets the buffer, so the result
; corresponds to the list whatever abstraction the input had.  The
; weakened theorem, proved.  The recognizer's own necessity is not
; evaluable: an object that is not a concrete buffer is refused by the
; stobj primitives before a step runs, which is what the recognizer is for.
(defthm ost-w-from-list-needs-only-the-recognizer
  (implies (and (fn-octets$cp c) (fn-cbor-octet-listp xs))
           (fn-octets$corr (fn-octets$c-from-list xs c)
                           (fn-octets$a-from-list xs a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-octets$c-from-list fn-octets$c-clear
                                   fn-octets$corr)
                                  (fn-octets$cp fn-oct-write-list nth update-nth))
           :use ((:instance fn-oct-write-list-steps
                            (fn-octets$c (update-nth 1 0 c)))))))
(defthm ost-w-17 ; a ground witness, proved by evaluation
 (and (fn-octets$corr *ost-c* *ost-a*) (not (fn-cbor-octet-listp '(1 300)))
      (not (fn-octets$corr (fn-octets$c-from-list '(1 300) *ost-c*)
                           (fn-octets$a-from-list '(1 300) *ost-a*))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-from-list-without-octets
   (implies (fn-octets$corr *ost-c* *ost-a*)
            (fn-octets$corr (fn-octets$c-from-list '(1 300) *ost-c*)
                            (fn-octets$a-from-list '(1 300) *ost-a*)))))

; -----------------------------------------------------------------------------
; The derived readers' correspondences on ground values, with the
; true-list hypothesis: an improper buffer value is read to its length.
; A reader takes the stobj variable at the top level, so each witness is
; a theorem over the plain value (ost-r-*), proved by evaluation.

(defthm ost-r-1 ; a ground witness over a plain value, proved by evaluation
 (and (equal (fn-oct-suffix-equalp 1 '(2 3) '(1 2 3)) t)
      (equal (nthcdr 1 '(1 2 3)) '(2 3))
      (equal (fn-oct-suffix-equalp 0 '(1 2) '(1 2 . 3)) t)
      (not (equal (nthcdr 0 '(1 2 . 3)) '(1 2)))
      (not (true-listp '(1 2 . 3))))
 :rule-classes nil)
(must-fail
 (defthm ost-t-suffix-without-true-listp
   (implies (natp 0)
            (equal (fn-oct-suffix-equalp 0 '(1 2) '(1 2 . 3))
                   (equal (nthcdr 0 '(1 2 . 3)) '(1 2))))))
(defthm ost-r-2 ; a ground witness over a plain value, proved by evaluation
 ; without (natp i): the walk answers for an empty tail
 (and (equal (fn-oct-suffix-equalp -1 nil '(1)) t)
      (not (equal (nthcdr -1 '(1)) nil)))
 :rule-classes nil)
(must-fail
 (defthm ost-t-suffix-without-natp
   (implies (true-listp '(1))
            (equal (fn-oct-suffix-equalp -1 nil '(1)) (equal (nthcdr -1 '(1)) nil)))))
(defthm ost-r-3 ; a ground witness over a plain value, proved by evaluation
 (and (equal (fn-oct-prefix-equalp 1 '(2 3) '(1 2 3 4)) t)
      (equal (fn-oct-list-prefixp '(2 3) (nthcdr 1 '(1 2 3 4))) t)
      (equal (fn-oct-prefix-equalp 1 '(2 4) '(1 2 3 4)) nil)
      (equal (fn-oct-list-prefixp '(2 4) (nthcdr 1 '(1 2 3 4))) nil)
      (equal (fn-oct-prefix-equalp 2 '(3) '(1 2 3 . 4)) t)
      (equal (fn-oct-list-prefixp '(3) (nthcdr 2 '(1 2 3 . 4))) t)
      ; the improper tail: the buffer has no third cell, the list does
      (equal (fn-oct-prefix-equalp 2 '(3 4) '(1 2 3 . 4)) nil)
      (equal (fn-oct-list-prefixp '(3 4) (nthcdr 2 '(1 2 3 . 4))) nil))
 :rule-classes nil)
(defthm ost-r-4 ; a ground witness over a plain value, proved by evaluation
 (and (equal (fn-oct-slice-list 1 3 '(1 2 3 4)) '(2 3))
      (equal (take 2 (nthcdr 1 '(1 2 3 4))) '(2 3)))
 :rule-classes nil)

; -----------------------------------------------------------------------------
; The consumer keystone on the completing owner's store: the article
; connection 4 injected (owner-served-invariants-tests *osi-completing*,
; reached by fn-own-run), completed, so the acceptance state holds it.

(defconst *ost-owner* (cdr (fn-own-finish *osi-completing* *osi-cfg*)))
(defconst *ost-s* (fn-own-store *ost-owner*))
(defconst *ost-articles*
  (fn-state-articles (fn-node-acceptance (fn-sn-node *ost-s*))))
(assert-event (consp *ost-articles*))
(defconst *ost-art* (car *ost-articles*))
(defconst *ost-msgid* (fn-article-msgid *ost-art*))
(defconst *ost-held* (fn-article-payload *ost-art*))
(defconst *ost-groups* (fn-article-groups *ost-art*))
(assert-event (and (stringp *ost-msgid*) (fn-cbor-octet-listp *ost-held*)
                   (< 100 (len *ost-held*))))

; The held article was injected: it opens with a Path line by the agent
; and its source reads.
(defconst *ost-agent* (fn-pb-path-agent *ost-held*))
(assert-event (consp *ost-agent*))
(defconst *ost-source*
  (fn-inj-source-of *ost-held* *ost-agent* (fn-record-string-octets *ost-msgid*)))
(assert-event (and (consp *ost-source*) (equal (car *ost-source*) t)
                   (consp (cdr *ost-source*))))

; The same article re-injected at another instant: the same source under
; a different Injection-Date, so the octets differ and the sources agree.
(defconst *ost-r1* (fn-inj-strip (fn-inj-path-line *ost-agent*) *ost-held*))
(defconst *ost-date*
  (fn-inj-take 31 (fn-inj-drop (len *fn-inj-injection-date-field*) *ost-r1*)))
(assert-event (equal (len *ost-date*) 31))
(defconst *ost-date2*
  (update-nth 30 (if (equal (nth 30 *ost-date*) 48) 49 48) *ost-date*))
(defconst *ost-reinjected*
  (append (fn-inj-path-line *ost-agent*)
          (fn-inj-injection-date-line *ost-date2*)
          (fn-inj-injection-info-line *ost-agent*)
          (cdr *ost-source*)))
(assert-event (and (not (equal *ost-reinjected* *ost-held*))
                   (equal (fn-inj-source-of *ost-reinjected* *ost-agent*
                                            (fn-record-string-octets *ost-msgid*))
                          *ost-source*)))
; A different article under the same Message-ID: one body octet changed.
(defconst *ost-changed*
  (update-nth (1- (len *ost-held*))
              (if (equal (nth (1- (len *ost-held*)) *ost-held*) 10) 11 10)
              *ost-held*))

; The buffer twin, run the way the host runs it: the payload filled into a
; live local buffer, the test read by index.
(defun ost-existing-action (msgid payload groups s)
  (declare (xargs :guard (fn-cbor-octet-listp payload) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (let ((fn-octets (fn-octets-from-list payload fn-octets)))
        (mv (fn-pbb-existing-action msgid fn-octets groups s) fn-octets))
      r)))

(assert-event
 (and (equal (fn-pb-existing-action *ost-msgid* *ost-held* *ost-groups* *ost-s*) :duplicate)
      (equal (ost-existing-action *ost-msgid* *ost-held* *ost-groups* *ost-s*) :duplicate)
      ; the source path: other octets, the same source
      (equal (fn-pb-existing-action *ost-msgid* *ost-reinjected* *ost-groups* *ost-s*)
             :duplicate)
      (equal (ost-existing-action *ost-msgid* *ost-reinjected* *ost-groups* *ost-s*)
             :duplicate)
      ; a changed body is another article
      (equal (fn-pb-existing-action *ost-msgid* *ost-changed* *ost-groups* *ost-s*) :conflict)
      (equal (ost-existing-action *ost-msgid* *ost-changed* *ost-groups* *ost-s*) :conflict)
      ; the same article to other groups
      (equal (fn-pb-existing-action *ost-msgid* *ost-held* (cons "fn.other" *ost-groups*)
                                    *ost-s*)
             :conflict)
      (equal (ost-existing-action *ost-msgid* *ost-held* (cons "fn.other" *ost-groups*)
                                  *ost-s*)
             :conflict)
      ; an unknown Message-ID
      (equal (fn-pb-existing-action "<ost-absent@example.invalid>" *ost-held* *ost-groups*
                                    *ost-s*)
             nil)
      (equal (ost-existing-action "<ost-absent@example.invalid>" *ost-held* *ost-groups*
                                  *ost-s*)
             nil)))

; The keystone's one hypothesis, (fn-octets-p fn-octets): on a value that is
; not an octet list (the held payload with an improper tail) the buffer
; reads to its length and answers :duplicate where the list test, comparing
; the whole values, answers :conflict.
(defconst *ost-improper* (append *ost-held* 3))
(assert-event
 (and (not (fn-octets-p *ost-improper*))
      (equal (fn-pb-existing-action *ost-msgid* *ost-improper* *ost-groups* *ost-s*)
             :conflict)))
(defthm ost-t-improper-buffer-reads-to-its-length
  (equal (fn-pbb-existing-action *ost-msgid* *ost-improper* *ost-groups* *ost-s*)
         :duplicate)
  :rule-classes nil)
(must-fail
 (defthm ost-t-existing-action-without-octets-p
   (equal (fn-pbb-existing-action *ost-msgid* *ost-improper* *ost-groups* *ost-s*)
          (fn-pb-existing-action *ost-msgid* *ost-improper* *ost-groups* *ost-s*))))

; The buffer's recognizer discharges the list entry's fn-octet-listp test.
(assert-event (and (fn-octets-p *ost-held*) (fn-octet-listp *ost-held*)
                   (not (fn-octets-p *ost-improper*))
                   (not (fn-octet-listp *ost-improper*))))
