; fn: tests for books/payload-arena-paged.lisp (lane arena-offheap, stage 1;
; the generated paged arena, lane s-vocab).
;
; What this book is evidence FOR.  The paged implementation's abstraction
; obligations (`fn-arena-paged-get{correspondence}' and the others, admitted
; by `defabsstobj' in the book, generated) say that every export's executable
; step over the directory and pool pages equals the list-of-lists operation of
; the generic.  Here the executable path runs on a live local `fn-arena-paged'
; and is compared with the generic `fn-arena' (the list-backed reference) on
; the same operations: small payloads, payloads that CROSS a pool-page
; boundary (a pool page is 16,384 octets, `*adt-pg-octets*'; the second
; payload starts mid page 2 and ends in page 4), a buffer seal and a range
; seal, reads at the last octet of a page and the first of the next, a bulk
; seal that crosses the table-page boundary (64 pool pages, 1 MiB), and a
; clear followed by a reseal (the clear releases the directory; the arena
; rebuilds from nothing).  Every function the host reaches is guard-verified.
; (The hand foundation's step lemmas and their teeth, the page-table
; arithmetic of the 262,144-octet page, went with it: the generator proves
; them once, books/def-representation-paged.lisp, and
; tests/acl2/def-representation-tests.lisp has its teeth.)

(in-package "ACL2")
(include-book "../../books/payload-arena-paged")
(include-book "../../books/payload-arena")
(include-book "must-fail-checked")

(assert-event
 (and (eq (symbol-class 'fn-arena-paged$c-len-of (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena-paged$c-inner-get (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena-paged$c-get-payload (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena-paged$c-clear (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena-paged$c-append1 (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena-paged$c-range-copy (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena-paged$c-seal-range (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena-paged$c-seal-buffer (w state)) :common-lisp-compliant)))

(defun pap-octets (i n acc)
  (declare (xargs :guard (and (natp i) (natp n) (true-listp acc)) :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      (reverse acc)
    (pap-octets (1+ i) n (cons (mod (* 7 i) 251) acc))))

(defconst *pap-a* (pap-octets 0 40000 nil))     ; ends mid page 2 (a pool page is 16,384 octets)
(defconst *pap-b* (pap-octets 3 30003 nil))     ; sealed at 40000: crosses the page boundary 49,152 and 65,536
(defconst *pap-c* '(1 2 3))

; The same run on either arena, as a macro over the export names.
(defmacro pap-run-body (st count len get payload seal-list seal-buffer seal-range clear)
  `(let* ((,st (,clear ,st))
          (,st (,seal-list *pap-a* ,st))
          (,st (,seal-list *pap-b* ,st))
          (,st (with-local-stobj fn-octets
                 (mv-let (,st fn-octets)
                   (let* ((fn-octets (fn-octets-from-list *pap-b* fn-octets))
                          (,st (,seal-buffer fn-octets ,st))
                          (,st (,seal-range 5000 9000 fn-octets ,st)))
                     (mv ,st fn-octets))
                   ,st)))
          (,st (,seal-list *pap-c* ,st))
          (result (list (,count ,st)
                        (,len 0 ,st) (,len 1 ,st) (,len 2 ,st) (,len 3 ,st) (,len 4 ,st)
                        (,get 1 9151 ,st)    ; the last octet of page 2 (pool offset 49151)
                        (,get 1 9152 ,st)    ; the first of page 3
                        (,get 1 29997 ,st)
                        (,get 3 3999 ,st)
                        (,get 4 2 ,st)
                        (equal (,payload 0 ,st) *pap-a*)
                        (equal (,payload 1 ,st) *pap-b*)
                        (equal (,payload 2 ,st) *pap-b*)
                        (equal (,payload 3 ,st) (take 4000 (nthcdr 5000 *pap-b*)))
                        (,payload 4 ,st)))
          (,st (,clear ,st))
          (after-clear (,count ,st))
          (,st (,seal-list *pap-c* ,st))
          (reseal (list (,count ,st) (,payload 0 ,st))))
     (mv (list result after-clear reseal) ,st)))

(defun pap-paged-run (fn-arena-paged)
  (declare (xargs :stobjs fn-arena-paged))
  (pap-run-body fn-arena-paged fn-arena-paged-count fn-arena-paged-payload-len
                fn-arena-paged-get fn-arena-paged-payload fn-arena-paged-seal-list
                fn-arena-paged-seal-buffer fn-arena-paged-seal-range fn-arena-paged-clear))

(defun pap-generic-run (fn-arena)
  (declare (xargs :stobjs fn-arena))
  (pap-run-body fn-arena fn-arena-count fn-arena-payload-len
                fn-arena-get fn-arena-payload fn-arena-seal-list
                fn-arena-seal-buffer fn-arena-seal-range fn-arena-clear))

(defun pap-paged ()
  (with-local-stobj fn-arena-paged
    (mv-let (result fn-arena-paged) (pap-paged-run fn-arena-paged) result)))

(defun pap-generic ()
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (pap-generic-run fn-arena) result)))

; The paged arena answers what the generic answers, and the answer is the
; one the payloads determine.
(assert-event (equal (pap-paged) (pap-generic)))

(assert-event
 (equal (pap-paged)
        (list (list 5 40000 30000 30000 4000 3
                    (nth 9151 *pap-b*) (nth 9152 *pap-b*)
                    (nth 29997 *pap-b*) (nth (+ 5000 3999) *pap-b*) 3
                    t t t t '(1 2 3))
              0
              (list 1 '(1 2 3)))))

; =============================================================================
;
; -----------------------------------------------------------------------------
; The bulk seal (lane snapshot-open-2).  One buffer seal of 1,200,000 octets
; starts at pool offset 3 and spans pool pages 0 to 73, across the table-page
; boundary at 1 MiB (the second level of the directory); a range seal of
; [524287, 1048579) of the same buffer follows, and each is read back against
; the generic, at the last octet of a pool page, the first of the next, and
; either side of the table-page boundary.
(defun pap-d () (declare (xargs :guard t)) (pap-octets 11 1200011 nil))

(defmacro pap-bulk-body (st count get payload seal-list seal-buffer seal-range clear)
  `(let* ((,st (,clear ,st))
          (,st (,seal-list *pap-c* ,st))
          (,st (with-local-stobj fn-octets
                 (mv-let (,st fn-octets)
                   (let* ((fn-octets (fn-octets-from-list (pap-d) fn-octets))
                          (,st (,seal-buffer fn-octets ,st))
                          (,st (,seal-range 524287 1048579 fn-octets ,st)))
                     (mv ,st fn-octets))
                   ,st))))
     (mv (list (,count ,st)
               (equal (,payload 1 ,st) (pap-d))
               (equal (,payload 2 ,st) (take (- 1048579 524287) (nthcdr 524287 (pap-d))))
               (,get 1 16380 ,st) (,get 1 16381 ,st) (,get 1 1048572 ,st)
               (,get 1 1048573 ,st) (,get 1 1199999 ,st) (,get 2 0 ,st) (,get 2 524291 ,st))
         ,st)))

(defun pap-bulk-paged-run (fn-arena-paged)
  (declare (xargs :stobjs fn-arena-paged :verify-guards nil))
  (pap-bulk-body fn-arena-paged fn-arena-paged-count fn-arena-paged-get fn-arena-paged-payload
                 fn-arena-paged-seal-list fn-arena-paged-seal-buffer fn-arena-paged-seal-range
                 fn-arena-paged-clear))

(defun pap-bulk-generic-run (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (pap-bulk-body fn-arena fn-arena-count fn-arena-get fn-arena-payload
                 fn-arena-seal-list fn-arena-seal-buffer fn-arena-seal-range fn-arena-clear))

(defun pap-bulk-paged ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena-paged
    (mv-let (result fn-arena-paged) (pap-bulk-paged-run fn-arena-paged) result)))

(defun pap-bulk-generic ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (pap-bulk-generic-run fn-arena) result)))

(assert-event
 (let ((r (pap-bulk-paged)))
   (and (equal r (pap-bulk-generic))
        (equal (car r) 3)
        (cadr r) (caddr r)
        (equal (nth 3 r) (nth 16380 (pap-d)))
        (equal (nth 4 r) (nth 16381 (pap-d)))
        (equal (nth 5 r) (nth 1048572 (pap-d)))
        (equal (nth 6 r) (nth 1048573 (pap-d)))
        (equal (nth 7 r) (nth 1199999 (pap-d)))
        (equal (nth 8 r) (nth 524287 (pap-d)))
        (equal (nth 9 r) (nth (+ 524287 524291) (pap-d))))))
