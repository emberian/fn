; fn: teeth for books/payload-arena-paged.lisp (lane arena-offheap, stage 1).
;
; What this book is evidence FOR.  The paged implementation's abstraction
; obligations (`fn-arena-paged-get{correspondence}' and the others, admitted
; by `defabsstobj' in the book) say that every export's executable step over
; the page table equals the list-of-lists operation of the generic.  Here
; the executable path runs on a live local `fn-arena-paged' and is compared
; with the generic `fn-arena' (the list-backed reference) on the same
; operations: small payloads, payloads that CROSS a page boundary (a page is
; 262,144 octets; the second payload starts mid page 0 and ends in page 1), a
; buffer seal and a range seal, reads at the last octet of a page and the
; first of the next, and a clear followed by a reseal (the clear releases
; the page table; the arena rebuilds from nothing).  Every function the
; host reaches is guard-verified.

(in-package "ACL2")
(include-book "../../books/payload-arena-paged")
(include-book "../../books/payload-arena")

(assert-event
 (and (eq (symbol-class 'fn-arena$p-payload-len (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$p-get (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$p-payload (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$p-clear (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-byte (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-put (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-add-page (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-write-octet (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-write (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-write-buffer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-seal-entry (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$p-seal-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$p-seal-buffer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$p-seal-range (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-page-down (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-list-pages (w state)) :common-lisp-compliant)))

(defun pap-octets (i n acc)
  (declare (xargs :guard (and (natp i) (natp n) (true-listp acc)) :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      (reverse acc)
    (pap-octets (1+ i) n (cons (mod (* 7 i) 251) acc))))

(defconst *pap-a* (pap-octets 0 250000 nil))    ; ends mid page 0 (a page is 262,144 octets)
(defconst *pap-b* (pap-octets 3 30003 nil))      ; sealed at 250000: crosses into page 1
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
                        (,get 1 12143 ,st)   ; the last octet of page 0
                        (,get 1 12144 ,st)   ; the first of page 1
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
        (list (list 5 250000 30000 30000 4000 3
                    (nth 12143 *pap-b*) (nth 12144 *pap-b*)
                    (nth 29997 *pap-b*) (nth (+ 5000 3999) *pap-b*) 3
                    t t t t '(1 2 3))
              0
              (list 1 '(1 2 3)))))

; -----------------------------------------------------------------------------
; The bulk write (lane snapshot-open-2): fn-arp-write-buffer's executable is
; fn-arp-write-run (the page and column once per page).  The runs above seal
; buffers through it (the second buffer seal starts mid page 1); here one
; buffer seal of 600,000 octets starts mid page 0 and spans pages 0, 1 and 2
; in one call, a range seal starts at the last octet of a page, and each is
; read back against the generic.
(defconst *pap-d* (pap-octets 11 600011 nil))

(defmacro pap-bulk-body (st count get payload seal-list seal-buffer seal-range clear)
  `(let* ((,st (,clear ,st))
          (,st (,seal-list *pap-c* ,st))
          (,st (with-local-stobj fn-octets
                 (mv-let (,st fn-octets)
                   (let* ((fn-octets (fn-octets-from-list *pap-d* fn-octets))
                          (,st (,seal-buffer fn-octets ,st))
                          (,st (,seal-range 262143 524290 fn-octets ,st)))
                     (mv ,st fn-octets))
                   ,st))))
     (mv (list (,count ,st)
               (equal (,payload 1 ,st) *pap-d*)
               (equal (,payload 2 ,st) (take (- 524290 262143) (nthcdr 262143 *pap-d*)))
               (,get 1 262140 ,st) (,get 1 262141 ,st) (,get 1 524284 ,st)
               (,get 1 524285 ,st) (,get 2 0 ,st) (,get 2 262146 ,st))
         ,st)))

(defun pap-bulk-paged-run (fn-arena-paged)
  (declare (xargs :stobjs fn-arena-paged))
  (pap-bulk-body fn-arena-paged fn-arena-paged-count fn-arena-paged-get fn-arena-paged-payload
                 fn-arena-paged-seal-list fn-arena-paged-seal-buffer fn-arena-paged-seal-range
                 fn-arena-paged-clear))

(defun pap-bulk-generic-run (fn-arena)
  (declare (xargs :stobjs fn-arena))
  (pap-bulk-body fn-arena fn-arena-count fn-arena-get fn-arena-payload
                 fn-arena-seal-list fn-arena-seal-buffer fn-arena-seal-range fn-arena-clear))

(defun pap-bulk-paged ()
  (with-local-stobj fn-arena-paged
    (mv-let (result fn-arena-paged) (pap-bulk-paged-run fn-arena-paged) result)))

(defun pap-bulk-generic ()
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (pap-bulk-generic-run fn-arena) result)))

(assert-event
 (let ((r (pap-bulk-paged)))
   (and (equal r (pap-bulk-generic))
        (equal (car r) 3)
        (cadr r) (caddr r)
        (equal (nth 3 r) (nth 262140 *pap-d*))
        (equal (nth 6 r) (nth 262143 *pap-d*)))))

(assert-event
 (and (eq (symbol-class 'fn-arp-put-kj (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-write-in-page (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arp-write-run (w state)) :common-lisp-compliant)))
