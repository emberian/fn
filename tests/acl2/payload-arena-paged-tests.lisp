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
(include-book "must-fail-checked")

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

; =============================================================================
; Teeth for PRF-281 (lane audit-fixes, packet G3-2 of the keystone audit of
; 2026-09-27): each step lemma and each registered {correspondence}
; obligation gets a positive witness asserting its complete antecedent and
; conclusion on a concrete arena the exports reach from the creator, and one
; removal witness per retained hypothesis (every other hypothesis holds, the
; omitted one fails, the conclusion fails), each proved by the rewriter over
; ground tuples.
;
; Why the prover and not evaluation: the page functions read their page
; through `stobj-let', whose executable counterpart refuses a non-live
; stobj ("Failed attempt to call NON-EXEC"), so a ground call is not
; evaluated; the theory `pap-open' opens them and `pap-no-exec' keeps the
; prover from trying.  A page is 262,144 octets; the tuples are built with
; `make-list', never spelled.
;
; A concrete arena is (PAGES OFF SIZE COUNT FILL NPAGES); a page is (BYTES).

(deftheory pap-open
  '(fn-arena$p-seal-list fn-arp-write fn-arp-write-octet fn-arp-add-page fn-arp-put
    fn-arp-seal-entry fn-arp-byte fn-arp-list-pages fn-arena$p-get fn-arena$p-payload
    fn-arena$p-seal-buffer fn-arena$p-seal-range fn-arp-write-buffer fn-arena$p-clear))

(deftheory pap-no-exec
  '((:e fn-arena$p-seal-list) (:e fn-arp-write) (:e fn-arp-write-octet) (:e fn-arp-add-page)
    (:e fn-arp-put) (:e fn-arp-byte) (:e fn-arp-list-pages) (:e fn-arena$p-get)
    (:e fn-arena$p-payload) (:e fn-arena$p-seal-buffer) (:e fn-arena$p-seal-range)
    (:e fn-arp-write-buffer)))

(defmacro pap-theory ()
  '(set-difference-theories (union-theories (current-theory :here) (theory 'pap-open))
                            (theory 'pap-no-exec)))

(defun pap-page (xs)
  (declare (xargs :verify-guards nil))
  (list (append xs (make-list (- 262144 (len xs)) :initial-element 0))))

(defun pap-zeros (n)
  (declare (xargs :verify-guards nil))
  (make-list n :initial-element 0))

; X0: the creator's arena.  X1: X0 after sealing (1 2 3) (the first write
; adds page 0 and the page table's eight slots; the seal sizes the handle
; arrays at 64).  X2: X1 after sealing (4 5).  X3: X2 cleared, then (7)
; sealed: the handle arrays keep X2's entries past the count (the clear
; releases the pages and resets the count, not the handle arrays).
(defconst *pap-x0* '(nil nil nil 0 0 0))
(defconst *pap-x1*
  (list (cons (pap-page '(1 2 3)) (make-list 7 :initial-element '(nil)))
        (pap-zeros 64) (update-nth 0 3 (pap-zeros 64)) 1 3 1))
(defconst *pap-x2*
  (list (cons (pap-page '(1 2 3 4 5)) (make-list 7 :initial-element '(nil)))
        (update-nth 1 3 (pap-zeros 64)) (update-nth 0 3 (update-nth 1 2 (pap-zeros 64))) 2 5 1))
(defconst *pap-x3*
  (list (cons (pap-page '(7)) (make-list 7 :initial-element '(nil)))
        (update-nth 1 3 (pap-zeros 64)) (update-nth 0 1 (update-nth 1 2 (pap-zeros 64))) 1 1 1))
(defconst *pap-x2-cleared*
  (list nil (nth 1 *pap-x2*) (nth 2 *pap-x2*) 0 0 0))
(defconst *pap-a1* '((1 2 3)))
(defconst *pap-a2* '((1 2 3) (4 5)))
(defconst *pap-a3* '((7)))

(defthm pap-x0-is-created
  (equal (create-fn-arena$p) *pap-x0*)
  :rule-classes nil)

(defthm pap-x1-x2-x3-are-reached
  (and (equal (fn-arena$p-seal-list '(1 2 3) *pap-x0*) *pap-x1*)
       (equal (fn-arena$p-seal-list '(4 5) *pap-x1*) *pap-x2*)
       (equal (fn-arena$p-clear *pap-x2*) *pap-x2-cleared*)
       (equal (fn-arena$p-seal-list '(7) *pap-x2-cleared*) *pap-x3*))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)

; Each reached arena corresponds to its payloads.
(defthm pap-reached-correspond
  (and (fn-arena$pcorr *pap-x0* nil)
       (fn-arena$pcorr *pap-x1* *pap-a1*)
       (fn-arena$pcorr *pap-x2* *pap-a2*)
       (fn-arena$pcorr *pap-x3* *pap-a3*))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; fn-arp-add-page-step: hypothesis (fn-arp-okp fn-arena$p).

(defmacro pap-add-page-concl (x i n)
  `(let ((next (fn-arp-add-page ,x)))
     (and (fn-arp-okp next)
          (equal (nth 1 next) (nth 1 ,x))
          (equal (nth 2 next) (nth 2 ,x))
          (equal (nth 3 next) (nth 3 ,x))
          (equal (nth 4 next) (nth 4 ,x))
          (equal (nth 5 next) (1+ (nth 5 ,x)))
          (implies (and (natp ,n) (<= ,n (fn-arp-cap ,x)))
                   (equal (fn-oct-list-from ,i ,n (fn-arp-buf next))
                          (fn-oct-list-from ,i ,n (fn-arp-buf ,x)))))))

; Positive, reached: the creator's arena (the first page, the table grown to
; eight slots), for every I and N; and X2 (a second page into a spare slot),
; the five octets below the fill kept.
(defthm pap-w-add-page-step
  (and (fn-arp-okp *pap-x0*)
       (pap-add-page-concl *pap-x0* i n)
       (fn-arp-okp *pap-x2*)
       (pap-add-page-concl *pap-x2* 0 5)
       (equal (fn-oct-list-from 0 5 (fn-arp-buf (fn-arp-add-page *pap-x2*))) '(1 2 3 4 5)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)

; Without (fn-arp-okp): corrupted state, a page count of 1 with no page.
; The added page is page 1; page 0 is an empty slot, so the result is not
; a table of full pages.
(defconst *pap-bad-np* '(nil nil nil 0 0 1))
(defthm pap-w-add-page-step-no-okp ; corrupted state
  (and (not (fn-arp-okp *pap-bad-np*))
       (not (pap-add-page-concl *pap-bad-np* 0 0)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-add-page-step-no-okp
   (pap-add-page-concl *pap-bad-np* 0 0)
   :hints (("Goal" :use pap-w-add-page-step-no-okp :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; fn-arp-write-octet-step: (fn-arp-okp x), (<= fill cap), (fn-cbor-octetp o).

(defmacro pap-write-octet-hyps (x o)
  `(and (fn-arp-okp ,x) (<= (nth 4 ,x) (fn-arp-cap ,x)) (fn-cbor-octetp ,o)))

(defmacro pap-write-octet-concl (x o)
  `(let ((next (fn-arp-write-octet ,o ,x)))
     (and (fn-arp-okp next)
          (equal (nth 1 next) (nth 1 ,x))
          (equal (nth 2 next) (nth 2 ,x))
          (equal (nth 3 next) (nth 3 ,x))
          (equal (nth 4 next) (1+ (nth 4 ,x)))
          (<= (nth 4 next) (fn-arp-cap next))
          (equal (nth (nth 4 ,x) (fn-arp-buf next)) ,o))))

; Positive, reached: the first octet of an arena (the add-page arm, fill =
; capacity = 0) and the next octet after X2 (the in-page arm).
(defthm pap-w-write-octet-step
  (and (pap-write-octet-hyps *pap-x0* 1)
       (pap-write-octet-concl *pap-x0* 1)
       (pap-write-octet-hyps *pap-x2* 6)
       (pap-write-octet-concl *pap-x2* 6))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)

; Without (fn-arp-okp): corrupted state, X2 with a count of -1.
(defconst *pap-x2-neg-count* (update-nth 3 -1 *pap-x2*))
(defthm pap-w-write-octet-step-no-okp ; corrupted state
  (and (not (fn-arp-okp *pap-x2-neg-count*))
       (<= (nth 4 *pap-x2-neg-count*) (fn-arp-cap *pap-x2-neg-count*))
       (fn-cbor-octetp 6)
       (not (pap-write-octet-concl *pap-x2-neg-count* 6)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-write-octet-step-no-okp
   (implies (and (<= (nth 4 *pap-x2-neg-count*) (fn-arp-cap *pap-x2-neg-count*))
                 (fn-cbor-octetp 6))
            (pap-write-octet-concl *pap-x2-neg-count* 6))
   :hints (("Goal" :use pap-w-write-octet-step-no-okp :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; Without (<= fill cap): corrupted state, X2 with the fill past two pages.
; The write adds page 1 (capacity 524,288) and puts the octet into page 2,
; an empty slot, so nothing is written and the fill passes the capacity.
(defconst *pap-x2-far-fill* (update-nth 4 524289 *pap-x2*))
(defthm pap-w-write-octet-step-no-room ; corrupted state
  (and (fn-arp-okp *pap-x2-far-fill*)
       (not (<= (nth 4 *pap-x2-far-fill*) (fn-arp-cap *pap-x2-far-fill*)))
       (fn-cbor-octetp 6)
       (not (pap-write-octet-concl *pap-x2-far-fill* 6)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-write-octet-step-no-room
   (implies (and (fn-arp-okp *pap-x2-far-fill*) (fn-cbor-octetp 6))
            (pap-write-octet-concl *pap-x2-far-fill* 6))
   :hints (("Goal" :use pap-w-write-octet-step-no-room :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; Without (fn-cbor-octetp o): 256 lands in a page, which is then no byte array.
(defthm pap-w-write-octet-step-no-octet
  (and (fn-arp-okp *pap-x2*)
       (<= (nth 4 *pap-x2*) (fn-arp-cap *pap-x2*))
       (not (fn-cbor-octetp 256))
       (not (pap-write-octet-concl *pap-x2* 256)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-write-octet-step-no-octet
   (implies (and (fn-arp-okp *pap-x2*) (<= (nth 4 *pap-x2*) (fn-arp-cap *pap-x2*)))
            (pap-write-octet-concl *pap-x2* 256))
   :hints (("Goal" :use pap-w-write-octet-step-no-octet :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; fn-arp-seal-list-step: (fn-arp-okp x), (<= fill cap), (<= count (len off)),
; (<= count (len size)), (fn-arn-rangesp 0 count off size fill),
; (fn-cbor-octet-listp xs).

(defmacro pap-seal-list-hyps (x xs)
  `(and (fn-arp-okp ,x)
        (<= (nth 4 ,x) (fn-arp-cap ,x))
        (<= (nth 3 ,x) (len (nth 1 ,x)))
        (<= (nth 3 ,x) (len (nth 2 ,x)))
        (fn-arn-rangesp 0 (nth 3 ,x) (nth 1 ,x) (nth 2 ,x) (nth 4 ,x))
        (fn-cbor-octet-listp ,xs)))

(defmacro pap-seal-list-concl (x xs)
  `(let ((next (fn-arena$p-seal-list ,xs ,x)))
     (and (fn-arp-okp next)
          (<= (nth 4 next) (fn-arp-cap next))
          (<= (nth 3 next) (len (nth 1 next)))
          (<= (nth 3 next) (len (nth 2 next)))
          (fn-arn-rangesp 0 (nth 3 next) (nth 1 next) (nth 2 next) (nth 4 next))
          (equal (fn-arn-slices 0 (nth 3 next) (nth 1 next) (nth 2 next) (fn-arp-buf next))
                 (append (fn-arn-slices 0 (nth 3 ,x) (nth 1 ,x) (nth 2 ,x) (fn-arp-buf ,x))
                         (list ,xs))))))

; Positive, reached: the first seal (X0, the handle arrays sized from
; nothing) and the second (X1 to X2).
(defthm pap-w-seal-list-step
  (and (pap-seal-list-hyps *pap-x0* '(1 2 3))
       (pap-seal-list-concl *pap-x0* '(1 2 3))
       (pap-seal-list-hyps *pap-x1* '(4 5))
       (pap-seal-list-concl *pap-x1* '(4 5))
       (equal (fn-arn-slices 0 2 (nth 1 *pap-x2*) (nth 2 *pap-x2*) (fn-arp-buf *pap-x2*))
              *pap-a2*))
  :hints (("Goal" :use pap-x1-x2-x3-are-reached
           :in-theory (disable fn-arena$p-seal-list (:e fn-arena$p-seal-list))))
  :rule-classes nil)

; Without (fn-arp-okp): corrupted state, X1 with 300 in page 0 above the
; fill; the seal writes below it, so the page is still no byte array.
(defconst *pap-x1-bad-byte*
  (update-nth 0 (cons (list (update-nth 100 300 (car (pap-page '(1 2 3)))))
                      (make-list 7 :initial-element '(nil)))
              *pap-x1*))
(defthm pap-w-seal-list-step-no-okp ; corrupted state
  (and (not (fn-arp-okp *pap-x1-bad-byte*))
       (<= (nth 4 *pap-x1-bad-byte*) (fn-arp-cap *pap-x1-bad-byte*))
       (<= (nth 3 *pap-x1-bad-byte*) (len (nth 1 *pap-x1-bad-byte*)))
       (<= (nth 3 *pap-x1-bad-byte*) (len (nth 2 *pap-x1-bad-byte*)))
       (fn-arn-rangesp 0 (nth 3 *pap-x1-bad-byte*) (nth 1 *pap-x1-bad-byte*)
                       (nth 2 *pap-x1-bad-byte*) (nth 4 *pap-x1-bad-byte*))
       (fn-cbor-octet-listp '(4 5))
       (not (pap-seal-list-concl *pap-x1-bad-byte* '(4 5))))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-seal-list-step-no-okp
   (implies (and (<= (nth 4 *pap-x1-bad-byte*) (fn-arp-cap *pap-x1-bad-byte*))
                 (<= (nth 3 *pap-x1-bad-byte*) (len (nth 1 *pap-x1-bad-byte*)))
                 (<= (nth 3 *pap-x1-bad-byte*) (len (nth 2 *pap-x1-bad-byte*)))
                 (fn-arn-rangesp 0 (nth 3 *pap-x1-bad-byte*) (nth 1 *pap-x1-bad-byte*) (nth 2 *pap-x1-bad-byte*) (nth 4 *pap-x1-bad-byte*)))
            (pap-seal-list-concl *pap-x1-bad-byte* '(4 5)))
   :hints (("Goal" :use pap-w-seal-list-step-no-okp :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; Without (<= fill cap): corrupted state, X1 with the fill past two pages.
; The octet adds page 1 and lands in the empty slot 2 (lost), and the fill
; ends past the two pages.
(defconst *pap-x1-far-fill* (update-nth 4 524289 *pap-x1*))
(defthm pap-w-seal-list-step-no-room ; corrupted state
  (and (fn-arp-okp *pap-x1-far-fill*)
       (not (<= (nth 4 *pap-x1-far-fill*) (fn-arp-cap *pap-x1-far-fill*)))
       (<= (nth 3 *pap-x1-far-fill*) (len (nth 1 *pap-x1-far-fill*)))
       (<= (nth 3 *pap-x1-far-fill*) (len (nth 2 *pap-x1-far-fill*)))
       (fn-arn-rangesp 0 (nth 3 *pap-x1-far-fill*) (nth 1 *pap-x1-far-fill*)
                       (nth 2 *pap-x1-far-fill*) (nth 4 *pap-x1-far-fill*))
       (fn-cbor-octet-listp '(4))
       (not (pap-seal-list-concl *pap-x1-far-fill* '(4))))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-seal-list-step-no-room
   (implies (and (fn-arp-okp *pap-x1-far-fill*)
                 (<= (nth 3 *pap-x1-far-fill*) (len (nth 1 *pap-x1-far-fill*)))
                 (<= (nth 3 *pap-x1-far-fill*) (len (nth 2 *pap-x1-far-fill*)))
                 (fn-arn-rangesp 0 (nth 3 *pap-x1-far-fill*) (nth 1 *pap-x1-far-fill*) (nth 2 *pap-x1-far-fill*) (nth 4 *pap-x1-far-fill*)))
            (pap-seal-list-concl *pap-x1-far-fill* '(4)))
   :hints (("Goal" :use pap-w-seal-list-step-no-room :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; (<= count (len off)) and (<= count (len size)) admit no removal witness:
; the ranges hypothesis implies both (a range reads the offset and the size
; of every handle below the count, and `nth' past a list is not a natural).
(defthm pap-natp-nth-is-below-len
  (implies (and (natp k) (integerp (nth k l))) (< k (len l)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth k l)))))
(defthm pap-rangesp-bounds-the-handle-arrays
  (implies (and (natp h) (natp count) (< h count) (fn-arn-rangesp h count off size top))
           (and (<= count (len off)) (<= count (len size))))
  :hints (("Goal" :induct (fn-arn-rangesp h count off size top)
           :in-theory (enable fn-arn-rangesp)))
  :rule-classes nil)
(defthm pap-rangesp-implies-the-array-hypotheses
  (implies (and (natp count) (fn-arn-rangesp 0 count off size top))
           (and (<= count (len off)) (<= count (len size))))
  :hints (("Goal" :use ((:instance pap-rangesp-bounds-the-handle-arrays (h 0)))))
  :rule-classes nil)

; Without the ranges: corrupted state, X1 with handle 0's size 10 past the
; fill; the next arena's ranges still name it, so they fail.
(defconst *pap-x1-long-size* (update-nth 2 (update-nth 0 10 (pap-zeros 64)) *pap-x1*))
(defthm pap-w-seal-list-step-no-ranges ; corrupted state
  (and (fn-arp-okp *pap-x1-long-size*)
       (<= (nth 4 *pap-x1-long-size*) (fn-arp-cap *pap-x1-long-size*))
       (<= (nth 3 *pap-x1-long-size*) (len (nth 1 *pap-x1-long-size*)))
       (<= (nth 3 *pap-x1-long-size*) (len (nth 2 *pap-x1-long-size*)))
       (not (fn-arn-rangesp 0 (nth 3 *pap-x1-long-size*) (nth 1 *pap-x1-long-size*)
                            (nth 2 *pap-x1-long-size*) (nth 4 *pap-x1-long-size*)))
       (fn-cbor-octet-listp '(4 5))
       (not (pap-seal-list-concl *pap-x1-long-size* '(4 5))))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-seal-list-step-no-ranges
   (implies (and (fn-arp-okp *pap-x1-long-size*)
                 (<= (nth 4 *pap-x1-long-size*) (fn-arp-cap *pap-x1-long-size*))
                 (<= (nth 3 *pap-x1-long-size*) (len (nth 1 *pap-x1-long-size*)))
                 (<= (nth 3 *pap-x1-long-size*) (len (nth 2 *pap-x1-long-size*))))
            (pap-seal-list-concl *pap-x1-long-size* '(4 5)))
   :hints (("Goal" :use pap-w-seal-list-step-no-ranges :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; Without (fn-cbor-octet-listp xs): 300 is written into the page.
(defthm pap-w-seal-list-step-no-octets
  (and (fn-arp-okp *pap-x1*)
       (<= (nth 4 *pap-x1*) (fn-arp-cap *pap-x1*))
       (<= (nth 3 *pap-x1*) (len (nth 1 *pap-x1*)))
       (<= (nth 3 *pap-x1*) (len (nth 2 *pap-x1*)))
       (fn-arn-rangesp 0 (nth 3 *pap-x1*) (nth 1 *pap-x1*) (nth 2 *pap-x1*) (nth 4 *pap-x1*))
       (not (fn-cbor-octet-listp '(4 300)))
       (not (pap-seal-list-concl *pap-x1* '(4 300))))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-seal-list-step-no-octets
   (implies (and (fn-arp-okp *pap-x1*) (<= (nth 4 *pap-x1*) (fn-arp-cap *pap-x1*)))
            (pap-seal-list-concl *pap-x1* '(4 300)))
   :hints (("Goal" :use pap-w-seal-list-step-no-octets :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; The registered {correspondence} obligations.  Their hypotheses are the
; ones `defabsstobj' generates: the correspondence and the export's guard
; over the logical arena.  An export's guard cannot be dropped from its
; obligation; where a guard conjunct admits no counterexample the witness
; below proves the weakened statement, so that it is shown redundant, not
; merely untoothed.

(deftheory pap-octets-no-exec
  '((:e fn-octets-get) (:e fn-octets-len)))

(defmacro pap-theory-octets ()
  '(set-difference-theories
    (union-theories (current-theory :here) (theory 'pap-open))
    (union-theories (theory 'pap-no-exec) (theory 'pap-octets-no-exec))))

; A payload list that is not X2's: the second payload's last octet differs.
(defconst *pap-a2-wrong* '((1 2 3) (4 9)))

; ---- fn-arena-paged-get{correspondence}: (corr c a), (natp h),
; (< h (count a)), (natp i), (< i (payload-len h a)).

(defmacro pap-get-hyps (c a h i)
  `(and (fn-arena$pcorr ,c ,a) (natp ,h) (< ,h (fn-arena$a-count ,a))
        (natp ,i) (< ,i (fn-arena$a-payload-len ,h ,a))))
(defmacro pap-get-concl (c a h i)
  `(equal (fn-arena$p-get ,h ,i ,c) (fn-arena$a-get ,h ,i ,a)))

; Positive, reached: X2's second payload's last octet and its first
; payload's last; X3's only octet.
(defthm pap-w-get
  (and (pap-get-hyps *pap-x2* *pap-a2* 1 1) (pap-get-concl *pap-x2* *pap-a2* 1 1)
       (equal (fn-arena$a-get 1 1 *pap-a2*) 5)
       (pap-get-hyps *pap-x2* *pap-a2* 0 2) (pap-get-concl *pap-x2* *pap-a2* 0 2)
       (pap-get-hyps *pap-x3* *pap-a3* 0 0) (pap-get-concl *pap-x3* *pap-a3* 0 0))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)

; Without the correspondence: X2 read against payloads it does not hold.
(defthm pap-w-get-no-corr ; corrupted pair
  (and (not (fn-arena$pcorr *pap-x2* *pap-a2-wrong*))
       (natp 1) (< 1 (fn-arena$a-count *pap-a2-wrong*))
       (natp 1) (< 1 (fn-arena$a-payload-len 1 *pap-a2-wrong*))
       (not (pap-get-concl *pap-x2* *pap-a2-wrong* 1 1)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-get-no-corr
   (implies (and (natp 1) (< 1 (fn-arena$a-count *pap-a2-wrong*))
                 (natp 1) (< 1 (fn-arena$a-payload-len 1 *pap-a2-wrong*)))
            (pap-get-concl *pap-x2* *pap-a2-wrong* 1 1))
   :hints (("Goal" :use pap-w-get-no-corr :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; Without (natp i): I = -1 reads the octet before the payload (3, the
; first payload's last) where the logic reads the payload's first (4).
(defthm pap-w-get-no-natp-i
  (and (fn-arena$pcorr *pap-x2* *pap-a2*) (natp 1) (< 1 (fn-arena$a-count *pap-a2*))
       (not (natp -1)) (< -1 (fn-arena$a-payload-len 1 *pap-a2*))
       (equal (fn-arena$p-get 1 -1 *pap-x2*) 3)
       (equal (fn-arena$a-get 1 -1 *pap-a2*) 4)
       (not (pap-get-concl *pap-x2* *pap-a2* 1 -1)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-get-no-natp-i
   (implies (and (fn-arena$pcorr *pap-x2* *pap-a2*) (natp 1) (< 1 (fn-arena$a-count *pap-a2*))
                 (< -1 (fn-arena$a-payload-len 1 *pap-a2*)))
            (pap-get-concl *pap-x2* *pap-a2* 1 -1))
   :hints (("Goal" :use pap-w-get-no-natp-i :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; Without (< i (payload-len h a)): position 3 of payload 0 is the next
; payload's first octet on the pages, and nothing in the logic.
(defthm pap-w-get-past-the-payload
  (and (fn-arena$pcorr *pap-x2* *pap-a2*) (natp 0) (< 0 (fn-arena$a-count *pap-a2*))
       (natp 3) (not (< 3 (fn-arena$a-payload-len 0 *pap-a2*)))
       (equal (fn-arena$p-get 0 3 *pap-x2*) 4)
       (equal (fn-arena$a-get 0 3 *pap-a2*) nil)
       (not (pap-get-concl *pap-x2* *pap-a2* 0 3)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-get-past-the-payload
   (implies (and (fn-arena$pcorr *pap-x2* *pap-a2*) (natp 0) (< 0 (fn-arena$a-count *pap-a2*))
                 (natp 3))
            (pap-get-concl *pap-x2* *pap-a2* 0 3))
   :hints (("Goal" :use pap-w-get-past-the-payload :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; (< h (count a)) admits no removal witness: a natural H at or past the
; count names no payload, whose length is 0, so no natural I is below it.
(defthm pap-get-count-hypothesis-is-implied
  (implies (and (natp h) (natp i) (< i (fn-arena$a-payload-len h a)))
           (< h (fn-arena$a-count a)))
  :hints (("Goal" :in-theory (enable fn-oct-nth)))
  :rule-classes nil)

; (natp h) admits no removal witness for the read of one octet: a
; non-natural H reads handle 0 on both sides (`nth' and `fn-oct-nth' take
; it as 0), and (< i (payload-len h a)) with a natural I needs a payload
; there.  Proved: the obligation holds without it.
(defthm pap-nth-of-a-non-natural
  (implies (not (natp h)) (equal (nth h l) (nth 0 l)))
  :hints (("Goal" :in-theory (enable nth))))
(defthm pap-get-without-natp-h
  (implies (and (fn-arena$pcorr c a) (< h (fn-arena$a-count a))
                (natp i) (< i (fn-arena$a-payload-len h a)))
           (equal (fn-arena$p-get h i c) (fn-arena$a-get h i a)))
  :hints (("Goal" :cases ((natp h)))
          ("Subgoal 2" :use ((:instance fn-arena-paged-get{correspondence}
                                        (fn-arena$p c) (fn-arena-paged a) (h 0)))
           :in-theory (e/d (fn-arena$p-get fn-arena$p-offi fn-arena$p-sizei)
                           (fn-arena$pcorr)))
          ("Subgoal 1" :use ((:instance fn-arena-paged-get{correspondence}
                                        (fn-arena$p c) (fn-arena-paged a)))))
  :rule-classes nil)
(in-theory (disable pap-nth-of-a-non-natural))

; ---- fn-arena-paged-payload{correspondence}: (corr c a), (natp h),
; (< h (count a)).

(defmacro pap-payload-hyps (c a h)
  `(and (fn-arena$pcorr ,c ,a) (natp ,h) (< ,h (fn-arena$a-count ,a))))
(defmacro pap-payload-concl (c a h)
  `(equal (fn-arena$p-payload ,h ,c) (fn-arena$a-payload ,h ,a)))

(defthm pap-w-payload
  (and (pap-payload-hyps *pap-x2* *pap-a2* 0) (pap-payload-concl *pap-x2* *pap-a2* 0)
       (pap-payload-hyps *pap-x2* *pap-a2* 1) (pap-payload-concl *pap-x2* *pap-a2* 1)
       (equal (fn-arena$a-payload 1 *pap-a2*) '(4 5))
       (pap-payload-hyps *pap-x3* *pap-a3* 0) (pap-payload-concl *pap-x3* *pap-a3* 0))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)

(defthm pap-w-payload-no-corr ; corrupted pair
  (and (not (fn-arena$pcorr *pap-x2* *pap-a2-wrong*))
       (natp 1) (< 1 (fn-arena$a-count *pap-a2-wrong*))
       (not (pap-payload-concl *pap-x2* *pap-a2-wrong* 1)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-payload-no-corr
   (implies (and (natp 1) (< 1 (fn-arena$a-count *pap-a2-wrong*)))
            (pap-payload-concl *pap-x2* *pap-a2-wrong* 1))
   :hints (("Goal" :use pap-w-payload-no-corr :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; Without (< h (count a)), on a REACHED arena: X3 is X2 cleared and resealed,
; and its handle arrays still hold X2's handle 1 past the count (offset 3,
; size 2).  The pages read two octets there; the logic has no payload 1.
(defthm pap-w-payload-past-the-count
  (and (fn-arena$pcorr *pap-x3* *pap-a3*) (natp 1)
       (not (< 1 (fn-arena$a-count *pap-a3*)))
       (equal (fn-arena$p-payload 1 *pap-x3*) '(0 0))
       (equal (fn-arena$a-payload 1 *pap-a3*) nil)
       (not (pap-payload-concl *pap-x3* *pap-a3* 1)))
  :hints (("Goal" :in-theory (pap-theory)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-payload-past-the-count
   (implies (and (fn-arena$pcorr *pap-x3* *pap-a3*) (natp 1))
            (pap-payload-concl *pap-x3* *pap-a3* 1))
   :hints (("Goal" :use pap-w-payload-past-the-count :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; Without (natp h), on a REACHED arena: X2 cleared holds no payload, and
; its handle arrays still hold X2's handle 0 (offset 0, size 3).  H = -1 is
; below the count 0 only because it is not a natural; the pages read handle
; 0's stale range (three octets of no page), the logic has no payload.
(defthm pap-w-payload-no-natp-h
  (and (fn-arena$pcorr *pap-x2-cleared* nil)
       (not (natp -1)) (< -1 (fn-arena$a-count nil))
       (equal (fn-arena$p-payload -1 *pap-x2-cleared*) '(0 0 0))
       (equal (fn-arena$a-payload -1 nil) nil)
       (not (pap-payload-concl *pap-x2-cleared* nil -1)))
  :hints (("Goal" :in-theory (set-difference-theories (pap-theory) '((:e fn-arp-page-down)))
           :expand ((fn-arp-list-pages 0 3 nil *pap-x2-cleared*)
                    (fn-arp-page-down 0 3 nil nil) (fn-arp-page-down 0 2 '(0) nil)
                    (fn-arp-page-down 0 1 '(0 0) nil) (fn-arp-page-down 0 0 '(0 0 0) nil))))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-payload-no-natp-h
   (implies (and (fn-arena$pcorr *pap-x2-cleared* nil) (< -1 (fn-arena$a-count nil)))
            (pap-payload-concl *pap-x2-cleared* nil -1))
   :hints (("Goal" :use pap-w-payload-no-natp-h :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; ---- fn-arena-paged-seal-buffer{correspondence}: (corr c a),
; (fn-octets-p fn-octets).  The buffer's logical value is its octet list.

(defmacro pap-seal-buffer-concl (c a o)
  `(fn-arena$pcorr (fn-arena$p-seal-buffer ,o ,c) (fn-arena$a-seal-buffer ,o ,a)))

; The buffer seal from X1 reaches X2, computed once.
(defthm pap-seal-buffer-of-x1
  (equal (fn-arena$p-seal-buffer '(4 5) *pap-x1*) *pap-x2*)
  :hints (("Goal" :in-theory (pap-theory-octets)))
  :rule-classes nil)

(defthm pap-w-seal-buffer
  (and (fn-arena$pcorr *pap-x1* *pap-a1*) (fn-octets-p '(4 5))
       (pap-seal-buffer-concl *pap-x1* *pap-a1* '(4 5))
       (equal (fn-arena$p-seal-buffer '(4 5) *pap-x1*) *pap-x2*)
       (equal (fn-arena$a-seal-buffer '(4 5) *pap-a1*) *pap-a2*))
  :hints (("Goal" :use pap-seal-buffer-of-x1
           :in-theory (disable fn-arena$p-seal-buffer (:e fn-arena$p-seal-buffer))))
  :rule-classes nil)

(defthm pap-w-seal-buffer-no-corr ; corrupted pair
  (and (not (fn-arena$pcorr *pap-x1* '((1 2 9)))) (fn-octets-p '(4 5))
       (not (pap-seal-buffer-concl *pap-x1* '((1 2 9)) '(4 5))))
  :hints (("Goal" :use pap-seal-buffer-of-x1
           :in-theory (disable fn-arena$p-seal-buffer (:e fn-arena$p-seal-buffer))))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-seal-buffer-no-corr
   (implies (fn-octets-p '(4 5)) (pap-seal-buffer-concl *pap-x1* '((1 2 9)) '(4 5)))
   :hints (("Goal" :use pap-w-seal-buffer-no-corr :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

(defthm pap-w-seal-buffer-no-octets
  (and (fn-arena$pcorr *pap-x1* *pap-a1*) (not (fn-octets-p '(4 300)))
       (not (pap-seal-buffer-concl *pap-x1* *pap-a1* '(4 300))))
  :hints (("Goal" :in-theory (pap-theory-octets)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-seal-buffer-no-octets
   (implies (fn-arena$pcorr *pap-x1* *pap-a1*) (pap-seal-buffer-concl *pap-x1* *pap-a1* '(4 300)))
   :hints (("Goal" :use pap-w-seal-buffer-no-octets :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; ---- fn-arena-paged-seal-range{correspondence}: (corr c a),
; (fn-octets-p fn-octets), (natp a), (natp b), (<= a b), (<= b (len)).

(defmacro pap-seal-range-hyps (c ab o a b)
  `(and (fn-arena$pcorr ,c ,ab) (fn-octets-p ,o) (natp ,a) (natp ,b) (<= ,a ,b)
        (<= ,b (fn-octets-len ,o))))
(defmacro pap-seal-range-concl (c ab o a b)
  `(fn-arena$pcorr (fn-arena$p-seal-range ,a ,b ,o ,c) (fn-arena$a-seal-range ,a ,b ,o ,ab)))

; The range seal of cells [1, 3) from X1 reaches X2, computed once.
(defthm pap-seal-range-of-x1
  (equal (fn-arena$p-seal-range 1 3 '(9 4 5 9) *pap-x1*) *pap-x2*)
  :hints (("Goal" :in-theory (pap-theory-octets)))
  :rule-classes nil)

(defthm pap-w-seal-range
  (and (pap-seal-range-hyps *pap-x1* *pap-a1* '(9 4 5 9) 1 3)
       (pap-seal-range-concl *pap-x1* *pap-a1* '(9 4 5 9) 1 3)
       (equal (fn-arena$p-seal-range 1 3 '(9 4 5 9) *pap-x1*) *pap-x2*)
       (equal (fn-arena$a-seal-range 1 3 '(9 4 5 9) *pap-a1*) *pap-a2*))
  :hints (("Goal" :use pap-seal-range-of-x1
           :in-theory (disable fn-arena$p-seal-range (:e fn-arena$p-seal-range)
                               fn-arp-seal-range-is-seal-list)))
  :rule-classes nil)

(defthm pap-w-seal-range-no-corr ; corrupted pair
  (and (not (fn-arena$pcorr *pap-x1* '((1 2 9)))) (fn-octets-p '(9 4 5 9))
       (natp 1) (natp 3) (<= 1 3) (<= 3 (fn-octets-len '(9 4 5 9)))
       (not (pap-seal-range-concl *pap-x1* '((1 2 9)) '(9 4 5 9) 1 3)))
  :hints (("Goal" :use pap-seal-range-of-x1
           :in-theory (disable fn-arena$p-seal-range (:e fn-arena$p-seal-range)
                               fn-arp-seal-range-is-seal-list)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-seal-range-no-corr
   (implies (and (fn-octets-p '(9 4 5 9)) (<= 3 (fn-octets-len '(9 4 5 9))))
            (pap-seal-range-concl *pap-x1* '((1 2 9)) '(9 4 5 9) 1 3))
   :hints (("Goal" :use pap-w-seal-range-no-corr :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

(defthm pap-w-seal-range-no-octets
  (and (fn-arena$pcorr *pap-x1* *pap-a1*) (not (fn-octets-p '(9 4 300 9)))
       (natp 1) (natp 3) (<= 1 3) (<= 3 (fn-octets-len '(9 4 300 9)))
       (not (pap-seal-range-concl *pap-x1* *pap-a1* '(9 4 300 9) 1 3)))
  :hints (("Goal" :in-theory (pap-theory-octets)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-seal-range-no-octets
   (implies (and (fn-arena$pcorr *pap-x1* *pap-a1*) (<= 3 (fn-octets-len '(9 4 300 9))))
            (pap-seal-range-concl *pap-x1* *pap-a1* '(9 4 300 9) 1 3))
   :hints (("Goal" :use pap-w-seal-range-no-octets :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; (natp a), (natp b) and (<= a b) admit no removal witness: off those, the
; pages write no octet and the logic slices nothing, so both seal an empty
; payload.  Proved: the obligation holds without the three.
(defthm pap-seal-range-without-the-range-guard
  (implies (and (fn-arena$pcorr c ab) (fn-octets-p o) (<= b (fn-octets-len o)))
           (fn-arena$pcorr (fn-arena$p-seal-range a b o c) (fn-arena$a-seal-range a b o ab)))
  :hints (("Goal" :cases ((and (natp a) (natp b) (<= a b))))
          ("Subgoal 1" :use ((:instance fn-arena-paged-seal-range{correspondence}
                                        (fn-arena$p c) (fn-arena-paged ab) (fn-octets o))))
          ("Subgoal 2" :use ((:instance fn-arena-paged-seal-list{correspondence}
                                        (fn-arena$p c) (fn-arena-paged ab) (xs nil)))
           :expand ((fn-oct-slice-list a b o))
           :in-theory (e/d (fn-arp-seal-range-is-seal-list fn-arena$a-seal-range fn-arena$a-seal-list)
                           (fn-arena$pcorr fn-oct-slice-list-is-take-nthcdr))))
  :rule-classes nil)

; Without (<= b (len)): the range [4, 5) runs past the four-cell buffer;
; the pages take the missing cell as NIL, which is no octet, so the arena
; after the seal is no page table of bytes (the proof opens the range read
; by hand: its ground call is outside its guard, so it is not evaluated).
(defconst *pap-x1-nil-cell*
  (list (cons (list (update-nth 3 nil (car (pap-page '(1 2 3)))))
              (make-list 7 :initial-element '(nil)))
        (update-nth 1 3 (pap-zeros 64)) (update-nth 0 3 (update-nth 1 1 (pap-zeros 64))) 2 4 1))
(defmacro pap-theory-range ()
  '(set-difference-theories (union-theories (pap-theory-octets) '(fn-oct-slice-list))
                            '((:e fn-oct-slice-list))))
(defthm pap-seal-range-past-the-buffer-writes-nil
  (equal (fn-arena$p-seal-range 4 5 '(9 4 5 9) *pap-x1*) *pap-x1-nil-cell*)
  :hints (("Goal" :in-theory (pap-theory-range)
           :expand ((fn-oct-slice-list 4 5 '(9 4 5 9)) (fn-oct-slice-list 5 5 '(9 4 5 9)))))
  :rule-classes nil)
(defthm pap-w-seal-range-past-the-buffer
  (and (fn-arena$pcorr *pap-x1* *pap-a1*) (fn-octets-p '(9 4 5 9))
       (natp 4) (natp 5) (<= 4 5) (not (<= 5 (fn-octets-len '(9 4 5 9))))
       (not (pap-seal-range-concl *pap-x1* *pap-a1* '(9 4 5 9) 4 5)))
  :hints (("Goal" :use pap-seal-range-past-the-buffer-writes-nil
           :in-theory (disable fn-arena$p-seal-range fn-arp-seal-range-is-seal-list)))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-seal-range-past-the-buffer
   (implies (and (fn-arena$pcorr *pap-x1* *pap-a1*) (fn-octets-p '(9 4 5 9)))
            (pap-seal-range-concl *pap-x1* *pap-a1* '(9 4 5 9) 4 5))
   :hints (("Goal" :use pap-w-seal-range-past-the-buffer :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))

; ---- fn-arena-paged-clear{correspondence}: (corr c a).

(defthm pap-w-clear
  (and (fn-arena$pcorr *pap-x2* *pap-a2*)
       (fn-arena$pcorr (fn-arena$p-clear *pap-x2*) (fn-arena$a-clear *pap-a2*))
       (equal (nth 5 (fn-arena$p-clear *pap-x2*)) 0))
  :hints (("Goal" :use pap-x1-x2-x3-are-reached
           :in-theory (disable fn-arena$p-clear (:e fn-arena$p-clear)
                               fn-arena$p-seal-list (:e fn-arena$p-seal-list))))
  :rule-classes nil)

; Without the correspondence: corrupted state, X2 with a negative offset in
; an unused handle slot; the clear keeps the handle arrays.
(defconst *pap-x2-bad-off* (update-nth 1 (update-nth 5 -1 (nth 1 *pap-x2*)) *pap-x2*))
(defthm pap-w-clear-no-corr ; corrupted state
  (and (not (fn-arena$pcorr *pap-x2-bad-off* *pap-a2*))
       (not (fn-arena$pcorr (fn-arena$p-clear *pap-x2-bad-off*) (fn-arena$a-clear *pap-a2*))))
  :rule-classes nil)
(must-fail-checked
 (defthm pap-t-clear-no-corr
   (fn-arena$pcorr (fn-arena$p-clear *pap-x2-bad-off*) (fn-arena$a-clear *pap-a2*))
   :hints (("Goal" :use pap-w-clear-no-corr :in-theory (theory 'minimal-theory)
            :do-not-induct t))
   :rule-classes nil))
