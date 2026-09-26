; fn: teeth for books/payload-arena.lisp.
;
; What this book is evidence FOR.  The abstraction theorems of the arena
; (`fn-arena-get{correspondence}' and the others) say that every export's
; executable step on the byte array and the handle arrays equals the
; list-of-lists operation on the abstraction whenever the correspondence
; and the export's guard hold; the keystones say a sealed handle is
; immutable under any later seal (`fn-arena-seal-keeps-sealed',
; `fn-arena-seals-keep-sealed'), a seal's handle is the old count and is
; never reused (`fn-arena-seal-new-handle', `fn-arena-seal-count'), and a
; commit and an open establish the same relation with a store history
; (`fn-arn-store-corr-of-commit', `fn-arn-store-corr-of-open').  Each gets
; a ground positive witness asserting its complete antecedent and
; conclusion, and for each hypothesis a witness on which every retained
; hypothesis holds, the omitted one fails, and the conclusion fails; a
; hypothesis that no witness can falsify is shown redundant by proving
; the weakened theorem.  The exec path is also run on a live local arena
; and a live local octet buffer, the way the host will run it.

(in-package "ACL2")
(include-book "../../books/payload-arena")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it may reach is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-arena$c-payload-len (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$c-get (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$c-payload (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$c-clear (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arn-write-octet (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arn-write (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arn-write-buffer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arn-seal-entry (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$c-seal-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$c-seal-buffer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arn-buf-list-down (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arn-seal-many (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The executable path on a live local arena and a live local buffer: three
; seals (a list, the octet buffer's contents, the empty payload), the reads,
; then a clear.  The buffer's seal is the host's entry: no list is built.

(defun pat-exec-run (fn-arena)
  (declare (xargs :stobjs fn-arena))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list '(1 2 3) fn-arena))
         (fn-arena (with-local-stobj fn-octets
                     (mv-let (fn-arena fn-octets)
                       (let* ((fn-octets (fn-octets-from-list '(4 5) fn-octets))
                              (fn-arena (fn-arena-seal-buffer fn-octets fn-arena)))
                         (mv fn-arena fn-octets))
                       fn-arena)))
         (fn-arena (fn-arena-seal-list nil fn-arena))
         (result (list (fn-arena-count fn-arena)
                       (fn-arena-payload-len 0 fn-arena)
                       (fn-arena-get 0 2 fn-arena)
                       (fn-arena-payload 0 fn-arena)
                       (fn-arena-payload-len 1 fn-arena)
                       (fn-arena-get 1 0 fn-arena)
                       (fn-arena-payload 1 fn-arena)
                       (fn-arena-payload-len 2 fn-arena)
                       (fn-arena-payload 2 fn-arena)))
         (fn-arena (fn-arena-clear fn-arena)))
    (mv (list result (fn-arena-count fn-arena)) fn-arena)))

(defun pat-exec ()
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (pat-exec-run fn-arena) result)))

(assert-event (equal (pat-exec)
                     '((3 3 3 (1 2 3) 2 4 (4 5) 0 nil) 0)))

; 3,000 octets sealed three times: the byte array doubles from 1,024 past
; 9,000 and the handle arrays grow from their first 64 cells; every handle
; reads back whole, and the middle one is unchanged by the seal after it.

(defun pat-big (n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n) acc (pat-big (1- n) (cons (mod (* 7 n) 256) acc))))

(defconst *pat-big* (pat-big 3000 nil))

(defun pat-exec-big-run (fn-arena)
  (declare (xargs :stobjs fn-arena))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list *pat-big* fn-arena))
         (before (fn-arena-payload 0 fn-arena))
         (fn-arena (with-local-stobj fn-octets
                     (mv-let (fn-arena fn-octets)
                       (let* ((fn-octets (fn-octets-from-list *pat-big* fn-octets))
                              (fn-arena (fn-arena-seal-buffer fn-octets fn-arena)))
                         (mv fn-arena fn-octets))
                       fn-arena)))
         (fn-arena (fn-arena-seal-list *pat-big* fn-arena)))
    (mv (list (fn-arena-count fn-arena)
              (equal before *pat-big*)
              (equal (fn-arena-payload 0 fn-arena) *pat-big*)
              (equal (fn-arena-payload 1 fn-arena) *pat-big*)
              (equal (fn-arena-payload 2 fn-arena) *pat-big*)
              (fn-arena-payload-len 1 fn-arena)
              (fn-arena-get 2 2999 fn-arena))
        fn-arena)))

(defun pat-exec-big ()
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (pat-exec-big-run fn-arena) result)))

(assert-event (and (fn-cbor-octet-listp *pat-big*) (equal (len *pat-big*) 3000)
                   (equal (pat-exec-big)
                          (list 3 t t t t 3000 (nth 2999 *pat-big*)))))

; -----------------------------------------------------------------------------
; The obligations on ground values.  *pat-c* is a concrete arena holding
; (1 2 3) then (4 5) in an 8-cell array with two spare cells; *pat-a* is its
; abstraction.  The concrete-side functions take the stobj variable at the
; top level, so ground statements about them are theorems proved by
; evaluation, as in octets-stobj-tests.

(defconst *pat-c* '((1 2 3 4 5 0 0 0) (0 3) (3 2) 2 5))
(defconst *pat-a* '((1 2 3) (4 5)))

(assert-event (fn-arena$corr *pat-c* *pat-a*))

; get: the positive witness, complete antecedent and conclusion.
(defthm pat-w-get
  (and (fn-arena$corr *pat-c* *pat-a*)
       (natp 1) (< 1 (fn-arena$a-count *pat-a*)) (natp 1) (< 1 (fn-arena$a-payload-len 1 *pat-a*))
       (equal (fn-arena$c-get 1 1 *pat-c*) (fn-arena$a-get 1 1 *pat-a*))
       (equal (fn-arena$c-get 1 1 *pat-c*) 5))
  :rule-classes nil)

; get without the correspondence: an abstraction that is not the slices.
(defconst *pat-a-wrong* '((1 2 3) (9 9)))
(defthm pat-w-get-without-corr
  (and (not (fn-arena$corr *pat-c* *pat-a-wrong*))
                   (natp 1) (< 1 (fn-arena$a-count *pat-a-wrong*)) (natp 0)
                   (< 0 (fn-arena$a-payload-len 1 *pat-a-wrong*))
                   (not (equal (fn-arena$c-get 1 0 *pat-c*)
                               (fn-arena$a-get 1 0 *pat-a-wrong*))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-get-without-corr
   (equal (fn-arena$c-get 1 0 *pat-c*) (fn-arena$a-get 1 0 *pat-a-wrong*))
   :rule-classes nil))

; get without the octet bound: past the payload the array holds the next
; payload's first octet, the abstraction holds nothing.
(defthm pat-w-get-without-bound
  (and (fn-arena$corr *pat-c* *pat-a*)
                   (natp 0) (< 0 (fn-arena$a-count *pat-a*)) (natp 3)
                   (not (< 3 (fn-arena$a-payload-len 0 *pat-a*)))
                   (not (equal (fn-arena$c-get 0 3 *pat-c*)
                               (fn-arena$a-get 0 3 *pat-a*))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-get-without-bound
   (equal (fn-arena$c-get 0 3 *pat-c*) (fn-arena$a-get 0 3 *pat-a*))
   :rule-classes nil))

; get without the handle bound: a handle at the count reads the spare cells.
(defconst *pat-c-spare* '((1 2 3 4 5 7 0 0) (0 3 5) (3 2 1) 2 5))
(defthm pat-w-get-without-handle-bound
  (and (fn-arena$corr *pat-c-spare* *pat-a*)
                   (natp 2) (not (< 2 (fn-arena$a-count *pat-a*))) (natp 0)
                   (not (equal (fn-arena$c-get 2 0 *pat-c-spare*)
                               (fn-arena$a-get 2 0 *pat-a*))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-get-without-handle-bound
   (equal (fn-arena$c-get 2 0 *pat-c-spare*) (fn-arena$a-get 2 0 *pat-a*))
   :rule-classes nil))

; get without (natp i): a negative offset reads the previous payload's
; last octet where the abstraction reads the payload's first.
(defthm pat-w-get-without-natp-i
  (and (fn-arena$corr *pat-c* *pat-a*)
                   (natp 1) (< 1 (fn-arena$a-count *pat-a*)) (not (natp -1))
                   (< -1 (fn-arena$a-payload-len 1 *pat-a*))
                   (not (equal (fn-arena$c-get 1 -1 *pat-c*)
                               (fn-arena$a-get 1 -1 *pat-a*))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-get-without-natp-i
   (equal (fn-arena$c-get 1 -1 *pat-c*) (fn-arena$a-get 1 -1 *pat-a*))
   :rule-classes nil))

; get's (natp h) cannot be falsified: a handle that is not a natural reads
; as handle 0 on both sides.  The weakened theorem, proved.
(local
 (defthm pat-nth-of-non-natp
   (implies (not (natp h))
            (equal (nth h x) (car x)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm pat-nth-0
   (equal (nth 0 x) (car x))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm pat-w-get-needs-no-natp-h
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (< h (fn-arena$a-count fn-arena))
                (natp i) (< i (fn-arena$a-payload-len h fn-arena)))
           (equal (fn-arena$c-get h i fn-arena$c) (fn-arena$a-get h i fn-arena)))
  :rule-classes nil
  :hints (("Goal" :cases ((natp h)))
          ("Subgoal 2" :in-theory (e/d (fn-arena$corr) (nth fn-arn-slices fn-arn-nth-of-slices))
           :use ((:instance fn-arn-nth-of-slices
                            (h 0) (k 0) (count (nth 3 fn-arena$c)) (off (nth 1 fn-arena$c))
                            (size (nth 2 fn-arena$c)) (buf (nth 0 fn-arena$c)))
                 (:instance fn-arn-rangesp-at
                            (h 0) (k 0) (count (nth 3 fn-arena$c)) (off (nth 1 fn-arena$c))
                            (size (nth 2 fn-arena$c)) (top (nth 4 fn-arena$c)))
                 (:instance fn-oct-nth-of-list-from
                            (i (car (nth 1 fn-arena$c)))
                            (n (+ (car (nth 1 fn-arena$c)) (car (nth 2 fn-arena$c))))
                            (k i) (buf (nth 0 fn-arena$c)))))
          ("Subgoal 1" :use ((:instance fn-arena-get{correspondence})))))

; seal-list: the positive witness on the ground arena.
(defthm pat-w-seal-list
  (and (fn-arena$corr *pat-c* *pat-a*) (fn-cbor-octet-listp '(6 7 8))
       (fn-arena$corr (fn-arena$c-seal-list '(6 7 8) *pat-c*)
                      (fn-arena$a-seal-list '(6 7 8) *pat-a*))
       (equal (fn-arena$a-seal-list '(6 7 8) *pat-a*) '((1 2 3) (4 5) (6 7 8))))
  :rule-classes nil)

; seal-list without octets: the array cannot hold 300 and the concrete
; recognizer fails; the abstraction still appends.
(defthm pat-w-seal-list-without-octets
  (and (fn-arena$corr *pat-c* *pat-a*) (not (fn-cbor-octet-listp '(300)))
                   (not (fn-arena$corr (fn-arena$c-seal-list '(300) *pat-c*)
                                       (fn-arena$a-seal-list '(300) *pat-a*))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-seal-list-without-octets
   (fn-arena$corr (fn-arena$c-seal-list '(300) *pat-c*)
                  (fn-arena$a-seal-list '(300) *pat-a*))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; The keystones on ground values.

; A sealed handle is immutable under a seal: handle 1 before and after.
(defthm pat-w-seal-keeps-sealed
  (and (natp 1) (< 1 (fn-arena-count *pat-a*))
       (equal (fn-arena-payload 1 (fn-arena-seal-list '(9) *pat-a*))
              (fn-arena-payload 1 *pat-a*))
       (equal (fn-arena-payload 1 *pat-a*) '(4 5)))
  :rule-classes nil)

; Without (natp h): on the empty arena a negative handle reads the new
; payload (nth of a negative is car) where before it read nothing.
(defthm pat-w-seal-keeps-sealed-without-natp
  (and (not (natp -1)) (< -1 (fn-arena-count nil))
                   (not (equal (fn-arena-payload -1 (fn-arena-seal-list '(9) nil))
                               (fn-arena-payload -1 nil))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-seal-keeps-sealed-without-natp
   (equal (fn-arena-payload -1 (fn-arena-seal-list '(9) nil))
          (fn-arena-payload -1 nil))
   :rule-classes nil))

; Without the bound: the handle at the count is the new payload, not nothing.
(defthm pat-w-seal-keeps-sealed-without-bound
  (and (natp 2) (not (< 2 (fn-arena-count *pat-a*)))
                   (not (equal (fn-arena-payload 2 (fn-arena-seal-list '(9) *pat-a*))
                               (fn-arena-payload 2 *pat-a*))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-seal-keeps-sealed-without-bound
   (equal (fn-arena-payload 2 (fn-arena-seal-list '(9) *pat-a*))
          (fn-arena-payload 2 *pat-a*))
   :rule-classes nil))

; The new handle is the old count and denotes the sealed octets; the count
; grows by one.  No hypothesis: no removal witness exists.
(defthm pat-w-seal-new-handle
  (and (equal (fn-arena-count *pat-a*) 2)
       (equal (fn-arena-payload 2 (fn-arena-seal-list '(9) *pat-a*)) '(9))
       (equal (fn-arena-count (fn-arena-seal-list '(9) *pat-a*)) 3))
  :rule-classes nil)

; A sequence of seals keeps every handle it found.
(defthm pat-w-seals-keep-sealed
  (and (natp 0) (< 0 (fn-arena-count *pat-a*))
       (equal (fn-arena-payload 0 (fn-arn-seal-many '((9) nil (8 8)) *pat-a*))
              (fn-arena-payload 0 *pat-a*))
       (equal (fn-arn-seal-many '((9) nil (8 8)) *pat-a*)
              '((1 2 3) (4 5) (9) nil (8 8))))
  :rule-classes nil)

(defthm pat-w-seals-keep-sealed-without-natp
  (and (not (natp -1)) (< -1 (fn-arena-count nil))
                   (not (equal (fn-arena-payload -1 (fn-arn-seal-many '((9)) nil))
                               (fn-arena-payload -1 nil))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-seals-keep-sealed-without-natp
   (equal (fn-arena-payload -1 (fn-arn-seal-many '((9)) nil))
          (fn-arena-payload -1 nil))
   :rule-classes nil))
(defthm pat-w-seals-keep-sealed-without-bound
  (and (natp 2) (not (< 2 (fn-arena-count *pat-a*)))
       (not (equal (fn-arena-payload 2 (fn-arn-seal-many '((9) nil (8 8)) *pat-a*))
                   (fn-arena-payload 2 *pat-a*))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-seals-keep-sealed-without-bound
   (equal (fn-arena-payload 2 (fn-arn-seal-many '((9) nil (8 8)) *pat-a*))
          (fn-arena-payload 2 *pat-a*))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; The store relation on a two-record history: a commit keeps it, an open
; from the empty arena establishes it, and an arena holding the records'
; payloads in the wrong order does not satisfy it.

(defconst *pat-r1* (fn-record-make 1 1 1 "<r1@example.invalid>" '(1 2 3) '("fn.test")
                                   "o1" "s1" "e1" 1 0))
(defconst *pat-r2* (fn-record-make 2 2 2 "<r2@example.invalid>" '(4 5) '("fn.test")
                                   "o2" "s2" "e2" 1 0))
(defconst *pat-r3* (fn-record-make 3 3 3 "<r3@example.invalid>" '(6) '("fn.test")
                                   "o3" "s3" "e3" 1 0))

(defthm pat-w-store-corr-ground
  (and (equal (fn-record-payload *pat-r1*) '(1 2 3))
                   (equal (fn-arn-payloads-of (list *pat-r1* *pat-r2*)) *pat-a*)
                   (fn-arn-store-corr *pat-a* (list *pat-r1* *pat-r2*))
                   (not (fn-arn-store-corr '((4 5) (1 2 3)) (list *pat-r1* *pat-r2*))))
  :rule-classes nil)

(defthm pat-w-store-corr-of-commit
  (and (fn-arn-store-corr *pat-a* (list *pat-r1* *pat-r2*))
       (fn-arn-store-corr (fn-arena-seal-list (fn-record-payload *pat-r3*) *pat-a*)
                          (append (list *pat-r1* *pat-r2*) (list *pat-r3*)))
       (equal (fn-arena-seal-list (fn-record-payload *pat-r3*) *pat-a*)
              '((1 2 3) (4 5) (6))))
  :rule-classes nil)

; Without the relation before the commit: an arena missing a payload.
(defthm pat-w-store-corr-of-commit-without-corr
  (and (not (fn-arn-store-corr '((1 2 3)) (list *pat-r1* *pat-r2*)))
                   (not (fn-arn-store-corr (fn-arena-seal-list (fn-record-payload *pat-r3*) '((1 2 3)))
                                           (append (list *pat-r1* *pat-r2*) (list *pat-r3*)))))
  :rule-classes nil)
(must-fail
 (defthm pat-r-store-corr-of-commit-without-corr
   (fn-arn-store-corr (fn-arena-seal-list (fn-record-payload *pat-r3*) '((1 2 3)))
                      (append (list *pat-r1* *pat-r2*) (list *pat-r3*)))
   :rule-classes nil))

(defthm pat-w-store-corr-of-open
  (and (fn-arn-store-corr (fn-arn-seal-many (fn-arn-payloads-of (list *pat-r1* *pat-r2* *pat-r3*)) nil)
                          (list *pat-r1* *pat-r2* *pat-r3*))
       (equal (fn-arn-seal-many (fn-arn-payloads-of (list *pat-r1* *pat-r2* *pat-r3*)) nil)
              '((1 2 3) (4 5) (6))))
  :rule-classes nil)
