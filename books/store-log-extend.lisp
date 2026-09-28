;; fn: the record log's segment extension as a modelled step (lane log-2,
;; 2026-09-27; PKT-COL-4 of lane commit-onto-log's record).
;;
;; When the open batch does not fit the segment, host/native/io.lisp
;; `fnn-log-ensure-extent' grows the segment to ACL2's next extent
;; (fn-olr-extension-target below) and fences it, before the
;; batch's append (fnn-log-commit-open-batch).  Its program, over the same
;; byte model as P-BATCH (fn-bs-write, fn-bs-fsync-file):
;;
;;   (:extend-to :segment NEXT)   zeros written from the segment's end to
;;                                NEXT (host: fnn-log-preallocate from the
;;                                old extent; posix_fallocate on Linux, whose
;;                                allocated range reads zeros: A-HOST)
;;   (:cut "log-extended")
;;   (:fence :segment :extend)    the barrier (fnn-log-fdatasync)
;;   (:cut "log-extent-fenced")
;;
;; The extension runs only at rest (no batch in flight: R's pending list is
;; empty), and changes no kernel field: the frontier, the committed records
;; and the chain head stay.
;;
;; Keystones:
;;   fn-lg-extend-program-keeps-the-relation   from R at rest and a NEXT of
;;       whole units past the segment's end, the run ends R-related to the
;;       SAME kernel with the segment NEXT octets long (the tail zeros);
;;   fn-lg-extension-written-crash-reads-the-committed-records   every crash
;;       image at log-extended (the zeros pending, any tear of them: landed,
;;       zeroed or garbled units) scans to exactly the committed records and
;;       frontier, ends on the chain head, is a whole number of units, and
;;       keeps the old segment's octets: the recovery program's hypotheses
;;       (books/store-log-programs.lisp
;;       fn-lg-recover-program-establishes-the-relation), so the cut is
;;       recoverable and recovery reads what was committed.  Hypothesis: at
;;       least a magic's worth of zeros past the frontier (the host keeps a
;;       spare unit past every append: fn-olr-extension-needed-p).
;; At log-extent-fenced nothing is pending and R holds (the first keystone).
(in-package "ACL2")
(include-book "store-log-kernel")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-bs-apply-op)
                          (:definition fn-lg-declared-len)
                          (:definition fn-lg-scan)
                          (:rewrite fn-lgc-take-all))))

; The host's rule: extend when the open batch, and one spare unit after it,
; do not fit the extent (OCTETS: the open batch's log length, which the host
; takes from books/store-log.lisp fn-lg-log-len: fn-olr-log-need-is-the-
; append-end).  The spare
; unit keeps zeros past the frontier after every append, so an extension
; never starts at a full segment (the crash keystone's hypothesis).
(defun fn-olr-extension-needed-p (frontier octets extent unit)
  (declare (xargs :guard t))
  (< (nfix extent) (+ (nfix frontier) (nfix octets) (nfix unit))))

; The target: at least twice the extent (so extensions are logarithmic in
; the log's size) and at least the batch and the spare unit, rounded up to
; the unit (books/store-log-route.lisp fn-olr-next-extent's rule).
(defun fn-olr-extension-target (frontier octets extent unit)
  (declare (xargs :guard t))
  (let* ((unit (if (posp unit) unit 1))
         (need (+ (nfix frontier) (nfix octets) unit)))
    (max (max (* 2 (nfix extent)) (* unit (ceiling need unit))) unit)))

(defun fn-lg-extend-program (next)
  (declare (xargs :guard t))
  (list (list :extend-to :segment next)
        (list :cut "log-extended")
        (list :fence :segment :extend)
        (list :cut "log-extent-fenced")))
(defun fn-lg-extend-step (bs ks step outcome ino)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-bs-durable-content bs ino)))
    (cond ((and (consp step) (equal (car step) :extend-to))
           (mv-let (r bs1)
             (fn-bs-write bs ino (len c) (fn-bs-zeros (- (nfix (nth 2 step)) (len c))) outcome)
             (mv r bs1 ks)))
          ((equal step '(:fence :segment :extend))
           (mv-let (r bs1) (fn-bs-fsync-file bs ino outcome)
             (mv r bs1 ks)))
          (t (mv :ok bs ks)))))
(defun fn-lg-extend-run (bs ks steps outcomes ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (mv-let (r bs1 ks1)
        (fn-lg-extend-step bs ks (car steps) (if (consp outcomes) (car outcomes) :ok) ino)
        (cons (cons bs1 ks1)
              (if (equal r :ok) (fn-lg-extend-run bs1 ks1 (cdr steps) (cdr outcomes) ino) nil)))
    nil))
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgx-mod-of-sum-zero
     (implies (and (natp a) (natp b) (posp unit)
                   (equal (mod a unit) 0) (equal (mod b unit) 0))
              (equal (mod (+ a b) unit) 0)))
   (defthm fn-lgx-mod-of-diff-zero
     (implies (and (natp a) (natp b) (posp unit) (< b a)
                   (equal (mod a unit) 0) (equal (mod b unit) 0))
              (equal (mod (+ a (- b)) unit) 0)))))
(local (defthm fn-lgx-len-append (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm fn-lgx-take-of-append-shorter
   (implies (and (natp n) (<= n (len a)))
            (equal (fn-bs-take n (append a b)) (fn-bs-take n a)))))
(local (defthm fn-lgx-nthcdr-of-append-shorter
   (implies (and (natp n) (<= n (len a)))
            (equal (nthcdr n (append a b)) (append (nthcdr n a) b)))
   :hints (("Goal" :induct (nthcdr n a)))))
(local (defthm fn-lgx-zerosp-append
   (implies (and (fn-lg-zerosp a) (fn-lg-zerosp b)) (fn-lg-zerosp (append a b)))))
(local (defthm fn-lgx-true-listp-append
   (implies (true-listp b) (true-listp (append a b)))))
(defthm fn-lgk-content-okp-of-zero-extension
  (implies (and (fn-lgk-content-okp c ks unit genesis max)
                (posp unit) (fn-lg-zerosp z) (equal (mod (len z) unit) 0))
           (fn-lgk-content-okp (append c z) ks unit genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-content-okp)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp
                            fn-frame-digestp fn-bs-take fn-lg-zerosp nthcdr mod len append
                            fn-lgk-frontier fn-lgk-inflight fn-lgk-batch fn-lgk-last fn-lgk-committed fn-lgk-acked))
           :use ((:instance fn-lgx-nthcdr-of-append-shorter (n (fn-lgk-frontier ks)) (a c) (b z))
                 (:instance fn-lgx-take-of-append-shorter (n (fn-lgk-frontier ks)) (a c) (b z))
                 (:instance fn-lgx-zerosp-append (a (nthcdr (fn-lgk-frontier ks) c)) (b z))
                 (:instance fn-lgx-mod-of-sum-zero (a (len c)) (b (len z)))))))

(local (defthm fn-lgx-take-all
   (implies (and (true-listp c) (equal n (len c))) (equal (fn-bs-take n c) c))))
(local (defthm fn-lgx-nthcdr-past
   (implies (and (true-listp c) (<= (len c) (nfix n))) (equal (nthcdr n c) nil))))
(local (defthm fn-lgx-append-nil
   (implies (true-listp x) (equal (append x nil) x))))
(local (defthm fn-lgx-splice-at-end
   (implies (true-listp c)
            (equal (fn-bs-splice c (len c) z) (append c (true-list-fix z))))
   :hints (("Goal" :in-theory (enable fn-bs-splice)))))
(local (defthm fn-lgx-zeros-true-listp (true-listp (fn-bs-zeros n))))
(local (defthm fn-lgx-true-list-fix-id
   (implies (true-listp x) (equal (true-list-fix x) x))))
(local (defthm fn-lgx-zeros-len (equal (len (fn-bs-zeros n)) (nfix n))))
(local (defthm fn-lgx-take-zeros
   (equal (fn-bs-take n (fn-bs-zeros n)) (fn-bs-zeros n))))
; The state after the extension's write and its barrier, from a state with
; nothing pending: the segment's content grown by the zeros.
(defun fn-lg-extended-state (bs ino next)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-bs-durable-content bs ino)))
    (fn-bs-make (fn-bs-unit bs)
                (fn-bs-put-assoc ino (append c (fn-bs-zeros (- (nfix next) (len c))))
                                 (fn-bs-inodes bs))
                (fn-bs-dirs bs) nil (fn-bs-next-ino bs))))
(defthm fn-lg-extend-run-is-the-extended-state
  (implies (and (null (fn-bs-pending bs)) (assoc-equal ino (fn-bs-inodes bs))
                (true-listp (fn-bs-durable-content bs ino))
                (< (len (fn-bs-durable-content bs ino)) (nfix next)))
           (let ((run (fn-lg-extend-run bs ks (fn-lg-extend-program next) nil ino)))
             (and (equal (len run) 4)
                  (equal (car (last run)) (cons (fn-lg-extended-state bs ino next) ks)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write fn-bs-fsync-file fn-bs-fence-file fn-bs-durable-content)
                           (fn-bs-zeros fn-bs-splice)))))

(local (defthm fn-lgx-zerosp-zeros (fn-lg-zerosp (fn-bs-zeros n))))
(local (defthm fn-lgx-assoc-put-assoc
   (implies k (equal (assoc-equal k (fn-bs-put-assoc k v a)) (cons k v)))))
(local (defthm fn-lgx-assoc-put-assoc-other-exists
   (implies (and k (assoc-equal k a)) (assoc-equal k (fn-bs-put-assoc j v a)))))
(local (defthm fn-lgx-content-okp-len
   (implies (fn-lgk-content-okp c ks unit genesis max)
            (and (true-listp c) (equal (mod (len c) unit) 0)))
   :rule-classes nil
   :hints (("Goal" :in-theory '(fn-lgk-content-okp)))))
(local (defthm fn-lgx-zero-extension-okp
   (implies (and (fn-lgk-content-okp c ks unit genesis max) (posp unit)
                 (natp next) (equal (mod next unit) 0) (< (len c) next))
            (fn-lgk-content-okp (append c (fn-bs-zeros (- next (len c)))) ks unit genesis max))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(nfix natp posp (:type-prescription len)))
            :use ((:instance fn-lgx-content-okp-len)
                  (:instance fn-lgx-zerosp-zeros (n (- next (len c))))
                  (:instance fn-lgx-zeros-len (n (- next (len c))))
                  (:instance fn-lgx-mod-of-diff-zero (a next) (b (len c)))
                  (:instance fn-lgk-content-okp-of-zero-extension (z (fn-bs-zeros (- next (len c))))))))))
(defthm fn-lg-extension-keeps-the-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (natp next) (equal (mod next (fn-bs-unit bs)) 0)
                (< (len (fn-bs-durable-content bs ino)) next))
           (let ((s (fn-lg-extended-state bs ino next)))
             (and (fn-lgk-relp s ks ino genesis max)
                  (equal (len (fn-bs-durable-content s ino)) next))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-relp fn-bs-durable-content)
                           (fn-lgk-content-okp fn-bs-zeros fn-lg-log fn-bs-put-assoc mod
                            fn-lgx-zero-extension-okp))
           :use ((:instance fn-lgx-zero-extension-okp
                            (c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs)))
                 (:instance fn-lgx-content-okp-len
                            (c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs)))))))
(defthm fn-lgk-relp-at-rest
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks))))
           (and (null (fn-bs-pending bs))
                (assoc-equal ino (fn-bs-inodes bs))
                (posp (fn-bs-unit bs)) ino
                (true-listp (fn-bs-durable-content bs ino))
                (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-relp) (fn-lgk-content-okp fn-bs-durable-content mod))
           :use ((:instance fn-lgx-content-okp-len (c (fn-bs-durable-content bs ino))
                            (unit (fn-bs-unit bs)))))))
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgx-next-natp
     (implies (and (natp l) (< l next) (posp unit) (equal (mod next unit) 0))
              (natp next))
     :rule-classes nil)))

(defthm fn-lg-extend-program-keeps-the-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (equal (mod next (fn-bs-unit bs)) 0)
                (< (len (fn-bs-durable-content bs ino)) next))
           (let* ((run (fn-lg-extend-run bs ks (fn-lg-extend-program next) nil ino))
                  (final (car (last run))))
             (and (equal (len run) 4)
                  (equal (cdr final) ks)
                  (fn-lgk-relp (car final) ks ino genesis max)
                  (equal (len (fn-bs-durable-content (car final) ino)) next))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-lgk-relp fn-lg-extend-run fn-lg-extend-program fn-lg-extended-state
                               fn-lg-extend-run-is-the-extended-state fn-lg-extension-keeps-the-relation))
           :use ((:instance fn-lg-extend-run-is-the-extended-state)
                 (:instance fn-lg-extension-keeps-the-relation)
                 (:instance fn-lgk-relp-at-rest)
                 (:instance fn-lgx-next-natp (l (len (fn-bs-durable-content bs ino)))
                            (unit (fn-bs-unit bs)))))))

; A zero front: the scan reads nothing past a region of zeros at least a
; magic long, whatever follows it.
(local (defthm fn-lgx-take-of-append-short
   (implies (and (natp n) (<= n (len a)))
            (equal (fn-bs-take n (append a b)) (fn-bs-take n a)))))
(local (defthm fn-lgx-take-zerosp-not-magic
   (implies (and (fn-lg-zerosp z) (<= 4 (len z)))
            (not (equal (fn-bs-take 4 z) *fn-lg-magic*)))
   :hints (("Goal" :expand ((fn-bs-take 4 z) (fn-bs-take 3 (cdr z)))))))
(defthm fn-lg-scan-of-zero-front
  (implies (and (fn-lg-zerosp z) (<= *fn-frame-magic-octets* (len z)))
           (and (equal (fn-lg-scan (append z y) prev unit max) (cons nil 0))
                (equal (fn-lg-scan-last (append z y) prev unit max) prev)))
  :hints (("Goal" :expand ((fn-lg-scan (append z y) prev unit max)
                           (fn-lg-scan-last (append z y) prev unit max)
                           (fn-lg-slice (append z y))
                           (fn-lg-declared-len (append z y)))
           :in-theory (disable fn-lg-entry-okp fn-bs-take)
           :use ((:instance fn-lgx-take-of-append-short (n 4) (a z) (b y))
                 (:instance fn-lgx-take-zerosp-not-magic)))))

(defun fn-lgx-units-p (n unit)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (cond ((zp n) (equal n 0))
        ((or (not (posp unit)) (< n unit)) nil)
        (t (fn-lgx-units-p (- n unit) unit))))
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgx-units-p-is-mod
     (implies (and (natp n) (posp unit))
              (equal (fn-lgx-units-p n unit) (equal (mod n unit) 0)))
     :hints (("Goal" :induct (fn-lgx-units-p n unit))))))
(defthm fn-lgx-units-p-plus-unit
  (implies (and (fn-lgx-units-p n unit) (posp unit) (natp n))
           (fn-lgx-units-p (+ n unit) unit))
  :hints (("Goal" :expand ((fn-lgx-units-p (+ n unit) unit)))))
(defun fn-lgx-aligned-writesp2 (ops unit)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (natp (nth 2 (car ops)))
           (fn-lgx-units-p (nth 2 (car ops)) unit)
           (equal (len (nth 3 (car ops))) unit)
           (fn-lgx-aligned-writesp2 (cdr ops) unit))
    t))
(defthm fn-lgx-pieces-aligned2
  (implies (and (natp start) (posp unit) (fn-lgx-units-p start unit)
                (fn-lgx-units-p (len w) unit))
           (fn-lgx-aligned-writesp2 (fn-lg-pieces ino start w sels unit) unit))
  :hints (("Goal" :induct (fn-lg-pieces ino start w sels unit)
           :in-theory (e/d () (fn-lgx-units-p-is-mod fn-bs-take fn-bs-zeros fn-lg-pieces-shift)))
          ("Subgoal *1/2" :expand ((fn-lgx-units-p (len w) unit)))
          ("Subgoal *1/3" :expand ((fn-lgx-units-p (len w) unit)))
          ("Subgoal *1/4" :expand ((fn-lgx-units-p (len w) unit)))))
(defthm fn-lgx-apply-aligned-keeps-units2
  (implies (and (posp unit) (fn-lgx-units-p (len c) unit)
                (fn-lgx-aligned-writesp2 ops unit))
           (fn-lgx-units-p (len (fn-lg-apply-to c ops)) unit))
  :hints (("Goal" :induct (fn-lg-apply-to c ops)
           :in-theory (disable fn-bs-splice fn-lgx-units-p-is-mod))
          ("Subgoal *1/1" :use ((:instance fn-lgx-units-p-plus-unit (n (nth 2 (car ops))))))))

(local (defthm fn-lgx-take-then-nthcdr
   (implies (and (true-listp x) (natp n) (<= n (len x)))
            (equal (append (fn-bs-take n x) (nthcdr n x)) x))
   :hints (("Goal" :induct (nthcdr n x)))))
(local (defthm fn-lgx-true-listp-take (true-listp (fn-bs-take n x))))
(defthm fn-lgk-content-okp-at-rest-parts
  (implies (fn-lgk-content-okp c ks unit genesis max)
           (let* ((f (fn-lgk-frontier ks)) (d (fn-bs-take f c)) (z (nthcdr f c)))
             (and (true-listp c) (true-listp d)
                  (equal (len d) f)
                  (<= f (len c))
                  (equal (fn-lg-scan d genesis unit max) (cons (fn-lgk-committed ks) f))
                  (equal (fn-lg-scan-last d genesis unit max) (fn-lgk-last ks))
                  (fn-lg-zerosp z)
                  (true-listp (fn-lgk-committed ks))
                  (equal (append d z) c))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-content-okp)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp fn-bs-take
                            fn-lg-zerosp fn-frame-digestp nthcdr mod fn-lgk-frontier)))))
(local (defthm fn-lgx-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))
(local (defthm fn-lgx-split-append
   (implies (equal (append d z) c)
            (equal (append c y) (append d (append z y))))
   :rule-classes nil))
; The scan of the rest-state's content grown by anything Y past its end.
(defthm fn-lg-scan-past-a-resting-log
  (implies (and (fn-lgk-content-okp c ks unit genesis max)
                (<= (+ (fn-lgk-frontier ks) *fn-frame-magic-octets*) (len c)))
           (and (equal (fn-lg-scan (append c y) genesis unit max)
                       (cons (fn-lgk-committed ks) (fn-lgk-frontier ks)))
                (equal (fn-lg-scan-last (append c y) genesis unit max) (fn-lgk-last ks))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-lgk-content-okp fn-lg-scan fn-lg-scan-last fn-bs-take nthcdr
                               fn-lg-scan-of-complete-append fn-lg-scan-last-of-complete-append
                               fn-lg-scan-of-zero-front fn-lg-zerosp fn-lgk-frontier
                               fn-lgx-append-assoc))
           :use ((:instance fn-lgk-content-okp-at-rest-parts)
                 (:instance fn-lgx-split-append (d (fn-bs-take (fn-lgk-frontier ks) c))
                            (z (nthcdr (fn-lgk-frontier ks) c)))
                 (:instance fn-lg-scan-of-complete-append
                            (d (fn-bs-take (fn-lgk-frontier ks) c)) (prev genesis)
                            (x (append (nthcdr (fn-lgk-frontier ks) c) y)))
                 (:instance fn-lg-scan-last-of-complete-append
                            (d (fn-bs-take (fn-lgk-frontier ks) c)) (prev genesis)
                            (x (append (nthcdr (fn-lgk-frontier ks) c) y)))
                 (:instance fn-lg-scan-of-zero-front
                            (z (nthcdr (fn-lgk-frontier ks) c)) (prev (fn-lgk-last ks)))))))

(defthm fn-lgk-relp-content
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lgk-content-okp (fn-bs-durable-content bs ino) ks (fn-bs-unit bs) genesis max))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lgk-relp) (fn-lgk-content-okp fn-bs-durable-content)))))

(defun fn-lg-extension-written-state (bs ino next)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-bs-durable-content bs ino)))
    (mv-let (r s) (fn-bs-write bs ino (len c) (fn-bs-zeros (- (nfix next) (len c))) :ok)
      (declare (ignore r))
      s)))
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgx-floor-times
     (implies (and (natp l) (posp unit) (equal (mod l unit) 0))
              (and (natp (floor l unit)) (equal (* (floor l unit) unit) l))))
   (defthm fn-lgx-mod-sum
     (implies (and (natp a) (natp b) (posp unit)
                   (equal (mod a unit) 0) (equal (mod b unit) 0))
              (equal (mod (+ a b) unit) 0)))))
(local (defthm fn-lgx-written-state-parts
   (implies (and (null (fn-bs-pending bs)) (assoc-equal ino (fn-bs-inodes bs))
                 (< (len (fn-bs-durable-content bs ino)) (nfix next)))
            (let ((s (fn-lg-extension-written-state bs ino next))
                  (c (fn-bs-durable-content bs ino)))
              (and (equal (fn-bs-unit s) (fn-bs-unit bs))
                   (equal (fn-bs-durable-content s ino) c)
                   (equal (fn-bs-pending s)
                          (list (list :write ino (len c) (fn-bs-zeros (- (nfix next) (len c)))))))))
   :hints (("Goal" :in-theory (e/d (fn-bs-write fn-bs-durable-content) (fn-bs-zeros))))))
(local (defthm fn-lgx-len-append2 (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm fn-lgx-take-len-append
   (implies (true-listp c) (equal (fn-bs-take (len c) (append c y)) c))))
(local (defthm fn-lgx-apply-to-nil-true-listp (true-listp (fn-lg-apply-to nil ops))))

(defun fn-lg-extension-tail (bs ino next image)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-bs-durable-content bs ino)))
    (fn-lg-apply-to nil (fn-lg-pieces ino 0 (fn-bs-zeros (- (nfix next) (len c)))
                                      (fn-lg-crash-sels (fn-lg-extension-written-state bs ino next) image)
                                      (fn-bs-unit bs)))))
(local (defthm fn-lgx-written-crash-content
   (implies (and (null (fn-bs-pending bs)) (assoc-equal ino (fn-bs-inodes bs))
                 (posp (fn-bs-unit bs)) ino
                 (true-listp (fn-bs-durable-content bs ino))
                 (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)
                 (< (len (fn-bs-durable-content bs ino)) (nfix next))
                 (fn-bs-crash-imagep (fn-lg-extension-written-state bs ino next) image))
            (equal (fn-bs-durable-content image ino)
                   (append (fn-bs-durable-content bs ino) (fn-lg-extension-tail bs ino next image))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(fn-lg-extension-tail nfix natp posp append-to-nil
                                         (:type-prescription len) (:type-prescription fn-bs-zeros)
                                         fn-lgx-zeros-true-listp))
            :use ((:instance fn-lgx-written-state-parts)
                  (:instance fn-lgx-floor-times (l (len (fn-bs-durable-content bs ino)))
                             (unit (fn-bs-unit bs)))
                  (:instance fn-bs-crash-of-aligned-append
                             (s (fn-lg-extension-written-state bs ino next))
                             (k (floor (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)))
                             (d (fn-bs-durable-content bs ino)) (z nil)
                             (w (fn-bs-zeros (- (nfix next) (len (fn-bs-durable-content bs ino)))))))))))
(local (defthm fn-lgx-units-p-zero (fn-lgx-units-p 0 unit)))
(local (defthm fn-lgx-tail-units
   (implies (and (posp (fn-bs-unit bs))
                 (fn-lgx-units-p (nfix (- (nfix next) (len (fn-bs-durable-content bs ino)))) (fn-bs-unit bs)))
            (fn-lgx-units-p (len (fn-lg-extension-tail bs ino next image)) (fn-bs-unit bs)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(fn-lg-extension-tail fn-lgx-zeros-len natp fn-lgx-units-p-zero
                                                (:executable-counterpart fn-lgx-units-p)
                                                (:executable-counterpart len)))
            :use ((:instance fn-lgx-pieces-aligned2 (start 0) (unit (fn-bs-unit bs))
                             (w (fn-bs-zeros (- (nfix next) (len (fn-bs-durable-content bs ino)))))
                             (sels (fn-lg-crash-sels (fn-lg-extension-written-state bs ino next) image)))
                  (:instance fn-lgx-apply-aligned-keeps-units2 (c nil) (unit (fn-bs-unit bs))
                             (ops (fn-lg-pieces ino 0 (fn-bs-zeros (- (nfix next) (len (fn-bs-durable-content bs ino))))
                                                (fn-lg-crash-sels (fn-lg-extension-written-state bs ino next) image)
                                                (fn-bs-unit bs)))))))))
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgx-units-of-append
     (implies (and (posp unit) (true-listp c) (equal (mod (len c) unit) 0)
                   (fn-lgx-units-p (len y) unit))
              (equal (mod (len (append c y)) unit) 0))
     :hints (("Goal" :in-theory (disable fn-lgx-units-p)
              :use ((:instance fn-lgx-units-p-is-mod (n (len y)))))))
   (defthm fn-lgx-units-of-diff
     (implies (and (posp unit) (natp a) (natp b) (< b a)
                   (equal (mod a unit) 0) (equal (mod b unit) 0))
              (fn-lgx-units-p (nfix (- a b)) unit))
     :hints (("Goal" :use ((:instance fn-lgx-units-p-is-mod (n (- a b)))))))))
(local (defthm fn-lgx-tail-true-listp (true-listp (fn-lg-extension-tail bs ino next image))))
(local
 (defthm fn-lgx-growth-crash
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (natp next) (equal (mod next (fn-bs-unit bs)) 0)
                (< (len (fn-bs-durable-content bs ino)) next)
                (<= (+ (fn-lgk-frontier ks) *fn-frame-magic-octets*)
                    (len (fn-bs-durable-content bs ino)))
                (fn-bs-crash-imagep (fn-lg-extension-written-state bs ino next) image))
           (let ((content (fn-bs-durable-content image ino))
                 (c (fn-bs-durable-content bs ino))
                 (unit (fn-bs-unit bs)))
             (and (equal (fn-lg-scan content genesis unit max)
                         (cons (fn-lgk-committed ks) (fn-lgk-frontier ks)))
                  (equal (fn-lg-scan-last content genesis unit max) (fn-lgk-last ks))
                  (true-listp content)
                  (equal (mod (len content) unit) 0)
                  (equal (fn-bs-take (len c) content) c))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(natp posp nfix fn-lgx-take-len-append
                                        fn-lgx-true-listp-append fn-lgx-tail-true-listp (:type-prescription len)
                                        (:type-prescription fn-lg-apply-to)))
           :use ((:instance fn-lgk-relp-at-rest)
                 (:instance fn-lgk-relp-content (bs bs))
                 (:instance fn-lgx-written-crash-content)
                 (:instance fn-lgx-units-of-diff (a next) (b (len (fn-bs-durable-content bs ino)))
                            (unit (fn-bs-unit bs)))
                 (:instance fn-lgx-tail-units)
                 (:instance fn-lgx-units-of-append (unit (fn-bs-unit bs)) (c (fn-bs-durable-content bs ino))
                            (y (fn-lg-extension-tail bs ino next image)))
                 (:instance fn-lg-scan-past-a-resting-log
                            (c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs))
                            (y (fn-lg-extension-tail bs ino next image))))))))


(local (defthm fn-lgx-written-state-when-no-growth
  (implies (and (null (fn-bs-pending bs)) (<= (nfix next) (len (fn-bs-durable-content bs ino))))
           (equal (fn-lg-extension-written-state bs ino next) bs))
  :hints (("Goal" :in-theory (e/d (fn-bs-write) ())))))

(local (defthm fn-lgx-crash-of-quiet-state
  (implies (and (null (fn-bs-pending s)) (fn-bs-crash-imagep s image))
           (equal (fn-bs-durable-content image ino) (fn-bs-durable-content s ino)))
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep fn-bs-crash fn-bs-durable-content)))))

(local (defthm fn-lgx-no-growth-crash
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (<= (nfix next) (len (fn-bs-durable-content bs ino)))
                (<= (+ (fn-lgk-frontier ks) *fn-frame-magic-octets*)
                    (len (fn-bs-durable-content bs ino)))
                (fn-bs-crash-imagep (fn-lg-extension-written-state bs ino next) image))
           (let ((content (fn-bs-durable-content image ino))
                 (c (fn-bs-durable-content bs ino))
                 (unit (fn-bs-unit bs)))
             (and (equal (fn-lg-scan content genesis unit max)
                         (cons (fn-lgk-committed ks) (fn-lgk-frontier ks)))
                  (equal (fn-lg-scan-last content genesis unit max) (fn-lgk-last ks))
                  (true-listp content)
                  (equal (mod (len content) unit) 0)
                  (equal (fn-bs-take (len c) content) c))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-lgx-take-all fn-lgx-append-nil))
           :use ((:instance fn-lgk-relp-at-rest)
                 (:instance fn-lgk-relp-content)
                 (:instance fn-lgx-written-state-when-no-growth)
                 (:instance fn-lgx-crash-of-quiet-state (s bs))
                 (:instance fn-lg-scan-past-a-resting-log
                            (c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs)) (y nil)))))))

; KEYSTONE: every crash image at log-extended (the extension's zeros
; pending: any tear of them lands, is zeroed or garbled) scans to exactly the
; committed records and frontier, ends on the chain head, is a whole number
; of units and keeps the old segment's octets.  (With NEXT at or below the
; segment's end nothing is written and the image is the store at rest.)
(defthm fn-lg-extension-written-crash-reads-the-committed-records
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (equal (mod next (fn-bs-unit bs)) 0)
                (<= (+ (fn-lgk-frontier ks) *fn-frame-magic-octets*)
                    (len (fn-bs-durable-content bs ino)))
                (fn-bs-crash-imagep (fn-lg-extension-written-state bs ino next) image))
           (let ((content (fn-bs-durable-content image ino))
                 (c (fn-bs-durable-content bs ino))
                 (unit (fn-bs-unit bs)))
             (and (equal (fn-lg-scan content genesis unit max)
                         (cons (fn-lgk-committed ks) (fn-lgk-frontier ks)))
                  (equal (fn-lg-scan-last content genesis unit max) (fn-lgk-last ks))
                  (true-listp content)
                  (equal (mod (len content) unit) 0)
                  (equal (fn-bs-take (len c) content) c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '(nfix natp posp (:type-prescription len)))
           :cases ((< (len (fn-bs-durable-content bs ino)) next))
           :use ((:instance fn-lgx-growth-crash)
                 (:instance fn-lgx-no-growth-crash)
                 (:instance fn-lgk-relp-at-rest)
                 (:instance fn-lgx-next-natp (l (len (fn-bs-durable-content bs ino)))
                            (unit (fn-bs-unit bs)))))))

; The run's first two states (the extension written, log-extended) are the
; written state the crash keystone quantifies over.
(defthm fn-lg-extend-run-writes-first
  (implies (and (null (fn-bs-pending bs)) (assoc-equal ino (fn-bs-inodes bs))
                (< (len (fn-bs-durable-content bs ino)) (nfix next)))
           (let ((run (fn-lg-extend-run bs ks (fn-lg-extend-program next) nil ino)))
             (and (equal (car (nth 0 run)) (fn-lg-extension-written-state bs ino next))
                  (equal (car (nth 1 run)) (fn-lg-extension-written-state bs ino next)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write fn-bs-durable-content) (fn-bs-zeros)))))

; The host's target is a valid extent past the old one that holds the
; batch and the spare unit.
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgx-rounded-up
     (implies (and (natp need) (posp unit))
              (let ((r (* unit (ceiling need unit))))
                (and (natp r) (equal (mod r unit) 0) (<= need r)))))
   (defthm fn-lgx-twice-units
     (implies (and (natp e) (posp unit) (equal (mod e unit) 0))
              (equal (mod (* 2 e) unit) 0)))
   (defthm fn-lgx-rounded-past-a-small-extent
     (implies (and (natp e) (posp unit) (natp need)
                   (<= (* 2 e) (* unit (ceiling need unit))))
              (< e (max (* unit (ceiling need unit)) unit)))
     :rule-classes nil)))

(defthm fn-olr-extension-target-is-an-extent
  (implies (and (posp unit) (equal (mod extent unit) 0))
           (let ((next (fn-olr-extension-target frontier octets extent unit)))
             (and (natp next)
                  (equal (mod next unit) 0)
                  (< (nfix extent) next)
                  (<= (+ (nfix frontier) (nfix octets) unit) next))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-olr-extension-target)
                           (mod ceiling fn-lgx-rounded-up fn-lgx-twice-units))
           :use ((:instance fn-lgx-rounded-up (need (+ (nfix frontier) (nfix octets) unit)))
                 (:instance fn-lgx-twice-units (e (nfix extent)))
                 (:instance fn-lgx-rounded-past-a-small-extent (e (nfix extent))
                            (need (+ (nfix frontier) (nfix octets) unit)))))))
