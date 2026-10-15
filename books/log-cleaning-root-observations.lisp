; Root publication/open captures the segment dependency set once. Unlink
; consumes that observation; it does not reopen or revalidate the root.
; The physical-record projection uses PGS's actual records and LC's actual
; adopted columns. No live set is inferred from a successful post-unlink read.
(in-package "ACL2")
(include-book "log-cleaning-images")

(defun-nx fn-lc-prefix-locator-segments (i n fn-lbc)
 (declare (xargs :measure (nfix n)))
 (if (zp (nfix n)) nil
  (cons (ec-call (fn-lbc-loc0 (nfix i) fn-lbc))
        (fn-lc-prefix-locator-segments (+ 1 (nfix i)) (1- (nfix n)) fn-lbc))))
(defun fn-lc-segment-ids-from (first segs)
 (declare (xargs :guard t))
 (if (consp segs)
  (if (<= (nfix first) (nfix (fn-lc-head (car segs))))
      (cons (fn-lc-head (car segs)) (fn-lc-segment-ids-from first (cdr segs)))
    (fn-lc-segment-ids-from first (cdr segs))) nil))
(defun-nx fn-lc-slot-needed-segments (disk r mode slot segs)
 (let* ((physical (fn-lc-physical-disk disk))
        (record (pgs-slot slot (pgs-root-slots r physical)))
        (single (pgs-set-root-slot r (if (equal slot 1) 0 1) nil physical))
        (header (fn-lc-cold-adopted-header single r mode))
        (fn-lbc (create-fn-lbc))
        (adopted (ec-call (fn-lc-adopt single r mode segs fn-lbc)))
        (fn-lbc (mv-nth 1 adopted)))
  (if (not (pgs-rec-valid record)) nil
   ; Prefix sources are needed even when a tail MOVE subsequently replaces
   ; their locators. S and every examined tail segment are needed as well.
   (union-equal
    (fn-lc-prefix-locator-segments 0 (ec-call (fn-lbc-count fn-lbc)) fn-lbc)
    (cons (fn-lc-at 0 (fn-lc-header-S header))
          (fn-lc-segment-ids-from (fn-lc-at 0 (fn-lc-header-S header)) segs))))))
(defun-nx fn-lc-slot-observation-boundp (disk r slot segs)
 (let ((observed (pgs-slot slot (pgs-root-slots r disk))))
  (or (not (equal (fn-lc-head observed) :lc-slot-observation))
      (and (true-listp observed) (equal (len observed) 3)
           (true-listp (fn-lc-at 2 observed))
           (subsetp-equal
            (union-equal (fn-lc-slot-needed-segments disk r :eager slot segs)
                         (fn-lc-slot-needed-segments disk r :lazy slot segs))
            (fn-lc-at 2 observed))))))
(defun-nx fn-lc-roots-resolvep (disk r segs)
 (and (fn-lc-segsp segs)
      (fn-lc-slot-observation-boundp disk r 0 segs)
      (fn-lc-slot-observation-boundp disk r 1 segs)
      (fn-lc-open-image-resolvesp (fn-lc-pgs-slot-open disk r :eager 0 segs) segs)
      (fn-lc-open-image-resolvesp (fn-lc-pgs-slot-open disk r :eager 1 segs) segs)
      (fn-lc-open-image-resolvesp (fn-lc-pgs-slot-open disk r :lazy 0 segs) segs)
      (fn-lc-open-image-resolvesp (fn-lc-pgs-slot-open disk r :lazy 1 segs) segs)))

(defun-nx fn-lc-capture-slot-observation (disk r slot segs)
 (let* ((physical (fn-lc-physical-disk disk))
        (record (pgs-slot slot (pgs-root-slots r physical))))
  (if (and (pgs-rec-valid record)
           (equal (fn-lc-head (fn-lc-pgs-slot-open physical r :eager slot segs)) :ok)
           (equal (fn-lc-head (fn-lc-pgs-slot-open physical r :lazy slot segs)) :ok))
      (list :lc-slot-observation record
       (union-equal (fn-lc-slot-needed-segments physical r :eager slot segs)
                    (fn-lc-slot-needed-segments physical r :lazy slot segs)))
    record)))
(defun-nx fn-lc-capture-root-observations (disk r segs)
 (let ((physical (fn-lc-physical-disk disk)))
  (cons (pgs-pages physical)
    (cons (cons r (cons (fn-lc-capture-slot-observation physical r 0 segs)
                       (fn-lc-capture-slot-observation physical r 1 segs)))
          (pgs-roots physical)))))

(verify-guards fn-lc-prefix-locator-segments)

(local (defthm lcro-prefix-locators-are-list
 (true-listp (fn-lc-prefix-locator-segments i n fn-lbc))
 :hints (("Goal" :induct (fn-lc-prefix-locator-segments i n fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-prefix-locator-segments true-listp (:induction fn-lc-prefix-locator-segments)
 car-cons cdr-cons (:executable-counterpart true-listp)))))))

(local (defthm lcro-tail-ids-are-list
 (true-listp (fn-lc-segment-ids-from first segs))
 :hints (("Goal" :induct (fn-lc-segment-ids-from first segs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-segment-ids-from true-listp (:induction fn-lc-segment-ids-from)
 car-cons cdr-cons (:executable-counterpart true-listp)))))))

(local (defthm lcro-union-is-list
 (implies (true-listp b) (true-listp (union-equal a b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'minimal-theory)
 '(union-equal true-listp len (:induction len) car-cons cdr-cons))))))

(local (defthm lcro-needed-is-list
 (true-listp (fn-lc-slot-needed-segments disk r mode slot segs))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-slot-needed-segments lcro-prefix-locators-are-list
 lcro-tail-ids-are-list lcro-union-is-list true-listp car-cons cdr-cons
 (:executable-counterpart true-listp)))))))

(verify-guards fn-lc-slot-needed-segments
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lcro-prefix-locators-are-list  lcro-tail-ids-are-list
 lcro-union-is-list true-listp car-cons cdr-cons)))))

(verify-guards fn-lc-slot-observation-boundp
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lcro-needed-is-list lcro-union-is-list)))))

(verify-guards fn-lc-roots-resolvep)

(verify-guards fn-lc-capture-slot-observation
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lcro-needed-is-list lcro-union-is-list)))))

(verify-guards fn-lc-capture-root-observations)
