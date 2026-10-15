; A5's exact approved statement was written before the controls and proof.
(in-package "ACL2")
(include-book "log-checkpoint-open-bound")
(include-book "log-checkpoint-bridge")
(include-book "defkeystone")
; (defthm fn-lc-open-reads-are-o-of-k
;   (let ((max (fn-lc-tail-max (fn-lc-cold-adopted-header disk r mode)))
;         (out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
;         (selection (fn-lc-open-selection disk r mode count segs
;                                          (fn-lc-cold-adopted-header disk r mode))))
;     (implies (and (fn-lbc-p fn-lbc) (fn-lc-segsp segs)
;                   (equal (car selection) :checkpoint)
;                   (natp k)
;                   (<= (len (fn-lc-selection-tail selection)) k))
;              (<= (fn-lc-read-octets (mv-nth 4 out))
;                  (+ (* 2 (fn-lc-root-slot-octets))
;                     (* (len (fn-lc-open-metadata-pages disk r mode))
;                        (fn-lc-page-octets))
;                     (* (+ 1 k) (fn-lc-entry-octets-bound max))))))
;   :rule-classes nil)
; Standing DROP: the two recognizers and NATP K are unnecessary. The stronger
; form below retains checkpoint selection and the actual suffix-length bound.
; The local include checks SAT, each remaining removal and the free-max mutant
; before the main proof. DEFTEETH requires an admitted theorem, so the same
; registration written in resume10/A5-TEETH-FIRST.lisp follows the proof.
(local (include-book "../tests/acl2/lc-composite-a5-tests"))

(local (defthm lc5-scale-bound
 (implies (and (natp a) (natp b) (<= a k))
  (<= (* (+ 1 a) b) (* (+ 1 k) b)))
 :rule-classes nil
 :hints (("Goal" :nonlinearp t
 :use ((:instance completion-of-< (x a) (y k))
       (:instance completion-of-< (x (* (+ 1 a) b)) (y (* (+ 1 k) b))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(natp unicity-of-1 unicity-of-0 distributivity commutativity-of-* commutativity-of-+
   associativity-of-+ fold-consts-in-+ rationalp-implies-acl2-numberp
   realpart imagpart complex-definition))))))

(local (defthm lc5-selected-header-by-definition
 (implies (equal (car (fn-lc-open-selection disk r mode count segs header)) :checkpoint)
  (equal header (fn-lc-adopted-header disk r mode)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-open-selection fn-lc-adopted-header car-cons cdr-cons
   (:executable-counterpart equal) (:executable-counterpart not)))))))

(local (defthm lc5-cold-entry-bridge
 (let* ((header (fn-lc-cold-adopted-header disk r mode))
        (selection (fn-lc-open-selection disk r mode count segs header)))
  (implies (equal (car selection) :checkpoint)
   (and (<= (len (fn-lc-cold-tail-entries disk r mode segs))
            (+ 1 (len (fn-lc-selection-tail selection))))
        (fn-lc-entries-boundedp (fn-lc-cold-tail-entries disk r mode segs)
                      (fn-lc-entry-octets-bound (fn-lc-tail-max header))))))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance lc5-selected-header-by-definition
    (header (fn-lc-cold-adopted-header disk r mode)))
  (:instance fn-lc-selected-tail-entry-bridge
    (header (fn-lc-cold-adopted-header disk r mode))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-cold-tail-entries fn-lc-tail-entries fn-lc-at-is-nth))))))

(local (defthm lc5-entry-bound-natp
 (natp (fn-lc-entry-octets-bound max))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-entry-octets-bound fn-lg-batch-entry-bound natp nfix max
   (:executable-counterpart binary-+)))))))

(local (defthm lc5-sum-bound
 (implies (and (natp bound) (fn-lc-entries-boundedp entries bound))
  (<= (fn-lc-tail-octets entries) (* (len entries) bound)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lc-tail-octets entries)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lc-tail-octets fn-lc-entries-boundedp natp nfix len
     (:induction fn-lc-tail-octets) distributivity commutativity-of-*
     commutativity-of-+ associativity-of-+ fold-consts-in-+
     (:type-prescription len)))))))

(local (defthm lc5-monotone-product
 (implies (and (natp a) (natp b) (<= a k))
  (<= (* a b) (* k b)))
 :rule-classes nil
 :hints (("Goal" :nonlinearp t
 :use ((:instance completion-of-< (x a) (y k))
       (:instance completion-of-< (x (* a b)) (y (* k b))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(natp unicity-of-1 unicity-of-0 distributivity commutativity-of-*
   commutativity-of-+ associativity-of-+ fold-consts-in-+
   rationalp-implies-acl2-numberp realpart imagpart complex-definition))))))

(local (defthm lc5-charge-of-bounded-count
 (implies (and (natp bound) (fn-lc-entries-boundedp entries bound)
               (<= (len entries) (+ 1 (len tail))) (<= (len tail) k))
  (<= (fn-lc-tail-octets entries) (* (+ 1 k) bound)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance lc5-sum-bound)
  (:instance lc5-monotone-product (a (len entries)) (b bound) (k (+ 1 (len tail))))
  (:instance lc5-scale-bound (a (len tail)) (b bound)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(natp (:type-prescription len)))))))

(defthm fn-lc-open-reads-are-o-of-k
 (let ((max (fn-lc-tail-max (fn-lc-cold-adopted-header disk r mode)))
      (out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
      (selection (fn-lc-open-selection disk r mode count segs
                   (fn-lc-cold-adopted-header disk r mode))))
  (implies (and (equal (car selection) :checkpoint) (<= (len (fn-lc-selection-tail selection)) k))
   (<= (fn-lc-read-octets (mv-nth 4 out))
    (+ (* 2 (fn-lc-root-slot-octets))
       (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
       (* (+ 1 k) (fn-lc-entry-octets-bound max))))))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance fn-lc-open-reads-bound)
  (:instance lc5-cold-entry-bridge)
  (:instance lc5-charge-of-bounded-count
   (entries (fn-lc-cold-tail-entries disk r mode segs))
   (tail (fn-lc-selection-tail
           (fn-lc-open-selection disk r mode count segs
             (fn-lc-cold-adopted-header disk r mode))))
   (bound (fn-lc-entry-octets-bound
           (fn-lc-tail-max (fn-lc-cold-adopted-header disk r mode))))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lc5-entry-bound-natp natp (:type-prescription len)
   fn-lc-root-slot-octets fn-lc-page-octets)))))

(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
; A5 reduced specification, written before its universal proof.
; Standing DROP candidates: fn-lbc-p, fn-lc-segsp, natp k.
(defteeth fn-lc-open-reads-are-o-of-k
 :claim (let ((max (fn-lc-tail-max (fn-lc-cold-adopted-header disk r mode)))
      (out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
      (selection (fn-lc-open-selection disk r mode count segs
                   (fn-lc-cold-adopted-header disk r mode))))
 (((chosen (equal (car selection) :checkpoint)) (within (<= (len (fn-lc-selection-tail selection)) k)))
 (<= (fn-lc-read-octets (mv-nth 4 out))
    (+ (* 2 (fn-lc-root-slot-octets))
       (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
       (* (+ 1 k) (fn-lc-entry-octets-bound max))))))
 :subject fn-lc-open
 :witness ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager)
   (configs (fn-lc-at 2 (lco-id5-input 1))) (frontier 8) (max-conns 4)
   (segs (fn-lc-at 3 (lco-id5-input 1)))
   (outcome (make-list 1100 :initial-element :ok)) (count 0) (k 0))
 :stobjs ((fn-lbc (fn-lc-open-bound-seed fn-lbc)))
 :stobj-checks (((let ((max (fn-lc-tail-max (fn-lc-cold-adopted-header disk r mode)))
      (out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
      (selection (fn-lc-open-selection disk r mode count segs
                   (fn-lc-cold-adopted-header disk r mode)))) (declare (ignorable max out selection)) (equal (car selection) :checkpoint))
 (lca5-tooth :chosen disk r mode configs frontier max-conns segs outcome count k fn-lbc)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-tooth lca5-fast-compact-is-the-formula-vector
   lca5-fast-compact-car-is-the-formula-vector lca5-formula-vector fn-ag-less
   fn-lc-at-is-nth nth mv-nth car-cons cdr-cons
   (:type-prescription lca5-fast-compact)
   (:executable-counterpart zp) (:executable-counterpart equal)
   (:executable-counterpart fn-lc-entry-octets-bound))))))
((let ((max (fn-lc-tail-max (fn-lc-cold-adopted-header disk r mode)))
      (out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
      (selection (fn-lc-open-selection disk r mode count segs
                   (fn-lc-cold-adopted-header disk r mode)))) (declare (ignorable max out selection)) (<= (len (fn-lc-selection-tail selection)) k))
 (lca5-tooth :tail disk r mode configs frontier max-conns segs outcome count k fn-lbc)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-tooth lca5-fast-compact-is-the-formula-vector
   lca5-fast-compact-car-is-the-formula-vector lca5-formula-vector fn-ag-less
   fn-lc-at-is-nth nth mv-nth car-cons cdr-cons
   (:type-prescription lca5-fast-compact)
   (:executable-counterpart zp) (:executable-counterpart equal)
   (:executable-counterpart fn-lc-entry-octets-bound))))))
((let ((max (fn-lc-tail-max (fn-lc-cold-adopted-header disk r mode)))
      (out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
      (selection (fn-lc-open-selection disk r mode count segs
                   (fn-lc-cold-adopted-header disk r mode)))) (declare (ignorable max out selection)) (<= (fn-lc-read-octets (mv-nth 4 out))
    (+ (* 2 (fn-lc-root-slot-octets))
       (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
       (* (+ 1 k) (fn-lc-entry-octets-bound max)))))
 (lca5-tooth :post disk r mode configs frontier max-conns segs outcome count k fn-lbc)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-tooth lca5-fast-compact-is-the-formula-vector
   lca5-fast-compact-car-is-the-formula-vector lca5-formula-vector fn-ag-less
   fn-lc-at-is-nth nth mv-nth car-cons cdr-cons
   (:type-prescription lca5-fast-compact)
   (:executable-counterpart zp) (:executable-counterpart equal)
   (:executable-counterpart fn-lc-entry-octets-bound))))))
((let ((max (fn-lc-tail-max (fn-lc-cold-adopted-header disk r mode)))
      (out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
      (selection (fn-lc-open-selection disk r mode count segs
                   (fn-lc-cold-adopted-header disk r mode)))) (declare (ignorable max out selection)) (<= (fn-lc-read-octets (mv-nth 4 out))
    (+ (* 2 (fn-lc-root-slot-octets))
       (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
       (* (+ 1 k) (fn-lc-entry-octets-bound 0)))))
 (lca5-tooth :oldmax disk r mode configs frontier max-conns segs outcome count k fn-lbc)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-tooth lca5-fast-compact-is-the-formula-vector
   lca5-fast-compact-car-is-the-formula-vector lca5-formula-vector fn-ag-less
   fn-lc-at-is-nth nth mv-nth car-cons cdr-cons
   (:type-prescription lca5-fast-compact)
   (:executable-counterpart zp) (:executable-counterpart equal)
   (:executable-counterpart fn-lc-entry-octets-bound)))))))
 :breaks ((chosen ((disk (fn-lc-at 0 (lcx-limit-input)))
    (configs (fn-lc-at 2 (lcx-limit-input))) (segs (lca5p-segs))
    (outcome '(:ok :ok :ok :ok :ok :ok :ok :ok :ok :ok)) (count -1) (k 0)))
  (within ((segs '((0 (65) nil) (1 nil nil))) (k -1))))
 :mutations ((free-max-zero (:conclusion (<= (fn-lc-read-octets (mv-nth 4 out))
    (+ (* 2 (fn-lc-root-slot-octets))
       (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
       (* (+ 1 k) (fn-lc-entry-octets-bound 0)))))
   ((disk (fn-lc-at 0 (lcx-limit-input))) (configs (fn-lc-at 2 (lcx-limit-input)))
    (segs (lcx-limit-segs)) (outcome '(:ok :ok :ok :ok :ok :ok :ok :ok))
    (count 0) (k 0))
   :fault "A4 free max=0 undercharges the original wide terminal frame by one octet")))
)
(defteeth-check (fn-lc-open-reads-are-o-of-k))
