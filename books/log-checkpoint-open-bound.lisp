; A3: metadata-format read charge for the actual LC cold open.
(in-package "ACL2")
(include-book "log-checkpoint-open")
(include-book "defkeystone")
; Statement FIRST, before the definitions, controls and proof below.
; ; A3: coordinator-approved all-examined-candidate metadata allowance.
; ; Addresses come from the checkpoint format, never from requests.
; ; Tail follows the actual metadata-only selected checkpoint.
; ; The former fn-lbc-p and fn-lc-segsp hypotheses are proposed DROPs: the
; ; charge is independent of the initial stobj and all list-shaped inputs.
; ; Their redundancy must be proved mechanically before these forms count.
; ; SAT empty/page99/late-control, old-text mutation on late-control.
; ; Selected-only removal: the same late-control fallback; mutation: omit one page.
; (defthm fn-lc-open-reads-bound
;  (let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))
;   (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))
;  :rule-classes nil)
; 
; (defthm fn-lc-open-reads-bound-without-fallback
;  (let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))
;   (implies (fn-lc-first-candidate-selectedp disk r mode)
;    (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (len (fn-lc-selected-metadata-pages disk r mode)) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs))))))
;  :rule-classes nil)

(defun fn-lc-open-metadata-pages (disk r mode)
 (declare (xargs :guard t) (ignore mode))
 (fn-lc-record-metadata-addresses-order (fn-lc-cold-root-order disk r)
                                       (pgs-root-slots r disk) (pgs-pages disk)))
(defun fn-lc-selected-metadata-pages (disk r mode)
 (declare (xargs :guard t))
 (let* ((choice (fn-lc-cold-pgs-choice disk r mode))
        (rec (pgs-slot (fn-lc-at 1 choice) (pgs-root-slots r disk))))
  (fn-lc-record-metadata-addresses rec (pgs-pages disk))))
; No semantic disk-validity premise: this says which PGS-order slot won.
(defun fn-lc-first-candidate-selectedp (disk r mode)
 (declare (xargs :guard t))
 (let ((choice (fn-lc-cold-pgs-choice disk r mode))
       (order (fn-lc-cold-root-order disk r)))
  (and (equal (fn-lc-head choice) :ok)
       (equal (fn-lc-at 1 choice) (fn-lc-head order)))))

; Cost-observation controls, not a second implementation of open.
(defun fn-lc-open-bound-limit (disk r mode segs style)
 (declare (xargs :guard t))
 (+ (* 2 (fn-lc-root-slot-octets))
    (* (if (equal style :old) (len (fn-lc-directory-path-pages disk r mode))
         (if (or (equal style :selected) (equal style :short))
             (if (equal style :short)
                 (nfix (1- (len (fn-lc-selected-metadata-pages disk r mode))))
               (len (fn-lc-selected-metadata-pages disk r mode)))
           (len (fn-lc-open-metadata-pages disk r mode))))
       (fn-lc-page-octets))
    (fn-lc-tail-octets (if (equal style :old) (fn-lc-tail-entries disk r mode segs)
                        (fn-lc-cold-tail-entries disk r mode segs)))))
(defun fn-lc-open-bound-seed (fn-lbc)
 (declare (xargs :stobjs fn-lbc)) fn-lbc)
(defun fn-lc-open-bound-tooth
 (style disk r mode configs frontier max-conns segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (if (equal style :first)
     (mv (fn-lc-first-candidate-selectedp disk r mode) fn-lbc)
   (let ((limit (fn-lc-open-bound-limit disk r mode segs style)))
    (mv-let (answer fn-lbc after-disk after-segs trace owner)
      (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)
      (declare (ignore answer after-disk after-segs owner))
      (mv (<= (fn-lc-read-octets trace) limit) fn-lbc)))))
(verify-guards fn-lc-open-bound-tooth)

(local (include-book "../tests/acl2/lc-cold-control-fallback-tests"))
(local (defun lco-a3-observe (disk input fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let ((before (fn-lbc-p fn-lbc)) (segs (fn-lc-at 3 input)))
  (mv-let (answer fn-lbc after-disk after-segs trace owner)
    (fn-lc-open disk :lc :eager (fn-lc-at 2 input) 8 4 segs (fn-lc-at 4 input) fn-lbc)
    (declare (ignore after-disk after-segs owner))
    (mv (list before (fn-lc-segsp segs) answer (fn-lc-read-octets trace)
              (fn-lc-open-bound-limit disk :lc :eager segs :a3)
              (fn-lc-open-bound-limit disk :lc :eager segs :selected)
              (fn-lc-open-bound-limit disk :lc :eager segs :old)
              (fn-lc-first-candidate-selectedp disk :lc :eager)) fn-lbc)))))
(local (defun lco-a3-fixture (kind)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((input (lco-id5-input 1))
        (disk (case kind (:page99 (lcc-fallback-disk))
                        (:late (lcc-late-fallback-disk))
                        (otherwise (fn-lc-at 0 input)))))
  (with-local-stobj fn-lbc
    (mv-let (result fn-lbc) (lco-a3-observe disk input fn-lbc) result)))))
(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
 ; Whole original type antecedents AND new A3 conclusion on all three fixtures.
 (assert-event
  (let ((out (lco-a3-fixture :empty)))
   (and (fn-lc-at 0 out) (fn-lc-at 1 out) (equal (fn-lc-at 2 out) :ok)
        (equal (fn-lc-at 3 out) 82180) (equal (fn-lc-at 4 out) 82180)
        (<= (fn-lc-at 3 out) (fn-lc-at 4 out))
        (fn-lc-at 7 out) (<= (fn-lc-at 3 out) (fn-lc-at 5 out)))))
 (assert-event
  (let ((out (lco-a3-fixture :page99)))
   (and (fn-lc-at 0 out) (fn-lc-at 1 out) (equal (fn-lc-at 2 out) :ok)
        (equal (fn-lc-at 3 out) 98564) (equal (fn-lc-at 4 out) 98564)
        (<= (fn-lc-at 3 out) (fn-lc-at 4 out)))))
 (assert-event
  (let ((out (lco-a3-fixture :late)))
   (and (fn-lc-at 0 out) (fn-lc-at 1 out) (equal (fn-lc-at 2 out) :ok)
        (equal (fn-lc-at 3 out) 164100) (equal (fn-lc-at 4 out) 164100)
        (<= (fn-lc-at 3 out) (fn-lc-at 4 out))
        (not (fn-lc-at 7 out))
        (> (fn-lc-at 3 out) (fn-lc-at 5 out))
        (> (fn-lc-at 3 out) (fn-lc-at 6 out)))))
 ; Biting selected-only mutation: charge one fewer format page, even without fallback.
 (assert-event
  (let ((out (lco-a3-fixture :empty)))
    (> (fn-lc-at 3 out) (- (fn-lc-at 5 out) (fn-lc-page-octets)))))
 (value-triple (list (lco-a3-fixture :empty) (lco-a3-fixture :page99) (lco-a3-fixture :late))))
; Controls and the complete registered package specification precede proof.

; (defteeth fn-lc-open-reads-bound
;  :claim (let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (() (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs))))))
;  :subject fn-lc-open
;  :witness ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager)
;  (configs (fn-lc-at 2 (lco-id5-input 1))) (frontier 8) (max-conns 4)
;  (segs (fn-lc-at 3 (lco-id5-input 1))) (outcome (fn-lc-at 4 (lco-id5-input 1))))
;  :stobjs ((fn-lbc (fn-lc-open-bound-seed fn-lbc)))
;  :stobj-checks (((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))
;  (fn-lc-open-bound-tooth :a3 disk r mode configs frontier max-conns segs outcome fn-lbc)
;  :hints (("Goal" :in-theory (e/d (fn-lc-open-bound-tooth fn-lc-open-bound-limit)
;   (fn-lc-open fn-lc-open-metadata-pages fn-lc-selected-metadata-pages
;    fn-lc-directory-path-pages fn-lc-tail-entries fn-lc-cold-tail-entries
;    fn-lc-first-candidate-selectedp fn-lc-read-octets fn-lc-tail-octets))))) ((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (len (fn-lc-directory-path-pages disk r mode)) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-tail-entries disk r mode segs)))))
;  (fn-lc-open-bound-tooth :old disk r mode configs frontier max-conns segs outcome fn-lbc)
;  :hints (("Goal" :in-theory (e/d (fn-lc-open-bound-tooth fn-lc-open-bound-limit)
;   (fn-lc-open fn-lc-open-metadata-pages fn-lc-selected-metadata-pages
;    fn-lc-directory-path-pages fn-lc-tail-entries fn-lc-cold-tail-entries
;    fn-lc-first-candidate-selectedp fn-lc-read-octets fn-lc-tail-octets))))))
;  :breaks nil
;  :mutations ((old-selected-path-allowance (:conclusion (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (len (fn-lc-directory-path-pages disk r mode)) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-tail-entries disk r mode segs)))))
;  ((disk (lcc-late-fallback-disk)))
;  :fault "old allowance drops rejected metadata; original late-control tooth must bite")))
; (defteeth fn-lc-open-reads-bound-without-fallback
;  :claim (let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))
;   (((no-fallback (fn-lc-first-candidate-selectedp disk r mode))) (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (len (fn-lc-selected-metadata-pages disk r mode)) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs))))))
;  :subject fn-lc-open
;  :witness ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager)
;  (configs (fn-lc-at 2 (lco-id5-input 1))) (frontier 8) (max-conns 4)
;  (segs (fn-lc-at 3 (lco-id5-input 1))) (outcome (fn-lc-at 4 (lco-id5-input 1))))
;  :stobjs ((fn-lbc (fn-lc-open-bound-seed fn-lbc)))
;  :stobj-checks (((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (fn-lc-first-candidate-selectedp disk r mode))
;  (fn-lc-open-bound-tooth :first disk r mode configs frontier max-conns segs outcome fn-lbc)
;  :hints (("Goal" :in-theory (e/d (fn-lc-open-bound-tooth fn-lc-open-bound-limit)
;   (fn-lc-open fn-lc-open-metadata-pages fn-lc-selected-metadata-pages
;    fn-lc-directory-path-pages fn-lc-tail-entries fn-lc-cold-tail-entries
;    fn-lc-first-candidate-selectedp fn-lc-read-octets fn-lc-tail-octets)))))
;  ((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (len (fn-lc-selected-metadata-pages disk r mode)) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))
;  (fn-lc-open-bound-tooth :selected disk r mode configs frontier max-conns segs outcome fn-lbc)
;  :hints (("Goal" :in-theory (e/d (fn-lc-open-bound-tooth fn-lc-open-bound-limit)
;   (fn-lc-open fn-lc-open-metadata-pages fn-lc-selected-metadata-pages
;    fn-lc-directory-path-pages fn-lc-tail-entries fn-lc-cold-tail-entries
;    fn-lc-first-candidate-selectedp fn-lc-read-octets fn-lc-tail-octets))))) ((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (nfix (1- (len (fn-lc-selected-metadata-pages disk r mode)))) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))
;  (fn-lc-open-bound-tooth :short disk r mode configs frontier max-conns segs outcome fn-lbc)
;  :hints (("Goal" :in-theory (e/d (fn-lc-open-bound-tooth fn-lc-open-bound-limit)
;   (fn-lc-open fn-lc-open-metadata-pages fn-lc-selected-metadata-pages
;    fn-lc-directory-path-pages fn-lc-tail-entries fn-lc-cold-tail-entries
;    fn-lc-first-candidate-selectedp fn-lc-read-octets fn-lc-tail-octets))))))
;  :breaks ((no-fallback ((disk (lcc-late-fallback-disk)))))
;  :mutations ((omits-selected-metadata-page (:conclusion (<= (fn-lc-read-octets (mv-nth 4 out))
;      (+ (* 2 (fn-lc-root-slot-octets))
;         (* (nfix (1- (len (fn-lc-selected-metadata-pages disk r mode)))) (fn-lc-page-octets))
;         (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))
;  nil :fault "even the first-candidate case must charge its final metadata page")))

; Proof and registry: controls above were checked first.
(local (defthm lca3-read-natural
 (natp (fn-lc-read-octets trace)) :rule-classes :type-prescription))
(local (defthm lca3-read-cons-unfolds
 (equal (fn-lc-read-octets (cons request rest))
  (+ (if (equal (car request) :pread) (nfix (nth 3 request)) 0)
     (fn-lc-read-octets rest)))))
(local (defthm lca3-read-nil-unfolds (equal (fn-lc-read-octets nil) 0)))
(local (defthm lca3-read-of-append
 (equal (fn-lc-read-octets (append a b))
        (+ (fn-lc-read-octets a) (fn-lc-read-octets b)))))
(local (defthm lca3-read-of-take
 (implies (natp n)
  (<= (fn-lc-read-octets (take n trace)) (fn-lc-read-octets trace)))
 
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :induct (take n trace) :in-theory (enable take nth)))))
(local (defthm lca3-read-of-pages
 (equal (fn-lc-read-octets (fn-lc-cold-page-program pages))
        (* (len pages) (fn-lc-page-octets)))))
(local (defthm lca3-read-of-tail
 (equal (fn-lc-read-octets (fn-lc-open-tail-program entries))
        (fn-lc-tail-octets entries))))
(local (defthm lca3-memo-length
 (<= (len (fn-lc-cold-first-requests pages seen)) (len pages))
 
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :induct (fn-lc-cold-first-requests pages seen)))))
(local (defthm lca3-prefix-length
 (implies (fn-lc-cold-prefix-p prefix whole) (<= (len prefix) (len whole)))
 :rule-classes (:rewrite :linear)
 ))
(local (defthm lca3-candidate-prefix-length
 (implies (fn-lc-cold-candidate-prefix-p (fn-lc-cold-candidate rec pages) rec pages)
  (<= (len (fn-lc-record-checked-metadata-path rec pages))
      (len (fn-lc-record-metadata-addresses rec pages))))
 
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :in-theory
  (e/d (fn-lc-cold-candidate-prefix-p)
       (fn-lc-record-checked-metadata-path fn-lc-record-metadata-addresses fn-lc-cold-candidate))))))
(local (defthm lca3-path-length
 (implies (fn-lc-cold-candidate-prefixes-p order slots pages)
  (<= (len (fn-lc-record-checked-path-order order slots pages))
      (len (fn-lc-record-metadata-addresses-order order slots pages))))
 
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :induct (fn-lc-record-checked-path-order order slots pages)
  :in-theory (disable fn-lc-cold-candidate fn-lc-cold-candidate-prefix-p
      fn-lc-record-checked-metadata-path fn-lc-record-metadata-addresses)))))
(local (defthm lca3-selection-read-bound
 (<= (fn-lc-read-octets (nth 5 (fn-lc-cold-select disk r mode)))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))))
 
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :use ((:instance fn-lc-cold-selection-is-metadata-only))
  :in-theory
  (e/d (fn-lc-open-metadata-pages)
       (fn-lc-cold-select fn-lc-cold-pgs-choice fn-lc-cold-root-order
        fn-lc-cold-candidate-prefixes-p fn-lc-record-checked-path-order
        fn-lc-record-metadata-addresses-order fn-lc-cold-first-requests
        fn-lc-cold-page-program fn-lc-read-octets
        fn-lc-cold-only-metadata-requests-p))))))
(local (defthm lca3-program-bound
 (<= (fn-lc-read-octets (fn-lc-open-program disk r mode segs))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs))))
 
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :use ((:instance lca3-selection-read-bound)) :in-theory
  (e/d (fn-lc-open-program)
       (fn-lc-cold-select fn-lc-cold-tail-entries fn-lc-open-metadata-pages
        fn-lc-open-tail-program fn-lc-tail-octets fn-lc-read-octets))))))
(local (defthm lca3-open-trace-by-definition
 (equal (mv-nth 4 (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
        (take (min (+ 1 (fn-lc-outcome-ok-count outcome (len (fn-lc-open-program disk r mode segs))))
                   (len (fn-lc-open-program disk r mode segs)))
              (fn-lc-open-program disk r mode segs)))
 :hints (("Goal" :in-theory
  (union-theories '(fn-lc-open fn-lc-at-is-nth fn-lc-take-is-take fn-lc-head
     nth mv-nth not min (:executable-counterpart binary-+) (:executable-counterpart <)
     (:executable-counterpart zp) (:executable-counterpart equal)
     car-cons cdr-cons) (theory 'minimal-theory))))))
(local (defthm lca3-first-choice-reduces-allowance
 (implies (fn-lc-first-candidate-selectedp disk r mode)
  (equal (fn-lc-open-metadata-pages disk r mode)
         (fn-lc-selected-metadata-pages disk r mode)))
 :hints (("Goal" :in-theory
  (e/d (fn-lc-first-candidate-selectedp fn-lc-open-metadata-pages
        fn-lc-selected-metadata-pages fn-lc-cold-root-order fn-lc-cold-pgs-choice
        fn-lc-cold-pgs-choice-order fn-lc-record-metadata-addresses-order pgs-open-order)
       (fn-lc-cold-candidate fn-lc-record-metadata-addresses pgs-root-slots pgs-pages
        pgs-rec-valid pgs-rec-txid fn-lc-cold-slot-refusals))))))
(local (defthm lca3-pgs-order-at-most-two
 (<= (len (fn-lc-cold-root-order disk r)) 2)
 :hints (("Goal" :in-theory (enable fn-lc-cold-root-order pgs-open-order)))
 :rule-classes :linear))

(defthm fn-lc-open-reads-bound
 (let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))
  (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))

 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories
   '(lca3-open-trace-by-definition (:type-prescription fn-lc-outcome-ok-count)
     (:type-prescription len) min natp natp-compound-recognizer
     fn-lc-root-slot-octets fn-lc-page-octets)
   (theory 'minimal-theory))
  :use ((:instance lca3-program-bound)
        (:instance lca3-read-of-take
   (n (min (+ 1 (fn-lc-outcome-ok-count outcome (len (fn-lc-open-program disk r mode segs))))
           (len (fn-lc-open-program disk r mode segs))))
   (trace (fn-lc-open-program disk r mode segs)))))))
(defthm fn-lc-open-reads-bound-without-fallback
 (let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))
  (implies (fn-lc-first-candidate-selectedp disk r mode)
   (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-selected-metadata-pages disk r mode)) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs))))))

 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lc-open-reads-bound))
  :in-theory (union-theories '(lca3-first-choice-reduces-allowance)
                             (theory 'minimal-theory)))))
(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
(defteeth fn-lc-open-reads-bound
 :claim (let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (() (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs))))))
 :subject fn-lc-open
 :witness ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager)
 (configs (fn-lc-at 2 (lco-id5-input 1))) (frontier 8) (max-conns 4)
 (segs (fn-lc-at 3 (lco-id5-input 1))) (outcome (fn-lc-at 4 (lco-id5-input 1))))
 :stobjs ((fn-lbc (fn-lc-open-bound-seed fn-lbc)))
 :stobj-checks (((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))
 (fn-lc-open-bound-tooth :a3 disk r mode configs frontier max-conns segs outcome fn-lbc)
 :hints (("Goal" :in-theory (union-theories '(fn-lc-open-bound-tooth fn-lc-open-bound-limit
   mv-nth car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart zp))
   (theory 'minimal-theory))))) ((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-directory-path-pages disk r mode)) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-tail-entries disk r mode segs)))))
 (fn-lc-open-bound-tooth :old disk r mode configs frontier max-conns segs outcome fn-lbc)
 :hints (("Goal" :in-theory (union-theories '(fn-lc-open-bound-tooth fn-lc-open-bound-limit
   mv-nth car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart zp))
   (theory 'minimal-theory))))))
 :breaks nil
 :mutations ((old-selected-path-allowance (:conclusion (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-directory-path-pages disk r mode)) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-tail-entries disk r mode segs)))))
 ((disk (lcc-late-fallback-disk)))
 :fault "old allowance drops rejected metadata; original late-control tooth must bite")))
(defteeth fn-lc-open-reads-bound-without-fallback
 :claim (let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))
  (((no-fallback (fn-lc-first-candidate-selectedp disk r mode))) (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-selected-metadata-pages disk r mode)) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs))))))
 :subject fn-lc-open
 :witness ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager)
 (configs (fn-lc-at 2 (lco-id5-input 1))) (frontier 8) (max-conns 4)
 (segs (fn-lc-at 3 (lco-id5-input 1))) (outcome (fn-lc-at 4 (lco-id5-input 1))))
 :stobjs ((fn-lbc (fn-lc-open-bound-seed fn-lbc)))
 :stobj-checks (((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (fn-lc-first-candidate-selectedp disk r mode))
 (fn-lc-open-bound-tooth :first disk r mode configs frontier max-conns segs outcome fn-lbc)
 :hints (("Goal" :in-theory (union-theories '(fn-lc-open-bound-tooth fn-lc-open-bound-limit
   mv-nth car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart zp))
   (theory 'minimal-theory)))))
 ((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (len (fn-lc-selected-metadata-pages disk r mode)) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))
 (fn-lc-open-bound-tooth :selected disk r mode configs frontier max-conns segs outcome fn-lbc)
 :hints (("Goal" :in-theory (union-theories '(fn-lc-open-bound-tooth fn-lc-open-bound-limit
   mv-nth car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart zp))
   (theory 'minimal-theory))))) ((let ((out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))) (declare (ignorable out)) (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (nfix (1- (len (fn-lc-selected-metadata-pages disk r mode)))) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))
 (fn-lc-open-bound-tooth :short disk r mode configs frontier max-conns segs outcome fn-lbc)
 :hints (("Goal" :in-theory (union-theories '(fn-lc-open-bound-tooth fn-lc-open-bound-limit
   mv-nth car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart zp))
   (theory 'minimal-theory))))))
 :breaks ((no-fallback ((disk (lcc-late-fallback-disk)))))
 :mutations ((omits-selected-metadata-page (:conclusion (<= (fn-lc-read-octets (mv-nth 4 out))
     (+ (* 2 (fn-lc-root-slot-octets))
        (* (nfix (1- (len (fn-lc-selected-metadata-pages disk r mode)))) (fn-lc-page-octets))
        (fn-lc-tail-octets (fn-lc-cold-tail-entries disk r mode segs)))))
 nil :fault "even the first-candidate case must charge its final metadata page")))
)
(defteeth-check (fn-lc-open-reads-bound fn-lc-open-reads-bound-without-fallback))
