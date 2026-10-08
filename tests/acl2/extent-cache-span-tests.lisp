; Slot-cache span and charge-ownership teeth. Public theorem variables name
; logical snapshots; registered ground lemmas check the entire claims. The
; native assertion below separately checks the same span on real stobjs.
(in-package "ACL2")
(include-book "../../books/extent-cache")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *xcst-token* '(:window 7 11 100 3 100 3 0 77))
(defconst *xcst-plan* (list :verified 11 100 3 0 3 77 0 7 47 *xcst-token* 100 3 0))
(defconst *xcst-worker* (list 0 7 :returned *xcst-token*))
(defconst *xcst-returned* (list nil nil nil (list (cons *xcst-token* '((16 0 0 0 0) :window :returned 0))) nil))
(defconst *xcst-cached* (list nil nil nil (list (cons *xcst-token* '((16 0 0 0 0) :cached nil))) nil))
(defconst *xcst-slots* '((2 t 7 0 11 100 3 100 3 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0)))
(defconst *xcst-duplicate-slots* '((2 t 7 0 11 100 3 100 3 0 0 0 77 0) (2 t 7 0 11 100 3 100 3 1 0 0 77 1)))
(defconst *xcst-whole-slots* '((1 t 7 9 11 100 3 0 0 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0)))
(defconst *xcst-cells* '(1 0 2))
(defconst *xcst-window* (list (append '(1 2 3) (make-list (- *fn-ew-span-capacity* 3) :initial-element 0))))
(defconst *xcst-dst* (list (make-list *fn-ew-span-capacity* :initial-element 0)))

(defun xcst-install-without-duplicate-check (kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (if (not (and (fn-xc-readyp fn-xcs fn-xcc)
                (fn-xc-keyp kind file eoff elen a b c d start trailer)
                (booleanp tokp) (unsigned-byte-p 64 tid) (unsigned-byte-p 64 tcid)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))))
      (mv :refused nil nil fn-xcs fn-xcc)
    (let* ((lo (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
           (present (fn-xc-find lo hi t kind file eoff elen a b c d trailer start fn-xcs)))
      (if present
          (mv-let (word fn-xcs fn-xcc) (fn-xc-touch present fn-xcs fn-xcc)
            (declare (ignore word))
            (mv :present present nil fn-xcs fn-xcc))
        (let* ((free (fn-xc-find-free lo hi fn-xcs))
               (victim (or free (fn-xc-lru lo hi nil fn-xcs))))
          (if (not (and (natp victim) (< victim (fn-xcs-count fn-xcs))))
              (mv :refused nil nil fn-xcs fn-xcc)
            (let ((evicted (if free nil (fn-xc-slot-token victim fn-xcs))))
              (mv-let (stamp fn-xcc) (fn-xc-next-stamp fn-xcc)
                (let ((fn-xcs (fn-xc-write victim kind tokp tid tcid file eoff elen a b c d
                                           start trailer stamp fn-xcs)))
                  (mv (if free :installed :replaced) victim evicted fn-xcs fn-xcc))))))))))

(set-ignore-ok t)
(defmacro xcst-ground-witness (name bindings claim)
  `(make-event
    (mv-let (bad term) (fn-dt-translate ',claim (w state))
      (mv-let (badb alist) (fn-dt-bindings-alist ',bindings (w state))
        (if (or bad badb)
            (er soft 'xcst-ground-witness "Witness translation failed")
          (value (list 'defthm ',name (fn-dt-subst term alist)
                       :rule-classes nil
                       :hints '(("Goal" :in-theory
                                 (union-theories (enable fn-xc-slot-token fn-xc-token fn-xcs-get-kind-is-nth fn-xcs-get-tokp-is-nth fn-xcs-get-tid-is-nth fn-xcs-get-tcid-is-nth fn-xcs-get-file-is-nth fn-xcs-get-eoff-is-nth fn-xcs-get-elen-is-nth fn-xcs-get-a-is-nth fn-xcs-get-b-is-nth fn-xcs-get-c-is-nth fn-xcs-get-d-is-nth fn-xcs-get-start-is-nth fn-xcs-get-trailer-is-nth nth)
                                                 (executable-counterpart-theory :here)))))))))))

(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-positive-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k 0))
  (and (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (natp k)) (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (< k (mv-nth 1 r))) (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready)) (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (<= (mv-nth 1 r) *fn-ew-span-capacity*)
          (<= (+ p (mv-nth 1 r)) end)
          (<= (+ p (mv-nth 1 r)) plen)
          (<= (+ p (mv-nth 1 r))
              (+ (fn-prl-nth 7 token) (nth 5 plan)))
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))
                 :byte)
          (equal (nth k (nth 0 (mv-nth 3 r)))
                 (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window)))))))

(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-without-index-natural-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 0) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k -1))
  (and (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (< k (mv-nth 1 r))) (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready)) (not (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (natp k))) (not (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (<= (mv-nth 1 r) *fn-ew-span-capacity*)
          (<= (+ p (mv-nth 1 r)) end)
          (<= (+ p (mv-nth 1 r)) plen)
          (<= (+ p (mv-nth 1 r))
              (+ (fn-prl-nth 7 token) (nth 5 plan)))
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))
                 :byte)
          (equal (nth k (nth 0 (mv-nth 3 r)))
                 (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))))))))

(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-without-index-in-span-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k 2))
  (and (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (natp k)) (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready)) (not (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (< k (mv-nth 1 r)))) (not (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (<= (mv-nth 1 r) *fn-ew-span-capacity*)
          (<= (+ p (mv-nth 1 r)) end)
          (<= (+ p (mv-nth 1 r)) plen)
          (<= (+ p (mv-nth 1 r))
              (+ (fn-prl-nth 7 token) (nth 5 plan)))
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))
                 :byte)
          (equal (nth k (nth 0 (mv-nth 3 r)))
                 (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))))))))

(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-without-returned-ready-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger nil) (worker *xcst-worker*) (k 0))
  (and (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (natp k)) (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (< k (mv-nth 1 r))) (not (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready))) (not (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (<= (mv-nth 1 r) *fn-ew-span-capacity*)
          (<= (+ p (mv-nth 1 r)) end)
          (<= (+ p (mv-nth 1 r)) plen)
          (<= (+ p (mv-nth 1 r))
              (+ (fn-prl-nth 7 token) (nth 5 plan)))
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))
                 :byte)
          (equal (nth k (nth 0 (mv-nth 3 r)))
                 (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))))))))

(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-mutant-overrun-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k 0))
  (and (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (natp k)) (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (< k (mv-nth 1 r))) (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready)) (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (<= (mv-nth 1 r) *fn-ew-span-capacity*)
          (<= (+ p (mv-nth 1 r)) end)
          (<= (+ p (mv-nth 1 r)) plen)
          (<= (+ p (mv-nth 1 r))
              (+ (fn-prl-nth 7 token) (nth 5 plan)))
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))
                 :byte)
          (equal (nth k (nth 0 (mv-nth 3 r)))
                 (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))))) (not (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (declare (ignorable r token)) (<= (+ p (mv-nth 1 r) 1) (+ (fn-prl-nth 7 token) (nth 5 plan)))))))

(defteeth fn-xc-span-at-is-the-returned-bytes
  :claim (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots))) (((index-natural (natp k)) (index-in-span (< k (mv-nth 1 r))) (returned-ready (equal (fn-pwr-outcome returned-ledger worker token plan) :ready))) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (<= (mv-nth 1 r) *fn-ew-span-capacity*)
          (<= (+ p (mv-nth 1 r)) end)
          (<= (+ p (mv-nth 1 r)) plen)
          (<= (+ p (mv-nth 1 r))
              (+ (fn-prl-nth 7 token) (nth 5 plan)))
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))
                 :byte)
          (equal (nth k (nth 0 (mv-nth 3 r)))
                 (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))))))
  :subject fn-xc-span-at
  :witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k 0))
  :witness-lemma fn-xc-span-at-is-the-returned-bytes-positive-witness
  :breaks ((index-natural ((p 0) (k -1)) :lemma fn-xc-span-at-is-the-returned-bytes-without-index-natural-witness)
           (index-in-span ((k 2)) :lemma fn-xc-span-at-is-the-returned-bytes-without-index-in-span-witness)
           (returned-ready ((returned-ledger nil)) :lemma fn-xc-span-at-is-the-returned-bytes-without-returned-ready-witness))
  :mutations ((overrun (:conclusion (<= (+ p (mv-nth 1 r) 1) (+ (fn-prl-nth 7 token) (nth 5 plan)))) () :fault "a span copy extending one byte past the published window" :lemma fn-xc-span-at-is-the-returned-bytes-mutant-overrun-witness)))

(xcst-ground-witness fn-xc-span-at-answers-an-owed-hit-positive-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*))
  (and (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 hit) :hit)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (fn-pwc-cachedp ledger token)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (natp end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (< p end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit))))))

(xcst-ground-witness fn-xc-span-at-answers-an-owed-hit-without-candidate-witness ((from 1) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*))
  (and (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (fn-pwc-cachedp ledger token)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (natp end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (< p end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte)) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 hit) :hit))) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))))))

(xcst-ground-witness fn-xc-span-at-answers-an-owed-hit-without-cached-witness ((from 0) (ledger *xcst-returned*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*))
  (and (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 hit) :hit)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (natp end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (< p end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte)) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (fn-pwc-cachedp ledger token))) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))))))

(xcst-ground-witness fn-xc-span-at-answers-an-owed-hit-without-end-natural-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 3/2) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*))
  (and (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 hit) :hit)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (fn-pwc-cachedp ledger token)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (< p end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte)) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (natp end))) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))))))

(xcst-ground-witness fn-xc-span-at-answers-an-owed-hit-without-nonempty-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 1) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*))
  (and (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 hit) :hit)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (fn-pwc-cachedp ledger token)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (natp end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte)) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (< p end))) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))))))

(xcst-ground-witness fn-xc-span-at-answers-an-owed-hit-without-first-byte-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 3) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*))
  (and (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 hit) :hit)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (fn-pwc-cachedp ledger token)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (natp end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (< p end)) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte))) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))))))

(xcst-ground-witness fn-xc-span-at-answers-an-owed-hit-mutant-always-miss-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*))
  (and (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 hit) :hit)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (fn-pwc-cachedp ledger token)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (natp end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (< p end)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte)) (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))) (not (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (declare (ignorable hit token r)) (equal (mv-nth 0 r) :miss)))))

(defteeth fn-xc-span-at-answers-an-owed-hit
  :claim (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))) (((candidate (equal (mv-nth 0 hit) :hit)) (cached (fn-pwc-cachedp ledger token)) (end-natural (natp end)) (nonempty (< p end)) (first-byte (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte))) (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))))
  :subject fn-xc-span-at
  :witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*))
  :witness-lemma fn-xc-span-at-answers-an-owed-hit-positive-witness
  :breaks ((candidate ((from 1)) :lemma fn-xc-span-at-answers-an-owed-hit-without-candidate-witness)
           (cached ((ledger *xcst-returned*)) :lemma fn-xc-span-at-answers-an-owed-hit-without-cached-witness)
           (end-natural ((end 3/2)) :lemma fn-xc-span-at-answers-an-owed-hit-without-end-natural-witness)
           (nonempty ((end 1)) :lemma fn-xc-span-at-answers-an-owed-hit-without-nonempty-witness)
           (first-byte ((p 3)) :lemma fn-xc-span-at-answers-an-owed-hit-without-first-byte-witness))
  :mutations ((always-miss (:conclusion (equal (mv-nth 0 r) :miss)) () :fault "suppressing an owed warm hit" :lemma fn-xc-span-at-answers-an-owed-hit-mutant-always-miss-witness)))

(xcst-ground-witness fn-xc-span-at-hit-touches-only-the-selected-slot-positive-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*))
  (and (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         slots cells window dst))) (declare (ignorable r)) (equal (mv-nth 0 r) :span)) (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         slots cells window dst))) (declare (ignorable r)) (and (equal (mv-nth 4 r)
                         (mv-nth 1 (fn-xc-touch (mv-nth 2 r) slots cells)))
                  (equal (mv-nth 5 r)
                         (mv-nth 2 (fn-xc-touch (mv-nth 2 r) slots cells)))))))

(xcst-ground-witness fn-xc-span-at-hit-touches-only-the-selected-slot-without-span-witness ((from 0) (ledger nil) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*))
  (and (not (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         slots cells window dst))) (declare (ignorable r)) (equal (mv-nth 0 r) :span))) (not (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         slots cells window dst))) (declare (ignorable r)) (and (equal (mv-nth 4 r)
                         (mv-nth 1 (fn-xc-touch (mv-nth 2 r) slots cells)))
                  (equal (mv-nth 5 r)
                         (mv-nth 2 (fn-xc-touch (mv-nth 2 r) slots cells))))))))

(xcst-ground-witness fn-xc-span-at-hit-touches-only-the-selected-slot-mutant-omit-touch-witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*))
  (and (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         slots cells window dst))) (declare (ignorable r)) (equal (mv-nth 0 r) :span)) (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         slots cells window dst))) (declare (ignorable r)) (and (equal (mv-nth 4 r)
                         (mv-nth 1 (fn-xc-touch (mv-nth 2 r) slots cells)))
                  (equal (mv-nth 5 r)
                         (mv-nth 2 (fn-xc-touch (mv-nth 2 r) slots cells))))) (not (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         slots cells window dst))) (declare (ignorable r)) (and (equal (mv-nth 4 r) slots) (equal (mv-nth 5 r) cells))))))

(defteeth fn-xc-span-at-hit-touches-only-the-selected-slot
  :claim (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         slots cells window dst))) (((span (equal (mv-nth 0 r) :span))) (and (equal (mv-nth 4 r)
                         (mv-nth 1 (fn-xc-touch (mv-nth 2 r) slots cells)))
                  (equal (mv-nth 5 r)
                         (mv-nth 2 (fn-xc-touch (mv-nth 2 r) slots cells))))))
  :subject fn-xc-span-at
  :witness ((from 0) (ledger *xcst-cached*) (plan *xcst-plan*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (window *xcst-window*) (dst *xcst-dst*))
  :witness-lemma fn-xc-span-at-hit-touches-only-the-selected-slot-positive-witness
  :breaks ((span ((ledger nil)) :lemma fn-xc-span-at-hit-touches-only-the-selected-slot-without-span-witness))
  :mutations ((omit-touch (:conclusion (and (equal (mv-nth 4 r) slots) (equal (mv-nth 5 r) cells))) () :fault "copying bytes but omitting the slot recency update" :lemma fn-xc-span-at-hit-touches-only-the-selected-slot-mutant-omit-touch-witness)))

(xcst-ground-witness fn-xc-held-token-has-one-slot-positive-witness ((slots *xcst-slots*) (i 0) (k 0) (token *xcst-token*))
  (and (fn-xc-token-disjointp slots) (fn-xc-holds i token slots) (fn-xc-holds k token slots) (equal i k)))

(xcst-ground-witness fn-xc-held-token-has-one-slot-without-unique-witness ((slots *xcst-duplicate-slots*) (i 0) (k 1) (token *xcst-token*))
  (and (fn-xc-holds i token slots) (fn-xc-holds k token slots) (not (fn-xc-token-disjointp slots)) (not (equal i k))))

(xcst-ground-witness fn-xc-held-token-has-one-slot-without-first-holder-witness ((slots *xcst-slots*) (i 1) (k 0) (token *xcst-token*))
  (and (fn-xc-token-disjointp slots) (fn-xc-holds k token slots) (not (fn-xc-holds i token slots)) (not (equal i k))))

(xcst-ground-witness fn-xc-held-token-has-one-slot-without-second-holder-witness ((slots *xcst-slots*) (i 0) (k 1) (token *xcst-token*))
  (and (fn-xc-token-disjointp slots) (fn-xc-holds i token slots) (not (fn-xc-holds k token slots)) (not (equal i k))))

(xcst-ground-witness fn-xc-held-token-has-one-slot-mutant-two-indices-witness ((slots *xcst-slots*) (i 0) (k 0) (token *xcst-token*))
  (and (fn-xc-token-disjointp slots) (fn-xc-holds i token slots) (fn-xc-holds k token slots) (equal i k) (not (not (equal i k)))))

(defteeth fn-xc-held-token-has-one-slot
  :claim (((unique (fn-xc-token-disjointp slots)) (first-holder (fn-xc-holds i token slots)) (second-holder (fn-xc-holds k token slots))) (equal i k))
  :subject fn-xc-holds
  :witness ((slots *xcst-slots*) (i 0) (k 0) (token *xcst-token*))
  :witness-lemma fn-xc-held-token-has-one-slot-positive-witness
  :breaks ((unique ((slots *xcst-duplicate-slots*) (k 1)) :lemma fn-xc-held-token-has-one-slot-without-unique-witness)
           (first-holder ((i 1)) :lemma fn-xc-held-token-has-one-slot-without-first-holder-witness)
           (second-holder ((k 1)) :lemma fn-xc-held-token-has-one-slot-without-second-holder-witness))
  :mutations ((two-indices (:conclusion (not (equal i k))) () :fault "treating two references to one charge as distinct slots" :lemma fn-xc-held-token-has-one-slot-mutant-two-indices-witness)))

(xcst-ground-witness fn-xc-install-duplicate-is-already-held-positive-witness ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (slots *xcst-slots*) (cells *xcst-cells*))
  (let* ((choice (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
         (target (mv-nth 0 choice)) (holder (mv-nth 1 choice))
         (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
         (r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells))) (declare (ignorable choice target holder token r)) (and (iff (equal (mv-nth 0 r) :duplicate)
              (and token (fn-xc-holds holder token slots) (not (equal holder target))))
         (implies (equal (mv-nth 0 r) :duplicate)
                  (and (equal (mv-nth 1 r) target) (equal (mv-nth 2 r) nil)
                       (equal (mv-nth 3 r) slots) (equal (mv-nth 4 r) cells))))))

(xcst-ground-witness fn-xc-install-duplicate-is-already-held-mutant-raw-window-old-install-witness ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (slots *xcst-slots*) (cells *xcst-cells*))
  (and (let* ((choice (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
         (target (mv-nth 0 choice)) (holder (mv-nth 1 choice))
         (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
         (r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells))) (declare (ignorable choice target holder token r)) (and (iff (equal (mv-nth 0 r) :duplicate)
              (and token (fn-xc-holds holder token slots) (not (equal holder target))))
         (implies (equal (mv-nth 0 r) :duplicate)
                  (and (equal (mv-nth 1 r) target) (equal (mv-nth 2 r) nil)
                       (equal (mv-nth 3 r) slots) (equal (mv-nth 4 r) cells))))) (not (let* ((choice (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
         (target (mv-nth 0 choice)) (holder (mv-nth 1 choice))
         (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
         (r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells))) (declare (ignorable choice target holder token r)) (implies (fn-xc-token-disjointp slots) (fn-xc-token-disjointp (mv-nth 3 (xcst-install-without-duplicate-check kind tokp tid tcid file eoff elen a b c d start trailer slots cells))))))))

(xcst-ground-witness fn-xc-install-duplicate-is-already-held-mutant-whole-entry-old-install-witness ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (slots *xcst-whole-slots*) (cells '(1 2 0)))
  (and (let* ((choice (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
         (target (mv-nth 0 choice)) (holder (mv-nth 1 choice))
         (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
         (r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells))) (declare (ignorable choice target holder token r)) (and (iff (equal (mv-nth 0 r) :duplicate)
              (and token (fn-xc-holds holder token slots) (not (equal holder target))))
         (implies (equal (mv-nth 0 r) :duplicate)
                  (and (equal (mv-nth 1 r) target) (equal (mv-nth 2 r) nil)
                       (equal (mv-nth 3 r) slots) (equal (mv-nth 4 r) cells))))) (not (let* ((choice (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
         (target (mv-nth 0 choice)) (holder (mv-nth 1 choice))
         (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
         (r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells))) (declare (ignorable choice target holder token r)) (implies (fn-xc-token-disjointp slots) (fn-xc-token-disjointp (mv-nth 3 (xcst-install-without-duplicate-check kind tokp tid tcid file eoff elen a b c d start trailer slots cells))))))))

(defteeth fn-xc-install-duplicate-is-already-held
  :claim (let* ((choice (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
         (target (mv-nth 0 choice)) (holder (mv-nth 1 choice))
         (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
         (r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells))) (() (and (iff (equal (mv-nth 0 r) :duplicate)
              (and token (fn-xc-holds holder token slots) (not (equal holder target))))
         (implies (equal (mv-nth 0 r) :duplicate)
                  (and (equal (mv-nth 1 r) target) (equal (mv-nth 2 r) nil)
                       (equal (mv-nth 3 r) slots) (equal (mv-nth 4 r) cells))))))
  :subject fn-xc-install
  :witness ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (slots *xcst-slots*) (cells *xcst-cells*))
  :witness-lemma fn-xc-install-duplicate-is-already-held-positive-witness
  :breaks ()
  :mutations ((raw-window-old-install (:conclusion (implies (fn-xc-token-disjointp slots) (fn-xc-token-disjointp (mv-nth 3 (xcst-install-without-duplicate-check kind tokp tid tcid file eoff elen a b c d start trailer slots cells))))) () :fault "old install binds a raw-window charge twice when c differs" :lemma fn-xc-install-duplicate-is-already-held-mutant-raw-window-old-install-witness)
              (whole-entry-old-install (:conclusion (implies (fn-xc-token-disjointp slots) (fn-xc-token-disjointp (mv-nth 3 (xcst-install-without-duplicate-check kind tokp tid tcid file eoff elen a b c d start trailer slots cells))))) ((kind 1) (tcid 9) (a 1) (b 0) (c 0) (slots *xcst-whole-slots*) (cells '(1 2 0))) :fault "old install binds a whole-entry charge twice when a differs" :lemma fn-xc-install-duplicate-is-already-held-mutant-whole-entry-old-install-witness)))

(local (must-fail-checked (defthm xcst-raw-window-old-install-would-preserve
  (implies (fn-xc-token-disjointp *xcst-slots*) (fn-xc-token-disjointp (mv-nth 3 (xcst-install-without-duplicate-check 2 t 7 0 11 100 3 100 3 1 0 0 77 *xcst-slots* *xcst-cells*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here)))))))

(local (must-fail-checked (defthm xcst-whole-entry-old-install-would-preserve
  (implies (fn-xc-token-disjointp *xcst-whole-slots*) (fn-xc-token-disjointp (mv-nth 3 (xcst-install-without-duplicate-check 1 t 7 9 11 100 3 1 0 0 0 0 77 *xcst-whole-slots* '(1 2 0)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here)))))))

; Actual stobj execution of the same model poststate. The host's publication
; provenance is fn-pwc-cache-only-a-published-window, not these fixtures.
(defun xcst-native-positive (fn-xcs fn-xcc fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-ew-buffer fn-ew-span) :verify-guards nil))
  (let* ((fn-xcs (fn-xcs-clear fn-xcs)) (fn-xcc (fn-xcc-clear fn-xcc))
         (fn-ew-buffer (update-fn-ew-bytesi 0 1 fn-ew-buffer))
         (fn-ew-buffer (update-fn-ew-bytesi 1 2 fn-ew-buffer))
         (fn-ew-buffer (update-fn-ew-bytesi 2 3 fn-ew-buffer)))
    (mv-let (init fn-xcs fn-xcc) (fn-xc-init 0 2 fn-xcs fn-xcc)
      (mv-let (installed target evicted fn-xcs fn-xcc)
        (fn-xc-install-window *xcst-token* fn-xcs fn-xcc)
        (mv-let (lookup found)
          (fn-xc-lookup 0 2 11 100 3 100 3 0 0 77 1 fn-xcs fn-xcc)
          (mv-let (word1 byte1)
            (fn-pwr-byte-at *xcst-returned* *xcst-worker* *xcst-token* *xcst-plan* 11 100 3 100 3 77 1 fn-ew-buffer)
            (mv-let (word2 byte2)
              (fn-pwr-byte-at *xcst-returned* *xcst-worker* *xcst-token* *xcst-plan* 11 100 3 100 3 77 2 fn-ew-buffer)
              (mv-let (word count slot fn-ew-span fn-xcs fn-xcc)
                (fn-xc-span-at 0 *xcst-cached* *xcst-plan* 11 100 3 100 3 77 1 99 fn-xcs fn-xcc fn-ew-buffer fn-ew-span)
                (mv (and (equal init :initialized) (equal installed :installed) (equal target 0) (not evicted)
                         (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                         (fn-ew-bufferp fn-ew-buffer) (fn-ew-spanp fn-ew-span)
                         (equal lookup :hit) (equal found 0)
                         (fn-pwc-cachedp *xcst-cached* *xcst-token*)
                         (equal (fn-pwr-outcome *xcst-returned* *xcst-worker* *xcst-token* *xcst-plan*) :ready)
                         (equal word1 :byte) (equal word2 :byte)
                         (equal word :span) (equal count 2) (equal slot 0)
                         (equal byte1 2) (equal byte2 3)
                         (equal (fn-ew-span-bytesi 0 fn-ew-span) byte1)
                         (equal (fn-ew-span-bytesi 1 fn-ew-span) byte2)
                         (natp 0) (< 0 count) (<= count *fn-ew-span-capacity*)
                         (<= (+ 1 count) 99) (<= (+ 1 count) 3)
                         (<= (+ 1 count) (+ (nth 7 *xcst-token*) (nth 5 *xcst-plan*)))
                         (equal (fn-xcs-get-stamp 0 fn-xcs) 1) (equal (fn-xc-tick fn-xcc) 2)
                         (fn-xc-token-disjointp fn-xcs))
                    fn-xcs fn-xcc fn-ew-buffer fn-ew-span)))))))))

(assert-event (xcst-native-positive fn-xcs fn-xcc fn-ew-buffer fn-ew-span)
         :stobjs-out '(nil fn-xcs fn-xcc fn-ew-buffer fn-ew-span))

; Every transition has a nonempty ground control; the write control meets
; the precise outside-target absence precondition.
(xcst-ground-witness xcst-transition-controls ()
  (and (fn-xc-token-disjointp *xcst-slots*)
       (fn-xc-write-okp 1 2 t 8 0 11 100 3 100 3 0 0 0 77 1 *xcst-slots*)
       (not (fn-xc-find-token-except
              (fn-xc-token 2 t 8 0 11 100 3 100 3 0 0 0 77) 1 0 *xcst-slots*))
       (fn-xc-token-disjointp
         (fn-xc-write 1 2 t 8 0 11 100 3 100 3 0 0 0 77 1 *xcst-slots*))
       (fn-xc-token-disjointp (mv-nth 1 (fn-xc-touch 0 *xcst-slots* *xcst-cells*)))
       (fn-xc-token-disjointp (mv-nth 2 (fn-xc-free 0 *xcst-slots*)))
       (fn-xc-token-disjointp (mv-nth 3 (fn-xc-yield *xcst-slots* *xcst-cells*)))))

(xcst-ground-witness xcst-duplicate-answers ()
  (let ((r2 (fn-xc-install 2 t 7 0 11 100 3 100 3 1 0 0 77 *xcst-slots* *xcst-cells*))
        (r1 (fn-xc-install 1 t 7 9 11 100 3 1 0 0 0 0 77 *xcst-whole-slots* '(1 2 0))))
    (and (equal (mv-nth 0 r2) :duplicate)
         (equal (mv-nth 3 r2) *xcst-slots*) (equal (mv-nth 4 r2) *xcst-cells*)
         (equal (mv-nth 0 r1) :duplicate)
         (equal (mv-nth 3 r1) *xcst-whole-slots*) (equal (mv-nth 4 r1) '(1 2 0)))))

(defteeth-check)
