; Slot-cache span and charge-ownership teeth. Public theorem variables name
; logical snapshots; registered ground lemmas check the entire claims. The
; native assertion below separately checks the same span on real stobjs.
(in-package "ACL2")
(include-book "../../books/extent-cache-span")
(include-book "../../books/extent-cache-disjoint")
(include-book "../../books/extent-cache-contracts")
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
(defconst *xcst-wins* (list (list *xcst-plan*) (list *xcst-window*)))
(defconst *xcst-c* *fn-ew-span-capacity*)
(defconst *xcst-plen* (+ *xcst-c* 3))
(defconst *xcst-t0* (list :window 7 11 100 *xcst-plen* 100 *xcst-plen* 0 77))
(defconst *xcst-t1* (list :window 8 11 100 *xcst-plen* 100 *xcst-plen* *xcst-c* 77))
(defconst *xcst-p0* (list :verified 11 100 *xcst-plen* 0 *xcst-c* 77 0 7 47 *xcst-t0* 100 *xcst-plen* 0))
(defconst *xcst-p1* (list :verified 11 100 *xcst-plen* *xcst-c* 3 77 0 8 47 *xcst-t1* 100 *xcst-plen* *xcst-c*))
(defconst *xcst-ledger2* (list nil nil nil (list (cons *xcst-t0* '((300000 0 0 0 0) :cached nil)) (cons *xcst-t1* '((300000 0 0 0 0) :cached nil))) nil))
(defconst *xcst-returned2* (list nil nil nil (list (cons *xcst-t0* '((300000 0 0 0 0) :window :returned 0)) (cons *xcst-t1* '((300000 0 0 0 0) :window :returned 0))) nil))
(defconst *xcst-worker1* (list 0 8 :returned *xcst-t1*))
(defconst *xcst-slots2* (list (list 2 t 7 0 11 100 *xcst-plen* 100 *xcst-plen* 0 0 0 77 0)
                              (list 2 t 8 0 11 100 *xcst-plen* 100 *xcst-plen* 0 0 *xcst-c* 77 1)))
(defconst *xcst-cells2* '(2 0 2))
(defconst *xcst-win0* (list (append '(4 5 6) (make-list (- *fn-ew-span-capacity* 3) :initial-element 0))))
(defconst *xcst-win1* (list (append '(7 8 9) (make-list (- *fn-ew-span-capacity* 3) :initial-element 0))))
(defconst *xcst-wins2* (list (list *xcst-p0* *xcst-p1*) (list *xcst-win0* *xcst-win1*)))


(defconst *xcst-slots2r* (list (list 2 t 7 0 11 100 *xcst-plen* 100 *xcst-plen* 0 0 0 77 0)
                               '(0 nil 0 0 0 0 0 0 0 0 0 0 0 0)))
(defconst *xcst-worker0* (list 0 7 :returned *xcst-t0*))
(defconst *xcst-slots9* (append (make-list 8 :initial-element '(0 nil 0 0 0 0 0 0 0 0 0 0 0 0))
                                (list (list 2 t 8 0 11 100 *xcst-plen* 100 *xcst-plen* 0 0 *xcst-c* 77 1))))
(defconst *xcst-wins9* (list (append (make-list 8 :initial-element nil) (list *xcst-p1*))
                             (append (make-list 8 :initial-element nil) (list *xcst-win1*))))
(defconst *xcst-slots2c* (list (list 2 t 7 0 11 100 *xcst-plen* 100 *xcst-plen* 0 0 0 77 0)
                               (list 2 t 8 0 11 100 *xcst-plen* 100 *xcst-plen* 1 0 *xcst-c* 77 1)))
(defconst *xcst-wins2l* (list (list *xcst-p0* (append *xcst-p1* 9)) (list *xcst-win0* *xcst-win1*)))
(defconst *xcst-wins2s* (list (list *xcst-p0* *xcst-p0*) (list *xcst-win0* *xcst-win0*)))

(defconst *xcst-slots9s* (append (make-list 8 :initial-element '(0 nil 0 0 0 0 0 0 0 0 0 0 0 0))
                                 (list (car *xcst-slots*))))
(defconst *xcst-wins9s* (list (append (make-list 8 :initial-element nil) (list *xcst-plan*))
                              (append (make-list 8 :initial-element nil) (list *xcst-window*))))
(defconst *xcst-winsl* (list (list (append *xcst-plan* 9)) (list *xcst-window*)))
(defconst *xcst-end2* (+ *xcst-c* 99))
(defconst *xcst-end-frac* (+ *xcst-c* 3/2))
(defconst *xcst-p-past* (+ *xcst-c* 3))


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
                       :hints '(("Goal" :expand ((:free (a b c d e f g h i j k l m n) (fn-xc-span-at a b c d e f g h i j k l m n))) :in-theory
                                 (union-theories (enable fn-xc-slot-token fn-xc-token fn-xcs-get-kind-is-nth fn-xcs-get-tokp-is-nth fn-xcs-get-tid-is-nth fn-xcs-get-tcid-is-nth fn-xcs-get-file-is-nth fn-xcs-get-eoff-is-nth fn-xcs-get-elen-is-nth fn-xcs-get-a-is-nth fn-xcs-get-b-is-nth fn-xcs-get-c-is-nth fn-xcs-get-d-is-nth fn-xcs-get-start-is-nth fn-xcs-get-trailer-is-nth nth)
                                                 (executable-counterpart-theory :here)))))))))))
(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-positive-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k 0))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (natp k)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (< k (mv-nth 1 r))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (<= (mv-nth 1 r) *fn-ew-span-capacity*) (<= (+ p (mv-nth 1 r)) end) (<= (+ p (mv-nth 1 r)) plen) (<= (+ p (mv-nth 1 r)) (+ (fn-prl-nth 7 token) (nth 5 plan))) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window)) :byte) (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window)))))))

(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-without-index-natural-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 0) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k -1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (< k (mv-nth 1 r))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (natp k))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (<= (mv-nth 1 r) *fn-ew-span-capacity*) (<= (+ p (mv-nth 1 r)) end) (<= (+ p (mv-nth 1 r)) plen) (<= (+ p (mv-nth 1 r)) (+ (fn-prl-nth 7 token) (nth 5 plan))) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window)) :byte) (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window))))))))

(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-without-index-in-span-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k 2))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (natp k)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (< k (mv-nth 1 r)))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (<= (mv-nth 1 r) *fn-ew-span-capacity*) (<= (+ p (mv-nth 1 r)) end) (<= (+ p (mv-nth 1 r)) plen) (<= (+ p (mv-nth 1 r)) (+ (fn-prl-nth 7 token) (nth 5 plan))) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window)) :byte) (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window))))))))

(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-without-returned-ready-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*) (returned-ledger nil) (worker *xcst-worker*) (k 0))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (natp k)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (< k (mv-nth 1 r))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (<= (mv-nth 1 r) *fn-ew-span-capacity*) (<= (+ p (mv-nth 1 r)) end) (<= (+ p (mv-nth 1 r)) plen) (<= (+ p (mv-nth 1 r)) (+ (fn-prl-nth 7 token) (nth 5 plan))) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window)) :byte) (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window))))))))

(xcst-ground-witness fn-xc-span-at-is-the-returned-bytes-mutant-overrun-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k 0))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (natp k)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (< k (mv-nth 1 r))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (<= (mv-nth 1 r) *fn-ew-span-capacity*) (<= (+ p (mv-nth 1 r)) end) (<= (+ p (mv-nth 1 r)) plen) (<= (+ p (mv-nth 1 r)) (+ (fn-prl-nth 7 token) (nth 5 plan))) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window)) :byte) (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window))))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (declare (ignorable r s token plan window)) (<= (+ p (mv-nth 1 r) 1) (+ (fn-prl-nth 7 token) (nth 5 plan)))))))

(defteeth fn-xc-span-at-is-the-returned-bytes
  :claim (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins)) (window (fn-xcw-window (fn-xc-row s cells) wins))) (((index-natural (natp k)) (index-in-span (< k (mv-nth 1 r))) (returned-ready (equal (fn-pwr-outcome returned-ledger worker token plan) :ready))) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (<= (mv-nth 1 r) *fn-ew-span-capacity*) (<= (+ p (mv-nth 1 r)) end) (<= (+ p (mv-nth 1 r)) plen) (<= (+ p (mv-nth 1 r)) (+ (fn-prl-nth 7 token) (nth 5 plan))) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window)) :byte) (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) window))))))
  :subject fn-xc-span-at
  :witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*) (returned-ledger *xcst-returned*) (worker *xcst-worker*) (k 0))
  :witness-lemma fn-xc-span-at-is-the-returned-bytes-positive-witness
  :breaks (
(index-natural ((p 0) (k -1)) :lemma fn-xc-span-at-is-the-returned-bytes-without-index-natural-witness)           (index-in-span ((k 2)) :lemma fn-xc-span-at-is-the-returned-bytes-without-index-in-span-witness)           (returned-ready ((returned-ledger nil)) :lemma fn-xc-span-at-is-the-returned-bytes-without-returned-ready-witness))
  :mutations (
(overrun (:conclusion (<= (+ p (mv-nth 1 r) 1) (+ (fn-prl-nth 7 token) (nth 5 plan)))) () :fault "a span copy extending one byte past the published window" :lemma fn-xc-span-at-is-the-returned-bytes-mutant-overrun-witness)))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-positive-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end2*) (slots *xcst-slots2*) (cells *xcst-cells2*) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i)))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-table-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end2*) (slots *xcst-slots2*) (cells '(2 0 3)) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells)))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-from-witness ((from 2) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end2*) (slots *xcst-slots2*) (cells *xcst-cells2*) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i)))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-region-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p 1) (end *xcst-end2*) (slots *xcst-slots2r*) (cells '(2 1 1)) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker0*) (i 0))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells)))))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-rows-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end2*) (slots *xcst-slots9*) (cells '(1 0 9)) (wins *xcst-wins9*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 8))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins)))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-match-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end2*) (slots *xcst-slots2c*) (cells *xcst-cells2*) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-end-natural-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end-frac*) (slots *xcst-slots2*) (cells *xcst-cells2*) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-nonempty-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-c*) (slots *xcst-slots2*) (cells *xcst-cells2*) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-cached-witness ((from 0) (ledger *xcst-returned2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end2*) (slots *xcst-slots2*) (cells *xcst-cells2*) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-plan-list-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end2*) (slots *xcst-slots2*) (cells *xcst-cells2*) (wins *xcst-wins2l*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-without-first-byte-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-p-past*) (end *xcst-end2*) (slots *xcst-slots2*) (cells *xcst-cells2*) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))))

(xcst-ground-witness fn-xc-span-at-answers-a-covered-slot-mutant-first-candidate-only-witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end2*) (slots *xcst-slots2*) (cells *xcst-cells2*) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (fn-xccp cells) (fn-xc-readyp slots cells))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp from) (<= from i))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (natp end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (< p end)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (fn-pwc-cachedp ledger token)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (true-listp plan)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (declare (ignorable r row token plan window)) (equal (mv-nth 2 r) (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)))))))

(defteeth fn-xc-span-at-answers-a-covered-slot
  :claim (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (row (fn-xc-row i cells)) (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))) (((table (and (fn-xccp cells) (fn-xc-readyp slots cells))) (from (and (natp from) (<= from i))) (region (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))) (rows (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))) (match (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)) (end-natural (natp end)) (nonempty (< p end)) (cached (fn-pwc-cachedp ledger token)) (plan-list (true-listp plan)) (first-byte (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer p window)) :byte))) (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r)) (natp (mv-nth 2 r)) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))
  :subject fn-xc-span-at
  :witness ((from 0) (ledger *xcst-ledger2*) (file 11) (eoff 100) (elen *xcst-plen*) (poff 100) (plen *xcst-plen*) (trailer 77) (p *xcst-c*) (end *xcst-end2*) (slots *xcst-slots2*) (cells *xcst-cells2*) (wins *xcst-wins2*) (dst *xcst-dst*) (returned-ledger *xcst-returned2*) (worker *xcst-worker1*) (i 1))
  :witness-lemma fn-xc-span-at-answers-a-covered-slot-positive-witness
  :breaks (
(table ((cells '(2 0 3))) :lemma fn-xc-span-at-answers-a-covered-slot-without-table-witness)           (from ((from 2)) :lemma fn-xc-span-at-answers-a-covered-slot-without-from-witness)           (region ((p 1) (i 0) (slots *xcst-slots2r*) (cells '(2 1 1)) (worker *xcst-worker0*)) :lemma fn-xc-span-at-answers-a-covered-slot-without-region-witness)           (rows ((i 8) (slots *xcst-slots9*) (cells '(1 0 9)) (wins *xcst-wins9*)) :lemma fn-xc-span-at-answers-a-covered-slot-without-rows-witness)           (match ((slots *xcst-slots2c*)) :lemma fn-xc-span-at-answers-a-covered-slot-without-match-witness)           (end-natural ((end *xcst-end-frac*)) :lemma fn-xc-span-at-answers-a-covered-slot-without-end-natural-witness)           (nonempty ((end *xcst-c*)) :lemma fn-xc-span-at-answers-a-covered-slot-without-nonempty-witness)           (cached ((ledger *xcst-returned2*)) :lemma fn-xc-span-at-answers-a-covered-slot-without-cached-witness)           (plan-list ((wins *xcst-wins2l*)) :lemma fn-xc-span-at-answers-a-covered-slot-without-plan-list-witness)           (first-byte ((p *xcst-p-past*)) :lemma fn-xc-span-at-answers-a-covered-slot-without-first-byte-witness))
  :mutations (
(first-candidate-only (:conclusion (equal (mv-nth 2 r) (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)))) () :fault "answering only from the first slot the lookup selects, so a later slot holding the octet is missed" :lemma fn-xc-span-at-answers-a-covered-slot-mutant-first-candidate-only-witness)))

(xcst-ground-witness fn-xc-span-at-hit-touches-only-the-selected-slot-positive-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  (and  (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (and (equal (mv-nth 4 r) (mv-nth 1 (fn-xc-touch (mv-nth 2 r) slots cells))) (equal (mv-nth 5 r) (mv-nth 2 (fn-xc-touch (mv-nth 2 r) slots cells)))))))

(xcst-ground-witness fn-xc-span-at-hit-touches-only-the-selected-slot-mutant-omit-touch-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (and (equal (mv-nth 4 r) (mv-nth 1 (fn-xc-touch (mv-nth 2 r) slots cells))) (equal (mv-nth 5 r) (mv-nth 2 (fn-xc-touch (mv-nth 2 r) slots cells))))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (and (equal (mv-nth 4 r) slots) (equal (mv-nth 5 r) cells))))))

(defteeth fn-xc-span-at-hit-touches-only-the-selected-slot
  :claim (let ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (() (and (equal (mv-nth 4 r) (mv-nth 1 (fn-xc-touch (mv-nth 2 r) slots cells))) (equal (mv-nth 5 r) (mv-nth 2 (fn-xc-touch (mv-nth 2 r) slots cells))))))
  :subject fn-xc-span-at
  :witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  :witness-lemma fn-xc-span-at-hit-touches-only-the-selected-slot-positive-witness
  :breaks (
)
  :mutations (
(omit-touch (:conclusion (and (equal (mv-nth 4 r) slots) (equal (mv-nth 5 r) cells))) () :fault "copying bytes but omitting the slot recency update" :lemma fn-xc-span-at-hit-touches-only-the-selected-slot-mutant-omit-touch-witness)))

(xcst-ground-witness fn-xc-span-at-answers-from-a-matching-slot-positive-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins))) (declare (ignorable r s token plan)) (equal (mv-nth 0 r) :span)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins))) (declare (ignorable r s token plan)) (and (natp s) (and (natp from) (<= from s)) (< s (fn-xcs-count slots)) (fn-xc-slot-matchp s nil 2 file eoff elen poff plen 0 0 trailer p slots) (fn-pwc-cachedp ledger token) (fn-pwr-plan-matches-token plan token)))))

(xcst-ground-witness fn-xc-span-at-answers-from-a-matching-slot-without-span-witness ((from 0) (ledger nil) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  (and (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins))) (declare (ignorable r s token plan)) (equal (mv-nth 0 r) :span))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins))) (declare (ignorable r s token plan)) (and (natp s) (and (natp from) (<= from s)) (< s (fn-xcs-count slots)) (fn-xc-slot-matchp s nil 2 file eoff elen poff plen 0 0 trailer p slots) (fn-pwc-cachedp ledger token) (fn-pwr-plan-matches-token plan token))))))

(xcst-ground-witness fn-xc-span-at-answers-from-a-matching-slot-mutant-stale-plan-accepted-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins))) (declare (ignorable r s token plan)) (equal (mv-nth 0 r) :span)) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins))) (declare (ignorable r s token plan)) (and (natp s) (and (natp from) (<= from s)) (< s (fn-xcs-count slots)) (fn-xc-slot-matchp s nil 2 file eoff elen poff plen 0 0 trailer p slots) (fn-pwc-cachedp ledger token) (fn-pwr-plan-matches-token plan token))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins))) (declare (ignorable r s token plan)) (not (fn-pwr-plan-matches-token plan token))))))

(defteeth fn-xc-span-at-answers-from-a-matching-slot
  :claim (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (s (mv-nth 2 r)) (token (fn-xc-slot-token s slots)) (plan (fn-xcw-plan (fn-xc-row s cells) wins))) (((span (equal (mv-nth 0 r) :span))) (and (natp s) (and (natp from) (<= from s)) (< s (fn-xcs-count slots)) (fn-xc-slot-matchp s nil 2 file eoff elen poff plen 0 0 trailer p slots) (fn-pwc-cachedp ledger token) (fn-pwr-plan-matches-token plan token))))
  :subject fn-xc-span-at
  :witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  :witness-lemma fn-xc-span-at-answers-from-a-matching-slot-positive-witness
  :breaks (
(span ((ledger nil)) :lemma fn-xc-span-at-answers-from-a-matching-slot-without-span-witness))
  :mutations (
(stale-plan-accepted (:conclusion (not (fn-pwr-plan-matches-token plan token))) () :fault "copying from a row whose plan was written for another slot's token" :lemma fn-xc-span-at-answers-from-a-matching-slot-mutant-stale-plan-accepted-witness)))

(xcst-ground-witness fn-xc-span-at-miss-changes-nothing-positive-witness ((from 0) (ledger nil) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (not (equal (mv-nth 0 r) :span))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (and (equal (mv-nth 0 r) :miss) (equal (mv-nth 1 r) 0) (equal (mv-nth 2 r) nil) (equal (mv-nth 3 r) dst) (equal (mv-nth 4 r) slots) (equal (mv-nth 5 r) cells)))))

(xcst-ground-witness fn-xc-span-at-miss-changes-nothing-without-miss-witness ((from 0) (ledger *xcst-cached*) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  (and (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (not (equal (mv-nth 0 r) :span)))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (and (equal (mv-nth 0 r) :miss) (equal (mv-nth 1 r) 0) (equal (mv-nth 2 r) nil) (equal (mv-nth 3 r) dst) (equal (mv-nth 4 r) slots) (equal (mv-nth 5 r) cells))))))

(xcst-ground-witness fn-xc-span-at-miss-changes-nothing-mutant-miss-reports-bytes-witness ((from 0) (ledger nil) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  (and (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (not (equal (mv-nth 0 r) :span))) (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (and (equal (mv-nth 0 r) :miss) (equal (mv-nth 1 r) 0) (equal (mv-nth 2 r) nil) (equal (mv-nth 3 r) dst) (equal (mv-nth 4 r) slots) (equal (mv-nth 5 r) cells))) (not (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (declare (ignorable r)) (equal (mv-nth 1 r) 1)))))

(defteeth fn-xc-span-at-miss-changes-nothing
  :claim (let ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))) (((miss (not (equal (mv-nth 0 r) :span)))) (and (equal (mv-nth 0 r) :miss) (equal (mv-nth 1 r) 0) (equal (mv-nth 2 r) nil) (equal (mv-nth 3 r) dst) (equal (mv-nth 4 r) slots) (equal (mv-nth 5 r) cells))))
  :subject fn-xc-span-at
  :witness ((from 0) (ledger nil) (file 11) (eoff 100) (elen 3) (poff 100) (plen 3) (trailer 77) (p 1) (end 99) (slots *xcst-slots*) (cells *xcst-cells*) (wins *xcst-wins*) (dst *xcst-dst*))
  :witness-lemma fn-xc-span-at-miss-changes-nothing-positive-witness
  :breaks (
(miss ((ledger *xcst-cached*)) :lemma fn-xc-span-at-miss-changes-nothing-without-miss-witness))
  :mutations (
(miss-reports-bytes (:conclusion (equal (mv-nth 1 r) 1)) () :fault "a declined walk that still reports a span length" :lemma fn-xc-span-at-miss-changes-nothing-mutant-miss-reports-bytes-witness)))


; A row left behind by another window must never yield bytes: slot 1 (token
; t1) carries the plan written for t0, so fn-pwc-span-at refuses the plan/token
; mismatch and the walk ends in :miss.  Removing the plan/token check would
; answer :span; the unchecked statement is must-fail.
(xcst-ground-witness xcst-stale-row-answers-miss ()
  (let ((r (fn-xc-span-at 0 *xcst-ledger2* 11 100 *xcst-plen* 100 *xcst-plen* 77 *xcst-c* *xcst-end2*
                          *xcst-slots2* *xcst-cells2* *xcst-wins2s* *xcst-dst*)))
    (and (equal (mv-nth 0 r) :miss) (equal (mv-nth 1 r) 0)
         (not (fn-pwr-plan-matches-token (fn-xcw-plan 1 *xcst-wins2s*) *xcst-t1*)))))

(local (must-fail-checked (defthm xcst-stale-row-would-answer-span
  (equal (mv-nth 0 (fn-xc-span-at 0 *xcst-ledger2* 11 100 *xcst-plen* 100 *xcst-plen* 77 *xcst-c* *xcst-end2*
                                  *xcst-slots2* *xcst-cells2* *xcst-wins2s* *xcst-dst*))
         :span)
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (enable fn-xc-slot-token fn-xc-token fn-xcs-get-kind-is-nth fn-xcs-get-tokp-is-nth fn-xcs-get-tid-is-nth fn-xcs-get-tcid-is-nth fn-xcs-get-file-is-nth fn-xcs-get-eoff-is-nth fn-xcs-get-elen-is-nth fn-xcs-get-a-is-nth fn-xcs-get-b-is-nth fn-xcs-get-c-is-nth fn-xcs-get-d-is-nth fn-xcs-get-start-is-nth fn-xcs-get-trailer-is-nth nth)
                                            (executable-counterpart-theory :here)))))))

; The first-candidate-only walk (no continuation) is the design this lane
; replaces: on S's two-window request it answers :miss while the real walk
; answers :span from slot 1.
(defun xcst-first-candidate-span-at (from ledger file eoff elen poff plen trailer p end
                                          fn-xcs fn-xcc fn-xcw fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xcw fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (natp from) (natp p)
                              (natp end) (natp plen))
                  :verify-guards nil))
  (mv-let (word slot)
    (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)
    (if (and (equal word :hit) (natp slot) (< slot (fn-xcs-count fn-xcs))
             (fn-xc-cellsp fn-xcc) (natp p) (natp end) (natp plen))
        (mv-let (answer j fn-ew-span)
          (fn-xc-span-row slot ledger file eoff elen poff plen trailer p end
                          fn-xcs fn-xcc fn-xcw fn-ew-span)
          (if (equal answer :span)
              (mv :span (- j p) slot fn-ew-span fn-xcs fn-xcc)
            (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc)))
      (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc))))

(xcst-ground-witness xcst-first-candidate-only-misses-what-the-walk-answers ()
  (and (equal (mv-nth 0 (xcst-first-candidate-span-at 0 *xcst-ledger2* 11 100 *xcst-plen* 100 *xcst-plen* 77 *xcst-c* *xcst-end2*
                                                      *xcst-slots2* *xcst-cells2* *xcst-wins2* *xcst-dst*))
              :miss)
       (equal (mv-nth 0 (fn-xc-span-at 0 *xcst-ledger2* 11 100 *xcst-plen* 100 *xcst-plen* 77 *xcst-c* *xcst-end2*
                                       *xcst-slots2* *xcst-cells2* *xcst-wins2* *xcst-dst*))
              :span)
       (equal (mv-nth 2 (fn-xc-span-at 0 *xcst-ledger2* 11 100 *xcst-plen* 100 *xcst-plen* 77 *xcst-c* *xcst-end2*
                                       *xcst-slots2* *xcst-cells2* *xcst-wins2* *xcst-dst*))
              1)
       (equal (mv-nth 1 (fn-xc-span-at 0 *xcst-ledger2* 11 100 *xcst-plen* 100 *xcst-plen* 77 *xcst-c* *xcst-end2*
                                       *xcst-slots2* *xcst-cells2* *xcst-wins2* *xcst-dst*))
              3)))

(local (must-fail-checked (defthm xcst-first-candidate-only-would-answer-span
  (equal (mv-nth 0 (xcst-first-candidate-span-at 0 *xcst-ledger2* 11 100 *xcst-plen* 100 *xcst-plen* 77 *xcst-c* *xcst-end2*
                                                 *xcst-slots2* *xcst-cells2* *xcst-wins2* *xcst-dst*))
         :span)
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (enable fn-xc-slot-token fn-xc-token fn-xcs-get-kind-is-nth fn-xcs-get-tokp-is-nth fn-xcs-get-tid-is-nth fn-xcs-get-tcid-is-nth fn-xcs-get-file-is-nth fn-xcs-get-eoff-is-nth fn-xcs-get-elen-is-nth fn-xcs-get-a-is-nth fn-xcs-get-b-is-nth fn-xcs-get-c-is-nth fn-xcs-get-d-is-nth fn-xcs-get-start-is-nth fn-xcs-get-trailer-is-nth nth)
                                            (executable-counterpart-theory :here)))))))

; The host installs through fn-xc-install-window-bytes and initialises through
; fn-xc-init-windows: nine windows are refused by name (the fn-xcw row count is
; the profile's eight), eight are laid out, and an install stores the plan and
; the staged octets with the slot.
(xcst-ground-witness xcst-init-windows-refuses-nine-and-readies-eight ()
  (and (equal (mv-nth 0 (fn-xc-init-windows 0 9 nil nil)) :refused-window-rows)
       (equal (mv-nth 1 (fn-xc-init-windows 0 9 nil nil)) nil)
       (equal (mv-nth 2 (fn-xc-init-windows 0 9 nil nil)) nil)
       (equal (mv-nth 0 (fn-xc-init-windows 0 8 nil nil)) :initialized)
       (equal (fn-xc-nw (mv-nth 2 (fn-xc-init-windows 0 8 nil nil))) 8)))

(xcst-ground-witness xcst-install-window-bytes-stores-the-pair ()
  (let* ((free '(0 nil 0 0 0 0 0 0 0 0 0 0 0 0))
         (r (fn-xc-install-window-bytes *xcst-token* *xcst-plan* (list free free) '(1 0 2)
                                        (list (list nil nil) (list *xcst-window* *xcst-window*))
                                        *xcst-window*)))
    (and (equal (mv-nth 0 r) :installed) (equal (mv-nth 1 r) 0)
         (equal (fn-xcw-plan 0 (mv-nth 5 r)) *xcst-plan*)
         (equal (take 3 (nth 0 (fn-xcw-window 0 (mv-nth 5 r)))) '(1 2 3))
         (equal (fn-xcw-plan 1 (mv-nth 5 r)) nil)
         (equal (mv-nth 0 (fn-xc-install-window-bytes *xcst-token* *xcst-plan* nil '(1 0 0)
                                                      (list (list nil nil) (list *xcst-window* *xcst-window*))
                                                      *xcst-window*))
                :refused)
         (equal (mv-nth 5 (fn-xc-install-window-bytes *xcst-token* *xcst-plan* nil '(1 0 0)
                                                      (list (list nil nil) (list *xcst-window* *xcst-window*))
                                                      *xcst-window*))
                (list (list nil nil) (list *xcst-window* *xcst-window*))))))

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

; Actual stobj execution, end to end through the host entries: init, two
; installs (the table decision plus the stored plan and window), then one
; walk.  The host's publication provenance is fn-pwc-cache-only-a-published-window,
; not these fixtures.
(defun xcst-native-single (fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span) :verify-guards nil))
  (let* ((fn-xcs (fn-xcs-clear fn-xcs)) (fn-xcc (fn-xcc-clear fn-xcc))
         (fn-ew-buffer (update-fn-ew-bytesi 0 1 fn-ew-buffer))
         (fn-ew-buffer (update-fn-ew-bytesi 1 2 fn-ew-buffer))
         (fn-ew-buffer (update-fn-ew-bytesi 2 3 fn-ew-buffer)))
    (mv-let (init fn-xcs fn-xcc) (fn-xc-init-windows 0 2 fn-xcs fn-xcc)
      (mv-let (installed target evicted fn-xcs fn-xcc fn-xcw)
        (fn-xc-install-window-bytes *xcst-token* *xcst-plan* fn-xcs fn-xcc fn-xcw fn-ew-buffer)
        (mv-let (lookup found)
          (fn-xc-lookup 0 2 11 100 3 100 3 0 0 77 1 fn-xcs fn-xcc)
          (mv-let (word count slot fn-ew-span fn-xcs fn-xcc)
            (fn-xc-span-at 0 *xcst-cached* 11 100 3 100 3 77 1 99 fn-xcs fn-xcc fn-xcw fn-ew-span)
            (mv (and (equal init :initialized) (equal installed :installed) (equal target 0) (not evicted)
                     (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                     (fn-ew-bufferp fn-ew-buffer) (fn-ew-spanp fn-ew-span) (fn-xcwp fn-xcw)
                     (equal lookup :hit) (equal found 0)
                     (equal (fn-xcw-plansi 0 fn-xcw) *xcst-plan*)
                     (equal word :span) (equal count 2) (equal slot 0)
                     (equal (fn-ew-span-bytesi 0 fn-ew-span) 2)
                     (equal (fn-ew-span-bytesi 1 fn-ew-span) 3)
                     (equal (fn-xcs-get-stamp 0 fn-xcs) 1) (equal (fn-xc-tick fn-xcc) 2)
                     (fn-xc-token-disjointp fn-xcs))
                fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span)))))))

(assert-event (xcst-native-single fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span)
         :stobjs-out '(nil fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span))

; S's counterexample on live stobjs: window [0,C) in slot 0 and [C,C+3) in
; slot 1; a request at p = C selects slot 0 first, which cannot supply the
; octet, and the walk answers from slot 1.
(defun xcst-native-two-windows (fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span) :verify-guards nil))
  (let* ((fn-xcs (fn-xcs-clear fn-xcs)) (fn-xcc (fn-xcc-clear fn-xcc))
         (fn-ew-buffer (update-fn-ew-bytesi 0 4 fn-ew-buffer))
         (fn-ew-buffer (update-fn-ew-bytesi 1 5 fn-ew-buffer))
         (fn-ew-buffer (update-fn-ew-bytesi 2 6 fn-ew-buffer)))
    (mv-let (init fn-xcs fn-xcc) (fn-xc-init-windows 0 2 fn-xcs fn-xcc)
      (mv-let (w0 s0 e0 fn-xcs fn-xcc fn-xcw)
        (fn-xc-install-window-bytes *xcst-t0* *xcst-p0* fn-xcs fn-xcc fn-xcw fn-ew-buffer)
        (let* ((fn-ew-buffer (update-fn-ew-bytesi 0 7 fn-ew-buffer))
               (fn-ew-buffer (update-fn-ew-bytesi 1 8 fn-ew-buffer))
               (fn-ew-buffer (update-fn-ew-bytesi 2 9 fn-ew-buffer)))
          (mv-let (w1 s1 e1 fn-xcs fn-xcc fn-xcw)
            (fn-xc-install-window-bytes *xcst-t1* *xcst-p1* fn-xcs fn-xcc fn-xcw fn-ew-buffer)
            (mv-let (first-word first-slot)
              (fn-xc-lookup 0 2 11 100 *xcst-plen* 100 *xcst-plen* 0 0 77 *xcst-c* fn-xcs fn-xcc)
              (mv-let (word count slot fn-ew-span fn-xcs fn-xcc)
                (fn-xc-span-at 0 *xcst-ledger2* 11 100 *xcst-plen* 100 *xcst-plen* 77 *xcst-c* *xcst-end2*
                               fn-xcs fn-xcc fn-xcw fn-ew-span)
                (mv (and (equal init :initialized)
                         (equal w0 :installed) (equal s0 0) (not e0)
                         (equal w1 :installed) (equal s1 1) (not e1)
                         (equal first-word :hit) (equal first-slot 0)
                         (equal (fn-xcw-plansi 0 fn-xcw) *xcst-p0*)
                         (equal (fn-xcw-plansi 1 fn-xcw) *xcst-p1*)
                         (equal word :span) (equal count 3) (equal slot 1)
                         (equal (fn-ew-span-bytesi 0 fn-ew-span) 7)
                         (equal (fn-ew-span-bytesi 1 fn-ew-span) 8)
                         (equal (fn-ew-span-bytesi 2 fn-ew-span) 9)
                         (equal (fn-xcs-get-stamp 1 fn-xcs) 2))
                    fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span)))))))))

(assert-event (xcst-native-two-windows fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span)
         :stobjs-out '(nil fn-xcs fn-xcc fn-xcw fn-ew-buffer fn-ew-span))


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

; Original-contract counterexamples under the guarded install.
; Each asserts the complete original antecedent and refutes its conclusion.
; Forms copied from origin/lane/s-extent-cache@248809ad2; only ground substitution.

(xcst-ground-witness xcst-old-install-when-present-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 8 0 11 100 3 100 3 1 0 0 77 0) (2 t 7 0 11 100 3 100 3 0 0 0 77 1))) (fn-xcc '(2 0 2)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs)) (not (let ((p (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                trailer start fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-install-call)) :present)
                  (equal (mv-nth 1 (fn-xc-install-call)) p)
                  (equal (mv-nth 2 (fn-xc-install-call)) nil)
                  (equal (mv-nth 3 (fn-xc-install-call)) (mv-nth 1 (fn-xc-touch p fn-xcs fn-xcc)))
                  (equal (mv-nth 4 (fn-xc-install-call)) (mv-nth 2 (fn-xc-touch p fn-xcs fn-xcc))))))))

(xcst-ground-witness xcst-old-install-when-present-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 8 9 11 100 3 1 0 0 0 0 77 0) (1 t 7 9 11 100 3 0 0 0 0 0 77 1))) (fn-xcc '(2 2 0)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs)) (not (let ((p (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                trailer start fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-install-call)) :present)
                  (equal (mv-nth 1 (fn-xc-install-call)) p)
                  (equal (mv-nth 2 (fn-xc-install-call)) nil)
                  (equal (mv-nth 3 (fn-xc-install-call)) (mv-nth 1 (fn-xc-touch p fn-xcs fn-xcc)))
                  (equal (mv-nth 4 (fn-xc-install-call)) (mv-nth 2 (fn-xc-touch p fn-xcs fn-xcc))))))))

(xcst-ground-witness xcst-old-install-when-free-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 7 0 11 100 3 100 3 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 0 2)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (not (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                 trailer start fn-xcs))
                (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)) (not (let ((f (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-install-call)) :installed)
                  (equal (mv-nth 1 (fn-xc-install-call)) f)
                  (equal (mv-nth 2 (fn-xc-install-call)) nil)
                  (equal (mv-nth 3 (fn-xc-install-call))
                         (fn-xc-write f kind tokp tid tcid file eoff elen a b c d start trailer
                                      (fn-xc-tick fn-xcc) fn-xcs))
                  (equal (mv-nth 4 (fn-xc-install-call)) (mv-nth 1 (fn-xc-next-stamp fn-xcc))))))))

(xcst-ground-witness xcst-old-install-when-free-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 7 9 11 100 3 0 0 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 2 0)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (not (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                 trailer start fn-xcs))
                (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)) (not (let ((f (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-install-call)) :installed)
                  (equal (mv-nth 1 (fn-xc-install-call)) f)
                  (equal (mv-nth 2 (fn-xc-install-call)) nil)
                  (equal (mv-nth 3 (fn-xc-install-call))
                         (fn-xc-write f kind tokp tid tcid file eoff elen a b c d start trailer
                                      (fn-xc-tick fn-xcc) fn-xcs))
                  (equal (mv-nth 4 (fn-xc-install-call)) (mv-nth 1 (fn-xc-next-stamp fn-xcc))))))))

(xcst-ground-witness xcst-old-install-when-full-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 7 0 11 100 3 100 3 0 0 0 77 1) (2 t 8 0 11 100 3 100 3 2 0 0 77 0))) (fn-xcc '(2 0 2)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (not (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                 trailer start fn-xcs))
                (not (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))) (not (let ((v (fn-xc-lru (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) nil fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-install-call)) :replaced)
                  (equal (mv-nth 1 (fn-xc-install-call)) v)
                  (equal (mv-nth 2 (fn-xc-install-call)) (fn-xc-slot-token v fn-xcs))
                  (equal (mv-nth 3 (fn-xc-install-call))
                         (fn-xc-write v kind tokp tid tcid file eoff elen a b c d start trailer
                                      (fn-xc-tick fn-xcc) fn-xcs))
                  (equal (mv-nth 4 (fn-xc-install-call)) (mv-nth 1 (fn-xc-next-stamp fn-xcc))))))))

(xcst-ground-witness xcst-old-install-when-full-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 7 9 11 100 3 0 0 0 0 0 77 1) (1 t 8 9 11 100 3 2 0 0 0 0 77 0))) (fn-xcc '(2 2 0)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (not (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                 trailer start fn-xcs))
                (not (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))) (not (let ((v (fn-xc-lru (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) nil fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-install-call)) :replaced)
                  (equal (mv-nth 1 (fn-xc-install-call)) v)
                  (equal (mv-nth 2 (fn-xc-install-call)) (fn-xc-slot-token v fn-xcs))
                  (equal (mv-nth 3 (fn-xc-install-call))
                         (fn-xc-write v kind tokp tid tcid file eoff elen a b c d start trailer
                                      (fn-xc-tick fn-xcc) fn-xcs))
                  (equal (mv-nth 4 (fn-xc-install-call)) (mv-nth 1 (fn-xc-next-stamp fn-xcc))))))))

(xcst-ground-witness xcst-old-install-then-lookup-hits-free-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 7 0 11 100 3 100 3 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 0 2)) (j 0))
  (and (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)) (not (fn-xc-lookup-after-install))))

(xcst-ground-witness xcst-old-install-then-lookup-hits-free-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 7 9 11 100 3 0 0 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 2 0)) (j 0))
  (and (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)) (not (fn-xc-lookup-after-install))))

(xcst-ground-witness xcst-old-install-then-lookup-hits-full-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 7 0 11 100 3 100 3 0 0 0 77 1) (2 t 8 0 11 100 3 100 3 2 0 0 77 0))) (fn-xcc '(2 0 2)) (j 0))
  (and (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (not (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))) (not (fn-xc-lookup-after-install))))

(xcst-ground-witness xcst-old-install-then-lookup-hits-full-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 7 9 11 100 3 0 0 0 0 0 77 1) (1 t 8 9 11 100 3 2 0 0 0 0 77 0))) (fn-xcc '(2 2 0)) (j 0))
  (and (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (not (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))) (not (fn-xc-lookup-after-install))))

(xcst-ground-witness xcst-old-install-then-lookup-hits-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 7 0 11 100 3 100 3 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 0 2)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer
                                                      fn-xcs fn-xcc))
                            :refused))) (not (fn-xc-lookup-after-install))))

(xcst-ground-witness xcst-old-install-then-lookup-hits-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 7 9 11 100 3 0 0 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 2 0)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer
                                                      fn-xcs fn-xcc))
                            :refused))) (not (fn-xc-lookup-after-install))))

(xcst-ground-witness xcst-old-install-present-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 8 0 11 100 3 100 3 1 0 0 77 0) (2 t 7 0 11 100 3 100 3 0 0 0 77 1))) (fn-xcc '(2 0 2)) (j 0))
  (and (and (fn-xc-case-hyps)
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs)) (not (let ((v (mv-nth 1 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :present)
                  (equal (mv-nth 2 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) nil)
                  (fn-xc-slot-matchp v t kind file eoff elen a b c d trailer start fn-xcs)
                  (implies (and (natp j) (not (equal j v)))
                           (equal (nth j (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))) (nth j fn-xcs))))))))

(xcst-ground-witness xcst-old-install-present-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 8 9 11 100 3 1 0 0 0 0 77 0) (1 t 7 9 11 100 3 0 0 0 0 0 77 1))) (fn-xcc '(2 2 0)) (j 0))
  (and (and (fn-xc-case-hyps)
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs)) (not (let ((v (mv-nth 1 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :present)
                  (equal (mv-nth 2 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) nil)
                  (fn-xc-slot-matchp v t kind file eoff elen a b c d trailer start fn-xcs)
                  (implies (and (natp j) (not (equal j v)))
                           (equal (nth j (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))) (nth j fn-xcs))))))))

(xcst-ground-witness xcst-old-install-fills-a-free-slot-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 7 0 11 100 3 100 3 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 0 2)) (j 0))
  (and (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)) (not (let ((v (mv-nth 1 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :installed)
                  (equal (mv-nth 2 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) nil)
                  (equal (fn-xcs-get-kind v fn-xcs) 0)
                  (implies (and (natp j) (not (equal j v)))
                           (equal (nth j (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))) (nth j fn-xcs))))))))

(xcst-ground-witness xcst-old-install-fills-a-free-slot-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 7 9 11 100 3 0 0 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 2 0)) (j 0))
  (and (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)) (not (let ((v (mv-nth 1 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :installed)
                  (equal (mv-nth 2 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) nil)
                  (equal (fn-xcs-get-kind v fn-xcs) 0)
                  (implies (and (natp j) (not (equal j v)))
                           (equal (nth j (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))) (nth j fn-xcs))))))))

(xcst-ground-witness xcst-old-install-evicts-the-least-recently-used-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 7 0 11 100 3 100 3 0 0 0 77 1) (2 t 8 0 11 100 3 100 3 2 0 0 77 0))) (fn-xcc '(2 0 2)) (j 0))
  (and (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (not (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))) (not (let ((v (mv-nth 1 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :replaced)
                  (natp v) (<= (fn-xc-lo kind fn-xcc) v) (< v (fn-xc-hi kind fn-xcc))
                  (not (equal (fn-xcs-get-kind v fn-xcs) 0))
                  (equal (mv-nth 2 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) (fn-xc-slot-token v fn-xcs))
                  ; every slot of the region was live, and none is older than the victim
                  (implies (and (natp j) (<= (fn-xc-lo kind fn-xcc) j) (< j (fn-xc-hi kind fn-xcc)))
                           (and (not (equal (fn-xcs-get-kind j fn-xcs) 0))
                                (<= (fn-xcs-get-stamp v fn-xcs) (fn-xcs-get-stamp j fn-xcs))))
                  (implies (and (natp j) (not (equal j v)))
                           (equal (nth j (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))) (nth j fn-xcs))))))))

(xcst-ground-witness xcst-old-install-evicts-the-least-recently-used-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 7 9 11 100 3 0 0 0 0 0 77 1) (1 t 8 9 11 100 3 2 0 0 0 0 77 0))) (fn-xcc '(2 2 0)) (j 0))
  (and (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (not (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))) (not (let ((v (mv-nth 1 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :replaced)
                  (natp v) (<= (fn-xc-lo kind fn-xcc) v) (< v (fn-xc-hi kind fn-xcc))
                  (not (equal (fn-xcs-get-kind v fn-xcs) 0))
                  (equal (mv-nth 2 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) (fn-xc-slot-token v fn-xcs))
                  ; every slot of the region was live, and none is older than the victim
                  (implies (and (natp j) (<= (fn-xc-lo kind fn-xcc) j) (< j (fn-xc-hi kind fn-xcc)))
                           (and (not (equal (fn-xcs-get-kind j fn-xcs) 0))
                                (<= (fn-xcs-get-stamp v fn-xcs) (fn-xcs-get-stamp j fn-xcs))))
                  (implies (and (natp j) (not (equal j v)))
                           (equal (nth j (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))) (nth j fn-xcs))))))))

(xcst-ground-witness xcst-old-install-placement-kind2-counterexample ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 7 0 11 100 3 100 3 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 0 2)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) (not (let* ((r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))
                  (word (mv-nth 0 r)) (v (mv-nth 1 r)) (s2 (mv-nth 3 r)) (c2 (mv-nth 4 r)))
             (and (member-equal word '(:installed :replaced :present :refused))
                  ; refused exactly when the region is empty: the cache is off for this kind
                  (iff (equal word :refused) (equal (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc)))
                  (implies (not (equal word :refused))
                           (and (natp v) (<= (fn-xc-lo kind fn-xcc) v) (< v (fn-xc-hi kind fn-xcc))))
                  (fn-xcsp s2) (fn-xccp c2)
                  (equal (fn-xcs-count s2) (fn-xcs-count fn-xcs))
                  (equal (fn-xc-ne c2) (fn-xc-ne fn-xcc))
                  (equal (fn-xc-nw c2) (fn-xc-nw fn-xcc))
                  (fn-xc-readyp s2 c2))))))

(xcst-ground-witness xcst-old-install-placement-kind1-counterexample ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 7 9 11 100 3 0 0 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 2 0)) (j 0))
  (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) (not (let* ((r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))
                  (word (mv-nth 0 r)) (v (mv-nth 1 r)) (s2 (mv-nth 3 r)) (c2 (mv-nth 4 r)))
             (and (member-equal word '(:installed :replaced :present :refused))
                  ; refused exactly when the region is empty: the cache is off for this kind
                  (iff (equal word :refused) (equal (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc)))
                  (implies (not (equal word :refused))
                           (and (natp v) (<= (fn-xc-lo kind fn-xcc) v) (< v (fn-xc-hi kind fn-xcc))))
                  (fn-xcsp s2) (fn-xccp c2)
                  (equal (fn-xcs-count s2) (fn-xcs-count fn-xcs))
                  (equal (fn-xc-ne c2) (fn-xc-ne fn-xcc))
                  (equal (fn-xc-nw c2) (fn-xc-nw fn-xcc))
                  (fn-xc-readyp s2 c2))))))

; The two old contracts that remain true, including duplicate answers.
(xcst-ground-witness xcst-original-install-occupancy-kind2-still-holds ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 7 0 11 100 3 100 3 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 0 2)) (j 0))
 (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
        (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
        (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))
                    :refused))) (let ((n0 (fn-xc-live-count (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))
                 (n1 (fn-xc-live-count (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)))))
             (and (equal n1 (if (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :installed) (+ 1 n0) n0))
                  (<= n1 (- (fn-xc-hi kind fn-xcc) (fn-xc-lo kind fn-xcc))))) (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))

(xcst-ground-witness xcst-original-install-occupancy-kind1-still-holds ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 7 9 11 100 3 0 0 0 0 0 77 0) (0 nil 0 0 0 0 0 0 0 0 0 0 0 0))) (fn-xcc '(1 2 0)) (j 0))
 (and (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
        (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
        (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))
                    :refused))) (let ((n0 (fn-xc-live-count (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))
                 (n1 (fn-xc-live-count (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)))))
             (and (equal n1 (if (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :installed) (+ 1 n0) n0))
                  (<= n1 (- (fn-xc-hi kind fn-xcc) (fn-xc-lo kind fn-xcc))))) (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))

(xcst-ground-witness xcst-original-install-then-lookup-hits-present-kind2-still-holds ((kind 2) (tokp t) (tid 7) (tcid 0) (file 11) (eoff 100) (elen 3) (a 100) (b 3) (c 1) (d 0) (start 0) (trailer 77) (fn-xcs '((2 t 8 0 11 100 3 100 3 1 0 0 77 0) (2 t 7 0 11 100 3 100 3 0 0 0 77 1))) (fn-xcc '(2 0 2)) (j 0))
 (and (and (fn-xc-case-hyps)
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs)) (fn-xc-lookup-after-install) (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))

(xcst-ground-witness xcst-original-install-then-lookup-hits-present-kind1-still-holds ((kind 1) (tokp t) (tid 7) (tcid 9) (file 11) (eoff 100) (elen 3) (a 1) (b 0) (c 0) (d 0) (start 0) (trailer 77) (fn-xcs '((1 t 8 9 11 100 3 1 0 0 0 0 77 0) (1 t 7 9 11 100 3 0 0 0 0 0 77 1))) (fn-xcc '(2 2 0)) (j 0))
 (and (and (fn-xc-case-hyps)
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs)) (fn-xc-lookup-after-install) (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))

(defteeth-check)
