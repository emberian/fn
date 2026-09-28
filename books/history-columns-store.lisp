; fn: the history stobj kept equal to the store's history across the owner
; (lane history-columns, stage 2a, 2026-09-27; PRF-301).
;
; books/history-columns.lisp is the stobj; this book is the relation the
; host maintains between it and the owner it holds:
;
;   R(o, fn-hist) :=  fn-hist = (fn-sf-records (fn-sn-files (fn-own-store o)))
;
; ESTABLISHED at every open by `fn-hist-load' of the opened history
; (`fn-hist-load-is-the-history', books/history-columns.lisp).  PRESERVED by
; `fn-hist-sync', which the host runs after owner steps: it appends the
; history's rows from the stobj's count to the history's count, reading
; each through `fn-sf-records-nth' (the snoc-list's newest end: O(distance
; from the newest), so O(1) per step that committed one record).  The
; history only grows under the owner relation (`fn-own-run-records-prefix',
; books/owner-invariants-served.lisp), so after ANY run of owner steps the
; synced stobj is the new history (KEYSTONE
; `fn-hist-sync-after-run-is-the-history').  No whole-state revalidation:
; the sync reads only the rows past the stobj's count.

(in-package "ACL2")
(include-book "history-columns-relation")
(include-book "owner-invariants-served")
(include-book "store-carried-folds")

(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-nntp-available-number-article-is-projectable))))

; fn-hist-sync and fn-hist-sync-of-prefix-is-the-history: books/history-columns-relation.lisp.

(local
 (defthm fn-hist-nthcdr-unroll
   (implies (and (natp k) (< k (len xs)))
            (equal (nthcdr k xs) (cons (nth k xs) (nthcdr (1+ k) xs))))))
(local (in-theory (disable fn-hist-nthcdr-unroll)))

(local
 (defthm fn-hist-own-relation-records-true-listp
   (implies (fn-own-relation o)
            (true-listp (fn-sf-records (fn-sn-files (fn-own-store o)))))
   :hints (("Goal" :in-theory (e/d (fn-own-relation) (fn-own-related-records-true-list))
            :use ((:instance fn-own-related-records-true-list (s (fn-own-store o))))))))

; KEYSTONE (the relation is preserved): the stobj equal to an owner's
; history before any run of owner steps, synced against the store after
; the run, is the history after it.
(defthm fn-hist-sync-after-run-is-the-history
  (implies (and (fn-own-relation o)
                (equal fn-hist (fn-sf-records (fn-sn-files (fn-own-store o)))))
           (equal (fn-hist-sync (fn-sn-files (fn-own-store (fn-own-run o events fn-arena)))
                                fn-hist)
                  (fn-sf-records (fn-sn-files (fn-own-store (fn-own-run o events fn-arena))))))
  :hints (("Goal" :use ((:instance fn-own-run-records-prefix)
                        (:instance fn-own-run-preserves-relation)
                        (:instance fn-hist-own-relation-records-true-listp
                                   (o (fn-own-run o events fn-arena))))
           :in-theory (disable fn-own-run-records-prefix fn-own-run-preserves-relation
                               fn-hist-own-relation-records-true-listp
                               fn-own-relation fn-own-run))))

; -----------------------------------------------------------------------------
; The store node's non-article readers, read from the history stobj
; (PKT-PRS-4: the carried folds of store-budget and store-carried-folds read
; sequences K .. count-1 through the index; here through `fn-hist-at', one
; array read each).  Each twin is the EXTEND specification its index
; version is proved to meet (fn-sbud-bytes-extend, fn-cvec-debt-extend,
; fn-pcb-usage-extend) under R alone, for every cache: no index, no
; `fn-ceis-indexedp', no bound on the history's length.

(defun fn-hist-octets-advance (k count sum fn-hist)
  (declare (xargs :stobjs fn-hist
                  :guard (and (natp k) (natp count) (acl2-numberp sum)
                              (<= count (fn-hist-count fn-hist)))
                  :measure (nfix (- (nfix count) (nfix k)))
                  :verify-guards nil))
  (if (and (natp k) (natp count) (< k count))
      (fn-hist-octets-advance (1+ k) count
                              (+ sum (fn-sbud-row-octets (fn-hist-at k fn-hist)))
                              fn-hist)
    sum))

(defun fn-hist-bytes-carried (cache s fn-hist)
  (declare (xargs :stobjs fn-hist :guard t :verify-guards nil))
  (let ((count (fn-hist-count fn-hist)))
    (if (and (consp cache) (natp (car cache)) (natp (cdr cache))
             (<= (car cache) count))
        (fn-hist-octets-advance (car cache) count (cdr cache) fn-hist)
      (fn-sbud-bytes-used s))))

(defun fn-hist-debt-advance (k count debt fn-hist)
  (declare (xargs :stobjs fn-hist
                  :guard (and (natp k) (natp count) (<= count (fn-hist-count fn-hist)))
                  :measure (nfix (- (nfix count) (nfix k)))
                  :verify-guards nil))
  (if (and (natp k) (natp count) (< k count))
      (fn-hist-debt-advance
       (1+ k) count
       (fn-cvec-debt-step (fn-store-event-kind (fn-hist-at k fn-hist)) debt)
       fn-hist)
    (nfix debt)))

(defun fn-hist-debt-carried (cache s fn-hist)
  (declare (xargs :stobjs fn-hist :guard t :verify-guards nil))
  (let ((count (fn-hist-count fn-hist)))
    (if (and (consp cache) (natp (car cache)) (natp (cdr cache))
             (<= (car cache) count))
        (fn-hist-debt-advance (car cache) count (cdr cache) fn-hist)
      (fn-cvec-record-debt (fn-sf-records (fn-sn-files s))))))

(defun fn-hist-tally-advance (k count tally fn-hist)
  (declare (xargs :stobjs fn-hist
                  :guard (and (natp k) (natp count) (<= count (fn-hist-count fn-hist)))
                  :measure (nfix (- (nfix count) (nfix k)))
                  :verify-guards nil))
  (if (and (natp k) (natp count) (< k count))
      (fn-hist-tally-advance (1+ k) count
                             (fn-scf-tally-step (fn-hist-at k fn-hist) tally)
                             fn-hist)
    tally))

(defun fn-hist-usage-carried (cache s fn-hist)
  (declare (xargs :stobjs fn-hist :guard t :verify-guards nil))
  (let ((count (fn-hist-count fn-hist)))
    (if (and (consp cache) (natp (car cache)) (<= (car cache) count))
        (fn-hist-tally-advance (car cache) count (cdr cache) fn-hist)
      (fn-pcb-tally-records (fn-sf-records (fn-sn-files s)) nil))))

(local
 (defthm fn-hist-octets-nthcdr-step
   (implies (and (natp k) (< k (len records)))
            (equal (fn-sbud-record-octets (nthcdr k records))
                   (+ (fn-sbud-row-octets (nth k records))
                      (fn-sbud-record-octets (nthcdr (1+ k) records)))))
   :hints (("Goal" :in-theory (e/d (fn-sbud-record-octets fn-hist-nthcdr-unroll)
                                   (fn-sbud-row-octets nth nthcdr len))))))

(local
 (defthm fn-hist-debt-nthcdr-step
   (implies (and (natp k) (< k (len records)))
            (equal (fn-cvec-debt-from d (nthcdr k records))
                   (fn-cvec-debt-from (fn-cvec-debt-step
                                       (fn-store-event-kind (nth k records)) d)
                                      (nthcdr (1+ k) records))))
   :hints (("Goal" :in-theory (e/d (fn-cvec-debt-from fn-hist-nthcdr-unroll)
                                   (fn-cvec-debt-step fn-store-event-kind
                                    nth nthcdr len))))))

(local
 (defthm fn-hist-tally-records-of-cons
   (equal (fn-pcb-tally-records (cons record rest) tally)
          (fn-pcb-tally-records rest (fn-scf-tally-step record tally)))
   :hints (("Goal" :expand ((fn-pcb-tally-records (cons record rest) tally))
            :in-theory (e/d (fn-scf-tally-step)
                            (fn-pcb-tally-records fn-pcb-tally-put fn-pcb-usage-plus
                             fn-pcb-tally-get fn-pcb-event-carriage))))))

(local
 (defthm fn-hist-tally-nthcdr-step
   (implies (and (natp k) (< k (len records)))
            (equal (fn-pcb-tally-records (nthcdr k records) tally)
                   (fn-pcb-tally-records (nthcdr (1+ k) records)
                                         (fn-scf-tally-step (nth k records) tally))))
   :hints (("Goal" :in-theory (e/d (fn-hist-nthcdr-unroll)
                                   (fn-pcb-tally-records fn-scf-tally-step
                                    nth nthcdr len))))))

(local
 (defthm fn-hist-nthcdr-past-len
   (implies (and (natp k) (<= (len x) k)) (not (consp (nthcdr k x))))))

(local
 (defthm fn-hist-folds-of-atom
   (implies (not (consp x))
            (and (equal (fn-sbud-record-octets x) 0)
                 (equal (fn-cvec-debt-from d x) (nfix d))
                 (equal (fn-pcb-tally-records x tally) tally)))
   :hints (("Goal" :in-theory (enable fn-sbud-record-octets fn-cvec-debt-from
                                      fn-pcb-tally-records)))))

(local
 (defthm fn-hist-octets-advance-is-suffix
   (implies (and (natp k) (<= k (len h)) (acl2-numberp sum))
            (equal (fn-hist-octets-advance k (len h) sum h)
                   (+ sum (fn-sbud-record-octets (nthcdr k h)))))
   :hints (("Goal" :induct (fn-hist-octets-advance k (len h) sum h)
            :in-theory (disable fn-sbud-row-octets nthcdr nth)))))

(local
 (defthm fn-hist-debt-advance-is-suffix
   (implies (and (natp k) (<= k (len h)))
            (equal (fn-hist-debt-advance k (len h) debt h)
                   (fn-cvec-debt-from debt (nthcdr k h))))
   :hints (("Goal" :induct (fn-hist-debt-advance k (len h) debt h)
            :in-theory (disable fn-cvec-debt-step fn-store-event-kind nthcdr nth)))))

(local
 (defthm fn-hist-tally-advance-is-suffix
   (implies (and (natp k) (<= k (len h)))
            (equal (fn-hist-tally-advance k (len h) tally h)
                   (fn-pcb-tally-records (nthcdr k h) tally)))
   :hints (("Goal" :induct (fn-hist-tally-advance k (len h) tally h)
            :in-theory (disable fn-scf-tally-step fn-pcb-tally-records nthcdr nth)))))

(local
 (defthm fn-hist-pcb-drop-is-nthcdr
   (implies (natp k) (equal (fn-pcb-drop k records) (nthcdr k records)))
   :hints (("Goal" :in-theory (enable fn-pcb-drop nthcdr)))))

; The count (PRF-180's fn-sbud-count, from the stobj).
(defthm fn-hist-count-is-used
  (implies (equal fn-hist (fn-sf-records (fn-sn-files s)))
           (equal (fn-hist-count fn-hist) (fn-sbud-used s)))
  :hints (("Goal" :in-theory (enable fn-sbud-used))))

(defthm fn-hist-bytes-carried-is-bytes-extend
  (implies (equal fn-hist (fn-sf-records (fn-sn-files s)))
           (equal (fn-hist-bytes-carried cache s fn-hist)
                  (fn-sbud-bytes-extend cache (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :in-theory (e/d (fn-sbud-bytes-used fn-sbud-bytes-extend)
                                  (fn-hist-octets-advance fn-sbud-record-octets)))))

(defthm fn-hist-debt-carried-is-debt-extend
  (implies (equal fn-hist (fn-sf-records (fn-sn-files s)))
           (equal (fn-hist-debt-carried cache s fn-hist)
                  (fn-cvec-debt-extend cache (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :in-theory (e/d (fn-cvec-debt-extend)
                                  (fn-hist-debt-advance fn-cvec-debt-from
                                   fn-cvec-record-debt)))))

(defthm fn-hist-usage-carried-is-usage-extend
  (implies (equal fn-hist (fn-sf-records (fn-sn-files s)))
           (equal (fn-hist-usage-carried cache s fn-hist)
                  (fn-pcb-usage-extend cache (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :in-theory (e/d (fn-pcb-usage-extend)
                                  (fn-hist-tally-advance fn-pcb-tally-records)))))

; The carried readers the host calls run guard-verified (stage 2b).
(verify-guards fn-hist-octets-advance)
(verify-guards fn-hist-bytes-carried)
(verify-guards fn-hist-debt-advance)
(verify-guards fn-hist-debt-carried)
(verify-guards fn-hist-tally-advance)
(verify-guards fn-hist-usage-carried)

; The committed record count the host reads is the snoc-list's own count
; (`fn-sf-records-count', O(1): its :exec is the carried count), which is
; `fn-sbud-used' with no relation at all: the budget's count no longer reads
; the store node's event index (PRF-180's `fn-sbud-count', which needed
; `fn-ceis-indexedp').
(defthm fn-sf-records-count-is-used-by-definition
  (equal (fn-sf-records-count (fn-sn-files s)) (fn-sbud-used s))
  :hints (("Goal" :in-theory (enable fn-sbud-used fn-sf-records-count))))
