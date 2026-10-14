; Every committed payload handle was allocated before the arena count.
; This is a carried writer invariant, never a served-read revalidation.
(in-package "ACL2")
(include-book "lb-log-model")

(defun fn-lb-log-entries-handles-below (entries n)
 (declare (xargs :guard t))
 (if (consp entries)
  (and (true-listp (car entries)) (natp (nth 5 (car entries)))
       (< (nth 5 (car entries)) (nfix n))
       (fn-lb-log-entries-handles-below (cdr entries) n))
  t))

(defun fn-lb-log-handles-below (log n)
 (declare (xargs :guard t))
 (if (consp log)
  (and (true-listp (car log))
       (fn-lb-log-entries-handles-below (caddr (car log)) n)
       (fn-lb-log-handles-below (cdr log) n))
  t))

(local (defthm fn-lbal-entry-key-is-fresh
 (implies (and (fn-lb-log-entries-handles-below entries n)
               (natp handle) (<= (nfix n) handle))
 (not (fn-lb-log-model-row-entry-in sequence handle entries)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-entries-handles-below fn-lb-log-model-row-entry-in nfix natp nth))))))

(local (defthm fn-lbal-head-entry-key-is-fresh
 (implies (and (consp log) (fn-lb-log-handles-below log n)
              (natp (fn-record-payload row)) (<= (nfix n) (fn-record-payload row)))
 (not (fn-lb-log-model-row-entry-in (fn-record-sequence row) (fn-record-payload row) (caddar log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbal-entry-key-is-fresh (sequence (fn-record-sequence row)) (handle (fn-record-payload row)) (entries (caddar log))))
 :expand ((fn-lb-log-handles-below log n))
 :in-theory (theory 'ground-zero)))))

(defthm fn-lb-log-handles-below-gives-fresh-key
 (implies (and (fn-lb-log-handles-below log n)
              (natp (fn-record-payload row)) (<= (nfix n) (fn-record-payload row)))
 (not (fn-lb-log-model-row-entry row log)))
 :hints (("Goal" :induct (fn-lb-log-handles-below log n)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-row-entry fn-lb-log-handles-below)))
 ("Subgoal *1/1" :use ((:instance fn-lbal-head-entry-key-is-fresh)))))

(local (defthm fn-lbal-entry-allocation-monotone
 (implies (and (fn-lb-log-entries-handles-below entries n) (<= (nfix n) (nfix newn)))
 (fn-lb-log-entries-handles-below entries newn))
 :hints (("Goal" :induct (fn-lb-log-entries-handles-below entries n)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-entries-handles-below))))))

(local (defthm fn-lbal-entry-allocation-of-append
 (equal (fn-lb-log-entries-handles-below (append entries tail) n)
 (and (fn-lb-log-entries-handles-below entries n) (fn-lb-log-entries-handles-below tail n)))
 :hints (("Goal" :induct (append entries tail)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-entries-handles-below binary-append))))))

(local (defthm fn-lbal-segment-append-allocation
 (implies (and (true-listp segment)
 (fn-lb-log-entries-handles-below (caddr segment) n)
 (<= (nfix n) (nfix newn)) (natp (fn-record-payload row)) (< (fn-record-payload row) (nfix newn)))
 (and (true-listp (fn-lb-log-model-append-to-segment row payload segment))
 (fn-lb-log-entries-handles-below (caddr (fn-lb-log-model-append-to-segment row payload segment)) newn)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbal-entry-allocation-monotone (entries (caddr segment))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append-to-segment fn-lbal-entry-allocation-of-append fn-lb-log-entries-handles-below nth true-listp))))))

(local (defthm fn-lbal-empty-entry-allocation-by-definition
 (fn-lb-log-entries-handles-below nil n)
 :hints (("Goal" :in-theory '(fn-lb-log-entries-handles-below)))))

(local (defthm fn-lbal-log-allocation-monotone
 (implies (and (fn-lb-log-handles-below log n) (<= (nfix n) (nfix newn)))
 (fn-lb-log-handles-below log newn))
 :hints (("Goal" :induct (fn-lb-log-handles-below log n)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-handles-below fn-lbal-empty-entry-allocation-by-definition)))
 ("Subgoal *1/1" :use ((:instance fn-lbal-entry-allocation-monotone (entries (caddar log))))))))

(local (defthm fn-lbal-segment-append-same-bound
 (implies (and (true-listp segment) (fn-lb-log-entries-handles-below (caddr segment) n)
 (natp (fn-record-payload row)) (< (fn-record-payload row) (nfix n)))
 (and (true-listp (fn-lb-log-model-append-to-segment row payload segment))
 (fn-lb-log-entries-handles-below (caddr (fn-lb-log-model-append-to-segment row payload segment)) n)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbal-segment-append-allocation (newn n)))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbal-log-append-same-bound
 (implies (and (fn-lb-log-handles-below log n)
 (natp (fn-record-payload row)) (< (fn-record-payload row) (nfix n)))
 (fn-lb-log-handles-below (fn-lb-log-model-append row payload target log) n))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append fn-lb-log-handles-below fn-lbal-segment-append-same-bound fn-lbal-empty-entry-allocation-by-definition true-listp))))))

(defthm fn-lb-log-handles-below-of-append
 (implies (and (fn-lb-log-handles-below log n)
 (<= (nfix n) (nfix newn)) (natp (fn-record-payload row)) (< (fn-record-payload row) (nfix newn)))
 (fn-lb-log-handles-below (fn-lb-log-model-append row payload target log) newn))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbal-log-allocation-monotone)
       (:instance fn-lbal-log-append-same-bound (n newn)))
 :in-theory (theory 'ground-zero))))

(defthm fn-lb-log-handles-below-of-recycle
 (implies (fn-lb-log-handles-below log n)
 (fn-lb-log-handles-below (fn-lb-log-model-recycle target log) n))
 :hints (("Goal" :induct (fn-lb-log-model-recycle target log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-handles-below fn-lb-log-model-recycle)))))

(defthm fn-lb-log-handles-below-of-arena-seal
 (implies (fn-lb-log-handles-below log (fn-arena-count fn-arena))
 (fn-lb-log-handles-below log (fn-arena-count (fn-arena-seal-list payload fn-arena))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbal-log-allocation-monotone (n (fn-arena-count fn-arena)) (newn (fn-arena-count (fn-arena-seal-list payload fn-arena)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len fn-arena-seal-list-len nfix natp)))))
