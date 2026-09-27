; fn: teeth for books/history-columns-store.lisp (lane history-columns, stage 2a).
;
; What this book is evidence FOR.  `fn-hist-sync-of-prefix-is-the-history'
; and the KEYSTONE `fn-hist-sync-after-run-is-the-history' say the sync the
; host runs keeps the stobj equal to the owner's history; the three
; `-is-...-extend' theorems say the store's carried folds read from the
; stobj are the EXTEND specifications their index versions meet.  The sync
; and the folds run on a live local stobj over a ground store whose history
; mixes held articles and a retention event.

(in-package "ACL2")
(include-book "history-columns-tests")
(include-book "../../books/history-columns-store")
(include-book "owner-operator-tests")
(include-book "must-fail-checked")

(assert-event
 (and (eq (symbol-class 'fn-hist-sync (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hist-sync-aux (w state)) :common-lisp-compliant)))

; A ground store: files whose history is the four plain events of
; history-columns-tests (the composite and the malformed event left out:
; the folds' encoders read wire events), inside an initial store node.
(defconst *hcs-records* (list *hct-a* *hct-b* *hct-retention* *hct-a2*))
(defconst *hcs-files* (fn-sf-make :ready nil nil *hcs-records* nil nil nil nil))
(defconst *hcs-s* (fn-sn-update (fn-sn-initial '("fn.test") 10) *hcs-files*
                                (fn-sn-node (fn-sn-initial '("fn.test") 10))))
(assert-event (equal (fn-sf-records (fn-sn-files *hcs-s*)) *hcs-records*))

; -----------------------------------------------------------------------------
; The sync on a live stobj: load a prefix of K records, sync against the
; files, answer the list.

(defun hcs-sync-run (prefix files)
  (declare (xargs :guard (true-listp prefix)))
  (with-local-stobj fn-hist
    (mv-let (answer fn-hist)
      (let* ((fn-hist (fn-hist-load prefix 77 fn-hist))
             (fn-hist (fn-hist-sync files fn-hist)))
        (mv (hct-ats 0 (fn-hist-count fn-hist) fn-hist) fn-hist))
      answer)))

; fn-hist-sync-of-prefix-is-the-history, positive at every prefix length.
(assert-event (and (fn-sf-prefixp nil *hcs-records*)
                   (equal (hcs-sync-run nil *hcs-files*) *hcs-records*)))
(assert-event (and (fn-sf-prefixp (take 2 *hcs-records*) *hcs-records*)
                   (equal (hcs-sync-run (take 2 *hcs-records*) *hcs-files*)
                          *hcs-records*)))
(assert-event (equal (hcs-sync-run *hcs-records* *hcs-files*) *hcs-records*))
; Removal of the prefix hypothesis: a stobj holding another first record
; keeps it; the sync appends only the rows past its count.
(assert-event (and (not (fn-sf-prefixp (list *hct-b*) *hcs-records*))
                   (true-listp *hcs-records*)
                   (not (equal (hcs-sync-run (list *hct-b*) *hcs-files*)
                               *hcs-records*))))
(must-fail-checked
 (defthm hcs-false-sync-without-prefix
   (implies (true-listp (fn-sf-records files))
            (equal (fn-hist-sync files fn-hist) (fn-sf-records files)))))

; KEYSTONE fn-hist-sync-after-run-is-the-history, positive on a real owner
; (owner-operator-tests' configured owner, related) and a real run.
(defthm hcs-after-run-witness
  (let ((o *opt-bare*)
        (events (list (list :configure *opt-config*) (list :observe *opt-obs*))))
    (and (fn-own-relation o)
         (equal (fn-sf-records (fn-sn-files (fn-own-store o))) nil)
         (equal (fn-hist-sync (fn-sn-files (fn-own-store (fn-own-run o events nil))) nil)
                (fn-sf-records (fn-sn-files (fn-own-store (fn-own-run o events nil)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist-sync fn-hist-sync-aux))))
; Removal of R: a stobj that is not the owner's history before the run.
(defthm hcs-after-run-without-r
  (let ((o *opt-bare*)
        (events (list (list :configure *opt-config*) (list :observe *opt-obs*)))
        (h (list *hct-a*)))
    (and (fn-own-relation o)
         (not (equal h (fn-sf-records (fn-sn-files (fn-own-store o)))))
         (not (equal (fn-hist-sync (fn-sn-files (fn-own-store (fn-own-run o events nil))) h)
                     (fn-sf-records (fn-sn-files (fn-own-store (fn-own-run o events nil))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist-sync fn-hist-sync-aux))))
; Removal of (fn-own-relation o): NOT constructed.  No ground owner whose
; run shrinks or rewrites its history was built here, and the weakened
; theorem is not proved; the hypothesis stays (the record says so).

; -----------------------------------------------------------------------------
; The carried folds from the stobj, on a live stobj, against the EXTEND
; specifications, for a valid cache, an absent one and one past the count.

(defun hcs-folds (records s caches)
  (declare (xargs :guard (true-listp records) :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (answer fn-hist)
      (let ((fn-hist (fn-hist-load records 5 fn-hist)))
        (mv (if (consp caches)
                (list (fn-hist-count fn-hist)
                      (fn-hist-bytes-carried (car caches) s fn-hist)
                      (fn-hist-debt-carried (car caches) s fn-hist)
                      (fn-hist-usage-carried (car caches) s fn-hist))
              nil)
            fn-hist))
      answer)))

(defun hcs-spec (records s cache)
  (declare (xargs :verify-guards nil))
  (list (fn-sbud-used s)
        (fn-sbud-bytes-extend cache records)
        (fn-cvec-debt-extend cache records)
        (fn-pcb-usage-extend cache records)))

(defconst *hcs-cache-bytes* (cons 2 (fn-sbud-record-octets (take 2 *hcs-records*))))
(assert-event (fn-sbud-octets-cache-validp *hcs-cache-bytes* *hcs-records*))
(assert-event (equal (hcs-folds *hcs-records* *hcs-s* (list *hcs-cache-bytes*))
                     (hcs-spec *hcs-records* *hcs-s* *hcs-cache-bytes*)))
(assert-event (equal (hcs-folds *hcs-records* *hcs-s* (list nil))
                     (hcs-spec *hcs-records* *hcs-s* nil)))
(assert-event (equal (hcs-folds *hcs-records* *hcs-s* (list (cons 9 0)))
                     (hcs-spec *hcs-records* *hcs-s* (cons 9 0))))
; Not vacuous: the octets are the held rows' plus the retention event's.
(assert-event (equal (second (hcs-folds *hcs-records* *hcs-s* (list nil)))
                     (fn-sbud-record-octets *hcs-records*)))
(assert-event (< 600 (fn-sbud-record-octets *hcs-records*)))
; Removal of R: a stobj holding two of the four records answers another
; count and other octets than the store's history.
(assert-event (not (equal (hcs-folds (take 2 *hcs-records*) *hcs-s* (list (cons 0 0)))
                          (hcs-spec *hcs-records* *hcs-s* (cons 0 0)))))
(must-fail-checked
 (defthm hcs-false-bytes-without-r
   (equal (fn-hist-bytes-carried cache s fn-hist)
          (fn-sbud-bytes-extend cache (fn-sf-records (fn-sn-files s))))))
