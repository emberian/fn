; Owner startup discards process-local work; C2 controls precede proofs.
(in-package "ACL2")
(include-book "log-checkpoint-open")
(include-book "log-checkpoint-independent-guards")
(include-book "owner-invariants-relation")
(include-book "defkeystone")
(local (include-book "../tests/acl2/lc-open-id-search-tests"))
; Statement first. Proposed standing DROP: even the :fault projection is empty.
; (defthm fn-lc-opened-owner-has-no-connections
;  (let ((oc (fn-lc-opened-owner
;    (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))))
;   (not (consp (fn-own-conns (fn-ocfg-owner oc))))) :rule-classes nil)
; (defthm fn-lc-opened-owner-has-no-local-work
;  (let ((oc (fn-lc-opened-owner
;    (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))))
;   (let ((o (fn-ocfg-owner oc)))
;    (and (not (consp (fn-own-queue o))) (null (fn-own-inflight o)))))
;  :rule-classes nil)
(local (defun lco-owner-restore-process-state (oc kind)
 (declare (xargs :guard t))
 (let* ((o (fn-ocfg-owner oc))
        (o (if (equal kind :connections)
               (ec-call (update-nth 2 '(old-connection) o))
             (ec-call (update-nth 11 :old-inflight
                        (ec-call (update-nth 10 '(old-queued-request) o)))))))
  (fn-ocfg-make o (fn-ocfg-config oc) (fn-ocfg-pins oc) (fn-ocfg-staged oc)))))

(local (defun lco-owner-clearedp (kind oc)
 (declare (xargs :guard t))
 (let ((o (fn-ocfg-owner oc)))
  (if (equal kind :connections) (not (consp (fn-own-conns o)))
   (and (not (consp (fn-own-queue o))) (null (fn-own-inflight o)))))))

(local (defun lco-owner-clearing-tooth (kind mutant disk r mode configs frontier max-conns segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (mv-let (answer fn-lbc nextdisk nextsegs trace oc)
  (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)
  (declare (ignore answer nextdisk nextsegs trace))
  (mv (lco-owner-clearedp kind (if mutant (lco-owner-restore-process-state oc kind) oc)) fn-lbc))))

(local (defun lco-owner-clearing-control (kind faultp fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (let* ((input (lco-id5-input 1)) (disk (fn-lc-at 0 input))
        (outcome (if faultp nil (fn-lc-at 4 input))))
  (mv-let (answer fn-lbc nextdisk nextsegs trace oc)
   (fn-lc-open disk :lc :eager (fn-lc-at 2 input) 8 4 (fn-lc-at 3 input) outcome fn-lbc)
   (declare (ignore nextdisk nextsegs trace))
   (mv (list answer (not (equal oc :fault))
         (lco-owner-clearedp kind oc)
         (lco-owner-clearedp kind (lco-owner-restore-process-state oc kind))) fn-lbc)))))

(local (defun lco-owner-clearing-run (kind faultp)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (out fn-lbc) (lco-owner-clearing-control kind faultp fn-lbc) out))))

(local (verify-guards lco-owner-clearing-run))

(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
 (assert-event (equal (lco-owner-clearing-run :connections nil) '(:ok t t nil)))
 (assert-event (equal (lco-owner-clearing-run :work nil) '(:ok t t nil)))
 ; Removing the old :fault antecedent still satisfies both conclusions.
 (assert-event (equal (lco-owner-clearing-run :connections t) '(:uncertain nil t nil)))
 (assert-event (equal (lco-owner-clearing-run :work t) '(:uncertain nil t nil))))


(local (defthm lco-start-clears-process
 (let ((o (fn-own-configure (fn-own-start st max-conns) post)))
  (and (equal (fn-own-conns o) nil) (equal (fn-own-queue o) nil)
       (equal (fn-own-inflight o) nil)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-configure fn-own-start fn-own-refresh-keeps-fields
   fn-own-conns-of-fn-own-make fn-own-queue-of-fn-own-make
   fn-own-inflight-of-fn-own-make))))))

(local (defthm lco-install-clears-process
 (and (lco-owner-clearedp :connections (fn-ock-install replayed opened max-conns))
      (lco-owner-clearedp :work (fn-ock-install replayed opened max-conns)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-ock-install lco-owner-clearedp fn-ocfg-owner-of-fn-ocfg-make
   lco-start-clears-process fn-ocfg-owner fn-ocfg-make
   (:executable-counterpart fn-own-conns) (:executable-counterpart fn-own-queue)
   (:executable-counterpart fn-own-inflight) (:executable-counterpart equal)
   (:executable-counterpart not) car-cons cdr-cons))))))

(local (defthm lco-seed-clears-process
 (and (lco-owner-clearedp :connections
        (fn-lc-owner-from-seed seed configs frontier tail max-conns))
      (lco-owner-clearedp :work
        (fn-lc-owner-from-seed seed configs frontier tail max-conns)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-owner-from-seed fn-ock-recover-extended lco-install-clears-process))))))

(local (defthm lco-open-clears-process
 (let ((oc (fn-lc-opened-owner
            (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))))
  (and (lco-owner-clearedp :connections oc) (lco-owner-clearedp :work oc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-open fn-lc-opened-owner fn-lc-at-is-nth nth mv-nth car-cons cdr-cons
   lco-seed-clears-process (:executable-counterpart zp)
   (:executable-counterpart lco-owner-clearedp)))))))

(defthm fn-lc-opened-owner-has-no-connections
 (let ((oc (fn-lc-opened-owner (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))) (not (consp (fn-own-conns (fn-ocfg-owner oc)))))
 :rule-classes nil
 :hints (("Goal" :use lco-open-clears-process
 :in-theory (union-theories (theory 'minimal-theory)
 '(lco-owner-clearedp (:executable-counterpart equal))))))

(defthm fn-lc-opened-owner-has-no-local-work
 (let ((oc (fn-lc-opened-owner (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))) (let ((o (fn-ocfg-owner oc))) (and (not (consp (fn-own-queue o))) (null (fn-own-inflight o)))))
 :rule-classes nil
 :hints (("Goal" :use lco-open-clears-process
 :in-theory (union-theories (theory 'minimal-theory)
 '(lco-owner-clearedp (:executable-counterpart equal))))))

(local (defthm lco-mv-nth-is-nth
 (equal (mv-nth n x) (nth n x))
 :hints (("Goal" :induct (mv-nth n x)
 :in-theory (union-theories (theory 'minimal-theory)
 '(mv-nth nth endp (:induction mv-nth)))))))

(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
(defteeth fn-lc-opened-owner-has-no-connections
 :claim (let ((oc (fn-lc-opened-owner (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))) (() (not (consp (fn-own-conns (fn-ocfg-owner oc))))))
 :subject fn-lc-open
 :witness ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager)
 (configs (fn-lc-at 2 (lco-id5-input 1))) (frontier 8) (max-conns 4)
 (segs (fn-lc-at 3 (lco-id5-input 1))) (outcome (fn-lc-at 4 (lco-id5-input 1))))
 :stobjs ((fn-lbc (fn-lc-teeth-empty-columns fn-lbc)))
 :stobj-checks (((let ((oc (fn-lc-opened-owner (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))) (declare (ignorable oc)) (not (consp (fn-own-conns (fn-ocfg-owner oc)))))
 (lco-owner-clearing-tooth :connections nil disk r mode configs frontier max-conns segs outcome fn-lbc)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lco-owner-clearing-tooth lco-owner-clearedp fn-lc-opened-owner
   fn-lc-at-is-nth lco-mv-nth-is-nth nth mv-nth car-cons cdr-cons (:type-prescription fn-lc-open)
   (:executable-counterpart equal) (:executable-counterpart zp))))))
((let ((oc (fn-lc-opened-owner (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))) (declare (ignorable oc)) (not (consp (fn-own-conns (fn-ocfg-owner (lco-owner-restore-process-state oc :connections))))))
 (lco-owner-clearing-tooth :connections t disk r mode configs frontier max-conns segs outcome fn-lbc)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lco-owner-clearing-tooth lco-owner-clearedp fn-lc-opened-owner
   fn-lc-at-is-nth lco-mv-nth-is-nth nth mv-nth car-cons cdr-cons (:type-prescription fn-lc-open)
   (:executable-counterpart equal) (:executable-counterpart zp)))))))
 :breaks nil
 :mutations ((restore-stale-process-state (:conclusion (not (consp (fn-own-conns (fn-ocfg-owner (lco-owner-restore-process-state oc :connections)))))) nil
 :fault "installing pre-crash process-local state after open")))

(defteeth fn-lc-opened-owner-has-no-local-work
 :claim (let ((oc (fn-lc-opened-owner (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))) (() (let ((o (fn-ocfg-owner oc))) (and (not (consp (fn-own-queue o))) (null (fn-own-inflight o))))))
 :subject fn-lc-open
 :witness ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager)
 (configs (fn-lc-at 2 (lco-id5-input 1))) (frontier 8) (max-conns 4)
 (segs (fn-lc-at 3 (lco-id5-input 1))) (outcome (fn-lc-at 4 (lco-id5-input 1))))
 :stobjs ((fn-lbc (fn-lc-teeth-empty-columns fn-lbc)))
 :stobj-checks (((let ((oc (fn-lc-opened-owner (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))) (declare (ignorable oc)) (let ((o (fn-ocfg-owner oc))) (and (not (consp (fn-own-queue o))) (null (fn-own-inflight o)))))
 (lco-owner-clearing-tooth :work nil disk r mode configs frontier max-conns segs outcome fn-lbc)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lco-owner-clearing-tooth lco-owner-clearedp fn-lc-opened-owner
   fn-lc-at-is-nth lco-mv-nth-is-nth nth mv-nth car-cons cdr-cons (:type-prescription fn-lc-open)
   (:executable-counterpart equal) (:executable-counterpart zp))))))
((let ((oc (fn-lc-opened-owner (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)))) (declare (ignorable oc)) (let ((o (fn-ocfg-owner (lco-owner-restore-process-state oc :work)))) (and (not (consp (fn-own-queue o))) (null (fn-own-inflight o)))))
 (lco-owner-clearing-tooth :work t disk r mode configs frontier max-conns segs outcome fn-lbc)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lco-owner-clearing-tooth lco-owner-clearedp fn-lc-opened-owner
   fn-lc-at-is-nth lco-mv-nth-is-nth nth mv-nth car-cons cdr-cons (:type-prescription fn-lc-open)
   (:executable-counterpart equal) (:executable-counterpart zp)))))))
 :breaks nil
 :mutations ((restore-stale-process-state (:conclusion (let ((o (fn-ocfg-owner (lco-owner-restore-process-state oc :work)))) (and (not (consp (fn-own-queue o))) (null (fn-own-inflight o))))) nil
 :fault "installing pre-crash process-local state after open"))))

(defteeth-check (fn-lc-opened-owner-has-no-connections fn-lc-opened-owner-has-no-local-work))
