(in-package "ACL2")
(include-book "../../books/obligation-configured-bounds")

; Actual observed recovery of two independent undertakings for one subject.
; The live view is reconstructed at this boundary, then queried directly.
(defconst *rovcbt-events*
  (list (fn-store-retention-event-make :undertake 0 0 0 "a" "shared" "ea" 7)
        (fn-store-retention-event-make :undertake 1 1 1 "b" "shared" "eb" 11)))
(defconst *rovcbt-open*
  (fn-cpo-open-observed (list *fn-cfg-default-record*) 2 *rovcbt-events*))
(defconst *rovcbt-store* (fn-sn-open-state *rovcbt-open*))
(defconst *rovcbt-ledger* (fn-node-retention (fn-sn-node *rovcbt-store*)))
(defconst *rovcbt-view* (fn-rov-build (fn-retain-pins *rovcbt-ledger*)))
(in-theory (disable (:executable-counterpart fn-rov-correspondp)
                    (:executable-counterpart fn-vdc-correspondp)))

(defthm rovcbt-live-configured-word-bounds
  (and (fn-sn-open-okp *rovcbt-open*)
       (fn-cst-relation *rovcbt-store*)
       (fn-rov-correspondp *rovcbt-view* (fn-retain-pins *rovcbt-ledger*))
       (equal (fn-rov-count *rovcbt-view*) 2)
       (equal (fn-rov-subject "shared" *rovcbt-view*) '(2 . 18))
       (unsigned-byte-p 32 (fn-retain-capacity *rovcbt-ledger*))
       (unsigned-byte-p 64 (fn-rov-count *rovcbt-view*))
       (unsigned-byte-p 64 (car (fn-rov-subject "shared" *rovcbt-view*)))
       (unsigned-byte-p 64 (cdr (fn-rov-subject "shared" *rovcbt-view*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rov-build-corresponds
                         (pins (fn-retain-pins *rovcbt-ledger*)))))))

; Corrupted carried total: retain the full phase-aware configured relation,
; violate correspondence, and fail the literal uint64 conclusion.
(defconst *rovcbt-bad-view* (cons (expt 2 64) (cdr *rovcbt-view*)))
(defthm rovcbt-corrupt-total-removes-correspondence
  (and (fn-cst-relation *rovcbt-store*)
       (not (fn-rov-correspondp *rovcbt-bad-view* (fn-retain-pins *rovcbt-ledger*)))
       (not (unsigned-byte-p 64 (fn-rov-count *rovcbt-bad-view*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rov-correspondp))))

; Corrupted node/configuration link: ledger and view agree, but this node
; was never installed by configured recovery. Preserve correspondence and
; fail the literal word bound without adding an artificial runtime ceiling.
(defconst *rovcbt-wide-ledger*
  (fn-retain-admit (fn-retain-initial-state (expt 2 64))
                   "wide" "wide" :forward "proof" (expt 2 64)))
(defconst *rovcbt-wide-node*
  (fn-node-make-state (fn-node-acceptance (fn-sn-node *rovcbt-store*))
                     *rovcbt-wide-ledger* nil nil))
(defconst *rovcbt-wide-store*
  (fn-sn-update *rovcbt-store* (fn-sn-files *rovcbt-store*) *rovcbt-wide-node*))
(defconst *rovcbt-wide-view* (fn-rov-build (fn-retain-pins *rovcbt-wide-ledger*)))
(defthm rovcbt-corrupt-configuration-removes-relation
  (and (not (fn-cst-relation *rovcbt-wide-store*))
       (not (unsigned-byte-p 32 (fn-retain-capacity *rovcbt-wide-ledger*)))
       (fn-rov-correspondp *rovcbt-wide-view*
         (fn-retain-pins (fn-node-retention (fn-sn-node *rovcbt-wide-store*))))
       (not (unsigned-byte-p 64 (cdr (fn-rov-subject "wide" *rovcbt-wide-view*)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rov-build-corresponds
                         (pins (fn-retain-pins *rovcbt-wide-ledger*)))))))
