(in-package "ACL2")
(include-book "../../books/retention-obligation-view-bounds")

(defconst *rovbt-max* (- (expt 2 64) 1))
(defconst *rovbt-ledger*
  (fn-retain-admit
   (fn-retain-admit (fn-retain-initial-state *rovbt-max*)
                    "a" "same-subject" :archive "archive-proof" (- *rovbt-max* 1))
   "b" "same-subject" :forward "receipt-proof" 1))
(defconst *rovbt-view* (fn-rov-build (fn-retain-pins *rovbt-ledger*)))
(in-theory (disable (:executable-counterpart fn-rov-correspondp)
                    (:executable-counterpart fn-vdc-correspondp)))

(defthm rovbt-positive-capacity-and-word
  (and (fn-retain-statep *rovbt-ledger*)
       (fn-rov-correspondp *rovbt-view* (fn-retain-pins *rovbt-ledger*))
       (< (fn-retain-capacity *rovbt-ledger*) (expt 2 64))
       (equal (fn-rov-count *rovbt-view*) 2)
       (equal (fn-rov-subject "same-subject" *rovbt-view*) (cons 2 *rovbt-max*))
       (<= (fn-rov-count *rovbt-view*) (fn-retain-capacity *rovbt-ledger*))
       (<= (car (fn-rov-subject "same-subject" *rovbt-view*)) (fn-retain-capacity *rovbt-ledger*))
       (<= (cdr (fn-rov-subject "same-subject" *rovbt-view*)) (fn-retain-capacity *rovbt-ledger*))
       (unsigned-byte-p 64 (fn-rov-count *rovbt-view*))
       (unsigned-byte-p 64 (car (fn-rov-subject "same-subject" *rovbt-view*)))
       (unsigned-byte-p 64 (cdr (fn-rov-subject "same-subject" *rovbt-view*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rov-build-corresponds
                         (pins (fn-retain-pins *rovbt-ledger*)))))))

; Corrupted accounting: correspondence is true but the capacity relation
; is false. This omits exactly the ledger invariant from the capacity theorem.
(defconst *rovbt-bad-ledger* (fn-retain-make-state 0 0 (fn-retain-pins *rovbt-ledger*) nil))
(defthm rovbt-corrupt-ledger-removes-state
  (and (not (fn-retain-statep *rovbt-bad-ledger*))
       (fn-rov-correspondp *rovbt-view* (fn-retain-pins *rovbt-bad-ledger*))
       (not (<= (fn-rov-count *rovbt-view*) (fn-retain-capacity *rovbt-bad-ledger*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rov-build-corresponds
                         (pins (fn-retain-pins *rovbt-ledger*)))))))

; Corrupted total: keep the entire ledger invariant, omit correspondence,
; and fail the capacity conclusion. The subject trie is unchanged.
(defconst *rovbt-bad-view* (cons (+ 1 *rovbt-max*) (cdr *rovbt-view*)))
(defthm rovbt-corrupt-total-removes-correspondence
  (and (fn-retain-statep *rovbt-ledger*)
       (< (fn-retain-capacity *rovbt-ledger*) (expt 2 64))
       (not (unsigned-byte-p 64 (fn-rov-count *rovbt-bad-view*)))
       (not (fn-rov-correspondp *rovbt-bad-view* (fn-retain-pins *rovbt-ledger*)))
       (not (<= (fn-rov-count *rovbt-bad-view*) (fn-retain-capacity *rovbt-ledger*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rov-correspondp))))

; This ledger is valid but its capacity exceeds uint64. Preserve the other
; two hypotheses and fail the word-size conclusion; never truncate it.
(defconst *rovbt-wide-ledger*
  (fn-retain-admit (fn-retain-initial-state (expt 2 64))
                   "wide" "wide-subject" :archive "proof" (expt 2 64)))
(defconst *rovbt-wide-view* (fn-rov-build (fn-retain-pins *rovbt-wide-ledger*)))
(defthm rovbt-wide-capacity-removes-word-bound
  (and (fn-retain-statep *rovbt-wide-ledger*)
       (fn-rov-correspondp *rovbt-wide-view* (fn-retain-pins *rovbt-wide-ledger*))
       (not (< (fn-retain-capacity *rovbt-wide-ledger*) (expt 2 64)))
       (not (unsigned-byte-p 64 (cdr (fn-rov-subject "wide-subject" *rovbt-wide-view*)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rov-build-corresponds
                         (pins (fn-retain-pins *rovbt-wide-ledger*)))))))

; For the literal uint64 theorem, corrupt only the wide ledger's accounting
; and capacity. Its correct wide view still exceeds the word bound.
(defconst *rovbt-bad-wide-ledger*
  (fn-retain-make-state 0 0 (fn-retain-pins *rovbt-wide-ledger*) nil))
(defthm rovbt-corrupt-ledger-removes-word-state
  (and (not (fn-retain-statep *rovbt-bad-wide-ledger*))
       (fn-rov-correspondp *rovbt-wide-view* (fn-retain-pins *rovbt-bad-wide-ledger*))
       (< (fn-retain-capacity *rovbt-bad-wide-ledger*) (expt 2 64))
       (not (unsigned-byte-p 64 (cdr (fn-rov-subject "wide-subject" *rovbt-wide-view*)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rov-build-corresponds
                         (pins (fn-retain-pins *rovbt-wide-ledger*)))))))
