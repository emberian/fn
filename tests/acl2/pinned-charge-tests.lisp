; Whole PIN/MOST witnesses and separating gaps. Native TEXT cases use the same
; 64 -> 10 bound and a real reclaim, in test_native_pinned_charge.py.
(in-package "ACL2")
(include-book "../../books/owner-memory-stored-charge")
(include-book "../../books/owner-memory-commit")
(include-book "../../books/owner-served-bound")
(include-book "../../books/defkeystone")

(defun pin-held-row (seq octets)
 (declare (xargs :guard (and (natp seq) (natp octets))))
 (fn-held-make seq seq seq "<pin@invalid>" seq '("fn.test") "o0" "s0" "e0" 4 0
  (fn-hf-make octets nil 0 nil)
  (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) nil nil))
(defconst *pin-small-row* (pin-held-row 0 10240))
(defconst *pin-big-row* (pin-held-row 1 65536))
(defconst *pin-big-records* (list *pin-big-row*))
(defconst *pin-big-store*
 (fn-sn-make nil 0 (fn-sf-make nil nil nil *pin-big-records* nil nil nil nil) nil nil nil))
(defconst *pin-profile-10*
 (update-nth 5 1 (update-nth 6 64
 (update-nth 13 32 (update-nth 14 32 (update-nth 15 256
 (fn-bs-profile-preset 128 25165824 10240)))))))
(defconst *pin-profile-64* (update-nth 4 65536 *pin-profile-10*))

(assert-event
 (and (fn-held-p *pin-small-row*) (fn-held-p *pin-big-row*)
      (fn-bs-profile-admittedp *pin-profile-10*)
      (fn-bs-profile-admittedp *pin-profile-64*)) :msg "PIN-FIXTURES-INHABITED")
(assert-event
 (and (equal (fn-adm-stored-article-most (list *pin-small-row*)) 10240)
      (equal (fn-adm-stored-article-most (list *pin-big-row*)) 65536)
      (< 10240 65536)) :msg "PIN-COMMIT-RAISES-GAP")
(defconst *pin-commit-state*
 (let ((initial (fn-sn-initial '("fn.test") 4)))
  (fn-sn-update initial
   (fn-sf-make :record-attempted 2 nil (list *pin-small-row*) *pin-big-row* nil nil
                *fn-sf-recovery-barrier-count*)
   (fn-sn-node initial))))
(assert-event
 (and (fn-sn-statep *pin-commit-state*)
      (equal (fn-sf-phase (fn-sn-files *pin-commit-state*)) :record-attempted)
      (equal (fn-adm-stored-article-most (fn-sf-records (fn-sn-files *pin-commit-state*))) 10240))
 :msg "PIN-REAL-COMMIT-ANTECEDENT")
(assert-event
 (let* ((s *pin-commit-state*) (next (fn-sn-io s :record-directory :ok))
        (before (fn-sf-records (fn-sn-files s)))
        (after (fn-sf-records (fn-sn-files next))) (cache '(1 . 10240)))
  (and (fn-sn-statep s) (fn-adm-stored-most-cache-validp cache before)
       (equal after (append before (list (fn-sf-record-candidate (fn-sn-files s)))))
       (fn-adm-stored-most-cache-validp cache after)
       (equal (fn-adm-stored-most-extend cache after) 65536)
       (< (fn-adm-stored-article-most before) (fn-adm-stored-article-most after))))
 :msg "PIN-REAL-COMMIT-RAISES-WHOLE")
(assert-event
 (let* ((records (list *pin-small-row*)) (more (list *pin-big-row*)) (cache '(1 . 10240)))
  (and (fn-adm-stored-most-cache-validp cache records)
       (fn-adm-stored-most-cache-validp cache (append records more))
       (equal (fn-adm-stored-article-most (append records more))
              (max (fn-adm-stored-article-most records)
                   (fn-adm-stored-article-most more)))
       (equal (fn-adm-stored-most-extend cache (append records more)) 65536)))
 :msg "PIN-COMMIT-RAISES-WHOLE")

(assert-event
 (let* ((before (list *pin-small-row* *pin-big-row*))
        (after (list *pin-small-row*))
        (old '(2 . 65536)) (reset '(0 . 0)))
  (and (fn-adm-stored-most-cache-validp old before)
       (fn-adm-stored-most-cache-validp reset after)
       (equal (fn-adm-stored-most-extend old before) 65536)
       (equal (fn-adm-stored-most-extend reset after) 10240)
       (not (fn-adm-stored-most-cache-validp old after))))
 :msg "PIN-RECLAIM-LOWERS-WHOLE")
(assert-event
 (< (fn-adm-stored-most-extend '(0 . 0) (list *pin-small-row*))
    (fn-adm-stored-most-extend '(2 . 65536) (list *pin-small-row* *pin-big-row*)))
 :msg "PIN-RECLAIM-LOWERS-GAP")

; R is proof-only on the served path. This test-only executable checker
; reads every fixture row, with an unconditional logical equality bridge.
(defun pin-history-matches (rows k fn-hist)
 (declare (xargs :stobjs fn-hist :guard (and (true-listp rows) (natp k)
                                           (<= (+ k (len rows)) (fn-hist-count fn-hist)))))
 (if (consp rows)
     (and (equal (car rows) (fn-hist-at k fn-hist))
          (pin-history-matches (cdr rows) (1+ k) fn-hist))
   t))
(local
 (defthm pin-history-nthcdr-unroll
  (implies (and (natp k) (< k (len h)))
   (equal (nthcdr k h) (cons (nth k h) (nthcdr (1+ k) h))))
  :hints (("Goal" :in-theory (enable nthcdr nth)))))
(local
 (defthm pin-history-nthcdr-end
  (implies (true-listp h) (equal (nthcdr (len h) h) nil))
  :hints (("Goal" :induct (len h) :in-theory (enable nthcdr)))))
(local
 (defthm pin-history-matches-is-nthcdr
  (implies (and (true-listp rows) (true-listp h) (natp k)
                (equal (+ k (len rows)) (len h)))
   (equal (pin-history-matches rows k h) (equal rows (nthcdr k h))))
  :hints (("Goal" :induct (pin-history-matches rows k h)
                  :in-theory (e/d (pin-history-matches pin-history-nthcdr-unroll) (nthcdr nth))))))
(defun pin-history-equality-check (rows fn-hist)
 (declare (xargs :stobjs fn-hist :guard t :verify-guards nil))
 (mv (mbe :logic (non-exec (equal fn-hist rows))
          :exec (and (true-listp rows) (equal (fn-hist-count fn-hist) (len rows))
                     (pin-history-matches rows 0 fn-hist))) fn-hist))
(verify-guards pin-history-equality-check
 :hints (("Goal" :use ((:instance pin-history-matches-is-nthcdr (h fn-hist) (k 0)))
                 :in-theory (disable pin-history-matches))))

; The generator substitutes a checker for this entire labelled premise.
; The equality checker is logically exact, executable only through row reads.
(defun pin-stored-premises-check (s rec cache fn-hist)
 (declare (xargs :stobjs fn-hist :guard t))
 (mv-let (corresponds fn-hist)
  (pin-history-equality-check (fn-sf-records (fn-sn-files s)) fn-hist)
  (mv (and corresponds
           (fn-adm-stored-most-cache-validp cache (fn-sf-records (fn-sn-files s)))
           (member-equal rec (fn-sf-records (fn-sn-files s)))
           (fn-held-p rec)) fn-hist)))

(defkeystone pin-k-stored
 (implies (and (and (equal fn-hist (fn-sf-records (fn-sn-files s)))
                   (fn-adm-stored-most-cache-validp cache (fn-sf-records (fn-sn-files s)))
                   (member-equal rec (fn-sf-records (fn-sn-files s)))
                   (fn-held-p rec)))
  (<= (+ (* 2 (nfix (fn-hf-octets (fn-held-facts rec)))) *fn-cbud-reply-status-octets*)
      (fn-mm-large-reply profile
       (update-nth 15 (max (nfix pins) (fn-hist-stored-most-carried cache s fn-hist)) (true-list-fix cfg)))))
 :id "PRF-100009" :restates fn-adm-pinned-cfg-charges-every-stored-article
 :subject fn-hist-stored-most-carried :hyps (stored-premises)
 :witness ((s *pin-big-store*) (rec *pin-big-row*) (cache '(1 . 65536))
           (pins 0) (cfg nil) (profile *pin-profile-10*) (rows *pin-big-records*))
 :stobjs ((fn-hist (fn-hist-load rows 0 fn-hist)))
 :stobj-checks (((and (equal fn-hist (fn-sf-records (fn-sn-files s)))
                      (fn-adm-stored-most-cache-validp cache (fn-sf-records (fn-sn-files s)))
                      (member-equal rec (fn-sf-records (fn-sn-files s)))
                      (fn-held-p rec))
                 (pin-stored-premises-check s rec cache fn-hist)))
 :breaks ((stored-premises ((cache '(1 . 0)))))
 :mutations ((old-profile-only
  (:conclusion (<= (+ (* 2 (nfix (fn-hf-octets (fn-held-facts rec)))) *fn-cbud-reply-status-octets*)
                   (fn-mm-large-reply profile cfg))) ()
  :fault "The old gate ignores the stored article after the live shrink"))
 :rule-classes nil :hints (("Goal" :by fn-adm-pinned-cfg-charges-every-stored-article)))

; Specific cache removal: R, membership and heldness still hold, but the
; invalid cache lies about the first record and the carried charge is too small.
(assert-event
 (and (fn-held-p *pin-big-row*)
      (member-equal *pin-big-row* (fn-sf-records (fn-sn-files *pin-big-store*)))
      (not (fn-adm-stored-most-cache-validp '(1 . 0) *pin-big-records*))
      (< (fn-adm-stored-most-extend '(1 . 0) *pin-big-records*)
         (fn-adm-stored-article-most *pin-big-records*)))
 :msg "PIN-CACHE-VALIDITY-REMOVAL-GAP")

; Rev 3a's rational-pins tooth: the old text is false, the new one true,
; on the same whole antecedent with R and a valid cache.
(local
 (defthm pin-most-advance-natural
  (implies (natp most)
   (natp (fn-hist-stored-most-advance k count most fn-hist)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-hist-stored-most-advance k count most fn-hist)
           :in-theory (e/d (fn-hist-stored-most-advance)
                           (fn-adm-stored-article-most fn-hist-at))))))
(defun pin-rational-pins-check (fn-hist)
 (declare (xargs :stobjs fn-hist :guard t
  :guard-hints (("Goal" :in-theory (disable fn-hist-stored-most-advance
                                               fn-adm-stored-article-most
                                               fn-mm-large-reply)))))
 (let* ((s *pin-big-store*) (rec *pin-big-row*) (cache '(1 . 65536))
        (profile *pin-profile-10*) (pins 131073/2)
        (most (fn-hist-stored-most-carried cache s fn-hist))
        (old (update-nth 15 (max pins most) nil))
        (new (update-nth 15 (max (nfix pins) most) nil))
        (required (+ (* 2 (nfix (fn-hf-octets (fn-held-facts rec)))) *fn-cbud-reply-status-octets*)))
  (and (fn-adm-stored-most-cache-validp cache (fn-sf-records (fn-sn-files s)))
       (member-equal rec (fn-sf-records (fn-sn-files s))) (fn-held-p rec)
       (equal (fn-hist-count fn-hist) 1) (equal (fn-hist-at 0 fn-hist) rec)
       (not (<= required (fn-mm-large-reply profile old)))
       (<= required (fn-mm-large-reply profile new)))))
(local
 (defun pin-rational-pins-witness ()
  (declare (xargs :guard t))
  (with-local-stobj fn-hist
   (mv-let (ok fn-hist)
    (let ((fn-hist (fn-hist-load *pin-big-records* 0 fn-hist)))
     (mv (pin-rational-pins-check fn-hist) fn-hist)) ok))))
(assert-event (pin-rational-pins-witness)
 :msg "PIN-RATIONAL-PINS-OLD-FALSE-NEW-TRUE-WHOLE")
(assert-event (and (not (natp 131073/2)) (> 131073/2 65536)
                  (equal (nfix 131073/2) 0)) :msg "PIN-RATIONAL-PINS-GAP")

(defteeth-check (pin-k-stored))
