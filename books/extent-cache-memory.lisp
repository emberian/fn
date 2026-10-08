; Charged whole-entry ownership and physical retirement. The raw table is
; S's decision model; the host uses these wrappers for owned backing.
(in-package "ACL2")
(include-book "extent-cache-storage")

(defun fn-xce-cached-charge (ledger token)
  (declare (xargs :guard t))
  (let ((row (cdr (fn-prl-binding token (fn-prl-nth 3 ledger)))))
    (if (and token (equal (fn-prl-nth 1 row) :cached))
        (nfix (fn-prl-nth 0 (fn-prl-nth 0 row))) 0)))

(defun fn-xce-drop (slot fn-xce)
  (declare (xargs :stobjs fn-xce :guard (natp slot)))
  (if (< slot (fn-xce-keys-length fn-xce))
      (let ((fn-xce (update-fn-xce-keysi slot nil fn-xce)))
        (stobj-let ((fn-xce-entry (fn-xce-entriesi slot fn-xce))) (fn-xce-entry)
          (fn-xce-entry-clear fn-xce-entry)
          fn-xce))
    fn-xce))

(defun fn-xc-free-bytes (slot fn-xcs fn-xce)
  (declare (xargs :stobjs (fn-xcs fn-xce)
                  :guard (and (fn-xcsp fn-xcs) (natp slot))))
  (mv-let (word token fn-xcs) (fn-xc-free slot fn-xcs)
    (let ((fn-xce (if (equal word :freed) (fn-xce-drop slot fn-xce) fn-xce)))
      (mv word token fn-xcs fn-xce))))

(defun fn-xc-yield-bytes (fn-xcs fn-xcc fn-xce)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xce)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (mv-let (word slot token fn-xcs) (fn-xc-yield fn-xcs fn-xcc)
    (let ((fn-xce (if (and (equal word :yielded) (natp slot))
                     (fn-xce-drop slot fn-xce) fn-xce)))
      (mv word slot token fn-xcs fn-xce))))

; The producer must already have leased the stage into :cached (as the
; window producers do). This is local admission, not whole-state validation.
; The caller releases EVICTED in the ledger only after this call completes.
(defun fn-xc-install-entry-funded (ledger file eoff elen trailer token fn-xcs fn-xcc fn-xce fn-xce-stage)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xce fn-xce-stage)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (if (not (and token (posp (fn-xce-stage-len fn-xce-stage))
                (<= (fn-xce-stage-len fn-xce-stage) (fn-xce-cached-charge ledger token))))
      (mv :refused-entry-charge nil nil fn-xcs fn-xcc fn-xce fn-xce-stage)
    (mv-let (word slot evicted fn-xcs fn-xcc fn-xce fn-xce-stage)
      (fn-xc-install-entry-bytes file eoff elen trailer token fn-xcs fn-xcc fn-xce fn-xce-stage)
      (let ((fn-xce-stage (if (member-equal word '(:installed :replaced))
                              (fn-xce-stage-clear fn-xce-stage) fn-xce-stage)))
        (mv word slot evicted fn-xcs fn-xcc fn-xce fn-xce-stage)))))

(defun-nx fn-xce-row-fundedp (i ledger slots entries)
  (let ((n (len (nth i (nth 1 entries)))))
    (or (equal n 0)
        (and (natp i) (< i (fn-xcs-count slots))
             (equal (fn-xcs-get-kind i slots) 1)
             (<= n (fn-xce-cached-charge ledger (fn-xc-slot-token i slots)))))))
(defun-nx fn-xce-funded-through (n ledger slots entries)
  (declare (xargs :measure (nfix n)))
  (if (zp n) t
    (and (fn-xce-row-fundedp (1- n) ledger slots entries)
         (fn-xce-funded-through (1- n) ledger slots entries))))
(defun-nx fn-xce-fundedp (ledger slots entries)
  (fn-xce-funded-through (fn-xce-keys-length entries) ledger slots entries))

(defthm fn-xce-drop-releases-the-row
  (implies (and (natp slot) (< slot (fn-xce-keys-length entries)))
           (and (equal (nth slot (nth 0 (fn-xce-drop slot entries))) nil)
                (equal (nth slot (nth 1 (fn-xce-drop slot entries))) nil)))
  :rule-classes nil)
(defthm fn-xce-drop-leaves-other-rows
  (implies (and (natp slot) (natp other) (not (equal slot other)))
           (and (equal (nth other (nth 0 (fn-xce-drop slot entries))) (nth other (nth 0 entries)))
                (equal (nth other (nth 1 (fn-xce-drop slot entries))) (nth other (nth 1 entries)))))
  :rule-classes nil)
(defthm fn-xc-free-bytes-is-the-table-decision
  (equal (take 3 (fn-xc-free-bytes slot slots entries)) (fn-xc-free slot slots))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-free))))
(defthm fn-xc-yield-bytes-is-the-table-decision
  (equal (take 4 (fn-xc-yield-bytes slots cells entries)) (fn-xc-yield slots cells))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-yield))))
(defthm fn-xc-install-entry-funded-releases-the-victim-buffer
  (let ((r (fn-xc-install-entry-funded ledger file eoff elen trailer token slots cells entries stage)))
    (implies (member-equal (mv-nth 0 r) '(:installed :replaced))
             (equal (mv-nth 6 r) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-install-entry-bytes))))
