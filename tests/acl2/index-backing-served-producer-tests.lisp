(in-package "ACL2")
(include-book "index-backing-publication-row-carry-tests")
(include-book "../../books/index-backing-served-producer-carry")
; Logical fixture: one actual staged row, one actual seal, then served prepare.
(defun-nx iprst-prepare (wire skew pending)
 (let* ((arena (create-fn-arena)) (octets (create-fn-octets)) (cat (create-fn-cat))
        (row (fn-intern-row-at wire nil 0 (+ skew (fn-arena-count arena))))
        (sealed (fn-arena-seal-buffer octets arena))
        (pc (fn-cat-prepare-sealed wire row nil nil pending sealed cat))
        (reference (mv-list 2 (fn-cat-prepare wire nil nil octets nil 0 pending arena cat))))
  (list (fn-ab-p (fn-row-binding wire))
        (equal (fn-octets-list octets) (fn-record-payload wire))
        (fn-ibrc-row-domainp (fn-pc-held pc) (fn-arena-count sealed))
        (and (equal pc (mv-nth 0 reference)) (or pending (equal sealed (mv-nth 1 reference))))
        pc (fn-arena-count sealed))))
(defthm iprst-sealed-prepare-positive
 (equal (take 4 (iprst-prepare *iprct-wire* 0 nil)) '(t t t t)) :rule-classes nil)
(defthm iprst-sealed-prepare-binding-removal
 (equal (take 4 (iprst-prepare (update-nth 11 nil *iprct-wire*) 0 nil)) '(nil t nil t)) :rule-classes nil)
(defthm iprst-buffer-equality-removal
 (equal (take 4 (iprst-prepare (update-nth 4 '(65) *iprct-wire*) 0 nil)) '(t nil t nil)) :rule-classes nil)
; Named refusals: wrong sealed handle and outstanding pending are not accepted.
(defthm iprst-wrong-sealed-handle-refuses
 (equal (nth 4 (iprst-prepare *iprct-wire* 1 nil)) '(:not-sealed)) :rule-classes nil)
(defthm iprst-outstanding-pending-refuses
 (equal (nth 4 (iprst-prepare *iprct-wire* 0 :outstanding)) '(:pending)) :rule-classes nil)

(defun-nx iprst-reserve-register (wire children capacity)
 (let* ((prepared (iprst-prepare wire 0 nil)) (pc (nth 4 prepared)) (prefix (nth 5 prepared))
        (segment (update-fn-ibp-gs-id 1 (create-fn-ibp-generation-segment)))
        (node (if children
                  (fn-ibp-node-children-put 'fn-ibp-generation-segment segment (create-fn-ibp-node))
                (create-fn-ibp-node)))
        (backing (update-fn-ibp-registry node
                   (update-fn-ibp-pool-capacity capacity (create-fn-index-backing))))
        (pool (fn-owner-page-read-keep-ledger
               (fn-prl-build '(1000 1000 5 5 99) '(0 0 0 0 0) 0 nil '(0 0 0 0 0))
               (create-fn-page-read-pool)))
        (reserve (mv-list 4 (fn-igr-reserve pc '(1 0 0 0 1) backing pool)))
        (reserved (mv-nth 2 reserve))
        (registered (mv-list 3 (fn-igr-register 1 reserved)))
        (after (mv-nth 2 registered)))
  (list (mv-nth 0 reserve) (mv-nth 0 registered)
        (fn-ibrc-row-domainp (fn-pc-held pc) prefix)
        (fn-iprc-builder-prepared-carryp (fn-ibp-builder reserved) pc prefix)
        (fn-iprc-builder-prepared-carryp (fn-ibp-builder after) pc prefix)
        (equal (fn-omk-at 6 (fn-omk-at 19 (fn-ibp-builder after))) pc)
        (fn-prl-nth 2 (fn-owner-page-read-ledger (mv-nth 3 reserve)))
        (fn-omk-at 1 (fn-ibp-builder after)))))

; Synthetic supported capacity and existing child are explicit prerequisites.
(defthm iprst-served-reserve-register-positive
 (equal (iprst-reserve-register *iprct-wire* t 1)
        '(:reserved :registered t t t t 1 :registered)) :rule-classes nil)
(defthm iprst-served-register-missing-child-retains-source
 (equal (iprst-reserve-register *iprct-wire* nil 1)
        '(:reserved :unavailable t t t t 1 :reserved)) :rule-classes nil)
(defthm iprst-served-reserve-register-binding-removal
 (equal (iprst-reserve-register (update-nth 11 nil *iprct-wire*) t 1)
        '(:reserved :registered nil nil nil t 1 :registered)) :rule-classes nil)
(defthm iprst-served-reserve-register-status-removal
 (equal (iprst-reserve-register *iprct-wire* t 0)
        '(:unavailable :stale t nil nil nil 0 nil)) :rule-classes nil)

; Actual committed row followed by withdrawal/redecision, with literal removals.
(defun-nx iprst-event-current (wire target by redecidep)
 (let* ((prepared (iprst-prepare wire 0 nil))
        (cat (fn-cat-commit (fn-pc-held (nth 4 prepared)) (create-fn-cat)))
        (prefix (nth 5 prepared))
        (result (if redecidep (fn-cat-redecide (nfix target) (fn-held-context (fn-cat-at 0 cat)) cat)
                  (fn-cat-withdraw (nfix target) by cat))))
  (list (fn-ibrc-prefixp cat (fn-cat-count cat) prefix)
        (if redecidep (< (nfix target) (fn-cat-count cat)) (natp by))
        (fn-ibrc-prefixp result (fn-cat-count result) prefix)
        (fn-cat-count result))))
(defthm iprst-current-actual-withdraw-positive
 (equal (iprst-event-current *iprct-wire* 0 1 nil) '(t t t 1)) :rule-classes nil)
(defthm iprst-current-actual-withdraw-carry-removal
 (equal (iprst-event-current (update-nth 11 nil *iprct-wire*) 0 1 nil) '(nil t nil 1)) :rule-classes nil)
(defthm iprst-current-actual-withdraw-by-removal
 (equal (iprst-event-current *iprct-wire* 0 :invalid nil) '(t nil nil 1)) :rule-classes nil)
(defthm iprst-current-actual-redecide-positive
 (equal (iprst-event-current *iprct-wire* 0 1 t) '(t t t 1)) :rule-classes nil)
(defthm iprst-current-actual-redecide-carry-removal
 (equal (iprst-event-current (update-nth 11 nil *iprct-wire*) 0 1 t) '(nil t nil 1)) :rule-classes nil)
(defthm iprst-current-actual-redecide-range-removal
 (equal (iprst-event-current *iprct-wire* 1 1 t) '(t nil nil 2)) :rule-classes nil)

(defthm iprst-current-event-executable-positive
 (let* ((prepared (iprst-prepare *iprct-wire* 0 nil))
        (held (fn-pc-held (nth 4 prepared)))
        (cat (fn-cat-commit held (create-fn-cat))))
  (and (fn-record-p *iprct-wire*) (fn-prin-keyringp nil)
       (fn-held-p held) (fn-cat-p cat) (< 0 (fn-cat-count cat))
       (fn-hc-p (fn-held-context (fn-cat-at 0 cat)))
       (equal (iprst-event-current *iprct-wire* 0 1 nil) '(t t t 1))
       (equal (iprst-event-current *iprct-wire* 0 1 t) '(t t t 1))))
 :rule-classes nil)
