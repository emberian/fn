; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5)
(in-package "ACL2")
(include-book "../../books/index-backing-publication-row-carry")

(defconst *iprct-binding*
 (fn-ab-make :relay-v1 (append *fn-ab-subject-head* (make-list 32 :initial-element 0))))
(defconst *iprct-wire*
 (fn-record-make 0 1 0 "<prepared@test>" nil '("g") "o" "s" "e" 1 0 *iprct-binding*))

; Actual prepare/buffer/arena, never FnPCMake with a supplied held fixture.
(defun-nx iprct-prepare (wire pending)
 (let* ((r (mv-list 2 (fn-cat-prepare wire nil nil (create-fn-octets) nil 0 pending
                                     (create-fn-arena) (create-fn-cat))))
        (pc (mv-nth 0 r)) (arena (mv-nth 1 r)))
  (list (fn-ab-p (fn-row-binding wire)) (not pending)
        (fn-ibrc-row-domainp (fn-pc-held pc) (fn-arena-count arena))
        pc (fn-arena-count arena))))
(defthm iprct-prepare-positive
 (equal (take 3 (iprct-prepare *iprct-wire* nil)) '(t t t)) :rule-classes nil)
; Literal removals: retained hypothesis checked, omitted hypothesis false,
; actual returned PreparedCommit row conclusion false.
(defthm iprct-prepare-binding-removal
 (equal (take 3 (iprct-prepare (update-nth 11 nil *iprct-wire*) nil)) '(nil t nil))
 :rule-classes nil)
(defthm iprct-prepare-pending-removal
 (equal (take 3 (iprct-prepare *iprct-wire* :outstanding)) '(t nil nil))
 :rule-classes nil)

; Synthetic capacity/child installation is explicit. The operations under
; test are actual shared issue/reserve/register; this is not installer funding.
(defun-nx iprct-reserve-register (wire children capacity)
 (let* ((prepared (iprct-prepare wire nil)) (pc (nth 3 prepared)) (prefix (nth 4 prepared))
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
(defthm iprct-reserve-register-positive
 (equal (iprct-reserve-register *iprct-wire* t 1)
        '(:reserved :registered t t t t 1 :registered)) :rule-classes nil)
; Missing constructor is a named refusal; the same PC/identity remains rooted.
(defthm iprct-register-missing-child
 (equal (iprct-reserve-register *iprct-wire* nil 1)
        '(:reserved :unavailable t t t t 1 :reserved)) :rule-classes nil)
; Reserve typed-input removal, actual reserve still succeeds on unrestricted PC.
(defthm iprct-reserve-domain-removal
 (equal (iprct-reserve-register (update-nth 11 nil *iprct-wire*) t 1)
        '(:reserved :registered nil nil nil t 1 :registered)) :rule-classes nil)
; Reserve status removal: input row typed but no actual reservation is acquired.
(defthm iprct-reserve-status-removal
 (equal (iprct-reserve-register *iprct-wire* t 0)
        '(:unavailable :stale t nil nil nil 0 nil)) :rule-classes nil)

(defun iprct-assignment-run (steps fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :measure (nfix steps) :verify-guards nil))
 (if (zp steps) fn-index-backing
  (mv-let (word left fn-index-backing)
   (fn-ibp-writer-assignment-one 1 fn-index-backing)
   (declare (ignore left))
   (if (eq word :numbers) fn-index-backing
    (iprct-assignment-run (- steps 1) fn-index-backing)))))

; Preinstalled publication/arena-held phase are explicit fixture prerequisites.
; This tests the actual assignment attachment, not their missing STATE join.
(defun-nx iprct-assignment (wire fuel)
 (let* ((prepared (iprct-prepare wire nil)) (pc (nth 3 prepared)) (prefix (nth 4 prepared))
        (publication (fn-ipub-make 9 :key nil 0 0 0 nil 0 1 nil 0 2 nil 3 :complete :view 7 0))
        (association (list :installed-publication '(:index-generation 9 1 1) publication))
        (backing (update-fn-ibp-current association
                   (update-fn-ibp-pool-capacity 1 (create-fn-index-backing))))
        (pool (fn-owner-page-read-keep-ledger
               (fn-prl-build '(1000 1000 5 5 99) '(0 0 0 0 0) 0 nil '(0 0 0 0 0))
               (create-fn-page-read-pool)))
        (reserve (mv-list 4 (fn-igr-reserve pc '(1 0 0 0 1) backing pool)))
        (reserved (mv-nth 2 reserve))
        (before (update-fn-ibp-builder (update-nth 1 :arena-held (fn-ibp-builder reserved)) reserved))
        (begin (mv-list 3 (fn-ibp-writer-assignment-begin fuel before)))
        (started (mv-nth 2 begin))
        (carry (fn-ibrc-assignment-carryp (fn-omk-at 18 (fn-ibp-builder started)) prefix))
        (after (if (eq (mv-nth 0 begin) :assigning) (iprct-assignment-run 64 started) started)))
  (list (fn-iprc-builder-prepared-carryp (fn-ibp-builder before) pc prefix)
        (mv-nth 0 begin) carry (fn-omk-at 1 (fn-ibp-builder after))
        (fn-ibrc-row-domainp (fn-omk-at 5 (fn-omk-at 8 (fn-ibp-builder after))) prefix))))
(defthm iprct-assignment-positive
 (equal (iprct-assignment *iprct-wire* 1) '(t :assigning t :numbers t)) :rule-classes nil)
(defthm iprct-assignment-domain-removal
 (equal (iprct-assignment (update-nth 11 nil *iprct-wire*) 1)
        '(nil :assigning nil :numbers nil)) :rule-classes nil)
(defthm iprct-assignment-status-removal
 (equal (iprct-assignment *iprct-wire* 0) '(t :yield nil :arena-held nil)) :rule-classes nil)

; Actual recursive right-child write -> seal -> read, same held16 pointer.
(defun-nx iprct-node (row ordinal fuel)
 (let* ((initialized (mv-list 2 (fn-ibp-row-initialize 7 3 (create-fn-ibp-row-page))))
        (child (fn-ibp-node-children-put 'fn-ibp-row-page (mv-nth 1 initialized) (create-fn-ibp-node)))
        (node (fn-ibp-node-children-put 'fn-ibp-node-right child (create-fn-ibp-node)))
        (written (mv-list 3 (fn-ibp-node-row-write 0 row nil 1 1 7 3 2 node)))
        (sealed (mv-list 3 (fn-ibp-node-row-write 0 nil t 1 1 7 3 2 (mv-nth 2 written))))
        (after (mv-nth 2 sealed))
        (read (mv-list 3 (fn-ibp-node-row-read ordinal fuel 1 1 7 3 after))))
  (list (fn-iprc-node-prefixp 1 1 1 1 after)
        (< (nfix (mod ordinal 256)) (nfix 1))
        (eq (mv-nth 0 read) :row)
        (fn-ibrc-row-domainp (mv-nth 1 read) 1)
        (mv-nth 0 read) (equal (mv-nth 1 read) row))))
(defun-nx iprct-held () (fn-pc-held (nth 3 (iprct-prepare *iprct-wire* nil))))
(defthm iprct-node-positive
 (equal (iprct-node (iprct-held) 0 2) '(t t t t :row t)) :rule-classes nil)
; Literal carry removal: same real seals/read status, malformed payload.
(defthm iprct-node-carry-removal
 (equal (iprct-node (update-nth 4 99 (iprct-held)) 0 2)
        '(nil t t nil :row t)) :rule-classes nil)
(defthm iprct-node-bound-removal
 (equal (iprct-node (iprct-held) 1 2) '(t nil t nil :row nil)) :rule-classes nil)
(defthm iprct-node-status-removal
 (equal (iprct-node (iprct-held) 0 0) '(t t nil nil :yield nil)) :rule-classes nil)

(defthm iprct-context-positive
 (and (fn-ibrc-row-domainp (iprct-held) 1)
      (fn-ibrc-row-domainp (fn-held-with-context (iprct-held) :new-context) 1))
 :rule-classes nil)
(defthm iprct-context-domain-removal
 (and (not (fn-ibrc-row-domainp nil 1))
      (not (fn-ibrc-row-domainp (fn-held-with-context nil :new-context) 1)))
 :rule-classes nil)

; Literal ONE subject: retain the cursor immediately before the final actual
; ONE transition, rather than infer its antecedent from a distant begin.
(defun iprct-terminal-one (steps fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :measure (nfix steps) :verify-guards nil))
 (let ((cursor (fn-omk-at 18 (fn-ibp-builder fn-index-backing))))
  (if (zp steps)
      (mv-let (word left fn-index-backing) (fn-ibp-writer-assignment-one 0 fn-index-backing)
       (declare (ignore left)) (mv word cursor fn-index-backing))
   (mv-let (word left fn-index-backing)
    (fn-ibp-writer-assignment-one 1 fn-index-backing)
    (declare (ignore left))
    (if (not (eq word :assigning)) (mv word cursor fn-index-backing)
     (iprct-terminal-one (- steps 1) fn-index-backing))))))
(defun-nx iprct-one (wire steps)
 (let* ((prepared (iprct-prepare wire nil)) (pc (nth 3 prepared)) (prefix (nth 4 prepared))
        (cursor (fn-gns-pending-begin pc nil 3))
        (builder (list :index-builder :assigning nil nil nil nil 0 (fn-pc-token pc)
                        (fn-pc-held pc) nil nil nil nil nil nil nil nil nil cursor nil))
        (backing (update-fn-ibp-builder builder (create-fn-index-backing)))
        (result (mv-list 3 (iprct-terminal-one steps backing))))
  (list (fn-ibrc-assignment-carryp (mv-nth 1 result) prefix)
        (eq (mv-nth 0 result) :numbers)
        (fn-ibrc-row-domainp (fn-omk-at 5 (fn-omk-at 8 (fn-ibp-builder (mv-nth 2 result)))) prefix))))
(defthm iprct-one-positive
 (equal (iprct-one *iprct-wire* 64) '(t t t)) :rule-classes nil)
(defthm iprct-one-domain-removal
 (equal (iprct-one (update-nth 11 nil *iprct-wire*) 64) '(nil t nil)) :rule-classes nil)
(defthm iprct-one-status-removal
 (equal (iprct-one *iprct-wire* 0) '(t nil nil)) :rule-classes nil)
