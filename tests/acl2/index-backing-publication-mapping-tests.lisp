; Modern held16 actual copy fixtures. Preinstalled physical children are
; explicit fixture setup; source/runtime constructor and publication are open.
(in-package "ACL2")
(include-book "index-backing-publication-row-carry-tests")

(defun-nx iprmt-write (old row ordinal sealp fuel)
 (let* ((initialized (mv-list 2 (fn-ibp-row-initialize 7 3 (create-fn-ibp-row-page))))
        (child (fn-ibp-node-children-put 'fn-ibp-row-page (mv-nth 1 initialized) (create-fn-ibp-node)))
        (node (fn-ibp-node-children-put 'fn-ibp-node-right child (create-fn-ibp-node)))
        (first (mv-list 3 (fn-ibp-node-row-write 0 old nil 1 1 7 3 2 node)))
        (before (mv-nth 2 first))
        (result (mv-list 3 (fn-ibp-node-row-write ordinal row sealp 1 1 7 3 fuel before)))
        (after (mv-nth 2 result)))
  (list (fn-iprc-node-prefixp 1 1 1 1 before)
        (or sealp (fn-ibrc-row-domainp row 1))
        (equal (mod ordinal 256) (nfix 1))
        (eq (mv-nth 0 result) :written)
        (fn-iprc-node-prefixp 1 1 1 1 after)
        (fn-iprc-node-prefixp 1 1 2 1 after))))
(defthm iprmt-write-and-extend-positive
 (equal (iprmt-write (iprct-held) (iprct-held) 1 nil 2) '(t t t t t t))
 :rule-classes nil)
(defthm iprmt-write-seal-positive
 (equal (iprmt-write (iprct-held) nil 0 t 2) '(t t nil nil t nil))
 :rule-classes nil)
; Prefix-preservation literal removals. These are corrupted row states,
; deliberately admitted by the raw representation, not produced typed inputs.
(defthm iprmt-write-carry-removal
 (equal (iprmt-write nil (iprct-held) 1 nil 2) '(nil t t t nil nil))
 :rule-classes nil)
(defthm iprmt-write-row-removal
 (equal (iprmt-write (iprct-held) nil 0 nil 2) '(t nil nil t nil nil))
 :rule-classes nil)
; Extension: each list retains all other three literal hypotheses.
(defthm iprmt-extend-carry-removal
 (equal (iprmt-write nil (iprct-held) 1 nil 2) '(nil t t t nil nil))
 :rule-classes nil)
(defthm iprmt-extend-row-removal
 (equal (iprmt-write (iprct-held) nil 1 nil 2) '(t nil t t t nil))
 :rule-classes nil)
(defthm iprmt-extend-position-removal
 (equal (iprmt-write (iprct-held) (iprct-held) 0 nil 2) '(t t nil t t nil))
 :rule-classes nil)
(defthm iprmt-extend-status-removal
 (equal (iprmt-write (iprct-held) (iprct-held) 1 nil 0) '(t t t nil t nil))
 :rule-classes nil)


(defun iprmt-assign-run (steps cursor)
 (declare (xargs :measure (nfix steps) :verify-guards nil))
 (if (or (zp steps) (member-eq (fn-gns-at 0 cursor) '(:done :refused))) cursor
  (iprmt-assign-run (- steps 1) (fn-gns-assign-step cursor))))
(defun-nx iprmt-produced ()
 (let* ((first (mv-list 2 (fn-cat-prepare *iprct-wire* nil nil (create-fn-octets) nil 0 nil
                                         (create-fn-arena) (create-fn-cat))))
        (held0 (fn-pc-held (mv-nth 0 first)))
        (cat (fn-cat-commit held0 (create-fn-cat)))
        (old (fn-cat-at 0 cat))
        (second (mv-list 2 (fn-cat-prepare (update-nth 3 "<next@test>" *iprct-wire*) nil nil
                                          (create-fn-octets) nil 0 nil (mv-nth 1 first) cat)))
        (pc (mv-nth 0 second))
        (root (fn-gns-memberships-root (fn-held-numbers old) 0 nil))
        (assigned (fn-gns-pending-result (iprmt-assign-run 64 (fn-gns-pending-begin pc root 99)))))
  (list old assigned pc (fn-arena-count (mv-nth 1 second)))))

(defun-nx iprmt-copy-node (old dest filled)
 (let* ((source (mv-nth 1 (fn-ibp-row-initialize 99 1 (create-fn-ibp-row-page))))
        (source (fn-ibp-row-set 0 old source)) (source (fn-ibp-row-set 1 old source))
        (source (mv-nth 1 (fn-ibp-row-seal 99 1 source)))
        (destination (mv-nth 1 (fn-ibp-row-initialize 17 17 (create-fn-ibp-row-page))))
        (destination (fn-ibp-row-set 0 dest destination))
        (destination (fn-ibp-row-set 1 dest destination))
        (owner (update-fn-ibp-pos-id 1 (create-fn-ibp-page-owner-segment)))
        (owner (mv-nth 1 (fn-ibp-page-owner-reserve '(:index-page 17 1 0) :rows 0 :synthetic
                          '(:index-generation 11 1 0) owner)))
        (owner (mv-nth 1 (fn-ibp-page-owner-built '(:index-page 17 1 0) owner)))
        (owner (update-fn-ibp-pos-rowsi 0
                 (update-nth 10 filled (fn-ibp-page-owner-row '(:index-page 17 1 0) owner)) owner))
        (dest-node (fn-ibp-node-children-put 'fn-ibp-page-owner-segment owner
                    (fn-ibp-node-children-put 'fn-ibp-row-page destination (create-fn-ibp-node))))
        (source-node (fn-ibp-node-children-put 'fn-ibp-row-page source (create-fn-ibp-node)))
        (branch (fn-ibp-node-children-put 'fn-ibp-node-right source-node
                  (fn-ibp-node-children-put 'fn-ibp-node-left dest-node (create-fn-ibp-node)))))
  (fn-ibp-node-children-put 'fn-ibp-node-left branch (create-fn-ibp-node))))
(defun-nx iprmt-copy-cell-observation (old dest assigned count filled fuel)
 (let* ((node (iprmt-copy-node old dest filled))
        (result (mv-list 3 (fn-ibp-row-copy-cell '(:index-page 17 1 0) assigned count
                              '(:chunk 2 99 1) 0 17 fuel 2 node)))
        (after (mv-nth 2 result)))
  (list (natp count) (fn-iprc-node-prefixp 0 2 filled 2 node)
        (fn-ibrc-row-domainp assigned 2)
        (fn-iprc-node-prefixp 2 2 (mod count 256) 2 node)
        (if (member-eq (mv-nth 0 result) '(:copied :appended)) t nil)
        (fn-iprc-node-prefixp 0 2 (+ 1 (nfix filled)) 2 after)
        (mv-nth 0 result))))


(defun-nx iprmt-old () (nth 0 (iprmt-produced)))
(defun-nx iprmt-assigned () (fn-omk-at 5 (nth 1 (iprmt-produced))))
(defthm iprmt-real-row-producers
 (and (equal (nth 3 (iprmt-produced)) 2)
      (eq (fn-omk-at 0 (nth 1 (iprmt-produced))) :assigned)
      (equal (fn-pc-expected (nth 2 (iprmt-produced))) 1)
      (fn-ibrc-row-domainp (iprmt-old) 2)
      (fn-ibrc-row-domainp (iprmt-assigned) 2)
      (equal (fn-record-payload (iprmt-old)) 0)
      (equal (fn-record-payload (iprmt-assigned)) 1)) :rule-classes nil)

(defthm iprmt-copy-positive
 (equal (iprmt-copy-cell-observation (iprmt-old) nil (iprmt-assigned) 1 0 12)
        '(t t t t t t :copied))  :rule-classes nil)
(defthm iprmt-append-positive
 (equal (iprmt-copy-cell-observation (iprmt-old) (iprmt-old) (iprmt-assigned) 1 1 12)
        '(t t t t t t :appended))  :rule-classes nil)
(defthm iprmt-copy-count-removal
 (equal (iprmt-copy-cell-observation nil nil (iprmt-assigned) 1/2 0 12)
        '(nil t t t t nil :copied))  :rule-classes nil)
(defthm iprmt-copy-destination-removal
 (equal (iprmt-copy-cell-observation (iprmt-old) nil (iprmt-assigned) 2 1 12)
        '(t nil t t t nil :copied))  :rule-classes nil)
(defthm iprmt-copy-assigned-removal
 (equal (iprmt-copy-cell-observation (iprmt-old) (iprmt-old) nil 1 1 12)
        '(t t nil t t nil :appended))  :rule-classes nil)
(defthm iprmt-copy-source-removal
 (equal (iprmt-copy-cell-observation nil nil (iprmt-assigned) 1 0 12)
        '(t t t nil t nil :copied))  :rule-classes nil)
(defthm iprmt-copy-status-removal
 (equal (iprmt-copy-cell-observation (iprmt-old) nil (iprmt-assigned) 1 0 0)
        '(t t t t nil nil :yield))  :rule-classes nil)


(defun-nx iprmt-copy-preservation (old dest assigned count filled carried)
 (let* ((node (iprmt-copy-node old dest filled))
        (result (mv-list 3 (fn-ibp-row-copy-cell '(:index-page 17 1 0) assigned count
                              '(:chunk 2 99 1) 0 17 12 2 node))))
  (list (natp count) (fn-iprc-node-prefixp 0 2 carried 2 node)
        (fn-ibrc-row-domainp assigned 2)
        (fn-iprc-node-prefixp 2 2 (mod count 256) 2 node)
        (fn-iprc-node-prefixp 0 2 carried 2 (mv-nth 2 result)))))
(defthm iprmt-copy-preservation-positive
 (equal (iprmt-copy-preservation (iprmt-old) (iprmt-old) (iprmt-assigned) 1 0 1)
        '(t t t t t)) :rule-classes nil)
(defthm iprmt-copy-preservation-count-removal
 (equal (iprmt-copy-preservation nil (iprmt-old) (iprmt-assigned) 1/2 0 1)
        '(nil t t t nil)) :rule-classes nil)
(defthm iprmt-copy-preservation-destination-removal
 (equal (iprmt-copy-preservation (iprmt-old) nil (iprmt-assigned) 1 1 1)
        '(t nil t t nil)) :rule-classes nil)
(defthm iprmt-copy-preservation-assigned-removal
 (equal (iprmt-copy-preservation (iprmt-old) (iprmt-old) nil 1 1 2)
        '(t t nil t nil)) :rule-classes nil)
(defthm iprmt-copy-preservation-source-removal
 (equal (iprmt-copy-preservation nil (iprmt-old) (iprmt-assigned) 1 0 1)
        '(t t t nil nil)) :rule-classes nil)


; Actual caller, seal and root-rebuild source scenario. These receipt/child
; installations are explicit fixture prerequisites, not installed authority.
(defun-nx iprmt-parent (bad fuel)
 (let* ((rows (iprmt-produced)) (old (nth 0 rows))
        (assigned (if bad (update-nth 5 nil (nth 1 rows)) (nth 1 rows)))
        (pc (nth 2 rows)) (pc-token (fn-pc-token pc))
        (pub (fn-ipub-make 7 :key 1 1 5 3 nil 0 7 '(:chunk 2 99 1) 0 7 nil 7 nil nil 7 1))
        (association (list :installed-publication '(:index-generation 7 1 0) pub))
        (reservation (list :generation-reservation 10 11 1 :fresh nil pc association))
        (builder (list :index-builder :layout '(:index-generation 11 1 0) '(:index-generation 7 1 0)
                       :key 1 1 pc-token assigned nil nil nil nil nil nil nil nil nil nil reservation))
        (receipt '(:page-reservation 16 17 0 :fresh (1 0 0 0 1) :rows
                   (:index-generation 11 1 0) 0 (:chunk 2 99 1) :built nil nil))
        (backing (update-fn-ibp-registry (iprmt-copy-node old nil 0)
                  (update-fn-ibp-slot-depth 2
                   (update-fn-ibp-builder builder
                    (update-fn-ibp-page-pending receipt (create-fn-index-backing))))))
        (copied (mv-list 3 (fn-ipa-row-copy-one 12 backing)))
        (before (mv-nth 2 copied))
        (appended (mv-list 3 (fn-ipa-row-copy-one fuel before)))
        (after (mv-nth 2 appended))
        (sealed (mv-list 3 (fn-ipa-row-seal 10 after)))
        (root1 (mv-list 3 (fn-ipa-row-root-one 1 (mv-nth 2 sealed))))
        (root2 (mv-list 3 (fn-ipa-row-root-one 1 (mv-nth 2 root1))))
        (final (mv-nth 2 root2))
        (descriptor (fn-omk-at 12 (fn-ibp-builder final)))
        (read (mv-list 3 (fn-ibp-node-row-read 1 3 (nth 1 descriptor) 2
                           (nth 2 descriptor) (nth 3 descriptor) (fn-ibp-registry final)))))
  (list (fn-iprc-copy-layout-domainp 2 before)
        (eq (mv-nth 0 appended) :appended)
        (fn-iprc-node-prefixp 0 2 2 2 (fn-ibp-registry after))
        (list (mv-nth 0 copied) (mv-nth 0 appended) (mv-nth 0 sealed) (mv-nth 0 root1) (mv-nth 0 root2))
        descriptor (mv-nth 0 read) (equal (mv-nth 1 read) (fn-omk-at 5 assigned))
        (fn-ibrc-row-domainp (mv-nth 1 read) 2)
        (equal (fn-ipub-row-root (fn-omk-at 2 (fn-omk-at 7 (fn-omk-at 19 (fn-ibp-builder final)))) )
               '(:chunk 2 99 1)))))
(defthm iprmt-copy-one-positive
 (equal (take 3 (iprmt-parent nil 12)) '(t t t)) :rule-classes nil)
(defthm iprmt-copy-one-carry-removal
 (equal (take 3 (iprmt-parent t 12)) '(nil t nil)) :rule-classes nil)
(defthm iprmt-copy-one-status-removal
 (equal (take 3 (iprmt-parent nil 0)) '(t nil nil)) :rule-classes nil)
(defthm iprmt-copy-seal-root-read-actual-scenario
 (equal (nthcdr 3 (iprmt-parent nil 12))
        '((:copied :appended :row-root :row-root :table-layout)
          (:chunk 0 17 17) :row t t t)) :rule-classes nil)
