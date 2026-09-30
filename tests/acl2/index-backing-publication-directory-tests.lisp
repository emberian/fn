; Actual row publication scenario. Fixture-installed children and table-ready
; metadata do not establish allocator, durable source, or full writer authority.
(in-package "ACL2")
(include-book "index-backing-publication-mapping-tests")
(include-book "../../books/index-backing-publication-directory-carry")

(defun-nx iprdt-copy-node (old dest filled)
 (let* ((source (mv-nth 1 (fn-ibp-row-initialize 99 1 (create-fn-ibp-row-page))))
        (source (fn-ibp-row-set 0 old source)) (source (fn-ibp-row-set 1 old source))
        (source (mv-nth 1 (fn-ibp-row-seal 99 1 source)))
        (destination (mv-nth 1 (fn-ibp-row-initialize 17 17 (create-fn-ibp-row-page))))
        (destination (fn-ibp-row-set 0 dest destination))
        (destination (fn-ibp-row-set 1 dest destination))
        (owner (update-fn-ibp-pos-id 1 (create-fn-ibp-page-owner-segment)))
        (owner (mv-nth 1 (fn-ibp-page-owner-reserve '(:index-page 17 1 0) :rows 0 :synthetic
                          '(:index-generation 11 1 1) owner)))
        (owner (mv-nth 1 (fn-ibp-page-owner-built '(:index-page 17 1 0) owner)))
        (owner (update-fn-ibp-pos-rowsi 0
                 (update-nth 10 filled (fn-ibp-page-owner-row '(:index-page 17 1 0) owner)) owner))
        (dest-node (fn-ibp-node-children-put 'fn-ibp-page-owner-segment owner
                    (fn-ibp-node-children-put 'fn-ibp-row-page destination (create-fn-ibp-node))))
        (source-node (fn-ibp-node-children-put 'fn-ibp-row-page source (create-fn-ibp-node)))
        (branch (fn-ibp-node-children-put 'fn-ibp-node-right source-node
                  (fn-ibp-node-children-put 'fn-ibp-node-left dest-node (create-fn-ibp-node)))))
  (fn-ibp-node-children-put 'fn-ibp-node-left branch (create-fn-ibp-node))))

(defun-nx iprdt-stages (bad fuel)
 (let* ((rows (iprmt-produced)) (old (nth 0 rows))
        (assigned (if bad (update-nth 5 nil (nth 1 rows)) (nth 1 rows)))
        (pc (nth 2 rows)) (pc-token (fn-pc-token pc))
        (pub (fn-ipub-make 7 :key 1 1 5 3 nil 0 7 '(:chunk 2 99 1) 0 7 nil 7 nil nil 7 1))
        (association (list :installed-publication '(:index-generation 7 1 0) pub))
        (reservation (list :generation-reservation 10 11 1 :fresh nil pc association))
        (builder (list :index-builder :layout '(:index-generation 11 1 1) '(:index-generation 7 1 0)
                       :key 1 1 pc-token assigned nil nil nil nil nil nil nil nil nil nil reservation))
        (receipt '(:page-reservation 16 17 0 :fresh (1 0 0 0 1) :rows
                   (:index-generation 11 1 1) 0 (:chunk 2 99 1) :built nil nil))
        (backing (update-fn-ibp-registry (iprdt-copy-node old nil 0)
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
        (final (mv-nth 2 root2)))
  (list pc pub assigned before after (mv-nth 2 sealed) final
        (list (mv-nth 0 copied) (mv-nth 0 appended) (mv-nth 0 sealed) (mv-nth 0 root1) (mv-nth 0 root2)))))

(defun-nx iprdt-generation-fixture (pub)
 (let* ((segment (update-fn-ibp-gs-id 1 (create-fn-ibp-generation-segment)))
        (segment (mv-nth 1 (fn-ibp-generation-begin '(:index-generation 7 1 0) :fixture-grant segment)))
        (segment (mv-nth 1 (fn-ibp-generation-capture-arena '(:index-generation 7 1 0) 7 1 segment)))
        (segment (mv-nth 1 (fn-ibp-generation-install-publication '(:index-generation 7 1 0) pub segment)))
        (segment (mv-nth 1 (fn-ibp-generation-begin '(:index-generation 11 1 1) :fixture-grant segment))))
  (mv-nth 1 (fn-ibp-generation-capture-arena '(:index-generation 11 1 1) 7 2 segment))))
(defun-nx iprdt-ready (stages bad)
 (let* ((backing (nth 6 stages)) (root (fn-ibp-registry backing))
        (left (fn-ibp-node-children-get 'fn-ibp-node-left root (create-fn-ibp-node)))
        (leaf (fn-ibp-node-children-get 'fn-ibp-node-left left (create-fn-ibp-node)))
        (leaf (fn-ibp-node-children-put 'fn-ibp-generation-segment (iprdt-generation-fixture (nth 1 stages)) leaf))
        (left (fn-ibp-node-children-put 'fn-ibp-node-left leaf left))
        (root (fn-ibp-node-children-put 'fn-ibp-node-left left root))
        (builder (update-nth 17 2 (update-nth 1 :ready (fn-ibp-builder backing))))
        (builder (if bad (update-nth 12 '(:chunk 2 99 1) builder) builder)))
  (update-fn-ibp-registry root
   (update-fn-ibp-builder builder
    (update-fn-ibp-current (list :installed-publication '(:index-generation 7 1 0) (nth 1 stages)) backing)))))
(defun-nx iprdt-publish (bad fuel)
 (let* ((stages (iprdt-stages nil 12)) (pc (nth 0 stages))
        (before (iprdt-ready stages bad))
        (out (mv-list 3 (fn-ibp-writer-complete pc 19 3 :fixture-visibility fuel before)))
        (after (mv-nth 2 out)) (pub (fn-omk-at 2 (fn-ibp-current after)))
        (borrow (mv-list 4 (fn-ibp-directory-step (fn-ibp-directory-start (fn-ipub-row-root pub) 0 (fn-ipub-row-depth pub)) 1)))
        (descriptor (mv-nth 2 borrow))
        (read (mv-list 3 (fn-ibp-node-row-read 1 3 (nth 1 descriptor) 2 (nth 2 descriptor) (nth 3 descriptor) (fn-ibp-registry after)))))
  (list (nth 7 stages)
        (fn-iprc-directory-row-domainp (fn-omk-at 12 (fn-ibp-builder before)) 0 (fn-omk-at 13 (fn-ibp-builder before)) 2 2 2 (fn-ibp-registry before))
        (eq (mv-nth 0 out) :published)
        (fn-iprc-directory-row-domainp (fn-ipub-row-root pub) 0 (fn-ipub-row-depth pub) 2 2 2 (fn-ibp-registry after))
        (list (fn-ipub-count pub) (fn-ipub-frontier pub) (fn-ipub-view pub) (fn-ipub-arena-incarnation pub) (fn-ipub-arena-prefix pub))
        (mv-nth 0 borrow) (mv-nth 0 read)
        (equal (mv-nth 1 read) (fn-omk-at 5 (nth 2 stages)))
        (fn-ibrc-row-domainp (mv-nth 1 read) 2))))

(defthm iprdt-actual-copy-seal-root-publication-read
 (equal (iprdt-publish nil 12)
 '((:copied :appended :row-root :row-root :table-layout)
   t t t (2 19 3 7 2) :borrow-ready :row t t))
 :rule-classes nil)

(defun-nx iprdt-writer-domain-observation (bad current-corrupt fuel)
 (let* ((stages (iprdt-stages bad 12)) (pc (nth 0 stages))
        (before (iprdt-ready stages nil))
        (before (if current-corrupt
                 (update-fn-ibp-current
                  (list :installed-publication '(:index-generation 7 1 0)
                   (update-nth 10 '(:chunk 1 88 88) (nth 1 stages))) before) before))
        (out (mv-list 3 (fn-ibp-writer-complete pc 19 3 :fixture-visibility fuel before)))
        (after (mv-nth 2 out)) (pub (fn-omk-at 2 (fn-ibp-current after))))
  (list
   (fn-iprc-directory-row-domainp (fn-omk-at 12 (fn-ibp-builder before)) 0
    (fn-omk-at 13 (fn-ibp-builder before)) 2 2 2 (fn-ibp-registry before))
   (eq (mv-nth 0 out) :published)
   (fn-iprc-directory-row-domainp (fn-ipub-row-root pub) 0 (fn-ipub-row-depth pub) 2 2 2 (fn-ibp-registry after)))))
(defthm iprdt-writer-domain-positive
 (equal (iprdt-writer-domain-observation nil nil 12) '(t t t)) :rule-classes nil)
; Corrupted assigned row: publication shape/status alone never proves the domain.
(defthm iprdt-writer-domain-carry-removal
 (equal (iprdt-writer-domain-observation t nil 12) '(nil t nil)) :rule-classes nil)
; Corrupted current root is a removal witness, not a produced publication.
(defthm iprdt-writer-domain-status-removal
 (equal (iprdt-writer-domain-observation nil t 0) '(t nil nil)) :rule-classes nil)

(defconst *iprdt-directory* '(:branch (:branch (:chunk 2 99 1) (:chunk 3 31 31)) (:branch (:chunk 4 41 41) (:chunk 5 51 51))))
(defun iprdt-put-run (steps cursor)
 (declare (xargs :measure (nfix steps) :verify-guards nil))
 (if (zp steps) cursor (iprdt-put-run (- steps 1) (fn-ibp-dir-put-step cursor))))
(defthm iprdt-directory-real-update-shares-other-leaves
 (let* ((start (fn-ibp-dir-put-begin *iprdt-directory* 2 2 '(:chunk 0 17 17)))
        (done (iprdt-put-run 6 start)) (root (fn-omk-at 1 done)))
  (and (fn-iprc-directory-writable-pathp *iprdt-directory* 2 2)
       (eq (fn-omk-at 0 done) :done)
       (equal root (fn-iprc-directory-intent start))
       (equal (fn-iprc-directory-select root 2 2) '(:chunk 0 17 17))
       (fn-iprc-directory-readable-pathp *iprdt-directory* 0 2)
       (not (equal 2 0))
       (equal (fn-iprc-directory-select root 0 2) (fn-iprc-directory-select *iprdt-directory* 0 2))
       (equal (fn-iprc-directory-select root 1 2) (fn-iprc-directory-select *iprdt-directory* 1 2))
       (equal (fn-iprc-directory-select root 3 2) (fn-iprc-directory-select *iprdt-directory* 3 2))))
 :rule-classes nil)
(defthm iprdt-directory-put-recovery-removal
 (let ((cursor '(:descent (:chunk 2 99 1) 0 1 (:chunk 0 17 17) ((0 (:chunk 8 81 81))))))
  (and (eq (fn-omk-at 0 (fn-ibp-dir-put-step cursor)) :recovery-required)
       (not (equal (fn-iprc-directory-intent (fn-ibp-dir-put-step cursor)) (fn-iprc-directory-intent cursor)))))
 :rule-classes nil)
(defthm iprdt-directory-put-done-positive
 (let ((cursor '(:rebuild (:chunk 0 17 17) 0 0 (:chunk 0 17 17) nil)))
  (and (member-eq (fn-omk-at 0 cursor) '(:descent :rebuild))
       (eq (fn-omk-at 0 (fn-ibp-dir-put-step cursor)) :done)
       (equal (fn-omk-at 1 (fn-ibp-dir-put-step cursor)) (fn-iprc-directory-intent cursor))))
 :rule-classes nil)
; Corrupted terminal phase with retained frames.
(defthm iprdt-directory-put-phase-removal
 (let ((cursor '(:done (:chunk 0 17 17) 0 0 nil ((0 (:chunk 2 99 1))))))
  (and (not (member-eq (fn-omk-at 0 cursor) '(:descent :rebuild)))
       (eq (fn-omk-at 0 (fn-ibp-dir-put-step cursor)) :done)
       (not (equal (fn-omk-at 1 (fn-ibp-dir-put-step cursor)) (fn-iprc-directory-intent cursor)))))
 :rule-classes nil)
(defthm iprdt-directory-put-done-removal
 (let ((cursor (fn-ibp-dir-put-begin *iprdt-directory* 2 2 '(:chunk 0 17 17))))
  (and (member-eq (fn-omk-at 0 cursor) '(:descent :rebuild))
       (not (eq (fn-omk-at 0 (fn-ibp-dir-put-step cursor)) :done))
       (not (equal (fn-omk-at 1 (fn-ibp-dir-put-step cursor)) (fn-iprc-directory-intent cursor)))))
 :rule-classes nil)
(defun iprdt-share-observation (root target selected depth)
 (declare (xargs :verify-guards nil))
 (list (fn-iprc-directory-writable-pathp root target depth)
       (fn-iprc-directory-readable-pathp root selected depth)
       (not (equal target selected))
       (equal (fn-iprc-directory-select (fn-iprc-directory-replace root target depth '(:chunk 0 17 17)) selected depth)
              (fn-iprc-directory-select root selected depth))))
(defthm iprdt-directory-share-positive
 (equal (iprdt-share-observation *iprdt-directory* 2 0 2) '(t t t t)) :rule-classes nil)
; Invalid target leaf ordinal destroys the target subtree's old leaf.
(defthm iprdt-directory-share-write-path-removal
 (equal (iprdt-share-observation *iprdt-directory* 4 0 2) '(nil t t nil)) :rule-classes nil)
; Malformed old branch is explicitly a corrupted directory witness.
(defthm iprdt-directory-share-read-path-removal
 (equal (iprdt-share-observation '(:branch (:chunk 2 99 1) (:chunk 3 31 31) :extra) 0 1 1)
        '(t nil t nil)) :rule-classes nil)
(defthm iprdt-directory-share-distinct-removal
 (equal (iprdt-share-observation *iprdt-directory* 2 2 2) '(t t nil nil)) :rule-classes nil)
(defthm iprdt-directory-step-real-yield-and-borrow
 (let* ((cursor (fn-ibp-directory-start *iprdt-directory* 2 2))
        (yielded (mv-list 4 (fn-ibp-directory-step cursor 1)))
        (borrowed (mv-list 4 (fn-ibp-directory-step (mv-nth 1 yielded) 2))))
  (and (eq (mv-nth 0 yielded) :yield)
       (equal (fn-iprc-directory-select (nth 0 (mv-nth 1 yielded)) (nth 1 (mv-nth 1 yielded)) (nth 2 (mv-nth 1 yielded)))
              (fn-iprc-directory-select *iprdt-directory* 2 2))
       (eq (mv-nth 0 borrowed) :borrow-ready)
       (equal (mv-nth 2 borrowed) (fn-iprc-directory-select *iprdt-directory* 2 2))))
 :rule-classes nil)

(defun-nx iprdt-read-observation (node cursor directory-fuel count ordinal fuel)
 (let* ((borrow (mv-list 4 (fn-ibp-directory-step cursor directory-fuel)))
        (descriptor (mv-nth 2 borrow))
        (read (mv-list 3 (fn-ibp-node-row-read ordinal fuel (nth 1 descriptor) 2 (nth 2 descriptor) (nth 3 descriptor) node))))
  (list (fn-iprc-directory-row-domainp (nth 0 cursor) (nth 1 cursor) (nth 2 cursor) count 2 2 node)
        (eq (mv-nth 0 borrow) :borrow-ready)
        (< (nfix (mod ordinal 256)) (nfix count))
        (eq (mv-nth 0 read) :row)
        (fn-ibrc-row-domainp (mv-nth 1 read) 2))))
(defthm iprdt-borrowed-read-positive
 (equal (iprdt-read-observation (fn-ibp-registry (nth 6 (iprdt-stages nil 12)))
          '((:chunk 0 17 17) 0 0) 1 2 1 3) '(t t t t t)) :rule-classes nil)
(defthm iprdt-borrowed-read-domain-removal
 (equal (iprdt-read-observation (fn-ibp-registry (nth 6 (iprdt-stages t 12)))
          '((:chunk 0 17 17) 0 0) 1 2 1 3) '(nil t t t nil)) :rule-classes nil)
(defthm iprdt-borrowed-read-ordinal-removal
 (equal (iprdt-read-observation (fn-ibp-registry (nth 6 (iprdt-stages t 12)))
          '((:chunk 0 17 17) 0 0) 1 1 1 3) '(t t nil t nil)) :rule-classes nil)
(defthm iprdt-borrowed-read-row-status-removal
 (equal (iprdt-read-observation (fn-ibp-registry (nth 6 (iprdt-stages nil 12)))
          '((:chunk 0 17 17) 0 0) 1 2 1 0) '(t t t nil nil)) :rule-classes nil)
; A corrupted raw row header can match the NIL fields of a missing borrow.
; This is not a guarded/produced row page; it isolates the borrow-status premise.
(defun-nx iprdt-missing-borrow-node ()
 (let* ((node (iprdt-copy-node (iprmt-old) nil 0))
        (left (fn-ibp-node-children-get 'fn-ibp-node-left node (create-fn-ibp-node)))
        (leaf (fn-ibp-node-children-get 'fn-ibp-node-left left (create-fn-ibp-node)))
        (page (fn-ibp-node-children-get 'fn-ibp-row-page leaf (create-fn-ibp-row-page)))
        (page (update-fn-ibp-row-id nil (update-fn-ibp-row-incarnation nil (update-fn-ibp-row-sealed 1 page))))
        (leaf (fn-ibp-node-children-put 'fn-ibp-row-page page leaf))
        (left (fn-ibp-node-children-put 'fn-ibp-node-left leaf left)))
  (fn-ibp-node-children-put 'fn-ibp-node-left left node)))
(defthm iprdt-borrowed-read-borrow-status-removal
 (equal (iprdt-read-observation (iprdt-missing-borrow-node)
          '((:chunk 2 99 1) 0 0) 0 2 1 3) '(t nil t t nil)) :hints (("Goal" :in-theory (disable (:executable-counterpart fn-ibp-node-row-read)))) :rule-classes nil)

(defun-nx iprdt-seal-observation (bad intent-corrupt fuel)
 (let* ((stages (iprdt-stages bad 12)) (before (nth 4 stages))
        (before (if intent-corrupt
         (update-fn-ibp-builder
          (update-nth 18 '(:rebuild (:chunk 1 88 88) 0 0 nil nil) (fn-ibp-builder before)) before) before))
        (out (mv-list 3 (fn-ipa-row-seal fuel before))) (after (mv-nth 2 out)))
  (list (fn-iprc-seal-directory-carryp 2 before) (eq (mv-nth 0 out) :row-root)
        (fn-iprc-directory-row-domainp
         (fn-iprc-directory-intent (fn-omk-at 18 (fn-ibp-builder after))) 0 0 2 2 2 (fn-ibp-registry after)))))
(defthm iprdt-seal-directory-positive
 (equal (iprdt-seal-observation nil nil 10) '(t t t)) :rule-classes nil)
(defthm iprdt-seal-directory-carry-removal
 (equal (iprdt-seal-observation t nil 10) '(nil t nil)) :rule-classes nil)
; Corrupted old continuation plus actual yield isolates successful-seal premise.
(defthm iprdt-seal-directory-status-removal
 (equal (iprdt-seal-observation nil t 0) '(t nil nil)) :rule-classes nil)
(defun-nx iprdt-root-observation (cursor node fuel page row-depth count)
 (let* ((builder (update-nth 18 cursor (update-nth 1 :row-root (make-list 20))))
        (before (update-fn-ibp-registry node (update-fn-ibp-builder builder (create-fn-index-backing))))
        (out (mv-list 3 (fn-ipa-row-root-one fuel before))) (after (mv-nth 2 out)))
  (list (if (member-eq (fn-omk-at 0 cursor) '(:descent :rebuild)) t nil)
        (fn-iprc-directory-row-domainp (fn-iprc-directory-intent cursor) page row-depth count 2 2 node)
        (eq (mv-nth 0 out) :table-layout)
        (fn-iprc-directory-row-domainp (fn-omk-at 12 (fn-ibp-builder after)) page row-depth count 2 2 (fn-ibp-registry after)))))
(defthm iprdt-root-directory-positive
 (equal (iprdt-root-observation '(:rebuild (:chunk 2 99 1) 0 0 nil nil)
          (iprdt-copy-node (iprmt-old) nil 0) 1 0 0 2) '(t t t t)) :rule-classes nil)
(defthm iprdt-root-directory-phase-removal
 (equal (iprdt-root-observation
          '(:done (:branch (:chunk 1 88 88) (:chunk 1 88 88)) 0 0 nil ((0 (:chunk 2 99 1))))
          (iprdt-copy-node (iprmt-old) nil 0) 1 1 1 2) '(nil t t nil)) :rule-classes nil)
(defthm iprdt-root-directory-carry-removal
 (equal (iprdt-root-observation '(:rebuild (:chunk 1 88 88) 0 0 nil nil)
          (iprdt-copy-node (iprmt-old) nil 0) 1 0 0 2) '(t nil t nil)) :rule-classes nil)
(defthm iprdt-root-directory-status-removal
 (equal (iprdt-root-observation (fn-ibp-dir-put-begin nil 0 0 '(:chunk 2 99 1))
          (iprdt-copy-node (iprmt-old) nil 0) 1 0 0 2) '(t t nil nil)) :rule-classes nil)

; Synthetic old full-page publication isolates the actual shared-page caller.
; Its typed prefix is carried separately; this fixture does not assert catalog coverage.
(defun-nx iprdt-share-caller ()
 (let* ((stages (iprdt-stages nil 12)) (backing (nth 6 stages))
        (pub (fn-ipub-make 7 :key 1 256 19 3 nil 0 7 '(:chunk 0 17 17) 0 7 nil 7 nil nil 7 2))
        (builder (fn-ibp-builder backing))
        (receipt (update-nth 7 (list :installed-publication '(:index-generation 7 1 0) pub) (fn-omk-at 19 builder)))
        (builder (update-nth 19 receipt (update-nth 17 nil (update-nth 6 256 builder))))
        (before (update-fn-ibp-page-pending nil (update-fn-ibp-builder builder backing)))
        (begin (mv-list 3 (fn-ipa-row-share-begin 1 before)))
        (walk (mv-list 3 (fn-ipa-row-share-one 1 (mv-nth 2 begin))))
        (retain (mv-list 3 (fn-ipa-row-share-one 6 (mv-nth 2 walk))))
        (after (mv-nth 2 retain))
        (row (mv-nth 1 (fn-ibp-node-page-owner-action '(:index-page 17 1 0) :read nil nil nil nil 3 0 2 (fn-ibp-registry after)))))
  (list (mv-nth 0 begin) (mv-nth 0 walk) (mv-nth 0 retain)
        (fn-iprc-node-prefixp 0 2 2 2 (fn-ibp-registry before))
        (equal (fn-iprc-node-prefixp 0 2 2 2 (fn-ibp-registry before))
               (fn-iprc-node-prefixp 0 2 2 2 (fn-ibp-registry after)))
        (fn-omk-at 6 row) (fn-omk-at 17 (fn-ibp-builder after)))))
(defthm iprdt-share-actual-retain-positive
 (equal (iprdt-share-caller) '(:row-share :row-share :table-layout t t 2 :rows-shared))
 :rule-classes nil)
