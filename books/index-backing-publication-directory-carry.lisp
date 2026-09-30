; Actual persistent row directory construction, sharing and reader correspondence.
; Proof-only relations: no directory/row traversal is added to served bodies.
(in-package "ACL2")
(include-book "index-backing-publication-row-carry")
(include-book "index-backing-row-retain")
(include-book "index-backing-writer")

; The predecessor keeps this normalizer local; an includer owns its own hint.
(local (defthm fn-ipdc-omk-at-is-nth
 (implies (natp i) (equal (fn-omk-at i xs) (nth i xs)))
 :hints (("Goal" :induct (fn-omk-at i xs)
                  :in-theory (enable fn-omk-at nth)))))

(encapsulate ()
(defthm fn-iprc-share-begin-preserves-registry
 (equal (fn-ibp-registry (mv-nth 2 (fn-ipa-row-share-begin fuel fn-index-backing)))
        (fn-ibp-registry fn-index-backing))
 :hints (("Goal" :in-theory (e/d (fn-ipa-row-share-begin) (nth update-nth floor mod)))))
(defthm fn-iprc-root-one-preserves-registry
 (equal (fn-ibp-registry (mv-nth 2 (fn-ipa-row-root-one fuel fn-index-backing)))
        (fn-ibp-registry fn-index-backing))
 :hints (("Goal" :in-theory (e/d (fn-ipa-row-root-one) (fn-ibp-dir-put-step nth update-nth)))))
(defthm fn-iprc-share-one-preserves-row-prefix
 (equal
  (fn-iprc-node-prefixp slot (fn-ibp-slot-depth fn-index-backing) count prefix
   (fn-ibp-registry (mv-nth 2 (fn-ipa-row-share-one fuel fn-index-backing))))
  (fn-iprc-node-prefixp slot (fn-ibp-slot-depth fn-index-backing) count prefix
   (fn-ibp-registry fn-index-backing)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ipa-row-share-one)
   (fn-iprc-node-prefixp fn-ibp-node-page-owner-action fn-ibp-directory-step
    fn-ibp-directory-start fn-omk-at nth update-nth mod floor mod-=-0 floor-=-x/y mod-type)))))
)

(encapsulate ()
(defun fn-iprc-directory-select (root index depth)
 (declare (xargs :measure (nfix depth) :verify-guards nil))
 (cond ((zp depth) (if (equal index 0) root nil))
       ((and (true-listp root) (equal (len root) 3) (eq (car root) :branch))
        (fn-iprc-directory-select
         (if (equal (mod index 2) 0) (nth 1 root) (nth 2 root))
         (floor index 2) (- depth 1)))
       (t nil)))
(defthm fn-iprc-directory-step-selection
 (implies
  (member-eq (mv-nth 0 (fn-ibp-directory-step cursor fuel)) '(:yield :borrow-ready))
  (equal
   (fn-iprc-directory-select
    (nth 0 (mv-nth 1 (fn-ibp-directory-step cursor fuel)))
    (nth 1 (mv-nth 1 (fn-ibp-directory-step cursor fuel)))
    (nth 2 (mv-nth 1 (fn-ibp-directory-step cursor fuel))))
   (fn-iprc-directory-select (nth 0 cursor) (nth 1 cursor) (nth 2 cursor))))
 :hints (("Goal" :induct (fn-ibp-directory-step cursor fuel)
  :in-theory (e/d (fn-ibp-directory-step fn-iprc-directory-select)
    (mod floor mod-=-0 floor-=-x/y mod-type)))))
(defthm fn-iprc-directory-borrow-is-selected
 (implies (eq (mv-nth 0 (fn-ibp-directory-step cursor fuel)) :borrow-ready)
  (equal (mv-nth 2 (fn-ibp-directory-step cursor fuel))
         (fn-iprc-directory-select (nth 0 cursor) (nth 1 cursor) (nth 2 cursor))))
 :hints (("Goal" :induct (fn-ibp-directory-step cursor fuel)
  :in-theory (e/d (fn-ibp-directory-step fn-iprc-directory-select)
    (mod floor mod-=-0 floor-=-x/y mod-type)))))
)

(encapsulate ()
(defun fn-iprc-directory-replace (root index depth leaf)
 (declare (xargs :measure (nfix depth) :verify-guards nil))
 (cond ((not (and (natp index) (natp depth))) nil)
       ((zp depth) (if (equal index 0) leaf nil))
       ((or (null root) (and (consp root) (eq (car root) :branch)))
        (if (equal (mod index 2) 0)
            (list :branch (fn-iprc-directory-replace (fn-omk-at 1 root) (floor index 2) (- depth 1) leaf) (fn-omk-at 2 root))
          (list :branch (fn-omk-at 1 root) (fn-iprc-directory-replace (fn-omk-at 2 root) (floor index 2) (- depth 1) leaf))))
       (t nil)))
(defun fn-iprc-directory-rebuild (node frames)
 (declare (xargs :verify-guards nil))
 (if (atom frames) node
  (fn-iprc-directory-rebuild
   (if (equal (fn-omk-at 0 (car frames)) 0)
       (list :branch node (fn-omk-at 1 (car frames)))
     (list :branch (fn-omk-at 1 (car frames)) node)) (cdr frames))))
(defun fn-iprc-directory-intent (cursor)
 (declare (xargs :verify-guards nil))
 (fn-iprc-directory-rebuild
  (if (eq (fn-omk-at 0 cursor) :descent)
      (fn-iprc-directory-replace (fn-omk-at 1 cursor) (fn-omk-at 2 cursor) (fn-omk-at 3 cursor) (fn-omk-at 4 cursor))
    (fn-omk-at 1 cursor))
  (fn-omk-at 5 cursor)))
(defthm fn-iprc-directory-put-preserves-intent
 (implies
  (not (eq (fn-omk-at 0 (fn-ibp-dir-put-step cursor)) :recovery-required))
  (equal (fn-iprc-directory-intent (fn-ibp-dir-put-step cursor))
         (fn-iprc-directory-intent cursor)))
 :hints (("Goal" :do-not-induct t
  :expand ((fn-iprc-directory-replace (fn-omk-at 1 cursor) (fn-omk-at 2 cursor) (fn-omk-at 3 cursor) (fn-omk-at 4 cursor)))
  :in-theory (e/d (fn-ibp-dir-put-step fn-iprc-directory-intent fn-iprc-directory-rebuild fn-iprc-directory-replace)
   (nth mod floor mod-=-0 floor-=-x/y mod-type)))))
(defthm fn-iprc-directory-put-done-root
 (implies (and (member-eq (fn-omk-at 0 cursor) '(:descent :rebuild))
               (eq (fn-omk-at 0 (fn-ibp-dir-put-step cursor)) :done))
  (equal (fn-omk-at 1 (fn-ibp-dir-put-step cursor)) (fn-iprc-directory-intent cursor)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibp-dir-put-step fn-iprc-directory-intent fn-iprc-directory-rebuild fn-iprc-directory-replace)
   (nth mod floor mod-=-0 floor-=-x/y mod-type)))))
)

(encapsulate ()
(defthm fn-iprc-root-one-publishes-intended-root
 (implies
  (and (member-eq (fn-omk-at 0 (fn-omk-at 18 (fn-ibp-builder fn-index-backing))) '(:descent :rebuild))
       (eq (mv-nth 0 (fn-ipa-row-root-one fuel fn-index-backing)) :table-layout))
  (equal (fn-omk-at 12 (fn-ibp-builder (mv-nth 2 (fn-ipa-row-root-one fuel fn-index-backing))))
         (fn-iprc-directory-intent (fn-omk-at 18 (fn-ibp-builder fn-index-backing)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-iprc-directory-put-done-root
          (cursor (fn-omk-at 18 (fn-ibp-builder fn-index-backing)))))
  :in-theory (e/d (fn-ipa-row-root-one)
   (fn-iprc-directory-put-done-root fn-ibp-dir-put-step fn-iprc-directory-intent nth update-nth fn-omk-at)))))
(defthm fn-iprc-root-one-retains-intended-root
 (implies
  (and (eq (mv-nth 0 (fn-ipa-row-root-one fuel fn-index-backing)) :row-root))
  (equal (fn-iprc-directory-intent
          (fn-omk-at 18 (fn-ibp-builder (mv-nth 2 (fn-ipa-row-root-one fuel fn-index-backing)))))
         (fn-iprc-directory-intent (fn-omk-at 18 (fn-ibp-builder fn-index-backing)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ipa-row-root-one)
   (fn-ibp-dir-put-step fn-iprc-directory-intent nth update-nth fn-omk-at)))))
(defun-nx fn-iprc-directory-row-domainp (root page row-depth count prefix depth node)
 (let ((descriptor (fn-iprc-directory-select root page row-depth)))
  (fn-iprc-node-prefixp (nth 1 descriptor) depth count prefix node)))
(defthm fn-iprc-borrowed-directory-row-read-domain
 (implies
  (and (fn-iprc-directory-row-domainp (nth 0 cursor) (nth 1 cursor) (nth 2 cursor) count prefix depth fn-ibp-node)
       (eq (mv-nth 0 (fn-ibp-directory-step cursor directory-fuel)) :borrow-ready)
       (< (nfix (mod ordinal 256)) (nfix count))
       (eq (mv-nth 0
        (fn-ibp-node-row-read ordinal fuel
         (nth 1 (mv-nth 2 (fn-ibp-directory-step cursor directory-fuel))) depth
         (nth 2 (mv-nth 2 (fn-ibp-directory-step cursor directory-fuel)))
         (nth 3 (mv-nth 2 (fn-ibp-directory-step cursor directory-fuel))) fn-ibp-node)) :row))
  (fn-ibrc-row-domainp
   (mv-nth 1 (fn-ibp-node-row-read ordinal fuel
    (nth 1 (mv-nth 2 (fn-ibp-directory-step cursor directory-fuel))) depth
    (nth 2 (mv-nth 2 (fn-ibp-directory-step cursor directory-fuel)))
    (nth 3 (mv-nth 2 (fn-ibp-directory-step cursor directory-fuel))) fn-ibp-node)) prefix))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-iprc-actual-node-read-row-domain
   (slot (nth 1 (mv-nth 2 (fn-ibp-directory-step cursor directory-fuel))))
   (id (nth 2 (mv-nth 2 (fn-ibp-directory-step cursor directory-fuel))))
   (incarnation (nth 3 (mv-nth 2 (fn-ibp-directory-step cursor directory-fuel))))))
  :in-theory (e/d (fn-iprc-directory-row-domainp)
   (fn-iprc-actual-node-read-row-domain fn-ibp-directory-step fn-iprc-directory-select fn-iprc-node-prefixp
    fn-ibp-node-row-read fn-ibrc-row-domainp nth nfix mod floor mod-=-0 floor-=-x/y mod-type)))))
)

(encapsulate ()
(defun fn-iprc-directory-writable-pathp (root index depth)
 (declare (xargs :measure (nfix depth) :verify-guards nil))
 (and (natp index) (natp depth)
  (if (zp depth) (equal index 0)
   (and (or (null root) (and (consp root) (eq (car root) :branch)))
    (fn-iprc-directory-writable-pathp
     (if (equal (mod index 2) 0) (fn-omk-at 1 root) (fn-omk-at 2 root))
     (floor index 2) (- depth 1))))))
(defthm fn-iprc-directory-replace-selects-new-leaf
 (implies (fn-iprc-directory-writable-pathp root index depth)
  (equal (fn-iprc-directory-select (fn-iprc-directory-replace root index depth leaf) index depth) leaf))
 :hints (("Goal" :induct (fn-iprc-directory-writable-pathp root index depth)
  :in-theory (e/d (fn-iprc-directory-writable-pathp fn-iprc-directory-replace fn-iprc-directory-select)
   (nth mod floor mod-=-0 floor-=-x/y mod-type)))))
(defthm fn-iprc-directory-replace-establishes-row-domain
 (implies
  (and (fn-iprc-directory-writable-pathp root page row-depth)
       (fn-iprc-node-prefixp (nth 1 descriptor) depth count prefix node))
  (fn-iprc-directory-row-domainp
   (fn-iprc-directory-replace root page row-depth descriptor) page row-depth count prefix depth node))
 :hints (("Goal" :in-theory (e/d (fn-iprc-directory-row-domainp)
  (fn-iprc-directory-writable-pathp fn-iprc-directory-replace fn-iprc-directory-select fn-iprc-node-prefixp nth)))))
)

(encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-iprc-same-branch-distinct-quotient
 (implies (and (natp index) (natp selected)
               (iff (equal (mod index 2) 0) (equal (mod selected 2) 0))
               (not (equal index selected)))
  (not (equal (floor index 2) (floor selected 2))))
 :hints (("Goal" :in-theory (enable mod)))
 :rule-classes nil)
)

(encapsulate ()
(local (defthm fn-iprc-distinct-quotient-rewrite
 (implies (and (natp index) (natp selected)
               (iff (equal (mod index 2) 0) (equal (mod selected 2) 0))
               (not (equal index selected)))
  (not (equal (floor index 2) (floor selected 2))))
 :hints (("Goal" :use fn-iprc-same-branch-distinct-quotient
  :in-theory (disable mod floor mod-=-0 floor-=-x/y mod-type)))))
(defun fn-iprc-directory-readable-pathp (root index depth)
 (declare (xargs :measure (nfix depth) :verify-guards nil))
 (and (natp index) (natp depth)
  (if (zp depth) (equal index 0)
   (and (true-listp root) (equal (len root) 3) (eq (car root) :branch)
    (fn-iprc-directory-readable-pathp
     (if (equal (mod index 2) 0) (nth 1 root) (nth 2 root))
     (floor index 2) (- depth 1))))))
(local (defun fn-iprc-directory-paired-induct (root index selected depth leaf)
 (declare (xargs :measure (nfix depth) :verify-guards nil))
 (if (zp depth) (list root index selected leaf)
  (fn-iprc-directory-paired-induct
   (if (equal (mod index 2) 0) (nth 1 root) (nth 2 root))
   (floor index 2) (floor selected 2) (- depth 1) leaf))))
(defthm fn-iprc-directory-replace-shares-other-leaf
 (implies
  (and (fn-iprc-directory-writable-pathp root index depth)
       (fn-iprc-directory-readable-pathp root selected depth)
       (not (equal index selected)))
  (equal
   (fn-iprc-directory-select (fn-iprc-directory-replace root index depth leaf) selected depth)
   (fn-iprc-directory-select root selected depth)))
 :hints (("Goal"
  :induct (fn-iprc-directory-paired-induct root index selected depth leaf)
  :do-not '(generalize eliminate-destructors)
  :in-theory (e/d (fn-iprc-directory-writable-pathp fn-iprc-directory-readable-pathp
                   fn-iprc-directory-replace fn-iprc-directory-select)
   (nth mod floor mod-=-0 floor-=-x/y mod-type floor-type-2 floor-type-3 floor-type-4)))))
)

(encapsulate ()
(defthm fn-iprc-row-seal-preserves-copied-prefix
 (let* ((receipt (fn-ibp-page-pending fn-index-backing))
        (physical (fn-omk-at 3 receipt)) (depth (fn-ibp-slot-depth fn-index-backing)))
  (implies (fn-iprc-node-prefixp physical depth count prefix (fn-ibp-registry fn-index-backing))
   (fn-iprc-node-prefixp physical depth count prefix
    (fn-ibp-registry (mv-nth 2 (fn-ipa-row-seal fuel fn-index-backing))))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ipa-row-seal)
   (fn-iprc-node-prefixp fn-ibp-node-page-owner-action fn-ibp-node-row-write
    fn-omk-at nth update-nth mod floor mod-=-0 floor-=-x/y mod-type)))))
(defthm fn-iprc-row-seal-starts-actual-directory-update
 (implies (eq (mv-nth 0 (fn-ipa-row-seal fuel fn-index-backing)) :row-root)
  (equal
   (fn-omk-at 18 (fn-ibp-builder (mv-nth 2 (fn-ipa-row-seal fuel fn-index-backing))))
   (fn-ibp-dir-put-begin
    (fn-ipub-row-root (fn-omk-at 2 (fn-omk-at 7 (fn-omk-at 19 (fn-ibp-builder fn-index-backing)))) )
    (fn-omk-at 8 (fn-ibp-page-pending fn-index-backing))
    (fn-ipub-row-depth (fn-omk-at 2 (fn-omk-at 7 (fn-omk-at 19 (fn-ibp-builder fn-index-backing)))))
    (list :chunk (fn-omk-at 3 (fn-ibp-page-pending fn-index-backing))
                 (fn-omk-at 2 (fn-ibp-page-pending fn-index-backing))
                 (fn-omk-at 2 (fn-ibp-page-pending fn-index-backing))))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ipa-row-seal)
   (fn-iprc-node-prefixp fn-ibp-node-page-owner-action fn-ibp-node-row-write
    fn-ibp-dir-put-begin fn-omk-at nth update-nth mod floor mod-=-0 floor-=-x/y mod-type)))))
)

(encapsulate ()
(defun-nx fn-iprc-seal-directory-carryp (prefix backing)
 (let* ((receipt (fn-ibp-page-pending backing)) (builder (fn-ibp-builder backing))
        (old (fn-omk-at 2 (fn-omk-at 7 (fn-omk-at 19 builder))))
        (page (fn-omk-at 8 receipt)) (physical (fn-omk-at 3 receipt)))
  (and (fn-iprc-directory-writable-pathp (fn-ipub-row-root old) page (fn-ipub-row-depth old))
       (fn-iprc-node-prefixp physical (fn-ibp-slot-depth backing)
        (+ 1 (mod (fn-omk-at 6 builder) 256)) prefix (fn-ibp-registry backing)))))
(defthm fn-iprc-row-seal-establishes-directory-carry
 (implies
  (and (fn-iprc-seal-directory-carryp prefix fn-index-backing)
       (eq (mv-nth 0 (fn-ipa-row-seal fuel fn-index-backing)) :row-root))
  (fn-iprc-directory-row-domainp
   (fn-iprc-directory-intent
    (fn-omk-at 18 (fn-ibp-builder (mv-nth 2 (fn-ipa-row-seal fuel fn-index-backing)))))
   (fn-omk-at 8 (fn-ibp-page-pending fn-index-backing))
   (fn-ipub-row-depth (fn-omk-at 2 (fn-omk-at 7 (fn-omk-at 19 (fn-ibp-builder fn-index-backing)))))
   (+ 1 (mod (fn-omk-at 6 (fn-ibp-builder fn-index-backing)) 256)) prefix
   (fn-ibp-slot-depth fn-index-backing)
   (fn-ibp-registry (mv-nth 2 (fn-ipa-row-seal fuel fn-index-backing)))))
  :hints (("Goal" :do-not-induct t
  :use ((:instance fn-iprc-row-seal-starts-actual-directory-update)
        (:instance fn-iprc-row-seal-preserves-copied-prefix
         (count (+ 1 (mod (fn-omk-at 6 (fn-ibp-builder fn-index-backing)) 256)))))
  :in-theory (e/d (fn-iprc-seal-directory-carryp fn-iprc-directory-intent
                   fn-ibp-dir-put-begin fn-iprc-directory-rebuild fn-iprc-directory-row-domainp)
   (fn-ipa-row-seal fn-iprc-directory-select fn-iprc-directory-replace
    fn-iprc-directory-writable-pathp fn-iprc-node-prefixp fn-omk-at nth mod floor)))))
(defthm fn-iprc-root-one-completes-directory-carry
 (implies
  (and (member-eq (fn-omk-at 0 (fn-omk-at 18 (fn-ibp-builder fn-index-backing))) '(:descent :rebuild))
       (fn-iprc-directory-row-domainp
        (fn-iprc-directory-intent (fn-omk-at 18 (fn-ibp-builder fn-index-backing)))
        page row-depth count prefix depth (fn-ibp-registry fn-index-backing))
       (eq (mv-nth 0 (fn-ipa-row-root-one fuel fn-index-backing)) :table-layout))
  (fn-iprc-directory-row-domainp
   (fn-omk-at 12 (fn-ibp-builder (mv-nth 2 (fn-ipa-row-root-one fuel fn-index-backing))))
   page row-depth count prefix depth
   (fn-ibp-registry (mv-nth 2 (fn-ipa-row-root-one fuel fn-index-backing)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-iprc-root-one-publishes-intended-root)
        (:instance fn-iprc-root-one-preserves-registry))
  :in-theory (disable fn-iprc-directory-row-domainp fn-iprc-directory-intent
    fn-ipa-row-root-one fn-omk-at nth))))
)

(encapsulate ()
(local (defun-nx fn-iprc-generation-path-induct (slot address depth fuel node)
 (declare (xargs :measure (nfix depth)))
 (if (zp depth) (list slot fuel node)
  (fn-iprc-generation-path-induct (floor slot 2) (floor address 2) (- depth 1) (- fuel 1)
   (fn-ibp-node-children-get
    (if (evenp address) 'fn-ibp-node-left 'fn-ibp-node-right) node (create-fn-ibp-node))))))
(defthm fn-iprc-generation-publish-preserves-row-prefix
 (equal
  (fn-iprc-node-prefixp slot depth count prefix
   (mv-nth 2 (fn-ibp-node-generation-publish token publication fuel address depth fn-ibp-node)))
  (fn-iprc-node-prefixp slot depth count prefix fn-ibp-node))
 :hints (("Goal" :induct (fn-iprc-generation-path-induct slot address depth fuel fn-ibp-node)
  :do-not '(generalize eliminate-destructors)
  :expand ((fn-iprc-node-prefixp slot depth count prefix fn-ibp-node)
           (fn-ibp-node-generation-publish token publication fuel address depth fn-ibp-node))
  :in-theory (e/d (fn-iprc-node-prefixp fn-ibp-node-generation-publish)
   (fn-ibp-generation-install-publication nth fn-ibrc-prefixp fn-ibrc-row-domainp
    mod floor mod-=-0 floor-=-x/y mod-type floor-type-2 floor-type-3 floor-type-4)))))
(defthm fn-iprc-generation-reference-preserves-row-prefix
 (equal
  (fn-iprc-node-prefixp slot depth count prefix
   (mv-nth 4 (fn-ibp-node-generation-reference token operation kind settlement fuel address depth fn-ibp-node)))
  (fn-iprc-node-prefixp slot depth count prefix fn-ibp-node))
 :hints (("Goal" :induct (fn-iprc-generation-path-induct slot address depth fuel fn-ibp-node)
  :do-not '(generalize eliminate-destructors)
  :expand ((fn-iprc-node-prefixp slot depth count prefix fn-ibp-node)
           (fn-ibp-node-generation-reference token operation kind settlement fuel address depth fn-ibp-node))
  :in-theory (e/d (fn-iprc-node-prefixp fn-ibp-node-generation-reference)
   (fn-ibp-generation-retain fn-ibp-generation-drop-reference fn-ibp-generation-finish-retirement
    nth fn-ibrc-prefixp fn-ibrc-row-domainp
    mod floor mod-=-0 floor-=-x/y mod-type floor-type-2 floor-type-3 floor-type-4)))))
(defthm fn-iprc-writer-complete-preserves-row-prefix
 (equal
  (fn-iprc-node-prefixp slot (fn-ibp-slot-depth fn-index-backing) count prefix
   (fn-ibp-registry (mv-nth 2 (fn-ibp-writer-complete pc frontier version visibility fuel fn-index-backing))))
  (fn-iprc-node-prefixp slot (fn-ibp-slot-depth fn-index-backing) count prefix (fn-ibp-registry fn-index-backing)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibp-writer-complete fn-ibp-generation-publish fn-ibp-generation-reference)
   (fn-iprc-node-prefixp fn-ibp-node-generation-publish fn-ibp-node-generation-reference
    fn-ibp-generation-read fn-ibp-writer-publication fn-ibp-writer-ready-p fn-ipub-shapep
    fn-omk-at nth update-nth mod floor mod-=-0 floor-=-x/y mod-type)))))
)

(encapsulate ()
(defthm fn-iprc-writer-complete-publishes-actual-coordinate
 (implies
  (eq (mv-nth 0 (fn-ibp-writer-complete pc frontier version visibility fuel fn-index-backing)) :published)
  (equal
   (fn-ibp-current (mv-nth 2 (fn-ibp-writer-complete pc frontier version visibility fuel fn-index-backing)))
   (list :installed-publication (fn-omk-at 2 (fn-ibp-builder fn-index-backing))
    (fn-ibp-writer-publication (fn-ibp-builder fn-index-backing) pc frontier version visibility
     (mv-nth 1 (fn-ibp-generation-read (fn-omk-at 2 (fn-ibp-builder fn-index-backing)) fuel fn-index-backing))))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibp-writer-complete)
   (fn-ibp-generation-publish fn-ibp-generation-reference fn-ibp-generation-read
    fn-ibp-writer-publication fn-ibp-writer-ready-p fn-ipub-shapep fn-omk-at nth update-nth)))))
(defthm fn-iprc-writer-complete-publishes-row-domain
 (implies
  (and (fn-iprc-directory-row-domainp
        (fn-omk-at 12 (fn-ibp-builder fn-index-backing)) page
        (fn-omk-at 13 (fn-ibp-builder fn-index-backing)) count prefix
        (fn-ibp-slot-depth fn-index-backing) (fn-ibp-registry fn-index-backing))
       (eq (mv-nth 0 (fn-ibp-writer-complete pc frontier version visibility fuel fn-index-backing)) :published))
  (let ((after (mv-nth 2 (fn-ibp-writer-complete pc frontier version visibility fuel fn-index-backing))))
   (fn-iprc-directory-row-domainp
    (fn-ipub-row-root (fn-omk-at 2 (fn-ibp-current after))) page
    (fn-ipub-row-depth (fn-omk-at 2 (fn-ibp-current after))) count prefix
    (fn-ibp-slot-depth fn-index-backing) (fn-ibp-registry after))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-iprc-writer-complete-publishes-actual-coordinate)
        (:instance fn-iprc-writer-complete-preserves-row-prefix
         (slot (nth 1 (fn-iprc-directory-select
                (fn-omk-at 12 (fn-ibp-builder fn-index-backing)) page
                (fn-omk-at 13 (fn-ibp-builder fn-index-backing)))))))
  :in-theory (e/d (fn-iprc-directory-row-domainp fn-ibp-writer-publication fn-ipub-make fn-ipub-row-root fn-ipub-row-depth)
   (fn-iprc-writer-complete-publishes-actual-coordinate fn-ibp-writer-complete
    fn-ibp-generation-read fn-iprc-directory-select fn-iprc-node-prefixp fn-omk-at nth)))))
)
