; Registered immutable publication and staged physical writer. No host root
; setter is exported. Builder construction/installation remains internal until
; its operation-derived shared-pool admission and runtime census are joined.
(in-package "ACL2")
(logic)
(include-book "index-backing-resource-driver")
(include-book "catalog-prepared-record")

; Fixed publication object. Root identities are issued by the same core
; allocator as the generation and bind these exact retained root objects.
(include-book "index-publication-shape")

(defun fn-ipub-capture (publication)
  (declare (xargs :guard t))
  (fn-ibp-capture-make (fn-ipub-generation publication) (fn-ipub-key publication)
    (fn-ipub-pages publication) (fn-ipub-count publication) (fn-ipub-frontier publication)
    (fn-ipub-table-root publication) (fn-ipub-table-depth publication) (fn-ipub-table-id publication)
    (fn-ipub-row-root publication) (fn-ipub-row-depth publication) (fn-ipub-row-id publication)))

(defun fn-ibp-current-publication (fn-mio$c)
  (declare (xargs :stobjs fn-mio$c :guard t))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (publication)
    (fn-ibp-current fn-index-backing)
    publication))

; One action installs at most one fixed node or one fixed table page. Missing
; interior nodes stop the action after construction; no recursive eager tree
; allocation occurs. ID/incarnation are internal registered-builder values.
(defun fn-ibp-node-install-table (slot depth id incarnation fuel fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
    :guard (and (natp slot) (natp depth) (posp id) (natp incarnation) (natp fuel))))
  (cond ((<= fuel depth) (mv :yield fuel fn-ibp-node))
        ((zp depth)
         (if (fn-ibp-node-children-boundp 'fn-ibp-table-page fn-ibp-node)
             (mv :already-present fuel fn-ibp-node)
           (stobj-let ((fn-ibp-table-page
                        (fn-ibp-node-children-get 'fn-ibp-table-page fn-ibp-node
                                                  (create-fn-ibp-table-page))))
             (status fn-ibp-table-page)
             (fn-ibp-table-initialize id incarnation fn-ibp-table-page)
             (mv status (- fuel 1) fn-ibp-node))))
        ((equal (mod slot 2) 0)
         (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
             (mv-let (status fn-ibp-node) (fn-ibp-node-add-left id fn-ibp-node)
               (mv status (- fuel 1) fn-ibp-node))
           (stobj-let ((fn-ibp-node-left
                        (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                                  (create-fn-ibp-node-left))))
             (status remaining fn-ibp-node-left)
             (fn-ibp-node-install-table (floor slot 2) (- depth 1) id incarnation
                                       (- fuel 1) fn-ibp-node-left)
             (mv status remaining fn-ibp-node))))
        (t
         (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
             (stobj-let ((fn-ibp-node-right
                          (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                                    (create-fn-ibp-node-right))))
               (fn-ibp-node-right)
               (update-fn-ibp-node-id id fn-ibp-node-right)
               (mv :installed (- fuel 1) fn-ibp-node))
           (stobj-let ((fn-ibp-node-right
                        (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                                  (create-fn-ibp-node-right))))
             (status remaining fn-ibp-node-right)
             (fn-ibp-node-install-table (floor slot 2) (- depth 1) id incarnation
                                       (- fuel 1) fn-ibp-node-right)
             (mv status remaining fn-ibp-node))))))
(verify-guards fn-ibp-node-install-table)

(defun fn-ibp-node-install-row (slot depth id incarnation fuel fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
    :guard (and (natp slot) (natp depth) (posp id) (natp incarnation) (natp fuel))))
  (cond ((<= fuel depth) (mv :yield fuel fn-ibp-node))
        ((zp depth)
         (if (fn-ibp-node-children-boundp 'fn-ibp-row-page fn-ibp-node)
             (mv :already-present fuel fn-ibp-node)
           (stobj-let ((fn-ibp-row-page
                        (fn-ibp-node-children-get 'fn-ibp-row-page fn-ibp-node
                                                  (create-fn-ibp-row-page))))
             (status fn-ibp-row-page)
             (fn-ibp-row-initialize id incarnation fn-ibp-row-page)
             (mv status (- fuel 1) fn-ibp-node))))
        ((equal (mod slot 2) 0)
         (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
             (mv-let (status fn-ibp-node) (fn-ibp-node-add-left id fn-ibp-node)
               (mv status (- fuel 1) fn-ibp-node))
           (stobj-let ((fn-ibp-node-left
                        (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                                  (create-fn-ibp-node-left))))
             (status remaining fn-ibp-node-left)
             (fn-ibp-node-install-row (floor slot 2) (- depth 1) id incarnation
                                       (- fuel 1) fn-ibp-node-left)
             (mv status remaining fn-ibp-node))))
        (t
         (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
             (stobj-let ((fn-ibp-node-right
                          (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                                    (create-fn-ibp-node-right))))
               (fn-ibp-node-right)
               (update-fn-ibp-node-id id fn-ibp-node-right)
               (mv :installed (- fuel 1) fn-ibp-node))
           (stobj-let ((fn-ibp-node-right
                        (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                                  (create-fn-ibp-node-right))))
             (status remaining fn-ibp-node-right)
             (fn-ibp-node-install-row (floor slot 2) (- depth 1) id incarnation
                                       (- fuel 1) fn-ibp-node-right)
             (mv status remaining fn-ibp-node))))))
(verify-guards fn-ibp-node-install-row)

; Placement selects only the registered unsealed destination child. Old sealed
; generations can never enter the chunk mutation kernel.
(defun fn-ibp-node-place (tag ordinal cursor pages page-index slot depth id incarnation fuel fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
                  :guard (and (posp tag) (unsigned-byte-p 64 tag) (natp ordinal) (unsigned-byte-p 64 (+ 1 ordinal)) (fn-mpr-cursorp cursor pages) (natp page-index) (< page-index pages) (natp slot) (natp depth) (posp id) (natp incarnation) (natp fuel) (<= fuel *fn-mpr-slot-quantum*))))
  (cond ((<= fuel depth) (mv :yield cursor fuel fn-ibp-node))
        ((zp depth)
         (if (not (fn-ibp-node-children-boundp 'fn-ibp-table-page fn-ibp-node))
             (mv :unavailable cursor fuel fn-ibp-node)
           (stobj-let ((fn-ibp-table-page
                        (fn-ibp-node-children-get 'fn-ibp-table-page fn-ibp-node
                                                  (create-fn-ibp-table-page))))
             (status next remaining fn-ibp-table-page)
             (if (and (equal (fn-ibp-table-id fn-ibp-table-page) id)
                      (equal (fn-ibp-table-incarnation fn-ibp-table-page) incarnation)
                      (equal (fn-ibp-table-sealed fn-ibp-table-page) 0))
                 (fn-miw-chunk-place tag ordinal cursor fuel pages page-index fn-ibp-table-page)
               (mv :recovery-required cursor fuel fn-ibp-table-page))
             (mv status next remaining fn-ibp-node))))
        ((equal (mod slot 2) 0)
         (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
             (mv :unavailable cursor fuel fn-ibp-node)
           (stobj-let ((fn-ibp-node-left (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node (create-fn-ibp-node-left))))
             (status next remaining fn-ibp-node-left)
             (fn-ibp-node-place tag ordinal cursor pages page-index (floor slot 2) (- depth 1) id incarnation (- fuel 1) fn-ibp-node-left)
             (mv status next remaining fn-ibp-node))))        (t
         (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
             (mv :unavailable cursor fuel fn-ibp-node)
           (stobj-let ((fn-ibp-node-right (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node (create-fn-ibp-node-right))))
             (status next remaining fn-ibp-node-right)
             (fn-ibp-node-place tag ordinal cursor pages page-index (floor slot 2) (- depth 1) id incarnation (- fuel 1) fn-ibp-node-right)
             (mv status next remaining fn-ibp-node))))))
(verify-guards fn-ibp-node-place
 :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))

; A bounded row write/seal action through the same exact destination registry.
(defun fn-ibp-node-row-write (ordinal held sealp slot depth id incarnation fuel fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
                 :guard (and (natp ordinal) (natp slot) (natp depth) (posp id)
                             (natp incarnation) (natp fuel))))
 (cond ((<= fuel depth) (mv :yield fuel fn-ibp-node))
       ((zp depth)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-row-page fn-ibp-node))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-row-page (fn-ibp-node-children-get 'fn-ibp-row-page fn-ibp-node (create-fn-ibp-row-page))))
            (status fn-ibp-row-page)
            (if (and (equal (fn-ibp-row-id fn-ibp-row-page) id)
                     (equal (fn-ibp-row-incarnation fn-ibp-row-page) incarnation)
                     (equal (fn-ibp-row-sealed fn-ibp-row-page) 0))
                (if sealp (fn-ibp-row-seal id incarnation fn-ibp-row-page)
                  (let ((fn-ibp-row-page (fn-ibp-row-set (mod ordinal 256) held fn-ibp-row-page)))
                    (mv :written fn-ibp-row-page)))
              (mv :recovery-required fn-ibp-row-page))
            (mv status (- fuel 1) fn-ibp-node))))
       ((equal (mod slot 2) 0)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-left (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node (create-fn-ibp-node-left))))
            (status remaining fn-ibp-node-left)
            (fn-ibp-node-row-write ordinal held sealp (floor slot 2) (- depth 1) id incarnation (- fuel 1) fn-ibp-node-left)
            (mv status remaining fn-ibp-node))))       (t
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-right (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node (create-fn-ibp-node-right))))
            (status remaining fn-ibp-node-right)
            (fn-ibp-node-row-write ordinal held sealp (floor slot 2) (- depth 1) id incarnation (- fuel 1) fn-ibp-node-right)
            (mv status remaining fn-ibp-node))))))
(verify-guards fn-ibp-node-row-write
 :hints (("Goal" :use ((:instance mod-bounded-by-modulus (x ordinal) (y 256)))
                  :in-theory (disable mod fn-ibp-row-pagep))))

; Persistent directory path update. Each action consumes one descent edge or
; rebuilds one fixed branch. Frames retain old siblings, so leased roots stay
; unchanged and no flat directory resize/copy is hidden here.
(defun fn-ibp-dir-put-begin (root index depth leaf)
 (declare (xargs :guard (and (natp index) (natp depth))))
 (list :descent root index depth leaf nil))
(defun fn-ibp-dir-put-step (cursor)
 (declare (xargs :guard t))
 (let ((phase (fn-omk-at 0 cursor)) (node (fn-omk-at 1 cursor))
       (index (fn-omk-at 2 cursor)) (depth (fn-omk-at 3 cursor))
       (leaf (fn-omk-at 4 cursor)) (frames (fn-omk-at 5 cursor)))
  (cond
   ((eq phase :descent)
    (cond ((not (and (natp index) (natp depth))) (list :recovery-required nil 0 0 nil nil))
          ((zp depth)
           (if (equal index 0) (list :rebuild leaf 0 0 leaf frames)
             (list :recovery-required nil 0 0 nil nil)))
          ((or (null node) (and (consp node) (eq (car node) :branch)))
           (let* ((zero (fn-omk-at 1 node)) (one (fn-omk-at 2 node))
                  (bit (mod index 2)))
             (list :descent (if (equal bit 0) zero one) (floor index 2) (- depth 1)
                   leaf (cons (list bit (if (equal bit 0) one zero)) frames))))
          (t (list :recovery-required nil 0 0 nil nil))))
   ((eq phase :rebuild)
    (if (consp frames)
        (let* ((frame (car frames)) (bit (fn-omk-at 0 frame)) (sibling (fn-omk-at 1 frame)))
          (list :rebuild (if (equal bit 0) (list :branch node sibling) (list :branch sibling node))
                0 0 leaf (cdr frames)))
      (list :done node 0 0 leaf nil)))
   (t cursor))))


; One scalar copy/seal action. The builder derives both source and destination
; descriptors from its retained roots; these arguments never cross D40.
(defun fn-ibp-node-word-action (operation word value slot depth id incarnation fuel fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
                 :guard (and (natp word) (< word 2048) (unsigned-byte-p 64 value)
                             (natp slot) (natp depth) (posp id) (natp incarnation) (natp fuel))))
 (cond ((<= fuel depth) (mv :yield nil fuel fn-ibp-node))
       ((zp depth)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-table-page fn-ibp-node))
            (mv :unavailable nil fuel fn-ibp-node)
          (stobj-let ((fn-ibp-table-page (fn-ibp-node-children-get 'fn-ibp-table-page fn-ibp-node (create-fn-ibp-table-page))))
            (status observed fn-ibp-table-page)
            (if (not (and (equal (fn-ibp-table-id fn-ibp-table-page) id)
                          (equal (fn-ibp-table-incarnation fn-ibp-table-page) incarnation)))
                (mv :recovery-required nil fn-ibp-table-page)
              (case operation
                (:read (if (equal (fn-ibp-table-sealed fn-ibp-table-page) 1)
                           (mv :word (fn-ibp-table-word word fn-ibp-table-page) fn-ibp-table-page)
                         (mv :recovery-required nil fn-ibp-table-page)))
                (:write (if (equal (fn-ibp-table-sealed fn-ibp-table-page) 0)
                            (let ((fn-ibp-table-page (fn-ibp-table-set word value fn-ibp-table-page)))
                              (mv :written value fn-ibp-table-page))
                          (mv :recovery-required nil fn-ibp-table-page)))
                (:seal (mv-let (status fn-ibp-table-page) (fn-ibp-table-seal id incarnation fn-ibp-table-page)
                         (mv status nil fn-ibp-table-page)))
                (otherwise (mv :recovery-required nil fn-ibp-table-page))))
            (mv status observed (- fuel 1) fn-ibp-node))))
       ((equal (mod slot 2) 0)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
            (mv :unavailable nil fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-left (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node (create-fn-ibp-node-left))))
            (status observed remaining fn-ibp-node-left)
            (fn-ibp-node-word-action operation word value (floor slot 2) (- depth 1) id incarnation (- fuel 1) fn-ibp-node-left)
            (mv status observed remaining fn-ibp-node))))       (t
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
            (mv :unavailable nil fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-right (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node (create-fn-ibp-node-right))))
            (status observed remaining fn-ibp-node-right)
            (fn-ibp-node-word-action operation word value (floor slot 2) (- depth 1) id incarnation (- fuel 1) fn-ibp-node-right)
            (mv status observed remaining fn-ibp-node))))))
(verify-guards fn-ibp-node-word-action)
