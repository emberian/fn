; P2 concrete provider representation. The recursive node table has only
; the two congruent child keys and fixed chunk/query/grant keys. This avoids
; resizing a global nested-child vector. No served API is exported yet.
(in-package "ACL2")
(logic)
(include-book "msgid-query-chunk")
(include-book "query-payload-grants")

(defstobj fn-ibp-node
  (fn-ibp-node-children :type (stobj-table 16))
  (fn-ibp-node-id :type (integer 0 *) :initially 0)
  :inline t)
(defstobj fn-ibp-node-left
  (fn-ibp-node-left-children :type (stobj-table 16))
  (fn-ibp-node-left-id :type (integer 0 *) :initially 0)
  :congruent-to fn-ibp-node :inline t)
(defstobj fn-ibp-node-right
  (fn-ibp-node-right-children :type (stobj-table 16))
  (fn-ibp-node-right-id :type (integer 0 *) :initially 0)
  :congruent-to fn-ibp-node :inline t)

; Representation prototype: one fixed child construction. Allocation
; authorization and fresh identity come from the provider builder, not host
; arguments. The builder/root publication and resource carry are next.
(defun fn-ibp-node-add-left (id fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :guard (posp id)))
  (if (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node)
      (mv :already-present fn-ibp-node)
    (stobj-let ((fn-ibp-node-left
                 (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                           (create-fn-ibp-node-left))))
      (fn-ibp-node-left)
      (update-fn-ibp-node-id id fn-ibp-node-left)
      (mv :installed fn-ibp-node))))

; Absent reads do not enter a default-creating stobj-let.
(defun fn-ibp-node-left-id-read (fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :guard t))
  (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
      (mv :unavailable nil)
    (stobj-let ((fn-ibp-node-left
                 (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                           (create-fn-ibp-node-left))))
      (id)
      (fn-ibp-node-id fn-ibp-node-left)
      (mv :present id))))

(defun fn-ibp-query-probingp (query)
  (declare (xargs :guard t))
  (and (equal (fn-miq-phase query) :probing)
       (null (fn-miq-pending query))
       (natp (fn-miq-tag query))
       (fn-mpr-cursorp (fn-miq-cursor query) (fn-miq-pages query))))

; One complete physical-slot traversal has DEPTH node steps. The registered
; profile supplies this depth; generation/ticket values do not address nodes.
; Insufficient fuel yields before the action, so no partial traversal is
; misrepresented as a persistent concrete child cursor.
(defun fn-ibp-node-query-next (query fuel slot depth id incarnation fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (fn-ibp-query-probingp query)
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*)
                              (natp slot) (natp depth) (posp id) (natp incarnation))
                  :verify-guards nil))
  (cond
   ((<= fuel depth) (mv :yield query nil fuel))
   ((zp depth)
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-table-page fn-ibp-node))
        (mv :unavailable query nil fuel)
      (stobj-let ((fn-ibp-table-page
                   (fn-ibp-node-children-get 'fn-ibp-table-page fn-ibp-node
                                             (create-fn-ibp-table-page))))
        (status next-query candidate fuel-left)
        (if (and (equal (fn-ibp-table-id fn-ibp-table-page) id)
                 (equal (fn-ibp-table-incarnation fn-ibp-table-page) incarnation)
                 (equal (fn-ibp-table-sealed fn-ibp-table-page) 1))
            (fn-miq-page-next query fuel (nth 0 (fn-miq-cursor query)) fn-ibp-table-page)
          (mv :recovery-required query nil fuel))
        (mv status next-query candidate fuel-left))))
   ((equal (mod slot 2) 0)
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable query nil fuel)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status next-query candidate fuel-left)
        (fn-ibp-node-query-next query (- fuel 1) (floor slot 2) (- depth 1)
                                id incarnation fn-ibp-node-left)
        (mv status next-query candidate fuel-left))))
   (t
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable query nil fuel)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status next-query candidate fuel-left)
        (fn-ibp-node-query-next query (- fuel 1) (floor slot 2) (- depth 1)
                                id incarnation fn-ibp-node-right)
        (mv status next-query candidate fuel-left))))))
(verify-guards fn-ibp-node-query-next
  :hints (("Goal" :in-theory (enable fn-ibp-query-probingp fn-mpr-cursorp))))

; One fixed registry segment. Profile concurrency installs as many funded
; segments as it needs;64 is a segment format, never the concurrency ceiling.
(defstobj fn-ibp-query-segment
  (fn-ibp-qs-controls :type (array t (64)) :initially nil)
  (fn-ibp-qs-captures :type (array t (64)) :initially nil)
  (fn-ibp-qs-admissions :type (array t (64)) :initially nil)
  (fn-ibp-qs-inputs :type (array t (64)) :initially nil)
  (fn-ibp-qs-tickets :type (array (integer 0 *) (64)) :initially 0)
  (fn-ibp-qs-borrows :type (array t (64)) :initially nil)
  (fn-ibp-qs-id :type (integer 0 *) :initially 0)
  (fn-ibp-qs-active :type (integer 0 64) :initially 0)
  :inline t)

(defun fn-ibp-query-token (nonce segment slot generation)
  (declare (xargs :guard (and (posp nonce) (posp segment)
                              (natp slot) (< slot 64) (posp generation))))
  (list :index-query nonce segment slot generation))
(defun fn-ibp-query-tokenp (token)
  (declare (xargs :guard t))
  (and (true-listp token) (equal (len token) 5)
       (equal (nth 0 token) :index-query)
       (posp (nth 1 token)) (posp (nth 2 token))
       (natp (nth 3 token)) (< (nth 3 token) 64) (posp (nth 4 token))))

(defun fn-ibp-query-slot-livep (token fn-ibp-query-segment)
  (declare (xargs :stobjs fn-ibp-query-segment :guard t))
  (and (fn-ibp-query-tokenp token)
       (equal (nth 2 token) (fn-ibp-qs-id fn-ibp-query-segment))
       (equal (nth 1 token) (fn-ibp-qs-ticketsi (nth 3 token) fn-ibp-query-segment))
       (equal (nth 4 token)
              (fn-miq-generation (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment)))))

; Registration is internal to funded capture. The immutable CAPTURE contains
; both roots plus C/F/key, and the query was produced from exactly that O.
(defun fn-ibp-query-slot-register (token query capture fn-ibp-query-segment)
  (declare (xargs :stobjs fn-ibp-query-segment :guard (fn-ibp-query-tokenp token)))
  (let ((slot (nth 3 token)))
    (if (or (not (equal (nth 2 token) (fn-ibp-qs-id fn-ibp-query-segment)))
            (not (equal (fn-ibp-qs-ticketsi slot fn-ibp-query-segment) 0))
            (not (< (fn-ibp-qs-active fn-ibp-query-segment) 64))
            (not (equal (fn-miq-ticket query) (nth 1 token)))
            (not (equal (fn-miq-generation query) (nth 4 token))))
        (mv :unavailable fn-ibp-query-segment)
      (let* ((fn-ibp-query-segment (update-fn-ibp-qs-controlsi slot query fn-ibp-query-segment))
             (fn-ibp-query-segment (update-fn-ibp-qs-capturesi slot capture fn-ibp-query-segment))
             (fn-ibp-query-segment (update-fn-ibp-qs-ticketsi slot (nth 1 token) fn-ibp-query-segment))
             (fn-ibp-query-segment (update-fn-ibp-qs-active (+ 1 (fn-ibp-qs-active fn-ibp-query-segment)) fn-ibp-query-segment)))
        (mv :captured fn-ibp-query-segment)))))

(defstobj fn-index-backing
  (fn-ibp-registry :type fn-ibp-node)
  (fn-ibp-current :type t :initially nil)
  (fn-ibp-next-ticket :type (integer 1 *) :initially 1)
  (fn-ibp-pool-capacity :type (integer 0 *) :initially 0)
  (fn-ibp-slot-depth :type (integer 0 *) :initially 0)
  (fn-ibp-payload-active :type (integer 0 *) :initially 0)
  (fn-ibp-builder :type t :initially nil)
  :inline t)
(defstobj fn-mio$c
  (fn-mio$c-provider :type fn-index-backing)
  :inline t)
(defun fn-ibp-payload-owned-p (fn-index-backing)
  (declare (xargs :stobjs fn-index-backing :guard t))
  (< 0 (fn-ibp-payload-active fn-index-backing)))

; Published directory nodes are immutable fixed tuples. A capture retains
; the root object itself. A query may retain an interior node cursor: these
; are immutable metadata, not aliased mutable nested stobjs.
; (:branch left right) and (:chunk physical-slot id incarnation).
(defun fn-ibp-directory-start (root index depth)
  (declare (xargs :guard (and (natp index) (natp depth))))
  (list root index depth))

(defun fn-ibp-directory-step (cursor fuel)
  (declare (xargs :measure (nfix fuel)
                  :guard (and (true-listp cursor) (equal (len cursor) 3)
                              (natp (nth 1 cursor)) (natp (nth 2 cursor))
                              (natp fuel))
                  :verify-guards nil))
  (let ((node (nth 0 cursor)) (index (nth 1 cursor)) (depth (nth 2 cursor)))
    (cond
     ((zp fuel) (mv :yield cursor nil 0))
     ((atom node) (mv :unavailable cursor nil (- fuel 1)))
     ((zp depth)
      (if (and (true-listp node) (equal (len node) 4)
               (eq (car node) :chunk) (natp (nth 1 node))
               (posp (nth 2 node)) (natp (nth 3 node)) (equal index 0))
          (mv :borrow-ready cursor node (- fuel 1))
        (mv :recovery-required cursor nil (- fuel 1))))
     ((and (true-listp node) (equal (len node) 3) (eq (car node) :branch))
      (fn-ibp-directory-step
       (list (if (equal (mod index 2) 0) (nth 1 node) (nth 2 node))
             (floor index 2) (- depth 1))
       (- fuel 1)))
     (t (mv :recovery-required cursor nil (- fuel 1))))))
(verify-guards fn-ibp-directory-step)

(fn-defrecord fn-ibp-capture
  :tag :fn-ibp-capture
  :constructor (fn-ibp-capture-make generation key pages count frontier
                                  table-root table-depth table-root-id row-root row-depth row-root-id)
  :fields ((fn-ibp-capture-generation t) (fn-ibp-capture-key t)
           (fn-ibp-capture-pages t) (fn-ibp-capture-count t)
           (fn-ibp-capture-frontier t) (fn-ibp-capture-table-root t)
           (fn-ibp-capture-table-depth t) (fn-ibp-capture-table-root-id t)
           (fn-ibp-capture-row-root t)
           (fn-ibp-capture-row-depth t) (fn-ibp-capture-row-root-id t))
  :recognizer nil)

(defun fn-ibp-query-capture-matchesp (query capture)
  (declare (xargs :guard t))
  (and (equal (fn-miq-generation query) (fn-ibp-capture-generation capture))
       (equal (fn-miq-key query) (fn-ibp-capture-key capture))
       (equal (fn-miq-pages query) (fn-ibp-capture-pages capture))
       (equal (fn-miq-count query) (fn-ibp-capture-count capture))
       (equal (fn-miq-frontier query) (fn-ibp-capture-frontier capture))
       (natp (fn-ibp-capture-table-depth capture))
       (natp (fn-ibp-capture-row-depth capture))))


(defun fn-ibp-directory-cursorp (cursor)
  (declare (xargs :guard t))
  (and (true-listp cursor) (equal (len cursor) 3)
       (natp (nth 1 cursor)) (natp (nth 2 cursor))))
(defun fn-ibp-query-slot-borrow-step (token fuel fn-ibp-query-segment)
  (declare (xargs :stobjs fn-ibp-query-segment
                  :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*))))
  (if (not (fn-ibp-query-slot-livep token fn-ibp-query-segment))
      (mv :stale nil fuel fn-ibp-query-segment)
    (let* ((slot (nth 3 token))
           (borrow (fn-ibp-qs-borrowsi slot fn-ibp-query-segment)))
      (if (not (true-listp borrow))
          (mv :recovery-required nil fuel fn-ibp-query-segment)
       (cond
       ((or (not (member-eq (nth 0 borrow) '(:table :rows)))
            (not (fn-ibp-directory-cursorp (nth 1 borrow))))
        (mv :recovery-required nil fuel fn-ibp-query-segment))
       ((nth 2 borrow)
        (mv :borrow-ready (nth 2 borrow) fuel fn-ibp-query-segment))
       (t
        (mv-let (status cursor descriptor fuel-left)
          (fn-ibp-directory-step (nth 1 borrow) fuel)
          (let ((fn-ibp-query-segment
                 (update-fn-ibp-qs-borrowsi slot (list (nth 0 borrow) cursor descriptor (nth 3 borrow))
                                            fn-ibp-query-segment)))
            (mv status descriptor fuel-left fn-ibp-query-segment)))))))))

; One constructor effect, invoked only after shared-ledger admission by the
; builder. It allocates one fixed chunk, never a growing vector of chunks.
(defun fn-ibp-node-table-create (id incarnation fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :guard (and (posp id) (natp incarnation))))
  (if (fn-ibp-node-children-boundp 'fn-ibp-table-page fn-ibp-node)
      (mv :already-present fn-ibp-node)
    (stobj-let ((fn-ibp-table-page
                 (fn-ibp-node-children-get 'fn-ibp-table-page fn-ibp-node
                                           (create-fn-ibp-table-page))))
      (status fn-ibp-table-page)
      (fn-ibp-table-initialize id incarnation fn-ibp-table-page)
      (mv status fn-ibp-node))))

(defun fn-ibp-node-query-confirm (query fuel slot depth id incarnation fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (natp (fn-miq-pending query))
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*)
                              (natp slot) (natp depth) (posp id) (natp incarnation))
                  :verify-guards nil))
  (cond
   ((<= fuel depth) (mv :yield query fuel))
   ((zp depth)
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-row-page fn-ibp-node))
        (mv :unavailable query fuel)
      (stobj-let ((fn-ibp-row-page
                   (fn-ibp-node-children-get 'fn-ibp-row-page fn-ibp-node
                                             (create-fn-ibp-row-page))))
        (status next-query)
        (if (and (equal (fn-ibp-row-id fn-ibp-row-page) id)
                 (equal (fn-ibp-row-incarnation fn-ibp-row-page) incarnation)
                 (equal (fn-ibp-row-sealed fn-ibp-row-page) 1))
            (fn-miq-row-confirm query (fn-miq-pending query) fn-ibp-row-page)
          (mv :recovery-required query))
        (mv status next-query (- fuel 1)))))
   ((equal (mod slot 2) 0)
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable query fuel)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status next-query fuel-left)
        (fn-ibp-node-query-confirm query (- fuel 1) (floor slot 2) (- depth 1)
                                   id incarnation fn-ibp-node-left)
        (mv status next-query fuel-left))))
   (t
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable query fuel)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status next-query fuel-left)
        (fn-ibp-node-query-confirm query (- fuel 1) (floor slot 2) (- depth 1)
                                   id incarnation fn-ibp-node-right)
        (mv status next-query fuel-left))))))
(verify-guards fn-ibp-node-query-confirm)

; Internal registered-state read. Host tokens never supply query or roots.
(defun fn-ibp-node-query-read (token fuel slot depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (fn-ibp-query-tokenp token) (natp fuel)
                              (natp slot) (natp depth)) :verify-guards nil))
  (cond ((<= fuel depth) (mv :yield nil nil nil fuel))
        ((zp depth) (if (not (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node))
        (mv :unavailable nil nil nil fuel)
      (stobj-let ((fn-ibp-query-segment
                   (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                             (create-fn-ibp-query-segment))))
        (status query capture borrow)
        (if (fn-ibp-query-slot-livep token fn-ibp-query-segment)
            (let ((local-slot (nth 3 token)))
              (mv :live (fn-ibp-qs-controlsi local-slot fn-ibp-query-segment)
                  (fn-ibp-qs-capturesi local-slot fn-ibp-query-segment)
                  (fn-ibp-qs-borrowsi local-slot fn-ibp-query-segment)))
          (mv :stale nil nil nil))
        (mv status query capture borrow (- fuel 1)))))
        ((equal (mod slot 2) 0) (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable nil nil nil fuel)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status query capture borrow fuel-left)
        (fn-ibp-node-query-read token (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
        (mv status query capture borrow fuel-left))))
        (t (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable nil nil nil fuel)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status query capture borrow fuel-left)
        (fn-ibp-node-query-read token (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
        (mv status query capture borrow fuel-left))))))
(verify-guards fn-ibp-node-query-read)

(defun fn-ibp-query-slot-update (token next-query borrow fn-ibp-query-segment)
  (declare (xargs :stobjs fn-ibp-query-segment :guard t))
  (if (not (fn-ibp-query-slot-livep token fn-ibp-query-segment))
      (mv :stale fn-ibp-query-segment)
    (let* ((slot (nth 3 token))
           (old (fn-ibp-qs-controlsi slot fn-ibp-query-segment))
           (capture (fn-ibp-qs-capturesi slot fn-ibp-query-segment)))
      (if (not (and (fn-ibp-query-capture-matchesp next-query capture)
                    (equal (fn-miq-ticket next-query) (fn-miq-ticket old))
                    (equal (fn-miq-msgid next-query) (fn-miq-msgid old))
                    (equal (fn-miq-tag next-query) (fn-miq-tag old))))
          (mv :recovery-required fn-ibp-query-segment)
        (let* ((fn-ibp-query-segment
                (update-fn-ibp-qs-controlsi slot next-query fn-ibp-query-segment))
               (fn-ibp-query-segment
                (update-fn-ibp-qs-borrowsi slot borrow fn-ibp-query-segment)))
          (mv :updated fn-ibp-query-segment))))))

(defun fn-ibp-node-query-update (token query borrow fuel slot depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (natp fuel) (natp slot) (natp depth)) :verify-guards nil))
  (cond ((<= fuel depth) (mv :yield fuel fn-ibp-node))
        ((zp depth) (if (not (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node))
        (mv :unavailable fuel fn-ibp-node)
      (stobj-let ((fn-ibp-query-segment
                   (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                             (create-fn-ibp-query-segment))))
        (status fn-ibp-query-segment)
        (fn-ibp-query-slot-update token query borrow fn-ibp-query-segment)
        (mv status (- fuel 1) fn-ibp-node))))
        ((equal (mod slot 2) 0) (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable fuel fn-ibp-node)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status fuel-left fn-ibp-node-left)
        (fn-ibp-node-query-update token query borrow (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
        (mv status fuel-left fn-ibp-node))))
        (t (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable fuel fn-ibp-node)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status fuel-left fn-ibp-node-right)
        (fn-ibp-node-query-update token query borrow (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
        (mv status fuel-left fn-ibp-node))))))
(verify-guards fn-ibp-node-query-update)

(defun fn-ibp-chunk-descriptorp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4) (eq (nth 0 x) :chunk)
       (natp (nth 1 x)) (posp (nth 2 x)) (natp (nth 3 x))))
(defun fn-ibp-query-borrow-plan (query capture borrow)
  (declare (xargs :guard t))
  (cond
   ((not (fn-ibp-query-capture-matchesp query capture)) (mv :recovery-required nil))
   ((eq (fn-miq-phase query) :done) (mv :done nil))
   (t
    (let* ((probing (fn-ibp-query-probingp query))
           (candidate (and (eq (fn-miq-phase query) :candidate)
                           (natp (fn-miq-pending query)) (natp (fn-miq-count query))
                           (< (fn-miq-pending query) (fn-miq-count query))))
           (kind (if probing :table :rows))
           (index (if probing (nth 0 (fn-miq-cursor query))
                    (floor (nfix (fn-miq-pending query)) 256))))
      (cond
       ((not (or probing candidate)) (mv :recovery-required nil))
       ((not borrow)
        (mv :borrowing
            (list kind
                  (fn-ibp-directory-start
                   (if probing (fn-ibp-capture-table-root capture) (fn-ibp-capture-row-root capture))
                   index
                   (if probing (fn-ibp-capture-table-depth capture) (fn-ibp-capture-row-depth capture)))
                  nil index)))
       ((and (true-listp borrow) (equal (len borrow) 4)
             (eq (nth 0 borrow) kind) (equal (nth 3 borrow) index)
             (fn-ibp-directory-cursorp (nth 1 borrow))
             (or (null (nth 2 borrow)) (fn-ibp-chunk-descriptorp (nth 2 borrow))))
        (mv :borrowing borrow))
       (t (mv :recovery-required nil)))))))

(defun fn-ibp-query-slot-borrow-start (token kind fn-ibp-query-segment)
  (declare (xargs :stobjs fn-ibp-query-segment :guard t))
  (if (not (fn-ibp-query-slot-livep token fn-ibp-query-segment))
      (mv :stale fn-ibp-query-segment)
    (let* ((slot (nth 3 token))
           (query (fn-ibp-qs-controlsi slot fn-ibp-query-segment))
           (capture (fn-ibp-qs-capturesi slot fn-ibp-query-segment)))
      (mv-let (status borrow)
        (fn-ibp-query-borrow-plan query capture (fn-ibp-qs-borrowsi slot fn-ibp-query-segment))
        (if (and (eq status :borrowing) (true-listp borrow) (eq kind (nth 0 borrow)))
            (let ((fn-ibp-query-segment (update-fn-ibp-qs-borrowsi slot borrow fn-ibp-query-segment)))
              (mv :borrowing fn-ibp-query-segment))
          (mv :recovery-required fn-ibp-query-segment))))))

(defthm fn-ibp-directory-step-fuel-bound
  (implies (natp fuel)
           (and (natp (mv-nth 3 (fn-ibp-directory-step cursor fuel)))
                (<= (mv-nth 3 (fn-ibp-directory-step cursor fuel)) fuel)))
  :hints (("Goal" :induct (fn-ibp-directory-step cursor fuel)
                  :in-theory (enable fn-ibp-directory-step))))
(defthm fn-ibp-directory-step-fuel-upper-bound
  (implies (natp fuel)
           (<= (mv-nth 3 (fn-ibp-directory-step cursor fuel)) fuel))
  :rule-classes :linear
  :hints (("Goal" :use fn-ibp-directory-step-fuel-bound
                  :in-theory (disable fn-ibp-directory-step))))


; Internal action on registered immutable observations. Only the outer
; ticket controller may obtain QUERY/CAPTURE/BORROW and invoke this function.
(defun fn-ibp-query-action (query capture borrow fuel capacity depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node
                  :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*)
                              (natp capacity) (natp depth))
                  :verify-guards nil))
  (mv-let (plan next-borrow)
    (fn-ibp-query-borrow-plan query capture borrow)
    (cond
     ((eq plan :done) (mv :done query nil (fn-miq-answer query) fuel))
     ((not (eq plan :borrowing)) (mv :recovery-required query borrow nil fuel))
     ((not (and (true-listp next-borrow)
                (fn-ibp-directory-cursorp (nth 1 next-borrow))))
      (mv :recovery-required query borrow nil fuel))
     (t
      (mv-let (dir-status dir-cursor descriptor after-directory)
        (if (nth 2 next-borrow)
            (mv :borrow-ready (nth 1 next-borrow) (nth 2 next-borrow) fuel)
          (fn-ibp-directory-step (nth 1 next-borrow) fuel))
        (let ((retained-borrow (list (nth 0 next-borrow) dir-cursor descriptor (nth 3 next-borrow))))
          (cond
           ((not (eq dir-status :borrow-ready))
            (mv dir-status query retained-borrow nil after-directory))
           ((not (and (fn-ibp-chunk-descriptorp descriptor)
                      (< (nth 1 descriptor) capacity)))
            (mv :recovery-required query retained-borrow nil after-directory))
           ((<= after-directory depth)
            (mv :yield query retained-borrow nil after-directory))
           ((and (eq (nth 0 next-borrow) :table) (fn-ibp-query-probingp query))
            (mv-let (status next-query candidate fuel-left)
              (fn-ibp-node-query-next query after-directory (nth 1 descriptor) depth
                                     (nth 2 descriptor) (nth 3 descriptor) fn-ibp-node)
              (mv status next-query
                  (if (and (eq status :yield)
                           (true-listp (fn-miq-cursor next-query))
                           (equal (nth 0 (fn-miq-cursor next-query)) (nth 3 next-borrow)))
                      retained-borrow nil)
                  candidate fuel-left)))
           ((and (eq (nth 0 next-borrow) :rows) (natp (fn-miq-pending query)))
            (mv-let (status next-query fuel-left)
              (fn-ibp-node-query-confirm query after-directory (nth 1 descriptor) depth
                                        (nth 2 descriptor) (nth 3 descriptor) fn-ibp-node)
              (mv status next-query (if (eq status :yield) retained-borrow nil) nil fuel-left)))
           (t (mv :recovery-required query retained-borrow nil after-directory)))))))))
(verify-guards fn-ibp-query-action
  :hints (("Goal" :in-theory (e/d (fn-ibp-chunk-descriptorp fn-ibp-directory-cursorp)
                                   (fn-ibp-query-borrow-plan)))))

; Actual controller subject: callers supply only an opaque issued token and
; quantum. Registered query/capture/borrow observations stay inside core.
; Funding/input-holder and generation publication carry must be established
; by capture before this subject becomes an authorized D40 export.
(defun fn-ibp-next (token fuel fn-index-backing)
  (declare (xargs :stobjs fn-index-backing
                  :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (let* ((depth (fn-ibp-slot-depth fn-index-backing))
         (capacity (fn-ibp-pool-capacity fn-index-backing))
         (write-cost (+ 1 depth)))
    (cond
     ((not (fn-ibp-query-tokenp token)) (mv :stale nil fuel fn-index-backing))
     ((>= (- (nth 2 token) 1) capacity) (mv :stale nil fuel fn-index-backing))
     ((< fuel (+ (* 3 write-cost) 1)) (mv :yield nil fuel fn-index-backing))
     (t
      (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
        (status candidate fuel-left fn-ibp-node)
        (mv-let (read-status query capture borrow after-read)
          (fn-ibp-node-query-read token fuel (- (nth 2 token) 1) depth fn-ibp-node)
          (cond
           ((not (eq read-status :live)) (mv read-status nil after-read fn-ibp-node))
           ((not (and (natp after-read) (<= after-read fuel) (<= write-cost after-read)))
            (mv :recovery-required nil fuel fn-ibp-node))
           (t
            (let ((work-fuel (- after-read write-cost)))
              (mv-let (action-status next-query next-borrow answer after-action)
                (fn-ibp-query-action query capture borrow work-fuel capacity depth fn-ibp-node)
                (if (not (and (natp after-action) (<= after-action work-fuel)))
                    (mv :recovery-required nil after-read fn-ibp-node)
                  (mv-let (update-status after-update fn-ibp-node)
                    (fn-ibp-node-query-update token next-query next-borrow
                                              (+ after-action write-cost)
                                              (- (nth 2 token) 1) depth fn-ibp-node)
                    (if (eq update-status :updated)
                        (mv action-status answer after-update fn-ibp-node)
                      (mv :recovery-required nil after-update fn-ibp-node)))))))))
        (mv status candidate fuel-left fn-index-backing))))))
(verify-guards fn-ibp-next)

(defun fn-miq-next (token fuel fn-mio$c)
  (declare (xargs :stobjs fn-mio$c
                  :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*))))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (status candidate fuel-left fn-index-backing)
    (fn-ibp-next token fuel fn-index-backing)
    (mv status candidate fuel-left fn-mio$c)))

; Terminal read selects only the registered completed minimum from captured rows.
(defun fn-ibp-node-row-read (ordinal fuel slot depth id incarnation fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (natp ordinal)
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*)
                              (natp slot) (natp depth) (posp id) (natp incarnation))
                  :verify-guards nil))
  (cond
   ((<= fuel depth) (mv :yield nil fuel))
   ((zp depth)
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-row-page fn-ibp-node))
        (mv :unavailable nil fuel)
      (stobj-let ((fn-ibp-row-page
                   (fn-ibp-node-children-get 'fn-ibp-row-page fn-ibp-node
                                             (create-fn-ibp-row-page))))
        (status held)
        (if (and (equal (fn-ibp-row-id fn-ibp-row-page) id)
                 (equal (fn-ibp-row-incarnation fn-ibp-row-page) incarnation)
                 (equal (fn-ibp-row-sealed fn-ibp-row-page) 1))
            (mv :row (fn-ibp-row (mod ordinal 256) fn-ibp-row-page))
          (mv :recovery-required nil))
        (mv status held (- fuel 1)))))
   ((equal (mod slot 2) 0)
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable nil fuel)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status held fuel-left)
        (fn-ibp-node-row-read ordinal (- fuel 1) (floor slot 2) (- depth 1)
                                   id incarnation fn-ibp-node-left)
        (mv status held fuel-left))))
   (t
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable nil fuel)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status held fuel-left)
        (fn-ibp-node-row-read ordinal (- fuel 1) (floor slot 2) (- depth 1)
                                   id incarnation fn-ibp-node-right)
        (mv status held fuel-left))))))
(verify-guards fn-ibp-node-row-read
  :hints (("Goal" :use ((:instance mod-bounded-by-modulus (x ordinal) (y 256)))
                  :in-theory (disable mod fn-ibp-row-pagep))))


(defun fn-ibp-node-selected-row (query ordinal fuel slot depth id incarnation fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node
                  :guard (and (natp ordinal) (natp fuel) (<= fuel *fn-mpr-slot-quantum*)
                              (natp slot) (natp depth) (posp id) (natp incarnation))))
  (mv-let (status held fuel-left)
    (fn-ibp-node-row-read ordinal fuel slot depth id incarnation fn-ibp-node)
    (if (not (eq status :row)) (mv status nil fuel-left)
      (if (and (natp (fn-miq-count query)) (< ordinal (fn-miq-count query))
               (natp (fn-miq-frontier query)) (natp (fn-record-sequence held))
               (< (fn-record-sequence held) (fn-miq-frontier query))
               (equal (fn-record-msgid held) (fn-miq-msgid query)))
          (mv :selected held fuel-left)
        (mv :recovery-required nil fuel-left)))))

(defun fn-miq-selected-token (token ordinal root-id)
  (declare (xargs :guard t))
  (list :index-selected token ordinal root-id))

(defun fn-ibp-selection-action (token query capture borrow fuel capacity depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :verify-guards nil
                  :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*)
                              (natp capacity) (natp depth))))
  (cond
   ((not (fn-ibp-query-capture-matchesp query capture))
    (mv :recovery-required borrow nil fuel))
   ((not (eq (fn-miq-phase query) :done)) (mv :yield borrow nil fuel))
   ((not (fn-miq-best query)) (mv :absent nil nil fuel))
   ((not (and (natp (fn-miq-best query)) (natp (fn-miq-count query))
              (< (fn-miq-best query) (fn-miq-count query))))
    (mv :recovery-required borrow nil fuel))
   (t
    (let* ((ordinal (fn-miq-best query))
           (selected-token (fn-miq-selected-token token ordinal (fn-ibp-capture-row-root-id capture))))
      (if (and (true-listp borrow) (equal (len borrow) 4) (eq (car borrow) :selected)
               (equal (nth 1 borrow) selected-token))
          (mv :selected borrow selected-token fuel)
        (let ((cursor (if (and (true-listp borrow) (equal (len borrow) 4)
                              (eq (car borrow) :select) (equal (nth 3 borrow) ordinal))
                          (nth 1 borrow)
                        (fn-ibp-directory-start (fn-ibp-capture-row-root capture)
                                                (floor ordinal 256)
                                                (fn-ibp-capture-row-depth capture)))))
          (if (not (fn-ibp-directory-cursorp cursor))
              (mv :recovery-required borrow nil fuel)
            (mv-let (status next-cursor descriptor after-directory)
              (fn-ibp-directory-step cursor fuel)
              (let ((next-borrow (list :select next-cursor descriptor ordinal)))
                (cond
                 ((not (eq status :borrow-ready)) (mv status next-borrow nil after-directory))
                 ((not (and (fn-ibp-chunk-descriptorp descriptor)
                            (< (nth 1 descriptor) capacity)))
                  (mv :recovery-required next-borrow nil after-directory))
                 ((<= after-directory depth) (mv :yield next-borrow nil after-directory))
                 (t
                  (mv-let (row-status held fuel-left)
                    (fn-ibp-node-selected-row query ordinal after-directory
                                             (nth 1 descriptor) depth
                                             (nth 2 descriptor) (nth 3 descriptor) fn-ibp-node)
                    (if (eq row-status :selected)
                        (mv :selected (list :selected selected-token held descriptor)
                            selected-token fuel-left)
                      (mv row-status next-borrow nil fuel-left))))))))))))))
(verify-guards fn-ibp-selection-action)

(defun fn-ibp-select (token fuel fn-index-backing)
  (declare (xargs :stobjs fn-index-backing
                  :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (let* ((depth (fn-ibp-slot-depth fn-index-backing))
         (capacity (fn-ibp-pool-capacity fn-index-backing))
         (write-cost (+ 1 depth)))
    (cond
     ((not (fn-ibp-query-tokenp token)) (mv :stale nil fuel fn-index-backing))
     ((>= (- (nth 2 token) 1) capacity) (mv :stale nil fuel fn-index-backing))
     ((< fuel (+ (* 3 write-cost) 1)) (mv :yield nil fuel fn-index-backing))
     (t
      (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
        (status candidate fuel-left fn-ibp-node)
        (mv-let (read-status query capture borrow after-read)
          (fn-ibp-node-query-read token fuel (- (nth 2 token) 1) depth fn-ibp-node)
          (cond
           ((not (eq read-status :live)) (mv read-status nil after-read fn-ibp-node))
           ((not (and (natp after-read) (<= after-read fuel) (<= write-cost after-read)))
            (mv :recovery-required nil fuel fn-ibp-node))
           (t
            (let ((work-fuel (- after-read write-cost)))
              (mv-let (action-status next-borrow answer after-action)
                (fn-ibp-selection-action token query capture borrow work-fuel capacity depth fn-ibp-node)
                (if (not (and (natp after-action) (<= after-action work-fuel)))
                    (mv :recovery-required nil after-read fn-ibp-node)
                  (mv-let (update-status after-update fn-ibp-node)
                    (fn-ibp-node-query-update token query next-borrow
                                              (+ after-action write-cost)
                                              (- (nth 2 token) 1) depth fn-ibp-node)
                    (if (eq update-status :updated)
                        (mv action-status answer after-update fn-ibp-node)
                      (mv :recovery-required nil after-update fn-ibp-node)))))))))
        (mv status candidate fuel-left fn-index-backing))))))
(verify-guards fn-ibp-select)


(defun fn-miq-select (token fuel fn-mio$c)
  (declare (xargs :stobjs fn-mio$c
                  :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*))))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (status candidate fuel-left fn-index-backing)
    (fn-ibp-select token fuel fn-index-backing)
    (mv status candidate fuel-left fn-mio$c)))


(defun fn-miq-selected-tokenp (selected)
  (declare (xargs :guard t))
  (and (true-listp selected) (equal (len selected) 4)
       (eq (car selected) :index-selected)
       (fn-ibp-query-tokenp (nth 1 selected)) (natp (nth 2 selected))
       (posp (nth 3 selected))))

; Internal readonly projection; active payload-grant validation is a separate
; required join before a sanctioned host readout can expose this observation.
(defun fn-ibp-selected-observation (selected query capture borrow)
  (declare (xargs :guard t))
  (if (and (fn-miq-selected-tokenp selected)
           (fn-ibp-query-capture-matchesp query capture)
           (eq (fn-miq-phase query) :done)
           (equal (fn-miq-best query) (nth 2 selected))
           (equal (fn-miq-ticket query) (nth 1 (nth 1 selected)))
           (equal (fn-miq-generation query) (nth 4 (nth 1 selected)))
           (equal (fn-ibp-capture-row-root-id capture) (nth 3 selected))
           (true-listp borrow) (equal (len borrow) 4)
           (eq (car borrow) :selected) (equal (nth 1 borrow) selected))
      (mv :selected (nth 2 borrow))
    (mv :recovery-required nil)))

(defun fn-ibp-selected-read (selected fuel fn-index-backing)
  (declare (xargs :stobjs fn-index-backing
                  :guard (natp fuel)))
  (let* ((depth (fn-ibp-slot-depth fn-index-backing))
         (capacity (fn-ibp-pool-capacity fn-index-backing)))
    (cond
     ((not (fn-miq-selected-tokenp selected)) (mv :stale nil fuel))
     ((>= (- (nth 2 (nth 1 selected)) 1) capacity) (mv :stale nil fuel))
     ((<= fuel depth) (mv :yield nil fuel))
     (t
      (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
        (status held fuel-left)
        (mv-let (read-status query capture borrow after-read)
          (fn-ibp-node-query-read (nth 1 selected) fuel
                                  (- (nth 2 (nth 1 selected)) 1) depth fn-ibp-node)
          (if (not (eq read-status :live))
              (mv read-status nil after-read)
            (mv-let (selected-status held)
              (fn-ibp-selected-observation selected query capture borrow)
              (mv selected-status held after-read))))
        (mv status held fuel-left))))))

; This internal projection is read-only in the concrete provider. The final
; selected-read export also validates its exact active query payload grant.
(defun fn-miq-selected-core-read (selected fuel fn-mio$c)
  (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (status held fuel-left)
    (fn-ibp-selected-read selected fuel fn-index-backing)
    (mv status held fuel-left)))

(defun fn-ibp-node-query-authorization (token fuel slot depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (fn-ibp-query-tokenp token) (natp fuel)
                              (natp slot) (natp depth)) :verify-guards nil))
  (cond ((<= fuel depth) (mv :yield nil nil fuel))
        ((zp depth) (if (not (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node))
        (mv :unavailable nil nil fuel)
      (stobj-let ((fn-ibp-query-segment
                   (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                             (create-fn-ibp-query-segment))))
        (status payload-token grant)
        (if (not (fn-ibp-query-slot-livep token fn-ibp-query-segment))
            (mv :stale nil nil)
          (let* ((slot (nth 3 token))
                 (capture (fn-ibp-qs-capturesi slot fn-ibp-query-segment))
                 (context (fn-ibp-qs-inputsi slot fn-ibp-query-segment))
                 (payload-token (fn-omk-at 5 context))
                 (row (fn-ibp-qs-admissionsi slot fn-ibp-query-segment))
                 (grant (list :query-grant (nth 1 token) (nth 2 token) slot (nth 4 token)
                              (fn-ibp-capture-table-root-id capture)
                              (fn-ibp-capture-row-root-id capture)
                              (fn-ibp-capture-count capture) (fn-ibp-capture-frontier capture)
                              (nth 4 token) (fn-omk-at 4 payload-token) (fn-omk-at 5 payload-token))))
            (if (and (fn-qpg-tokenp payload-token)
                     (equal (fn-omk-at 1 payload-token) (nth 1 token))
                     (equal (fn-omk-at 2 payload-token) slot)
                     (equal (fn-omk-at 3 payload-token) (nth 4 token))
                     (equal (fn-omk-at 6 payload-token) (nth 2 token))
                     (equal (fn-omk-at 0 row) grant)
                     (eq (fn-omk-at 2 row) :active))
                (mv :authorized payload-token grant)
              (mv :recovery-required nil nil))))
        (mv status payload-token grant (- fuel 1)))))
        ((equal (mod slot 2) 0) (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable nil nil fuel)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status payload-token grant fuel-left)
        (fn-ibp-node-query-authorization token (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
        (mv status payload-token grant fuel-left))))
        (t (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable nil nil fuel)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status payload-token grant fuel-left)
        (fn-ibp-node-query-authorization token (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
        (mv status payload-token grant fuel-left))))))
(verify-guards fn-ibp-node-query-authorization)


(defun fn-ibp-node-payload-live (token grant fuel slot depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (fn-qpg-tokenp token) (natp fuel)
                              (natp slot) (natp depth)) :verify-guards nil))
  (cond ((<= fuel depth) (mv :yield nil nil fuel))
        ((zp depth) (if (not (fn-ibp-node-children-boundp 'fn-query-payload-grants fn-ibp-node))
        (mv :unavailable nil nil fuel)
      (stobj-let ((fn-query-payload-grants
                   (fn-ibp-node-children-get 'fn-query-payload-grants fn-ibp-node
                                             (create-fn-query-payload-grants))))
        (live)
        (and (fn-qpg-livep token fn-query-payload-grants)
             (< (fn-qpg-slot token) 64)
             (let ((row (fn-qpg-rowsi (fn-qpg-slot token) fn-query-payload-grants)))
               (and (eq (fn-omk-at 2 row) :active)
                    (equal (fn-omk-at 1 row) grant))))
        (mv (if live :authorized :recovery-required) nil nil (- fuel 1)))))
        ((equal (mod slot 2) 0) (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable nil nil fuel)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status payload-token grant fuel-left)
        (fn-ibp-node-payload-live token grant (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
        (mv status payload-token grant fuel-left))))
        (t (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable nil nil fuel)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status payload-token grant fuel-left)
        (fn-ibp-node-payload-live token grant (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
        (mv status payload-token grant fuel-left))))))
(verify-guards fn-ibp-node-payload-live)


(defun fn-miq-selected-read (selected fuel fn-mio$c)
  (declare (xargs :stobjs fn-mio$c :verify-guards nil
                  :guard (natp fuel)))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (status held payload-token fuel-left)
    (mv-let (read-status held after-read)
      (fn-ibp-selected-read selected fuel fn-index-backing)
      (if (not (and (eq read-status :selected) (fn-miq-selected-tokenp selected)
                    (natp after-read) (<= after-read fuel)))
          (mv read-status nil nil after-read)
        (let* ((token (nth 1 selected)) (depth (fn-ibp-slot-depth fn-index-backing)))
          (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
            (status held payload-token fuel-left)
            (mv-let (auth-status payload-token grant after-auth)
              (fn-ibp-node-query-authorization token after-read
                                               (- (nth 2 token) 1) depth fn-ibp-node)
              (if (not (and (eq auth-status :authorized) (fn-qpg-tokenp payload-token)
                            (natp after-auth) (<= after-auth after-read)))
                  (mv auth-status nil nil after-auth)
                (mv-let (live-status ignored1 ignored2 after-live)
                  (fn-ibp-node-payload-live payload-token grant after-auth
                                           (- (nth 2 token) 1) depth fn-ibp-node)
                  (declare (ignore ignored1 ignored2))
                  (if (eq live-status :authorized)
                      (mv :selected held payload-token after-live)
                    (mv live-status nil nil after-live)))))
            (mv status held payload-token fuel-left)))))
    (mv status held payload-token fuel-left)))
(verify-guards fn-miq-selected-read)
