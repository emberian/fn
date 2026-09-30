; Fixed generation metadata for charged published roots and actual pin/query
; holders. Internal operations; no host supplied publication installation.
(in-package "ACL2")
(logic)
(include-book "index-backing-publication")

(defstobj fn-ibp-generation-segment
 (fn-ibp-gs-rows :type (array t (64)) :initially nil)
 (fn-ibp-gs-id :type (integer 0 *) :initially 0)
 (fn-ibp-gs-active :type (integer 0 64) :initially 0)
 :inline t)
(defun fn-ibp-generation-tokenp (token)
 (declare (xargs :guard t))
 (and (true-listp token) (equal (len token) 4) (eq (car token) :index-generation)
      (posp (nth 1 token)) (posp (nth 2 token)) (natp (nth 3 token)) (< (nth 3 token) 64)))
(defun fn-ibp-generation-row (token fn-ibp-generation-segment)
 (declare (xargs :stobjs fn-ibp-generation-segment :guard t))
 (if (and (fn-ibp-generation-tokenp token)
          (equal (nth 2 token) (fn-ibp-gs-id fn-ibp-generation-segment)))
     (let ((row (fn-ibp-gs-rowsi (nth 3 token) fn-ibp-generation-segment)))
       (if (equal (fn-omk-at 1 row) token) row nil))
   nil))
; Row fixed11: tag,token,publication,current,pins,queries,writers,phase,grant,
; arena incarnation,prefix. Reserved rows own no arena; building/live/retiring
; rows retain the exact registered coordinate until joined retirement.
(defun fn-ibp-generation-begin (token grant fn-ibp-generation-segment)
 (declare (xargs :stobjs fn-ibp-generation-segment :guard t))
 (if (not (and grant (fn-ibp-generation-tokenp token)
               (equal (nth 2 token) (fn-ibp-gs-id fn-ibp-generation-segment))
               (< (fn-ibp-gs-active fn-ibp-generation-segment) 64)))
     (mv :refused fn-ibp-generation-segment)
   (let* ((slot (nth 3 token)) (old (fn-ibp-gs-rowsi slot fn-ibp-generation-segment))
          (old-token (fn-omk-at 1 old)))
     (if (or (member-eq (fn-omk-at 7 old) '(:reserved :building :live :retiring))
             (and (fn-ibp-generation-tokenp old-token) (<= (nth 1 token) (nth 1 old-token))))
         (mv :stale fn-ibp-generation-segment)
       (let* ((fn-ibp-generation-segment
               (update-fn-ibp-gs-rowsi slot (list :generation token nil 0 0 0 0 :reserved grant nil nil) fn-ibp-generation-segment))
              (fn-ibp-generation-segment
               (update-fn-ibp-gs-active (+ 1 (fn-ibp-gs-active fn-ibp-generation-segment)) fn-ibp-generation-segment)))
         (mv :reserved fn-ibp-generation-segment))))))
 ; Internal coordinate installation; only the actual STATE/arena adapter may
; compose this with the registered reserved row and aggregate transition.
(defun fn-ibp-generation-capture-arena (token incarnation prefix fn-ibp-generation-segment)
 (declare (xargs :stobjs fn-ibp-generation-segment :guard t))
 (let ((row (fn-ibp-generation-row token fn-ibp-generation-segment)))
  (if (not (and (fn-ibp-generation-tokenp token)
                (eq (fn-omk-at 7 row) :reserved) (natp incarnation) (natp prefix)))
      (mv :stale fn-ibp-generation-segment)
    (let ((fn-ibp-generation-segment
           (update-fn-ibp-gs-rowsi (nth 3 token)
             (list :generation token nil 0 0 0 1 :building (fn-omk-at 8 row)
                   incarnation prefix) fn-ibp-generation-segment)))
      (mv :captured fn-ibp-generation-segment)))))
(defun fn-ibp-generation-install-publication (token publication fn-ibp-generation-segment)
 (declare (xargs :stobjs fn-ibp-generation-segment :guard t))
 (let ((row (fn-ibp-generation-row token fn-ibp-generation-segment)))
   (if (not (and (fn-ibp-generation-tokenp token) (eq (fn-omk-at 7 row) :building)
                 (fn-ipub-shapep publication) (equal (fn-ipub-generation publication) (nth 1 token))
                 (equal (fn-omk-at 6 row) 1)
                 (equal (fn-ipub-arena-incarnation publication) (fn-omk-at 9 row))
                 (equal (fn-ipub-arena-prefix publication) (fn-omk-at 10 row))))
       (mv :recovery-required fn-ibp-generation-segment)
     (let ((fn-ibp-generation-segment
             (update-fn-ibp-gs-rowsi (nth 3 token)
               (list :generation token publication 1 0 0 0 :live (fn-omk-at 8 row) (fn-omk-at 9 row) (fn-omk-at 10 row)) fn-ibp-generation-segment)))
       (mv :published fn-ibp-generation-segment)))))
(defun fn-ibp-generation-retain (token kind fn-ibp-generation-segment)
 (declare (xargs :stobjs fn-ibp-generation-segment :guard t))
 (let ((row (fn-ibp-generation-row token fn-ibp-generation-segment)))
  (if (not (and (fn-ibp-generation-tokenp token) (eq (fn-omk-at 7 row) :live)
                (member-eq kind '(:pin :query :writer))
                (natp (fn-omk-at 4 row)) (natp (fn-omk-at 5 row)) (natp (fn-omk-at 6 row))))
      (mv :stale nil fn-ibp-generation-segment)
    (let* ((publication (fn-omk-at 2 row))
           (next (list :generation token publication (fn-omk-at 3 row)
                       (+ (fn-omk-at 4 row) (if (eq kind :pin) 1 0))
                       (+ (fn-omk-at 5 row) (if (eq kind :query) 1 0))
                       (+ (fn-omk-at 6 row) (if (eq kind :writer) 1 0))
                       :live (fn-omk-at 8 row) (fn-omk-at 9 row) (fn-omk-at 10 row)))
           (fn-ibp-generation-segment (update-fn-ibp-gs-rowsi (nth 3 token) next fn-ibp-generation-segment)))
      (mv :retained publication fn-ibp-generation-segment)))))

(defun fn-ibp-node-generation-capture-arena (token incarnation prefix fuel slot depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :guard (and (natp fuel) (natp slot) (natp depth))
                 :measure (nfix depth) :verify-guards nil))
 (cond ((zp fuel) (mv :yield fuel fn-ibp-node))
       ((zp depth)
        (if (not (and (zp slot) (fn-ibp-node-children-boundp 'fn-ibp-generation-segment fn-ibp-node)))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-generation-segment
                       (fn-ibp-node-children-get 'fn-ibp-generation-segment fn-ibp-node
                                                (create-fn-ibp-generation-segment))))
            (status fn-ibp-generation-segment)
            (fn-ibp-generation-capture-arena token incarnation prefix fn-ibp-generation-segment)
            (mv status (- fuel 1) fn-ibp-node))))
       ((evenp slot)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-left
                       (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                                (create-fn-ibp-node-left))))
            (status fuel-left fn-ibp-node-left)
            (fn-ibp-node-generation-capture-arena token incarnation prefix (- fuel 1)
                                                (floor slot 2) (- depth 1) fn-ibp-node-left)
            (mv status fuel-left fn-ibp-node))))       (t
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-right
                       (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                                (create-fn-ibp-node-right))))
            (status fuel-left fn-ibp-node-right)
            (fn-ibp-node-generation-capture-arena token incarnation prefix (- fuel 1)
                                                (floor slot 2) (- depth 1) fn-ibp-node-right)
            (mv status fuel-left fn-ibp-node))))))
(verify-guards fn-ibp-node-generation-capture-arena)

; Internal actual registered parent transition, not a sanctioned scalar setter.
; STATE/arena adapter derives coordinates; reserved generation row is authority.
(defun fn-ibp-generation-capture-coordinate (token incarnation prefix fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (if (not (fn-ibp-generation-tokenp token))
     (mv :stale fuel fn-index-backing)
   (let ((depth (fn-ibp-slot-depth fn-index-backing)))
    (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
     (status remaining fn-ibp-node)
     (fn-ibp-node-generation-capture-arena token incarnation prefix fuel
       (- (nth 2 token) 1) depth fn-ibp-node)
     (let ((fn-index-backing
            (if (eq status :captured)
                (update-fn-ibp-publication-payload-active
                  (+ 1 (fn-ibp-publication-payload-active fn-index-backing)) fn-index-backing)
              fn-index-backing)))
       (mv status remaining fn-index-backing))))))
(defun fn-mio-generation-capture-coordinate (token incarnation prefix fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
   (status remaining fn-index-backing)
   (fn-ibp-generation-capture-coordinate token incarnation prefix fuel fn-index-backing)
   (mv status remaining fn-mio$c)))

(defun fn-ibp-node-generation-read (token fuel slot depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :guard (and (natp fuel) (natp slot) (natp depth))
                 :measure (nfix depth) :verify-guards nil))
 (cond ((zp fuel) (mv :yield nil fuel))
       ((zp depth)
        (if (not (and (zp slot) (fn-ibp-node-children-boundp 'fn-ibp-generation-segment fn-ibp-node)))
            (mv :unavailable nil fuel)
          (stobj-let ((fn-ibp-generation-segment
                       (fn-ibp-node-children-get 'fn-ibp-generation-segment fn-ibp-node
                                                (create-fn-ibp-generation-segment))))
            (row)
            (fn-ibp-generation-row token fn-ibp-generation-segment)
            (mv (if row :present :stale) row (- fuel 1)))))
       ((evenp slot)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
            (mv :unavailable nil fuel)
          (stobj-let ((fn-ibp-node-left
                       (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                                (create-fn-ibp-node-left))))
            (status row fuel-left)
            (fn-ibp-node-generation-read token (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
            (mv status row fuel-left))))       (t
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
            (mv :unavailable nil fuel)
          (stobj-let ((fn-ibp-node-right
                       (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                                (create-fn-ibp-node-right))))
            (status row fuel-left)
            (fn-ibp-node-generation-read token (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
            (mv status row fuel-left))))))
(verify-guards fn-ibp-node-generation-read)
(defun fn-mio-generation-read (token fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
   (status row remaining)
   (let ((depth (fn-ibp-slot-depth fn-index-backing)))
     (if (not (fn-ibp-generation-tokenp token))
         (mv :stale nil fuel)
       (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
         (status row remaining)
         (fn-ibp-node-generation-read token fuel (- (nth 2 token) 1) depth fn-ibp-node)
         (mv status row remaining))))
   (mv status row remaining)))

; INTERNAL: callers must consume their exact registered holder once. This
; counter operation alone is not a host release authority or alias join.
(defun fn-ibp-generation-drop-reference (token kind fn-ibp-generation-segment)
 (declare (xargs :stobjs fn-ibp-generation-segment :guard t))
 (let* ((row (fn-ibp-generation-row token fn-ibp-generation-segment))
        (index (case kind (:current 3) (:pin 4) (:query 5) (:writer 6) (otherwise nil))))
  (if (not (and (fn-ibp-generation-tokenp token) index
                (member-eq (fn-omk-at 7 row) '(:building :live))
                (natp (fn-omk-at 3 row)) (natp (fn-omk-at 4 row))
                (natp (fn-omk-at 5 row)) (natp (fn-omk-at 6 row))
                (posp (fn-omk-at index row))))
      (mv :stale fn-ibp-generation-segment)
    (let* ((current (- (fn-omk-at 3 row) (if (eq kind :current) 1 0)))
           (pins (- (fn-omk-at 4 row) (if (eq kind :pin) 1 0)))
           (queries (- (fn-omk-at 5 row) (if (eq kind :query) 1 0)))
           (writers (- (fn-omk-at 6 row) (if (eq kind :writer) 1 0)))
           (phase (if (equal (+ current pins queries writers) 0) :retiring (fn-omk-at 7 row)))
           (fn-ibp-generation-segment
            (update-fn-ibp-gs-rowsi (nth 3 token)
              (list :generation token (fn-omk-at 2 row) current pins queries writers phase
                    (fn-omk-at 8 row) (fn-omk-at 9 row) (fn-omk-at 10 row)) fn-ibp-generation-segment)))
      (mv phase fn-ibp-generation-segment)))))

; Joined means the concrete bounded directory/chunk retirement and all
; registered aliases have completed; publication debt survives :retiring.
(defun fn-ibp-generation-finish-retirement (token settlement fn-ibp-generation-segment)
 (declare (xargs :stobjs fn-ibp-generation-segment :guard t))
 (let ((row (fn-ibp-generation-row token fn-ibp-generation-segment)))
  (if (not (and (fn-ibp-generation-tokenp token) (eq settlement :joined)
                (eq (fn-omk-at 7 row) :retiring)
                (equal (fn-omk-at 3 row) 0) (equal (fn-omk-at 4 row) 0)
                (equal (fn-omk-at 5 row) 0) (equal (fn-omk-at 6 row) 0)
                (< 0 (fn-ibp-gs-active fn-ibp-generation-segment))))
      (mv :stale 0 fn-ibp-generation-segment)
    (let* ((fn-ibp-generation-segment
            (update-fn-ibp-gs-rowsi (nth 3 token)
              (list :generation token nil 0 0 0 0 :retired nil nil nil) fn-ibp-generation-segment))
           (fn-ibp-generation-segment
            (update-fn-ibp-gs-active (- (fn-ibp-gs-active fn-ibp-generation-segment) 1) fn-ibp-generation-segment)))
      (mv :retired 1 fn-ibp-generation-segment)))))

(defun fn-ibp-node-generation-reference (token operation kind settlement fuel slot depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :guard (and (natp fuel) (natp slot) (natp depth))
                 :measure (nfix depth) :verify-guards nil))
 (cond ((zp fuel) (mv :yield nil 0 fuel fn-ibp-node))
       ((zp depth)
        (if (not (and (zp slot) (fn-ibp-node-children-boundp 'fn-ibp-generation-segment fn-ibp-node)))
            (mv :unavailable nil 0 fuel fn-ibp-node)
          (stobj-let ((fn-ibp-generation-segment
                       (fn-ibp-node-children-get 'fn-ibp-generation-segment fn-ibp-node
                                                (create-fn-ibp-generation-segment))))
            (status publication delta fn-ibp-generation-segment)
            (case operation
              (:retain (mv-let (word publication fn-ibp-generation-segment)
                         (fn-ibp-generation-retain token kind fn-ibp-generation-segment)
                         (mv word publication 0 fn-ibp-generation-segment)))
              (:drop (mv-let (word fn-ibp-generation-segment)
                       (fn-ibp-generation-drop-reference token kind fn-ibp-generation-segment)
                       (mv word nil 0 fn-ibp-generation-segment)))
              (:retire (mv-let (word delta fn-ibp-generation-segment)
                         (fn-ibp-generation-finish-retirement token settlement fn-ibp-generation-segment)
                         (mv word nil delta fn-ibp-generation-segment)))
              (otherwise (mv :refused nil 0 fn-ibp-generation-segment)))
            (mv status publication delta (- fuel 1) fn-ibp-node))))
       ((evenp slot)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
            (mv :unavailable nil 0 fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-left
                       (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                                (create-fn-ibp-node-left))))
            (status publication delta remaining fn-ibp-node-left)
            (fn-ibp-node-generation-reference token operation kind settlement (- fuel 1)
              (floor slot 2) (- depth 1) fn-ibp-node-left)
            (mv status publication delta remaining fn-ibp-node))))       (t
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
            (mv :unavailable nil 0 fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-right
                       (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                                (create-fn-ibp-node-right))))
            (status publication delta remaining fn-ibp-node-right)
            (fn-ibp-node-generation-reference token operation kind settlement (- fuel 1)
              (floor slot 2) (- depth 1) fn-ibp-node-right)
            (mv status publication delta remaining fn-ibp-node))))))
(verify-guards fn-ibp-node-generation-reference)
(defthm fn-ibp-node-generation-reference-preserves-shape
 (implies (fn-ibp-nodep fn-ibp-node)
  (fn-ibp-nodep (mv-nth 4 (fn-ibp-node-generation-reference token operation kind settlement fuel slot depth fn-ibp-node))))
 :hints (("Goal" :expand ((fn-ibp-node-generation-reference token operation kind settlement fuel slot depth fn-ibp-node))
                  :in-theory (disable fn-ibp-node-generation-reference fn-ibp-nodep fn-ibp-node-children-put))))
(defun fn-ibp-generation-reference (token operation kind settlement fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel) :verify-guards nil))
 (let ((depth (fn-ibp-slot-depth fn-index-backing))
       (active (fn-ibp-publication-payload-active fn-index-backing)))
  (if (or (not (fn-ibp-generation-tokenp token))
          (and (eq operation :retire) (zp active)))
      (mv :stale nil fuel fn-index-backing)
    (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
      (status publication delta remaining fn-ibp-node)
      (fn-ibp-node-generation-reference token operation kind settlement fuel
        (- (nth 2 token) 1) depth fn-ibp-node)
      (let ((fn-index-backing
             (if (and (eq operation :retire) (equal delta 1))
                 (update-fn-ibp-publication-payload-active
                   (- active 1) fn-index-backing)
               fn-index-backing)))
        (mv status publication remaining fn-index-backing))))))
(verify-guards fn-ibp-generation-reference
 :hints (("Goal" :in-theory (disable fn-ibp-node-generation-reference fn-ibp-nodep fn-ibp-node-children-put))))
(defun fn-mio-generation-reference (token operation kind settlement fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
   (status publication remaining fn-index-backing)
   (fn-ibp-generation-reference token operation kind settlement fuel fn-index-backing)
   (mv status publication remaining fn-mio$c)))
