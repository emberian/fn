; Indexed current physical page ownership. These kernels are INTERNAL:
; allocation receipts are supplied only by the shared-pool issuer. A nonnil
; receipt does not establish runtime constructor adequacy or permit allocation.
(in-package "ACL2")
(logic)
(include-book "index-backing-generations")

(defstobj fn-ibp-page-owner-segment
 (fn-ibp-pos-rows :type (array t (64)) :initially nil)
 (fn-ibp-pos-id :type (integer 0 *) :initially 0)
 (fn-ibp-pos-active :type (integer 0 64) :initially 0)
 :inline t)

(defun fn-ibp-page-owner-tokenp (token)
 (declare (xargs :guard t))
 (and (fn-omk-widthp token 4) (true-listp token)
      (eq (fn-omk-at 0 token) :index-page)
      (posp (fn-omk-at 1 token)) (posp (fn-omk-at 2 token))
      (natp (fn-omk-at 3 token)) (< (fn-omk-at 3 token) 64)))

; Row13: tag,token,kind,physical-slot,chunk-ID,incarnation,generation refs,
; query refs,native borrows,phase,clear cursor,allocation receipt,builder token.
(defun fn-ibp-page-owner-row (token fn-ibp-page-owner-segment)
 (declare (xargs :stobjs fn-ibp-page-owner-segment :guard t))
 (if (and (fn-ibp-page-owner-tokenp token)
          (equal (fn-omk-at 2 token) (fn-ibp-pos-id fn-ibp-page-owner-segment)))
     (let ((row (fn-ibp-pos-rowsi (fn-omk-at 3 token) fn-ibp-page-owner-segment)))
      (if (equal (fn-omk-at 1 row) token) row nil))
   nil))

(defun fn-ibp-page-owner-reserve (token kind physical receipt builder fn-ibp-page-owner-segment)
 (declare (xargs :stobjs fn-ibp-page-owner-segment :guard t))
 (cond
  ((not (and (fn-ibp-page-owner-tokenp token)
             (equal (fn-omk-at 2 token) (fn-ibp-pos-id fn-ibp-page-owner-segment))
             (member-eq kind '(:table :rows)) (natp physical)
             receipt (fn-ibp-generation-tokenp builder)
             (< (fn-ibp-pos-active fn-ibp-page-owner-segment) 64)))
   (mv :refused fn-ibp-page-owner-segment))
  (t
   (let* ((slot (fn-omk-at 3 token))
          (old (fn-ibp-pos-rowsi slot fn-ibp-page-owner-segment))
          (old-token (fn-omk-at 1 old)))
    (if (or (member-eq (fn-omk-at 9 old) '(:reserved :clearing :building :sealed :retiring))
            (and (fn-ibp-page-owner-tokenp old-token)
                 (<= (fn-omk-at 1 token) (fn-omk-at 1 old-token))))
        (mv :stale fn-ibp-page-owner-segment)
      (let* ((row (list :page-owner token kind physical (fn-omk-at 1 token)
                       (fn-omk-at 1 token) 0 0 0 :reserved 0 receipt builder))
             (fn-ibp-page-owner-segment
              (update-fn-ibp-pos-rowsi slot row fn-ibp-page-owner-segment))
             (fn-ibp-page-owner-segment
              (update-fn-ibp-pos-active (+ 1 (fn-ibp-pos-active fn-ibp-page-owner-segment))
                                      fn-ibp-page-owner-segment)))
       (mv :reserved fn-ibp-page-owner-segment)))))))

; A copied directory retains a physical page by CURRENT registered identity.
; Query/native borrow acquisition and release use the same indexed row.
(defun fn-ibp-page-owner-reference (token operation kind fn-ibp-page-owner-segment)
 (declare (xargs :stobjs fn-ibp-page-owner-segment :guard t))
 (let* ((row (fn-ibp-page-owner-row token fn-ibp-page-owner-segment))
        (index (case kind (:generation 6) (:query 7) (:native 8) (otherwise nil))))
  (if (not (and index (fn-ibp-page-owner-tokenp token)
                (member-eq (fn-omk-at 9 row) '(:building :sealed :retiring))
                (natp (fn-omk-at index row))
                (or (and (eq operation :retain) (not (eq (fn-omk-at 9 row) :retiring)))
                    (and (eq operation :drop) (< 0 (fn-omk-at index row))))
                (true-listp row)))
      (mv :stale fn-ibp-page-owner-segment)
    (let* ((count (fn-omk-at index row))
           (next (update-nth index (if (eq operation :retain) (+ count 1) (- count 1)) row))
           (fn-ibp-page-owner-segment
            (update-fn-ibp-pos-rowsi (fn-omk-at 3 token) next fn-ibp-page-owner-segment)))
     (mv :updated fn-ibp-page-owner-segment)))))

; Called only after the exact registered destination has been initialized.
; One builder root owns the new page; publication transfers that same owner,
; rather than incrementing a phantom second reference.
(defun fn-ibp-page-owner-built (token fn-ibp-page-owner-segment)
 (declare (xargs :stobjs fn-ibp-page-owner-segment :guard t))
 (let ((row (fn-ibp-page-owner-row token fn-ibp-page-owner-segment)))
  (if (not (and (fn-ibp-page-owner-tokenp token)
                (eq (fn-omk-at 9 row) :reserved) (true-listp row)))
      (mv :stale fn-ibp-page-owner-segment)
    (let ((fn-ibp-page-owner-segment
           (update-fn-ibp-pos-rowsi (fn-omk-at 3 token)
             (update-nth 9 :building (update-nth 6 1 row)) fn-ibp-page-owner-segment)))
     (mv :building fn-ibp-page-owner-segment)))))

(defun fn-ibp-page-owner-sealed (token fn-ibp-page-owner-segment)
 (declare (xargs :stobjs fn-ibp-page-owner-segment :guard t))
 (let ((row (fn-ibp-page-owner-row token fn-ibp-page-owner-segment)))
  (if (not (and (fn-ibp-page-owner-tokenp token)
                (eq (fn-omk-at 9 row) :building) (true-listp row)))
      (mv :stale fn-ibp-page-owner-segment)
    (let ((fn-ibp-page-owner-segment
           (update-fn-ibp-pos-rowsi (fn-omk-at 3 token)
             (update-nth 9 :sealed row) fn-ibp-page-owner-segment)))
     (mv :sealed fn-ibp-page-owner-segment)))))

; Start retirement only from CURRENT ownership with no remaining roots or
; borrows. The parent also joins its physical aliases before completing this
; phase; zero logical counters alone do not prove a native join.
(defun fn-ibp-page-owner-retire (token fn-ibp-page-owner-segment)
 (declare (xargs :stobjs fn-ibp-page-owner-segment :guard t))
 (let ((row (fn-ibp-page-owner-row token fn-ibp-page-owner-segment)))
  (if (not (and (fn-ibp-page-owner-tokenp token)
                (member-eq (fn-omk-at 9 row) '(:building :sealed))
                (equal (fn-omk-at 6 row) 0) (equal (fn-omk-at 7 row) 0)
                (equal (fn-omk-at 8 row) 0) (true-listp row)))
      (mv :held fn-ibp-page-owner-segment)
    (let ((fn-ibp-page-owner-segment
           (update-fn-ibp-pos-rowsi (fn-omk-at 3 token)
             (update-nth 9 :retiring row) fn-ibp-page-owner-segment)))
     (mv :retiring fn-ibp-page-owner-segment)))))

; INTERNAL definite join completion. The parent supplies this only after its
; core-held physical alias settlement, never a host Boolean. Retired physical
; capacity stays charged in U; this clears ownership, not memory funding.
(defun fn-ibp-page-owner-finish-retirement (token settlement fn-ibp-page-owner-segment)
 (declare (xargs :stobjs fn-ibp-page-owner-segment :guard t))
 (let ((row (fn-ibp-page-owner-row token fn-ibp-page-owner-segment)))
  (if (not (and (fn-ibp-page-owner-tokenp token)
                (eq settlement :joined) (eq (fn-omk-at 9 row) :retiring)
                (equal (fn-omk-at 6 row) 0) (equal (fn-omk-at 7 row) 0)
                (equal (fn-omk-at 8 row) 0)
                (< 0 (fn-ibp-pos-active fn-ibp-page-owner-segment))))
      (mv :unsettled 0 fn-ibp-page-owner-segment)
    (let* ((retired (list :page-owner token (fn-omk-at 2 row) (fn-omk-at 3 row)
                         (fn-omk-at 4 row) (fn-omk-at 5 row)
                         0 0 0 :retired 0 nil nil))
           (fn-ibp-page-owner-segment
            (update-fn-ibp-pos-rowsi (fn-omk-at 3 token) retired fn-ibp-page-owner-segment))
           (fn-ibp-page-owner-segment
            (update-fn-ibp-pos-active (- (fn-ibp-pos-active fn-ibp-page-owner-segment) 1)
                                    fn-ibp-page-owner-segment)))
     (mv :retired 1 fn-ibp-page-owner-segment)))))

; The actual registry boundary fetches the CURRENT owner child. It never
; receives a row snapshot and absent lookup does not construct a child.
(defun fn-ibp-node-page-owner-action
 (token operation kind physical receipt builder fuel address depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
                 :guard (and (natp fuel) (natp address) (natp depth))))
 (cond
  ((<= fuel depth) (mv :yield nil 0 fuel fn-ibp-node))
  ((zp depth)
   (if (not (and (zp address)
                 (fn-ibp-node-children-boundp 'fn-ibp-page-owner-segment fn-ibp-node)))
       (mv :unavailable nil 0 fuel fn-ibp-node)
     (stobj-let ((fn-ibp-page-owner-segment
                  (fn-ibp-node-children-get 'fn-ibp-page-owner-segment fn-ibp-node
                                            (create-fn-ibp-page-owner-segment))))
      (word row delta fn-ibp-page-owner-segment)
      (mv-let (word delta fn-ibp-page-owner-segment)
       (case operation
        (:read (mv :present 0 fn-ibp-page-owner-segment))
        (:finish (fn-ibp-page-owner-finish-retirement token receipt fn-ibp-page-owner-segment))
        (otherwise
         (mv-let (word fn-ibp-page-owner-segment)
          (case operation
           (:reserve
            (if (and (fn-ibp-page-owner-tokenp token)
                     (equal physical (+ (* 64 (- (fn-omk-at 2 token) 1))
                                        (fn-omk-at 3 token))))
                (fn-ibp-page-owner-reserve token kind physical receipt builder fn-ibp-page-owner-segment)
              (mv :refused fn-ibp-page-owner-segment)))
           (:built (fn-ibp-page-owner-built token fn-ibp-page-owner-segment))
           (:sealed (fn-ibp-page-owner-sealed token fn-ibp-page-owner-segment))
           (:retain
            (if (or (eq kind :generation)
                    (eq (fn-omk-at 9 (fn-ibp-page-owner-row token fn-ibp-page-owner-segment)) :sealed))
                (fn-ibp-page-owner-reference token :retain kind fn-ibp-page-owner-segment)
              (mv :stale fn-ibp-page-owner-segment)))
           (:drop (fn-ibp-page-owner-reference token :drop kind fn-ibp-page-owner-segment))
           (:retire (fn-ibp-page-owner-retire token fn-ibp-page-owner-segment))
           (otherwise (mv :refused fn-ibp-page-owner-segment)))
          (mv word 0 fn-ibp-page-owner-segment))))
       (let ((row (fn-ibp-page-owner-row token fn-ibp-page-owner-segment)))
        (mv (if (and (eq word :present) (null row)) :stale word)
            row delta fn-ibp-page-owner-segment)))
      (mv word row delta (- fuel 1) fn-ibp-node))))
  ((evenp address)
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
       (mv :unavailable nil 0 fuel fn-ibp-node)
     (stobj-let ((fn-ibp-node-left
                  (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                            (create-fn-ibp-node-left))))
      (word row delta remaining fn-ibp-node-left)
      (fn-ibp-node-page-owner-action token operation kind physical receipt builder
        (- fuel 1) (floor address 2) (- depth 1) fn-ibp-node-left)
      (mv word row delta remaining fn-ibp-node))))
  (t
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
       (mv :unavailable nil 0 fuel fn-ibp-node)
     (stobj-let ((fn-ibp-node-right
                  (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                            (create-fn-ibp-node-right))))
      (word row delta remaining fn-ibp-node-right)
      (fn-ibp-node-page-owner-action token operation kind physical receipt builder
        (- fuel 1) (floor address 2) (- depth 1) fn-ibp-node-right)
      (mv word row delta remaining fn-ibp-node))))
 ))
(verify-guards fn-ibp-node-page-owner-action)
