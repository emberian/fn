; CURRENT registered destination row progress. These internal subjects do not
; authorize constructors; installation and retained capacity have their own
; shared-pool/source/runtime obligations before the :built receipt exists.
(in-package "ACL2")
(logic)
(include-book "index-backing-layout")

(defun fn-ibp-row-owner-filled (token expected fn-ibp-page-owner-segment)
 (declare (xargs :stobjs fn-ibp-page-owner-segment :guard (natp expected)))
 (let ((row (fn-ibp-page-owner-row token fn-ibp-page-owner-segment)))
  (if (not (and (fn-ibp-page-owner-tokenp token)
                (true-listp row) (eq (fn-omk-at 2 row) :rows)
                (eq (fn-omk-at 9 row) :building)
                (equal (fn-omk-at 10 row) expected) (< expected 256)))
      (mv :stale fn-ibp-page-owner-segment)
    (let ((fn-ibp-page-owner-segment
           (update-fn-ibp-pos-rowsi (fn-omk-at 3 token)
             (update-nth 10 (+ 1 expected) row) fn-ibp-page-owner-segment)))
     (mv :advanced fn-ibp-page-owner-segment)))))

(defun fn-ibp-node-row-owner-filled (token expected fuel address depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
                 :guard (and (natp expected) (natp fuel) (natp address) (natp depth))))
 (cond
  ((<= fuel depth) (mv :yield fuel fn-ibp-node))
  ((zp depth)
   (if (not (and (zp address)
                 (fn-ibp-node-children-boundp 'fn-ibp-page-owner-segment fn-ibp-node)))
       (mv :unavailable fuel fn-ibp-node)
     (stobj-let ((fn-ibp-page-owner-segment
                  (fn-ibp-node-children-get 'fn-ibp-page-owner-segment fn-ibp-node
                                            (create-fn-ibp-page-owner-segment))))
      (word fn-ibp-page-owner-segment)
      (fn-ibp-row-owner-filled token expected fn-ibp-page-owner-segment)
      (mv word (- fuel 1) fn-ibp-node))))
  ((evenp address)
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
       (mv :unavailable fuel fn-ibp-node)
     (stobj-let ((fn-ibp-node-left
                  (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                            (create-fn-ibp-node-left))))
      (word left fn-ibp-node-left)
      (fn-ibp-node-row-owner-filled token expected (- fuel 1)
                                    (floor address 2) (- depth 1) fn-ibp-node-left)
      (mv word left fn-ibp-node))))
  (t
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
       (mv :unavailable fuel fn-ibp-node)
     (stobj-let ((fn-ibp-node-right
                  (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                            (create-fn-ibp-node-right))))
      (word left fn-ibp-node-right)
      (fn-ibp-node-row-owner-filled token expected (- fuel 1)
                                    (floor address 2) (- depth 1) fn-ibp-node-right)
      (mv word left fn-ibp-node))))))
(verify-guards fn-ibp-node-row-owner-filled)

; One action reads at most one old immutable row, writes one destination cell,
; then advances that destination's CURRENT cursor. The parent derives count,
; assigned row and both descriptors from the registered builder/reservation.
; Missing old rows and any post-write uncertainty fence the builder.
(defun fn-ibp-row-copy-cell
 (token assigned count old-descriptor physical nonce fuel depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :verify-guards nil
                 :guard (and (natp count) (natp physical) (posp nonce)
                             (natp fuel) (<= fuel *fn-mpr-slot-quantum*) (natp depth))))
 (let ((action (+ 1 depth)))
  (if (< fuel (* 4 action)) (mv :yield fuel fn-ibp-node)
   (mv-let (word owner delta read-left fn-ibp-node)
    (fn-ibp-node-page-owner-action token :read nil nil nil nil action
                                  (floor physical 64) depth fn-ibp-node)
    (let ((position (fn-omk-at 10 owner)) (prefix (mod count 256)))
     (cond
      ((not (and (eq word :present) (equal delta 0) (natp read-left)
                 (equal (fn-omk-at 2 owner) :rows)
                 (equal (fn-omk-at 3 owner) physical)
                 (equal (fn-omk-at 4 owner) nonce) (equal (fn-omk-at 5 owner) nonce)
                 (eq (fn-omk-at 9 owner) :building)
                 (natp position) (<= position prefix)))
       (mv :recovery-required (- fuel action) fn-ibp-node))
      (t
       (mv-let (source-word held source-left)
        (if (equal position prefix) (mv :row assigned action)
          (if (fn-ibp-chunk-descriptorp old-descriptor)
              (fn-ibp-node-row-read position action (nth 1 old-descriptor) depth
                 (nth 2 old-descriptor) (nth 3 old-descriptor) fn-ibp-node)
            (mv :recovery-required nil action)))
        (if (not (and (eq source-word :row) (natp source-left)))
            (mv :recovery-required (- fuel (* 2 action)) fn-ibp-node)
          (mv-let (write-word write-left fn-ibp-node)
           (fn-ibp-node-row-write position held nil physical depth nonce nonce action fn-ibp-node)
           (if (not (and (eq write-word :written) (natp write-left)))
               (mv :recovery-required (- fuel (* 3 action)) fn-ibp-node)
             (mv-let (advance-word advance-left fn-ibp-node)
              (fn-ibp-node-row-owner-filled token position action (floor physical 64) depth fn-ibp-node)
              (mv (if (and (eq advance-word :advanced) (natp advance-left))
                      (if (equal position prefix) :appended :copied)
                    :recovery-required)
                  (- fuel (* 4 action)) fn-ibp-node))))))))))))
 )
(verify-guards fn-ibp-row-copy-cell
 :hints (("Goal" :in-theory (disable fn-ibp-node-page-owner-action
                                    fn-ibp-node-row-read fn-ibp-node-row-write
                                    fn-ibp-node-row-owner-filled))))

(defun fn-ipa-row-copy-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :verify-guards nil
                 :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*))))
 (let* ((receipt (fn-ibp-page-pending fn-index-backing))
        (builder (fn-ibp-builder fn-index-backing))
        (nonce (fn-omk-at 2 receipt)) (physical (fn-omk-at 3 receipt))
        (count (fn-omk-at 6 builder)) (depth (fn-ibp-slot-depth fn-index-backing)))
  (cond
   ((not (and (fn-omk-widthp receipt 13) (true-listp receipt)
              (eq (fn-omk-at 0 receipt) :page-reservation)
              (eq (fn-omk-at 6 receipt) :rows)
              (fn-omk-widthp builder 20) (true-listp builder)
              (eq (fn-omk-at 1 builder) :layout)
              (equal (fn-omk-at 7 receipt) (fn-omk-at 2 builder))
              (posp nonce) (natp physical) (natp count)
              (equal (fn-omk-at 8 receipt) (floor count 256))))
    (mv :stale fuel fn-index-backing))
   ((eq (fn-omk-at 10 receipt) :copied) (mv :appended fuel fn-index-backing))
   ((not (eq (fn-omk-at 10 receipt) :built)) (mv :stale fuel fn-index-backing))
   ((< fuel (* 4 (+ 1 depth))) (mv :yield fuel fn-index-backing))
   (t
    (let ((token (list :index-page nonce (+ 1 (floor physical 64)) (mod physical 64))))
     (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
      (word left fn-ibp-node)
      (fn-ibp-row-copy-cell token (fn-omk-at 5 (fn-omk-at 8 builder)) count
                           (fn-omk-at 9 receipt) physical nonce fuel depth fn-ibp-node)
      (cond
       ((eq word :appended)
        (let ((fn-index-backing
               (update-fn-ibp-page-pending (update-nth 10 :copied receipt) fn-index-backing)))
         (mv :appended left fn-index-backing)))
       ((member-eq word '(:yield :copied)) (mv word left fn-index-backing))
       (t
        (let ((fn-index-backing
               (update-fn-ibp-builder (update-nth 1 :recovery-required builder) fn-index-backing)))
         (mv :recovery-required left fn-index-backing))))))))))
(verify-guards fn-ipa-row-copy-one
 :hints (("Goal" :in-theory (disable fn-ibp-row-copy-cell))))

; Seal only after CURRENT owner cursor proves every copied cell and the actual
; assigned append completed. Then retain the immutable path-rebuild cursor;
; no new row root is published by this step.
(defun fn-ipa-row-seal (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :verify-guards nil :guard (natp fuel)))
 (let* ((receipt (fn-ibp-page-pending fn-index-backing))
        (builder (fn-ibp-builder fn-index-backing))
        (nonce (fn-omk-at 2 receipt)) (physical (fn-omk-at 3 receipt))
        (count (fn-omk-at 6 builder)) (page (fn-omk-at 8 receipt))
        (old (fn-omk-at 2 (fn-omk-at 7 (fn-omk-at 19 builder))))
        (row-depth (fn-ipub-row-depth old))
        (depth (fn-ibp-slot-depth fn-index-backing)) (action (+ 1 depth)))
  (cond
   ((not (and (fn-omk-widthp receipt 13) (true-listp receipt)
              (eq (fn-omk-at 0 receipt) :page-reservation)
              (eq (fn-omk-at 6 receipt) :rows)
              (eq (fn-omk-at 10 receipt) :copied)
              (fn-omk-widthp builder 20) (true-listp builder)
              (eq (fn-omk-at 1 builder) :layout)
              (fn-ibp-generation-tokenp (fn-omk-at 2 builder))
              (fn-omk-widthp (fn-omk-at 8 builder) 8)
              (eq (fn-omk-at 0 (fn-omk-at 8 builder)) :assigned)
              (equal (fn-omk-at 3 (fn-omk-at 8 builder)) count)
              (equal (fn-omk-at 2 (fn-omk-at 8 builder)) (fn-omk-at 7 builder))
              (equal (fn-omk-at 7 receipt) (fn-omk-at 2 builder))
              (posp nonce) (natp physical) (natp count) (natp page)
              (equal page (floor count 256)) (natp row-depth)))
    (mv :stale fuel fn-index-backing))
   ((< fuel (+ (* 3 action) 1)) (mv :yield fuel fn-index-backing))
   (t
    (let ((token (list :index-page nonce (+ 1 (floor physical 64)) (mod physical 64))))
     (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
      (word fn-ibp-node)
      (mv-let (read-word owner delta read-left fn-ibp-node)
       (fn-ibp-node-page-owner-action token :read nil nil nil nil action
                                      (floor physical 64) depth fn-ibp-node)
       (if (not (and (eq read-word :present) (equal delta 0) (natp read-left)
                     (eq (fn-omk-at 2 owner) :rows) (eq (fn-omk-at 9 owner) :building)
                     (equal (fn-omk-at 3 owner) physical)
                     (equal (fn-omk-at 4 owner) nonce) (equal (fn-omk-at 5 owner) nonce)
                     (equal (fn-omk-at 12 owner) (fn-omk-at 2 builder))
                     (equal (fn-omk-at 10 owner) (+ 1 (mod count 256)))))
           (mv :recovery-required fn-ibp-node)
         (mv-let (seal-word seal-left fn-ibp-node)
          (fn-ibp-node-row-write 0 nil t physical depth nonce nonce action fn-ibp-node)
          (if (not (and (eq seal-word :sealed) (natp seal-left)))
              (mv :recovery-required fn-ibp-node)
            (mv-let (owner-word next-owner delta owner-left fn-ibp-node)
             (fn-ibp-node-page-owner-action token :sealed nil nil nil nil action
                                            (floor physical 64) depth fn-ibp-node)
             (mv (if (and (eq owner-word :sealed) (eq (fn-omk-at 9 next-owner) :sealed)
                          (equal delta 0) (natp owner-left)) :sealed :recovery-required)
                 fn-ibp-node))))))
      (if (not (eq word :sealed))
          (let ((fn-index-backing
                 (update-fn-ibp-builder (update-nth 1 :recovery-required builder) fn-index-backing)))
           (mv :recovery-required (- fuel (+ (* 3 action) 1)) fn-index-backing))
        (let* ((cursor (fn-ibp-dir-put-begin (fn-ipub-row-root old) page row-depth
                                            (list :chunk physical nonce nonce)))
               (next (update-nth 1 :row-root
                       (update-nth 13 row-depth
                        (update-nth 14 (fn-omk-at 1 (fn-omk-at 2 builder))
                         (update-nth 18 cursor builder)))))
               (fn-index-backing (update-fn-ibp-builder next fn-index-backing))
               (fn-index-backing
                (update-fn-ibp-page-pending (update-nth 10 :sealed receipt) fn-index-backing)))
         (mv :row-root (- fuel (+ (* 3 action) 1)) fn-index-backing))))))))
 )
(verify-guards fn-ipa-row-seal
 :hints (("Goal" :in-theory (disable fn-ibp-node-page-owner-action fn-ibp-node-row-write))))

(defun fn-ipa-row-root-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let ((builder (fn-ibp-builder fn-index-backing)))
  (cond ((zp fuel) (mv :yield fuel fn-index-backing))
        ((not (and (fn-omk-widthp builder 20) (true-listp builder)
                   (eq (fn-omk-at 1 builder) :row-root)))
         (mv :stale fuel fn-index-backing))
        (t
         (let* ((cursor (fn-ibp-dir-put-step (fn-omk-at 18 builder)))
                (phase (fn-omk-at 0 cursor))
                (next (cond
                       ((eq phase :done)
                        (update-nth 1 :table-layout
                         (update-nth 12 (fn-omk-at 1 cursor)
                          (update-nth 18 nil builder))))
                       ((eq phase :recovery-required) (update-nth 1 :recovery-required builder))
                       (t (update-nth 18 cursor builder))))
                (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
          (mv (cond ((eq phase :done) :table-layout)
                    ((eq phase :recovery-required) :recovery-required)
                    (t :row-root)) (- fuel 1) fn-index-backing))))))
