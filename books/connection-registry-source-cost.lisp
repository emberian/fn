; Actual connection :reserve registry path. Child-resolution constructors remain
; named unresolved units; explicit row cells and executed arithmetic are exact.
(in-package "ACL2")
(include-book "connection-reserve-source-cost")
(defun fn-ichc-reserve (token id grant fn-ibp-connection-segment)
 (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
 (if (not (and (fn-ich-tokenp token) (natp id) grant
                (equal (fn-omk-at 2 token) (fn-ich-segment-id fn-ibp-connection-segment))
                (< (fn-ich-active fn-ibp-connection-segment) 64)))
      (mv :refused fn-ibp-connection-segment (list nil 0 nil nil))
   (let* ((slot (fn-omk-at 3 token)) (old (fn-ich-rowsi slot fn-ibp-connection-segment))
          (old-token (fn-omk-at 1 old)))
    (if (or (and old
                   (not (and (fn-omk-widthp old 7)
                             (eq (fn-omk-at 0 old) :connection-holder)
                             (eq (fn-omk-at 4 old) :released)
                             (null (fn-omk-at 3 old)) (null (fn-omk-at 5 old))
                             (equal (fn-omk-at 6 old) 0) (fn-ich-tokenp old-token)
                             (equal (fn-omk-at 2 old-token) (fn-omk-at 2 token))
                             (equal (fn-omk-at 3 old-token) slot))))
            (and (fn-ich-tokenp old-token) (<= (fn-omk-at 1 token) (fn-omk-at 1 old-token))))
        (mv :stale fn-ibp-connection-segment (list nil 0 nil nil))
      (let* ((active (fn-ich-active fn-ibp-connection-segment))
             (fn-ibp-connection-segment (update-fn-ich-rowsi slot
               (list :connection-holder token id nil :reserved grant 0) fn-ibp-connection-segment))
             (fn-ibp-connection-segment (update-fn-ich-active (+ 1 active) fn-ibp-connection-segment)))
       (mv :reserved fn-ibp-connection-segment
           (list nil 7 (list (list :add (list 1 active))) '((:constructor :connection-holder-row 7)))))))))
(defthm fn-ichc-reserve-observes-complete-actual-result
 (equal (let ((seen (fn-ichc-reserve token id grant segment)))
          (list (mv-nth 0 seen) (mv-nth 1 seen)))
        (fn-ich-reserve token id grant segment))
 :hints (("Goal" :in-theory (disable fn-ich-tokenp fn-omk-at fn-omk-widthp))) :rule-classes nil)
(local (defthm fn-ichc-reserve-fields
 (and (equal (mv-nth 0 (fn-ichc-reserve token id grant segment)) (mv-nth 0 (fn-ich-reserve token id grant segment)))
      (equal (mv-nth 1 (fn-ichc-reserve token id grant segment)) (mv-nth 1 (fn-ich-reserve token id grant segment))))
 :hints (("Goal" :use fn-ichc-reserve-observes-complete-actual-result
  :in-theory (disable fn-ichc-reserve fn-ich-reserve)))))
(defun fn-ibpc-node-reserve (token id grant fuel slot depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :guard (and (natp fuel) (natp slot) (natp depth))
  :measure (nfix depth) :verify-guards nil))
 (cond ((zp fuel) (mv :yield nil fuel fn-ibp-node (list nil 0 nil nil)))
       ((zp depth)
        (if (not (and (zp slot) (fn-ibp-node-children-boundp 'fn-ibp-connection-segment fn-ibp-node)))
            (mv :unavailable nil fuel fn-ibp-node (list nil 0 nil nil))
          (stobj-let ((fn-ibp-connection-segment
                       (fn-ibp-node-children-get 'fn-ibp-connection-segment fn-ibp-node (create-fn-ibp-connection-segment))))
            (word fn-ibp-connection-segment seen)
            (fn-ichc-reserve token id grant fn-ibp-connection-segment)
            (mv word nil (- fuel 1) fn-ibp-node
              (fn-copsc-join seen (list nil 0 (list (list :subtract (list fuel 1)))
                       '((:unpriced-child-resolution fn-ibp-connection-segment))))))))
       ((evenp slot)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
            (mv :unavailable nil fuel fn-ibp-node (list nil 0 nil nil))
          (stobj-let ((fn-ibp-node-left (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node (create-fn-ibp-node-left))))
            (word payload left fn-ibp-node-left seen)
            (fn-ibpc-node-reserve token id grant (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
            (mv word payload left fn-ibp-node
              (fn-copsc-join (list nil 0
               (list (list :subtract (list fuel 1)) (list :floor (list slot 2)) (list :subtract (list depth 1)))
               '((:unpriced-child-resolution fn-ibp-node-left))) seen)))))
       (t
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
            (mv :unavailable nil fuel fn-ibp-node (list nil 0 nil nil))
          (stobj-let ((fn-ibp-node-right (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node (create-fn-ibp-node-right))))
            (word payload left fn-ibp-node-right seen)
            (fn-ibpc-node-reserve token id grant (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
            (mv word payload left fn-ibp-node
              (fn-copsc-join (list nil 0
               (list (list :subtract (list fuel 1)) (list :floor (list slot 2)) (list :subtract (list depth 1)))
               '((:unpriced-child-resolution fn-ibp-node-right))) seen)))))))
(defthm fn-ibpc-node-reserve-observes-complete-actual-result
 (and
  (equal (mv-nth 0 (fn-ibpc-node-reserve token id grant fuel slot depth node))
         (mv-nth 0 (fn-ibp-node-connection-event token :reserve id grant fuel slot depth node)))
  (equal (mv-nth 1 (fn-ibpc-node-reserve token id grant fuel slot depth node))
         (mv-nth 1 (fn-ibp-node-connection-event token :reserve id grant fuel slot depth node)))
  (equal (mv-nth 2 (fn-ibpc-node-reserve token id grant fuel slot depth node))
         (mv-nth 2 (fn-ibp-node-connection-event token :reserve id grant fuel slot depth node)))
  (equal (mv-nth 3 (fn-ibpc-node-reserve token id grant fuel slot depth node))
         (mv-nth 3 (fn-ibp-node-connection-event token :reserve id grant fuel slot depth node))))
 :hints (("Goal" :induct (fn-ibpc-node-reserve token id grant fuel slot depth node)
  :in-theory (disable fn-ichc-reserve fn-ich-reserve fn-copsc-join fn-ich-tokenp fn-omk-at fn-omk-widthp
   floor evenp fn-ibp-node-children-get fn-ibp-node-children-boundp)))
 :rule-classes nil)
(verify-guards fn-ibpc-node-reserve
 :hints (("Goal" :in-theory (disable fn-ichc-reserve fn-copsc-join))))
(defun fn-ibpc-reserve (token id grant fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (if (not (fn-ich-tokenp token))
     (mv :stale nil fuel fn-index-backing (list nil 0 nil nil))
  (let ((depth (fn-ibp-slot-depth fn-index-backing)))
   (if (<= fuel depth) (mv :yield nil fuel fn-index-backing (list nil 0 nil nil))
    (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
     (word payload left fn-ibp-node seen)
     (fn-ibpc-node-reserve token id grant fuel (- (fn-omk-at 2 token) 1) depth fn-ibp-node)
     (mv word payload left fn-index-backing
      (fn-copsc-join (list nil 0 (list (list :subtract (list (fn-omk-at 2 token) 1))) nil) seen)))))))
(defthm fn-ibpc-reserve-observes-complete-actual-result
 (equal (let ((seen (fn-ibpc-reserve token id grant fuel backing)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen)))
        (fn-ibp-connection-event token :reserve id grant fuel backing))
 :hints (("Goal" :in-theory (disable fn-ibpc-node-reserve fn-ibp-node-connection-event
   fn-ich-tokenp fn-omk-at fn-copsc-join)
  :use ((:instance fn-ibpc-node-reserve-observes-complete-actual-result
         (slot (- (fn-omk-at 2 token) 1))
         (depth (fn-ibp-slot-depth backing)) (node (fn-ibp-registry backing)))))) :rule-classes nil)
(defthm fn-ichc-reserve-row-source-census
 (let ((seen (fn-ichc-reserve token id grant segment)))
  (and (equal (fn-atsc-cells (mv-nth 2 seen)) (if (eq (mv-nth 0 seen) :reserved) 7 0))
       (equal (len (fn-atsc-ops (mv-nth 2 seen))) (if (eq (mv-nth 0 seen) :reserved) 1 0))))
 :hints (("Goal" :in-theory (disable fn-ich-tokenp fn-omk-at fn-omk-widthp))))

(defun fn-icrc-register-contained (token fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let ((receipt (fn-ibp-connection-pending fn-index-backing)))
  (cond ((not (and (fn-ich-tokenp token)
                   (eq (fn-omk-at 0 receipt) :connection-reservation)
                   (equal (fn-omk-at 1 receipt) token)))
         (mv :stale fuel fn-index-backing (list nil 0 nil '(register-ticket-check))))
        ((eq (fn-omk-at 6 receipt) :registered)
         (mv :registered fuel fn-index-backing (list nil 0 nil '(register-ticket-check))))
        ((not (eq (fn-omk-at 6 receipt) :charged))
         (mv :recovery-required fuel fn-index-backing (list nil 0 nil '(register-ticket-check))))
        (t
         (let ((fn-index-backing (update-fn-ibp-connection-pending
                  (fn-icr-keep-phase receipt :register-intent nil) fn-index-backing)))
          (mv-let (word payload left fn-index-backing nested)
           (fn-ibpc-reserve token (fn-omk-at 2 receipt)
                                   (fn-omk-at 5 receipt) fuel fn-index-backing)
           (let ((sites (list (list 'fn-ibp-connection-event
                        (list token :reserve (fn-omk-at 2 receipt) (fn-omk-at 5 receipt) fuel)
                        (list word payload left)))))
            (if (not (eq word :reserved))
                (let ((fn-index-backing (update-fn-ibp-connection-pending receipt fn-index-backing)))
                 (mv word left fn-index-backing (fn-copsc-join (list nil 8 nil sites) nested)))
              (let ((fn-index-backing (update-fn-ibp-connection-pending
                       (fn-icr-keep-phase receipt :registered nil) fn-index-backing)))
               (mv :registered left fn-index-backing (fn-copsc-join (list nil 16 nil sites) nested)))))))))))
(local (defthm fn-ibpc-reserve-fields
 (and
  (equal (mv-nth 0 (fn-ibpc-reserve token id grant fuel backing)) (mv-nth 0 (fn-ibp-connection-event token :reserve id grant fuel backing)))
  (equal (mv-nth 1 (fn-ibpc-reserve token id grant fuel backing)) (mv-nth 1 (fn-ibp-connection-event token :reserve id grant fuel backing)))
  (equal (mv-nth 2 (fn-ibpc-reserve token id grant fuel backing)) (mv-nth 2 (fn-ibp-connection-event token :reserve id grant fuel backing)))
  (equal (mv-nth 3 (fn-ibpc-reserve token id grant fuel backing)) (mv-nth 3 (fn-ibp-connection-event token :reserve id grant fuel backing))))
 :hints (("Goal" :use fn-ibpc-reserve-observes-complete-actual-result
  :in-theory (disable fn-ibpc-reserve fn-ibp-connection-event)))))
(defthm fn-icrc-register-contained-observes-complete-actual-result
 (equal (let ((seen (fn-icrc-register-contained token fuel backing)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen)))
        (fn-icr-register token fuel backing))
 :hints (("Goal" :in-theory (disable fn-ibpc-reserve fn-ibp-connection-event fn-icr-keep-phase fn-omk-at fn-copsc-join)))
 :rule-classes nil)
