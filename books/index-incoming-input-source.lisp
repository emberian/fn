; Actual completed-input source projection, no host-supplied authority.
(in-package "ACL2")
(include-book "incoming-copy-association")
(include-book "consumer-position-fields")

; Called only after actual constructor/scratch issuance. The view export is
; fixed metadata; it never copies the input buffer or imposes a payload ceiling.
(defun fn-iiq-completed-input-source (context fn-input-copy fn-page-read-pool)
 (declare (xargs :stobjs (fn-input-copy fn-page-read-pool) :guard t))
 (let* ((holder (fn-cp-nth 1 context))
        (descriptor (fn-owner-incoming-backing fn-page-read-pool))
        (row (fn-owner-incoming-row fn-page-read-pool)))
  (if (not (and (fn-owner-incoming-copy-associatedp holder fn-input-copy fn-page-read-pool)
                (eq (fn-ioh-access row holder :read) :holder-readonly)
                (fn-ibc-descriptorp descriptor)))
      (mv :source-unavailable nil)
    (let* ((view (fn-input-copy-view fn-input-copy))
           (total (fn-prl-nth 1 view)) (capacity (fn-prl-nth 2 view)))
     (if (not (and (equal (fn-prl-nth 0 view) holder)
                   (eq (fn-prl-nth 6 view) :complete)
                   (natp total) (natp capacity) (<= total capacity)
                   (equal capacity (fn-prl-nth 2 descriptor))
                   (equal total (fn-prl-nth 4 view))
                   (null (fn-prl-nth 5 view))))
         (mv :source-unavailable nil)
       ; Incarnation is descriptor1; the issue nonce is holder1. They are
       ; independently retained, never required to be equal.
       (mv :source-current
           (list :incoming-input-source holder descriptor total capacity view)))))))

(defthm fn-iiq-source-current-retains-completed-original-input
 (implies
  (equal (mv-nth 0 (fn-iiq-completed-input-source context fn-input-copy fn-page-read-pool))
         :source-current)
  (let* ((source (mv-nth 1 (fn-iiq-completed-input-source
                           context fn-input-copy fn-page-read-pool)))
         (holder (fn-cp-nth 1 context)) (view (fn-cp-nth 5 source)))
   (and (equal (fn-cp-nth 1 source) holder)
        (equal (fn-cp-nth 2 source) (fn-owner-incoming-backing fn-page-read-pool))
        (fn-owner-incoming-copy-associatedp holder fn-input-copy fn-page-read-pool)
        (equal (fn-ioh-access (fn-owner-incoming-row fn-page-read-pool) holder :read)
               :holder-readonly)
        (equal (fn-prl-nth 0 view) holder)
        (equal (fn-prl-nth 6 view) :complete)
        (equal (fn-prl-nth 1 view) (fn-prl-nth 4 view))
        (null (fn-prl-nth 5 view))
        (<= (fn-prl-nth 1 view) (fn-prl-nth 2 view)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-iiq-completed-input-source fn-cp-nth fn-prl-nth)
               (fn-owner-incoming-copy-associatedp fn-input-copy-view
                fn-owner-incoming-row fn-owner-incoming-backing fn-ioh-access)))))
