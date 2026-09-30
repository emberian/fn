; Readonly authority projection for core-issued retained admission input.
; Registration and the query/alias lifetime producer remain owner obligations.
(in-package "ACL2")
(include-book "page-read-pool-state")
(include-book "incoming-buffer-carrier-shape")
(include-book "incoming-octet-holder")
(include-book "owner-canonical-epoch")

(defun fn-owner-incoming-context-read (fn-page-read-pool state)
  (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
  (let* ((slot (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool)))
         (token (fn-prl-nth 0 slot))
         (context (if (boundp-global 'fn-owner-incoming-context state)
                      (f-get-global 'fn-owner-incoming-context state) nil)))
    (if (and (equal (fn-prl-nth 0 context) :incoming-context)
             (equal (fn-ioh-access slot token :read) :holder-readonly)
             (equal token (fn-prl-nth 1 context))
             (equal (fn-owner-canonical-epoch state) (fn-prl-nth 2 context)))
        context nil)))
