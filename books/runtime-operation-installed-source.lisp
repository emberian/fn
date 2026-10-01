; Internal image-source publication after genuine bootstrap installation.
; No caller coordinates, table, price or Boolean setter is accepted.
(in-package "ACL2")
(include-book "runtime-operation-compiled-source")
(include-book "allocation-epoch")
(include-book "page-read-pool-state")
(include-book "state-globals")

(defun fn-owner-runtime-operation-binding (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-runtime-operation-binding state)
      (f-get-global 'fn-owner-runtime-operation-binding state)))

(defun fn-owner-runtime-operation-binding-currentp (fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
 (mv-let (word compiled) (fn-runtime-operation-compiled-coordinate)
  (let ((installed (fn-owner-runtime-operation-binding state))
        (association (fn-aec-at 1 (fn-prp-alloc-installation fn-page-read-pool))))
   (and (eq word :compiled-operation-source) compiled installed
        ; Both fixed records are from the sole internal compiler publication.
        (equal compiled installed)
        association (equal (fn-aec-at 4 installed) association)
        (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining))))))

(defun fn-owner-runtime-operation-binding-install-internal (fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
 (mv-let (word compiled) (fn-runtime-operation-compiled-coordinate)
  (let* ((prior (fn-owner-runtime-operation-binding state))
         (installation (fn-prp-alloc-installation fn-page-read-pool))
         (association (fn-aec-at 1 installation)))
   (cond
    (prior (mv :runtime-operation-binding-already-attempted state))
    ((not (and (eq word :compiled-operation-source) compiled
                (fn-aec-installationp installation)
                (eq (fn-prp-alloc-mode fn-page-read-pool) :active)
                (equal (fn-prp-alloc-active-turns fn-page-read-pool) 0)
                (equal (fn-aec-at 4 compiled) association)
                (equal (fn-aec-at 1 compiled) (fn-aec-at 1 association))
                (equal (fn-aec-at 2 compiled) (fn-aec-at 2 association))
                (equal (fn-aec-at 3 compiled) (fn-aec-at 3 association))))
     (mv :runtime-operation-binding-unavailable state))
    (t (let ((state (f-put-global 'fn-owner-runtime-operation-binding compiled state)))
         (mv :runtime-operation-binding-installed state)))))))
