; Teeth for books/heap-store-open-walk.lisp (Builder M,
; BATCH-ENTRY-UNDER-CHARGE): KEYSTONE fn-heap-open-walk-entry-within-the-term
; over a batch entry at the batch payload bound (16 MiB + 42 octets) under
; the small preset (R = 192 KiB).
;   WITNESS: the batch header, its whole entry inside the extent, OU the
;     extent: the entry is within the entry array component.
;   BREAK: an extent past OU (the entry is read past the array component).
;   MUTATION: the entry priced at the chunk bound (1 MiB + R), the term this
;     landing replaces: the batch entry refutes it -- the gate that would
;     have seen the under-charge.
; fn-heap-open-walk-record-within-the-term is L's fn-lgb-span-within-max at
; MAX = R + 32 (its teeth are L's, tests/acl2/store-log-buffer-tests.lisp).

(in-package "ACL2")
(include-book "../../books/heap-store-open-walk")
(include-book "../../books/defkeystone")
(include-book "../../books/heap-figure")

(defconst *hsowt-profile* *fn-heap-small-profile*)
; magic "FNLG", version, kind 2 (batch), payload length 16777216 (u32 BE).
(defconst *hsowt-h* '(70 78 76 71 1 2 1 0 0 0))
(defconst *hsowt-n* (+ 42 16777216))
(defun hsowt-st () (declare (xargs :guard t)) (fn-lgw-start *fn-lg-genesis* 1))
(defun hsowt-n (extent)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgw-entry-len-bounded *hsowt-h* (hsowt-st) extent
                            (fn-lgu-log-max (fn-bs-profile-max-record-octets *hsowt-profile*))))

(assert-event (equal (hsowt-n *hsowt-n*) *hsowt-n*))
(assert-event (equal (fn-heap-open-entry-array-bound *hsowt-profile* *hsowt-n*) *hsowt-n*))
(assert-event (< (fn-heap-open-chunk-bound *hsowt-profile* *hsowt-n*) *hsowt-n*))
(assert-event (null (hsowt-n (1- *hsowt-n*))))

(defteeth fn-heap-open-walk-entry-within-the-term
  :claim (((within (<= (nfix extent) (nfix ou))))
          (<= (nfix (fn-lgw-entry-len-bounded h st extent
                                              (fn-lgu-log-max (fn-bs-profile-max-record-octets profile))))
              (fn-heap-open-entry-array-bound profile ou)))
  :subject fn-heap-store-open-octets
  :witness ((h *hsowt-h*) (st (hsowt-st)) (extent *hsowt-n*) (ou *hsowt-n*) (profile *hsowt-profile*))
  :breaks ((within ((h *hsowt-h*) (st (hsowt-st)) (extent *hsowt-n*) (ou 1048576)
                    (profile *hsowt-profile*))))
  :mutations ((entry-priced-at-the-chunk-bound
               (:conclusion (<= (nfix (fn-lgw-entry-len-bounded h st extent
                                                                (fn-lgu-log-max (fn-bs-profile-max-record-octets profile))))
                                (fn-heap-open-chunk-bound profile ou)))
               ((h *hsowt-h*) (st (hsowt-st)) (extent *hsowt-n*) (ou *hsowt-n*) (profile *hsowt-profile*))
               :fault "a batch entry of 16 MiB + 42 octets priced at the chunk bound, 1 MiB + R (BATCH-ENTRY-UNDER-CHARGE)")))
