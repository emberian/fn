(in-package "ACL2")
(include-book "../../books/index-range-literal-reply-refinement")
(defthm ibrliteral-actual-head-window-model-positive
 (let* ((p (fn-spp-make nil nil '((:reply (65 66)) (:later 2)) :source :resource))
        (cur (fn-srb-effect-octets (fn-ag-car (fn-spp-rest p))))
        (r (fn-ibr-literal-reply-one p)) (h (fn-spp-head-window p 1 nil)))
  (and (eq (fn-spp-status p) :reply) (fn-cbor-octetp (fn-ag-car cur))
       (eq (mv-nth 0 r) :reply-byte) (eq (mv-nth 0 h) :ok)
       (equal (mv-nth 2 r) (mv-nth 1 h))
       (equal (fn-octets-list (mv-nth 2 h)) (list (mv-nth 1 r)))))
 :rule-classes nil)
; MUTATION: malformed plan tag is never the installed actor.
(defthm ibrliteral-status-removal-mutation
 (let* ((p (cons :broken (cdr (fn-spp-make '(65) nil '((:later 2)) :source :resource))))
        (cur (fn-spp-cur p)) (r (fn-ibr-literal-reply-one p)))
  (and (not (eq (fn-spp-status p) :reply))
       (fn-cbor-octetp (fn-ag-car cur))
       (not (eq (mv-nth 0 r) :reply-byte))))
 :rule-classes nil)
; MUTATION: invalid octet is never a qualified bounded output window.
(defthm ibrliteral-octet-removal-mutation
 (let* ((p (fn-spp-make '(300) nil '((:later 2)) :source :resource))
        (cur (fn-spp-cur p)) (r (fn-ibr-literal-reply-one p)))
  (and (eq (fn-spp-status p) :reply)
       (not (fn-cbor-octetp (fn-ag-car cur)))
       (not (eq (mv-nth 0 r) :reply-byte))))
 :rule-classes nil)
