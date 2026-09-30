; One-shot RH acquisition vocabulary; actual producer provenance and
; terminal/physical receipts remain open. No public tuple setter.
(in-package "ACL2")
(include-book "receiver-index-custody")

; INTERNAL actual RH installer companion. These six references must be
; projected from the actual RH/install transaction by its owning producer.
; No native tuple setter is exported. The phase is one-shot for this query.
(defun fn-ric-custody-render-acquire (row live plan pin query resource origin)
 (declare (xargs :guard t))
 (cond
  ((not (and (fn-omk-widthp row 12)
             (eq (fn-omk-at 0 row) :receiver-custody)
             (fn-ibp-query-tokenp query)
             (equal query (fn-omk-at 7 row)) live resource))
   (mv :unavailable-custody row))
  ((eq (fn-omk-at 6 row) :render-owned)
   (mv :already-render-owned row))
  ((not (and (eq (fn-omk-at 6 row) :query-owned)
             (null (fn-omk-at 8 row))))
   (mv :unavailable-custody row))
  (t
   (mv :render-acquired
    (list (fn-omk-at 0 row) (fn-omk-at 1 row) (fn-omk-at 2 row)
          (fn-omk-at 3 row) (fn-omk-at 4 row) (fn-omk-at 5 row)
          :render-owned (fn-omk-at 7 row)
          (list :receiver-render-root live plan pin query resource origin)
          (fn-omk-at 9 row) (fn-omk-at 10 row) (fn-omk-at 11 row))))))

(defthm fn-ric-custody-render-acquire-preserves-source-suffix-query
 (let ((answer (fn-ric-custody-render-acquire row live plan pin query resource origin)))
  (implies (eq (mv-nth 0 answer) :render-acquired)
   (and (equal (fn-omk-at 1 (mv-nth 1 answer)) (fn-omk-at 1 row))
        (equal (fn-omk-at 2 (mv-nth 1 answer)) (fn-omk-at 2 row))
        (equal (fn-omk-at 3 (mv-nth 1 answer)) (fn-omk-at 3 row))
        (equal (fn-omk-at 4 (mv-nth 1 answer)) (fn-omk-at 4 row))
        (equal (fn-omk-at 5 (mv-nth 1 answer)) (fn-omk-at 5 row))
        (equal (fn-omk-at 7 (mv-nth 1 answer)) query)
        (equal (fn-omk-at 8 (mv-nth 1 answer))
               (list :receiver-render-root live plan pin query resource origin)))))
 :hints (("Goal" :in-theory (e/d (fn-ric-custody-render-acquire fn-omk-at)
                                (fn-ibp-query-tokenp fn-omk-widthp))))
 :rule-classes nil)
