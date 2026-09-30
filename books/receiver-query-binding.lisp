; Unchanged internal adoption binding; no receiver/controller dependency.
(in-package "ACL2")
(include-book "index-backing-provider")

; Internal adoption helper; the caller derives both tokens from the SAME
; actual request/adoption transaction. This is not an exported row setter.
; Recipient2 remains immutable provenance. Query root7 names the selected
; generation token, including when its generation differs from the request.
(defun fn-ric-custody-bind-query (row original selected)
 (declare (xargs :guard t))
 (cond
  ((not (and (fn-omk-widthp row 12)
             (eq (fn-omk-at 0 row) :receiver-custody)
             (fn-ibp-query-tokenp original) (fn-ibp-query-tokenp selected)
             (equal original (fn-omk-at 2 row))
             (equal (fn-omk-at 1 original) (fn-omk-at 1 selected))
             (equal (fn-omk-at 2 original) (fn-omk-at 2 selected))
             (equal (fn-omk-at 3 original) (fn-omk-at 3 selected))))
   (mv :unavailable-custody row))
  ((and (eq (fn-omk-at 6 row) :query-owned)
        (equal selected (fn-omk-at 7 row)))
   (mv :already-bound row))
  ((not (and (eq (fn-omk-at 6 row) :retained)
             (equal original (fn-omk-at 7 row))))
   (mv :unavailable-custody row))
  (t (mv :query-bound
         (list (fn-omk-at 0 row) (fn-omk-at 1 row) (fn-omk-at 2 row)
               (fn-omk-at 3 row) (fn-omk-at 4 row) (fn-omk-at 5 row)
               :query-owned selected (fn-omk-at 8 row) (fn-omk-at 9 row)
               (fn-omk-at 10 row) (fn-omk-at 11 row))))))

(defthm fn-ric-custody-bind-query-keeps-source-suffix-and-original-recipient
 (let ((answer (fn-ric-custody-bind-query row original selected)))
  (implies (equal (mv-nth 0 answer) :query-bound)
   (and (equal (fn-omk-at 1 (mv-nth 1 answer)) (fn-omk-at 1 row))
        (equal (fn-omk-at 2 (mv-nth 1 answer)) (fn-omk-at 2 row))
        (equal (fn-omk-at 3 (mv-nth 1 answer)) (fn-omk-at 3 row))
        (equal (fn-omk-at 4 (mv-nth 1 answer)) (fn-omk-at 4 row))
        (equal (fn-omk-at 5 (mv-nth 1 answer)) (fn-omk-at 5 row))
        (equal (fn-omk-at 7 (mv-nth 1 answer)) selected))))
 :hints (("Goal" :in-theory (e/d (fn-ric-custody-bind-query fn-omk-at)
                                (fn-ibp-query-tokenp fn-omk-widthp))))
 :rule-classes nil)
