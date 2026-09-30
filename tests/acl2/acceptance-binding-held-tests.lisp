(in-package "ACL2")
(include-book "../../books/acceptance-binding-held")
(include-book "../../books/crypto-attach")

; Descriptors come from the actual received-octet producer at execution,
; never from a fixture-wide default digest.  Stored bytes deliberately differ.
(defconst *fn-abht-received* '(65 13 10))
(defconst *fn-abht-stored* '(66 13 10))
(defun fn-abht-row (binding)
  (declare (xargs :guard t))
  (fn-held-plain
   (fn-record-make 1 2 3 "<a>" *fn-abht-stored* '("g") "o" "s" "e" 4 5 binding)
   0))

(assert-event
 (let* ((b (fn-ab-for-received :relay-v1 *fn-abht-received*))
        (h (fn-abht-row b)))
   (mv-let (article binding) (fn-ab-held-projections h)
     (and (fn-ab-p b) (fn-held-p h)
          (equal (fn-ab-held-binding-action "<a>" b h) :same-binding)
          (equal article (fn-make-article "<a>" 0 '("g") nil t 5))
          (equal binding b)))))

; Same received octets and stored row, different typed profile: conflict.
; A native profile claim is tested as evidence, not as authority.
(assert-event
 (let* ((b (fn-ab-for-received :relay-v1 *fn-abht-received*))
        (other (fn-ab-for-received :native-source *fn-abht-received*))
        (h (fn-abht-row b)))
   (and (fn-ab-p b) (fn-ab-p other) (fn-held-p h)
        (equal (fn-ab-received-subject b) (fn-ab-received-subject other))
        (not (equal b other))
        (equal (fn-ab-held-binding-action "<a>" other h) :conflict))))

(assert-event
 (let* ((b (fn-ab-for-received :relay-v1 *fn-abht-received*))
        (other (fn-ab-for-received :relay-v1 '(67 13 10)))
        (h (fn-abht-row b)))
   (and (fn-ab-p b) (fn-ab-p other) (fn-held-p h)
        (not (equal b other))
        (equal (fn-ab-held-binding-action "<a>" other h) :conflict))))

; Historical acceptance survives withdrawal and redecision metadata changes.
(assert-event
 (let* ((b (fn-ab-for-received :relay-v1 *fn-abht-received*))
        (h (fn-abht-row b))
        (withdrawn (fn-held-with-withdrawn h '(1 . 0)))
        (redecided (fn-held-with-context h
                    (fn-hc-make (fn-stx-make-verdict :absent nil 1) nil 1))))
   (mv-let (withdrawn-article withdrawn-binding) (fn-ab-held-projections withdrawn)
     (declare (ignore withdrawn-article))
     (mv-let (redecided-article redecided-binding) (fn-ab-held-projections redecided)
       (declare (ignore redecided-article))
       (and (fn-held-p h) (fn-held-p withdrawn) (fn-held-p redecided)
            (equal (fn-ab-held-binding-action "<a>" b withdrawn) :same-binding)
            (equal (fn-ab-held-binding-action "<a>" b redecided) :same-binding)
            (equal withdrawn-binding b)
            (equal redecided-binding b))))))

; Corrupted descriptor and index/row association are recovery conditions.
(assert-event
 (let* ((b (fn-ab-for-received :relay-v1 *fn-abht-received*))
        (h (fn-abht-row b))
        (corrupt (update-nth 15 nil h)))
   (and (fn-ab-p b) (fn-held-p h) (not (fn-held-p corrupt))
        (equal (fn-ab-held-binding-action "<a>" b corrupt) :recovery-required)
        (equal (fn-ab-held-binding-action "<other>" b h) :recovery-required))))

(assert-event
 (let* ((b (fn-ab-for-received :relay-v1 *fn-abht-received*))
        (h (fn-abht-row b)))
   (and (fn-held-p h)
        (not (fn-ab-p nil))
        (equal (fn-ab-held-binding-action "<a>" nil h) :invalid-binding)
        (equal (fn-ab-held-binding-action "<a>" nil nil) :invalid-binding)
        (equal (fn-ab-held-binding-action "<a>" b nil) :absent)
        (not (fn-held-shapep (butlast h 1)))
        (null (fn-row-binding (butlast h 1))))))
