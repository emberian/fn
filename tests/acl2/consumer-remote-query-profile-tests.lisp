(in-package "ACL2")
(include-book "../../books/consumer-remote-query-profile-model")
; Reachable positive: both current source coordinates and the entire lookup
; conclusion hold. A nonmatching first row yields; first matching row wins.
(assert-event
 (let* ((key '(:query-policy-current 1 2))
        (rows '(("other" "" "" 3) ("max-consumer-query-groups" "" "" 65536)
                ("max-consumer-query-groups" "" "" 1)))
        (s (fn-crp-state key rows 20000000 :lookup nil))
        (a (fn-crp-tick s key 20000000))
        (s2 (cadr a)) (b (fn-crp-tick s2 key 20000000)))
  (and (equal key (fn-cp-nth 1 s)) (equal 20000000 (fn-cp-nth 3 s))
       (equal (fn-crpm-answer a) (fn-crpm-observe s))
       (eq (car a) :yield) (eq (car b) :ready)
       (equal (fn-crp-finish (cadr b) key 20000000)
              (fn-crp-policy-verdict 65536 20000000)))))
; Hypothesis removal: each retained hypothesis is affirmed, the omitted
; current key / record ceiling differs, and the lookup conclusion fails.
(assert-event
 (let* ((s (fn-crp-state '(1 2) '(("max-consumer-query-groups" "" "" 2)) 1000 :lookup nil))
        (key '(1 3)))
  (and (not (equal key (fn-cp-nth 1 s))) (equal 1000 (fn-cp-nth 3 s))
       (not (equal (fn-crpm-answer (fn-crp-tick s key 1000)) (fn-crpm-observe s))))))
(assert-event
 (let* ((key '(1 2)) (s (fn-crp-state key '(("max-consumer-query-groups" "" "" 2)) 1000 :lookup nil)))
  (and (equal key (fn-cp-nth 1 s)) (not (equal 1001 (fn-cp-nth 3 s)))
       (not (equal (fn-crpm-answer (fn-crp-tick s key 1001)) (fn-crpm-observe s))))))
; Codec/record theorem positive and omitted antecedent witness.
(assert-event
 (let* ((g 65536) (r 20000000) (p (fn-crp-policy-verdict g r)))
  (and (eq (fn-cp-nth 0 p) :query-policy) (posp g) (fn-cp-uintp g) (fn-frame-spec-listp (fn-cr-spec g))
       (<= (fn-frame-specs-width (fn-cr-spec g)) *fn-frame-max-payload*)
       (natp r) (<= (fn-crp-event-ceiling g) r)
       (equal (fn-cp-nth 1 p) g) (equal (fn-cp-nth 2 p) (fn-cr-read-bound g)))))
(assert-event
 (let* ((g 0) (r 1000) (p (fn-crp-policy-verdict g r)))
  (and (not (eq (fn-cp-nth 0 p) :query-policy))
       (not (and (posp g) (fn-cp-uintp g) (fn-frame-spec-listp (fn-cr-spec g))
          (<= (fn-frame-specs-width (fn-cr-spec g)) *fn-frame-max-payload*)
          (natp r) (<= (fn-crp-event-ceiling g) r)
          (equal (fn-cp-nth 1 p) g) (equal (fn-cp-nth 2 p) (fn-cr-read-bound g)))))))
(assert-event
 (and (equal (fn-crp-tick (fn-crp-state '(1) nil 1000 :lookup nil) '(1) 1000)
             '(:unavailable :consumer-query-limit))
      (equal (fn-crp-policy-verdict 0 1000) '(:refused :consumer-query-count))
      (equal (fn-crp-policy-verdict 4294967295 2000000000000)
             '(:refused :consumer-query-fncr-width))
      (equal (fn-crp-policy-verdict 2 809) '(:refused :consumer-query-record-width))
      (equal (fn-crp-config-proposal 2 1000)
             (list :config-proposal (fn-cfg-set-limit "max-consumer-query-groups" 2)))
      (equal (fn-crp-runtime-verdict (fn-crp-policy-verdict 2 1000))
             '(:unavailable :consumer-query-runtime-representation))))
; Existing typed C grammar carries the required dimension without a profile
; format change. This is serialization evidence, not durable acceptance.
(assert-event
 (let ((record (fn-cfg-record-make 0 0 1
                (list (cadr (fn-crp-config-proposal 2 1000))) *fn-cfg-default-stamp*)))
  (and (fn-cfg-recordp record)
       (equal (fn-cfg-decode-exact (fn-cfg-encode record)) (list :ok record nil)))))

; A large Store event ceiling does not invent an article report ceiling.
(assert-event
 (eq (car (fn-crp-policy-verdict 1 4294967295)) :query-policy))
