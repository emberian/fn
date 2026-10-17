(in-package "ACL2")
(include-book "../../books/owner-authority-transitions")
(include-book "../../books/defkeystone")

(defteeth fn-oauth-publication-rejects-published-root
  :claim (((published (fn-cp-nth 3 full4)))
          (and (not (mv-nth 0 (fn-oauth-publication r full4 epoch)))
               (equal (mv-nth 1 (fn-oauth-publication r full4 epoch)) :recovery-required)
               (equal (mv-nth 3 (fn-oauth-publication r full4 epoch)) r)))
  :subject fn-oauth-publication
  :witness ((r '(old-carries old-root old-canonical))
            (full4 '(:durable next metadata unexpected-root)) (epoch 0))
  :breaks ((published ((r '(nil nil nil)) (full4 '(:durable nil metadata nil)) (epoch 0))))
  :mutations ((write-after-refusal (:conclusion
                (equal (mv-nth 3 (fn-oauth-publication r full4 epoch))
                       (fn-oauth-make (fn-cp-nth 2 full4) nil nil)))
              ((r '(old-carries old-root old-canonical))
               (full4 '(:durable next metadata unexpected-root)) (epoch 0))
              :fault "refusal must preserve all authority observations")))

(defteeth fn-oauth-publication-does-not-invent-root
  :claim (((absent (not (fn-oauth-root r))))
          (not (fn-oauth-root (mv-nth 3 (fn-oauth-publication r full4 epoch)))))
  :subject fn-oauth-publication
  :witness ((r '(nil nil nil)) (full4 '(:durable nil metadata nil)) (epoch 0))
  :breaks ((absent ((r '(nil (:ready 0 adopted 9 aliases footprint) nil))
                   (full4 '(:durable nil metadata nil)) (epoch 0))))
  :mutations ((nil-means-ready (:conclusion
                (equal (fn-oauth-root (mv-nth 3 (fn-oauth-publication r full4 epoch)))
                       '(:ready 0 nil 0 nil nil)))
              ((r '(nil nil nil)) (full4 '(:durable nil metadata nil)) (epoch 0))
              :fault "missing authority is unavailable, not ready-empty")))

; Exercise the successful readiness branch, alias retention, and mismatch.
(defconst *fn-oauth-test-next*
  (list (list (append (make-list 11 :initial-element nil)
                     (list '(nil nil nil nil nil nil (tag 12 nil adopted)))))))
(assert-event
 (mv-let (installp word next record)
   (fn-oauth-publication
    '(old (:ready 7 adopted 9 aliases footprint) (:ready canonical-tail))
    (list :durable *fn-oauth-test-next* 'metadata nil) 7)
   (and installp (equal word :durable) (equal next *fn-oauth-test-next*)
        (equal record '(metadata (:ready 7 adopted 12 aliases footprint)
                               (:unavailable canonical-tail))))))
(assert-event
 (mv-let (installp word next record)
   (fn-oauth-publication
    '(old (:ready 7 adopted 9 aliases footprint) (:ready canonical-tail))
    (list :durable *fn-oauth-test-next* 'metadata nil) 8)
   (and installp (equal word :durable) (equal next *fn-oauth-test-next*)
        (equal record '(metadata (:unavailable 7 adopted 9 aliases footprint)
                               (:unavailable canonical-tail))))))
(assert-event
 (equal (fn-oauth-put :canonical nil '(carries root canonical)) '(carries root nil)))
(defteeth-check (fn-oauth-publication-rejects-published-root
                fn-oauth-publication-does-not-invent-root))
