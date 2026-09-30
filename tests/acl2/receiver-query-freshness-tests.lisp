(in-package "ACL2")
(include-book "../../books/receiver-query-freshness")
(defthm fn-rqf-query-read-zero-fuel-positive-literal
 (let ((answer (fn-ibp-node-query-read '(:index-query 2 1 1 3)
                                     0 0 0 '(nil 0))))
  (and (natp 0) (natp 0)
       (equal answer (mv :yield nil nil nil 0))
       (natp (mv-nth 4 answer)) (<= (mv-nth 4 answer) 0)))
 :rule-classes nil)
(defthm fn-rqf-query-read-negative-fuel-removal-literal
 (let ((answer (fn-ibp-node-query-read '(:index-query 2 1 1 3)
                                     -1 0 0 '(nil 0))))
  (and (natp 0) (not (natp -1))
       (equal answer (mv :yield nil nil nil -1))
       (not (natp (mv-nth 4 answer)))))
 :rule-classes nil)
; Literal publication-coordinate models only. C=7 and F=19 deliberately
; differ; these are not actual durable publication or authority witnesses.
(defconst *fn-rqf-test-capture*
 '(:fn-ibp-capture 3 :key 2 7 19 :table 1 11 :rows 1 12))
(defconst *fn-rqf-test-publication*
 '(:index-publication 3 :key 2 7 19 :view :table 1 11 :rows 1 12
   :numbers 13 :completion :visibility 1 20))
(defthm fn-rqf-distinct-count-frontier-positive-literal
 (and (equal (fn-ibp-capture-count *fn-rqf-test-capture*) 7)
      (equal (fn-ibp-capture-frontier *fn-rqf-test-capture*) 19)
      (not (equal 7 19))
      (equal (fn-rqf-publication-status *fn-rqf-test-capture*
                                      *fn-rqf-test-publication*) :current))
 :rule-classes nil)
(defthm fn-rqf-new-catalog-count-same-frontier-stale-literal
 (let ((pub (update-nth 4 8 *fn-rqf-test-publication*)))
  (and (equal (fn-ipub-frontier pub) 19)
       (equal (fn-ipub-count pub) 8)
       (equal (fn-rqf-publication-status *fn-rqf-test-capture* pub)
              :recapture-required)))
 :rule-classes nil)
(defthm fn-rqf-new-row-identity-stale-literal
 (let ((pub (update-nth 12 14 *fn-rqf-test-publication*)))
  (and (equal (fn-ipub-count pub) 7)
       (equal (fn-ipub-frontier pub) 19)
       (equal (fn-ipub-row-id pub) 14)
       (equal (fn-rqf-publication-status *fn-rqf-test-capture* pub)
              :recapture-required)))
 :rule-classes nil)
(defthm fn-rqf-corrupted-frontier-refusal-literal
 (let ((pub (update-nth 5 :bad *fn-rqf-test-publication*)))
  (and (not (natp (fn-ipub-frontier pub)))
       (equal (fn-rqf-publication-status *fn-rqf-test-capture* pub)
              :unavailable)))
 :rule-classes nil)
