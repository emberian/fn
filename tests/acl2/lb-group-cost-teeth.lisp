; GROUP reads only its maintained summary, with a real legacy row-codec fault.
(in-package "ACL2")
(include-book "../../books/catalog-columns-command-cost")
(include-book "lb-column-read-cost-teeth")
(defun fn-lbcct-wasteful-group (group row-octets fn-lbc)
 (declare (xargs :stobjs fn-lbc
  :guard (and (< 0 (fn-lbc-count fn-lbc))
              (alistp (fn-lbc-escape-store-get 0 fn-lbc))
              (fn-scc-octet-listp row-octets)) :verify-guards nil))
 (list (fn-lbc-group-live group fn-lbc)
       (fn-lbc-render-nov 0 fn-lbc) (fn-scc-decode-tree row-octets)))
(def-cost fn-lbcct-wasteful-group
 :unaccounted (fn-lbc-render-nov fn-scc-decode-tree)
 :calls ((row-fetches (fn-lbc-render-nov)) (decodes (fn-scc-decode-tree))))
(defthm fn-lbcct-group-row-fetches-whole-witness
 (equal (fn-lbc-group-live-row-fetches "fn.test" (fn-lbcc-test-one-state)) 0) :rule-classes nil
 :hints (("Goal" :in-theory '(fn-lbc-group-live-row-fetches))))
(defthm fn-lbcct-group-row-fetches-fault-whole-witness
 (and (equal (fn-lbc-group-live-row-fetches "fn.test" (fn-lbcc-test-one-state)) 0) (not (equal (fn-lbcct-wasteful-group-row-fetches "fn.test" (fn-scc-encode (fn-cat-served-projection (fn-lbcc-test-decided-row))) (fn-lbcc-test-one-state)) 0))) :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-group-live-row-fetches fn-lbcct-wasteful-group-row-fetches)))))
(defteeth fn-lbc-group-live-zero-row-fetches
 :claim (nil (equal (fn-lbc-group-live-row-fetches group fn-lbc-v) 0))
 :subject fn-lbc-group-live
 :witness ((group "fn.test") (fn-lbc-v (fn-lbcc-test-one-state)))
 :witness-lemma fn-lbcct-group-row-fetches-whole-witness :breaks ()
 :mutations ((legacy-row-path
  (:conclusion (equal (fn-lbcct-wasteful-group-row-fetches group row-octets fn-lbc-v) 0))
  ((group "fn.test") (row-octets (fn-scc-encode (fn-cat-served-projection (fn-lbcc-test-decided-row))))
   (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "GROUP restores a full NOV fetch and the retired per-row tree decode"
  :lemma fn-lbcct-group-row-fetches-fault-whole-witness)))
(defthm fn-lbcct-group-decodes-whole-witness
 (equal (fn-lbc-group-live-decodes "fn.test" (fn-lbcc-test-one-state)) 0) :rule-classes nil
 :hints (("Goal" :in-theory '(fn-lbc-group-live-decodes))))
(defthm fn-lbcct-group-decodes-fault-whole-witness
 (and (equal (fn-lbc-group-live-decodes "fn.test" (fn-lbcc-test-one-state)) 0) (not (equal (fn-lbcct-wasteful-group-decodes "fn.test" (fn-scc-encode (fn-cat-served-projection (fn-lbcc-test-decided-row))) (fn-lbcc-test-one-state)) 0))) :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-group-live-decodes fn-lbcct-wasteful-group-decodes)))))
(defteeth fn-lbc-group-live-zero-decodes
 :claim (nil (equal (fn-lbc-group-live-decodes group fn-lbc-v) 0))
 :subject fn-lbc-group-live
 :witness ((group "fn.test") (fn-lbc-v (fn-lbcc-test-one-state)))
 :witness-lemma fn-lbcct-group-decodes-whole-witness :breaks ()
 :mutations ((legacy-row-path
  (:conclusion (equal (fn-lbcct-wasteful-group-decodes group row-octets fn-lbc-v) 0))
  ((group "fn.test") (row-octets (fn-scc-encode (fn-cat-served-projection (fn-lbcc-test-decided-row))))
   (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "GROUP restores a full NOV fetch and the retired per-row tree decode"
  :lemma fn-lbcct-group-decodes-fault-whole-witness)))
(defun fn-lbcct-native-summary-only-group-control ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (ok fn-lbc)
   (let* ((row (fn-lbcc-test-decided-row)) (view (fn-cat-served-projection row))
          (row-octets (fn-scc-encode view))
          (log (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil))
          (fn-lbc (fn-lbc-open-rebuild (list row) log fn-lbc))
          (mutant (fn-lbcct-wasteful-group "fn.test" row-octets fn-lbc)))
    (mv (and (equal (fn-lbc-group-live "fn.test" fn-lbc) '(1 1 1 2))
             (equal (nth 2 mutant) (list :ok view))) fn-lbc))
   ok)))
(with-guard-checking-event t (assert-event (fn-lbcct-native-summary-only-group-control)))
