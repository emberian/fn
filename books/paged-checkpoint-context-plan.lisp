; The host's stripped metadata context plans the same publication.
(in-package "ACL2")
(include-book "paged-checkpoint-host")
(include-book "paged-checkpoint-context")

(defthm fn-pck-publish-plan-at-context-congruence
  (implies (fn-pck-context-agreep a b)
           (equal (fn-pck-publish-plan-at cnt tail tree delta base a)
                  (fn-pck-publish-plan-at cnt tail tree delta base b)))
  :rule-classes nil
  :hints (("Goal" :use (:instance fn-pck-context-rows-congruence (recs delta))
           :in-theory (union-theories '(fn-pck-publish-plan-at fn-pck-dirty-at)
                                      (theory 'minimal-theory)))))

(defthm fn-pck-publish-plan-at-context-is-the-plan
  ; The summary plan is the model plan: CNT and TAIL are those of the prefix's
  ; tape, TREE is the root of the live capture extended by the delta.
  (let ((w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix))))
    (implies (and (equal cnt (len w))
                  (equal tail (nthcdr (* *pgs-page-words* (floor (len w) *pgs-page-words*)) w))
                  (true-listp delta)
                  (equal base (fn-pck-plen prefix 0))
                  (fn-pck-context-agreep st (fn-pck-st-of (fn-pck-seed) prefix))
                  (equal c (fn-sco-capture configs prefix))
                  (equal tree (fn-pck-root-tree-of-capture (fn-sco-extend c configs delta)
                                                            (fn-pck-f configs (append prefix delta))
                                                            (fn-pck-plen (append prefix delta) 0))))
             (equal (fn-pck-publish-plan-at cnt tail tree delta base st)
                    (fn-pck-publish-plan configs prefix delta))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pck-publish-plan-at-is-the-plan
                                  (st (fn-pck-st-of (fn-pck-seed) prefix)))
                        (:instance fn-pck-publish-plan-at-context-congruence
                                   (a st) (b (fn-pck-st-of (fn-pck-seed) prefix))))
           :in-theory (theory 'minimal-theory))))
