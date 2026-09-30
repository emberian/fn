; PRF-1115: actual nonempty node transitions across canonical handles.
(in-package "ACL2")
(include-book "../../books/snapshot-node-alpha")
(defconst *osa-source-arena* '((99) (1 2 3) (4 5)))
(defconst *osa-target-arena* '((1 2 3) (4 5)))
(defconst *osa-initial* (fn-node-initial-state '("fn.test") 20))
(defconst *osa-a-first*
  (fn-node-prepare *osa-initial* 0 "<one@example>" 1 '("fn.test")
                   "one" "subject-one" "evidence-one" 1 841000000))
(defconst *osa-b-first*
  (fn-node-prepare *osa-initial* 0 "<one@example>" 0 '("fn.test")
                   "one" "subject-one" "evidence-one" 1 841000000))
(defconst *osa-a* (fn-node-complete *osa-a-first* 0 0 :durable))
(defconst *osa-b* (fn-node-complete *osa-b-first* 0 0 :durable))
(defconst *osa-a-next*
  (fn-node-prepare *osa-a* 1 "<two@example>" 2 '("fn.test")
                   "two" "subject-two" "evidence-two" 1 841000001))
(defconst *osa-b-next*
  (fn-node-prepare *osa-b* 1 "<two@example>" 1 '("fn.test")
                   "two" "subject-two" "evidence-two" 1 841000001))

; Every literal preparation hypothesis, with a prior committed ARTICLE and
; a newly staged second ARTICLE. The handles differ on both articles.
(defthm osa-node-prepare-alpha-positive-tooth
  (and (fn-node-statep *osa-a*) (fn-node-statep *osa-b*)
       (consp (fn-state-articles (fn-node-acceptance *osa-a*)))
       (consp (fn-node-stage *osa-a-next*))
       (not (equal *osa-a* *osa-b*))
       (equal (fn-osa-node-alpha *osa-a* *osa-source-arena*)
              (fn-osa-node-alpha *osa-b* *osa-target-arena*))
       (natp 2) (natp 1)
       (equal (fn-handle-bytes 2 *osa-source-arena*)
              (fn-handle-bytes 1 *osa-target-arena*))
       (equal (fn-osa-node-alpha *osa-a-next* *osa-source-arena*)
              (fn-osa-node-alpha *osa-b-next* *osa-target-arena*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osa-node-alpha fn-osa-acceptance-alpha
                                     fn-osa-pending-alpha fn-articles-wire-of
                                     fn-handle-bytes))))

; All literal completion hypotheses; accepted, aborted and uncertain results
; are compared independently and the second accepted ARTICLE is present.
(defthm osa-node-complete-alpha-positive-tooth
  (and (fn-node-statep *osa-a-next*) (fn-node-statep *osa-b-next*)
       (consp (fn-node-stage *osa-a-next*))
       (equal (fn-osa-node-alpha *osa-a-next* *osa-source-arena*)
              (fn-osa-node-alpha *osa-b-next* *osa-target-arena*))
       (equal (fn-osa-node-alpha (fn-node-complete *osa-a-next* 1 1 :durable) *osa-source-arena*)
              (fn-osa-node-alpha (fn-node-complete *osa-b-next* 1 1 :durable) *osa-target-arena*))
       (equal (fn-osa-node-alpha (fn-node-complete *osa-a-next* 1 1 :aborted) *osa-source-arena*)
              (fn-osa-node-alpha (fn-node-complete *osa-b-next* 1 1 :aborted) *osa-target-arena*))
       (equal (fn-osa-node-alpha (fn-node-complete *osa-a-next* 1 1 :indeterminate) *osa-source-arena*)
              (fn-osa-node-alpha (fn-node-complete *osa-b-next* 1 1 :indeterminate) *osa-target-arena*))
       (equal (len (fn-state-articles
                    (fn-node-acceptance (fn-node-complete *osa-a-next* 1 1 :durable)))) 2))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osa-node-alpha fn-osa-acceptance-alpha
                                     fn-osa-pending-alpha fn-articles-wire-of
                                     fn-handle-bytes))))

; Physical-payload-map hypothesis removal: both nodes and all initial alpha
; fields agree, both offered handles are naturals, but the newly referenced
; target bytes differ. Every retained hypothesis is affirmative.
(defthm osa-node-prepare-wrong-payload-map-tooth
  (and (fn-node-statep *osa-a*) (fn-node-statep *osa-b*)
       (equal (fn-osa-node-alpha *osa-a* *osa-source-arena*)
              (fn-osa-node-alpha *osa-b* '((1 2 3) (7))))
       (natp 2) (natp 1)
       (not (equal (fn-handle-bytes 2 *osa-source-arena*)
                   (fn-handle-bytes 1 '((1 2 3) (7)))))
       (not (equal (fn-osa-node-alpha *osa-a-next* *osa-source-arena*)
                   (fn-osa-node-alpha *osa-b-next* '((1 2 3) (7))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osa-node-alpha fn-osa-acceptance-alpha
                                     fn-osa-pending-alpha fn-articles-wire-of
                                     fn-handle-bytes))))
