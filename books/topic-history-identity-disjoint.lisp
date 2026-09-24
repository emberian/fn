; A topic Store event cannot enter any of the three identity replay arms.
; These facts expose only the first field of the generated records.  The
; payload codecs remain closed in composed Store transition proofs.
(in-package "ACL2")
(include-book "store-events")

(defthm fn-th-topic-event-has-topic-tag
  (implies (fn-th-topic-eventp event)
           (member-equal (car event)
                         '(:topic-admin-install :topic-anchor :topic-admit)))
  :hints (("Goal" :in-theory (enable fn-th-topic-eventp
                                     fn-th-local-admin-eventp fn-th-at))))

(defthm fn-th-topic-event-is-not-stxk
  (implies (fn-th-topic-eventp event)
           (not (fn-stxk-p event)))
  :hints (("Goal" :in-theory (enable fn-th-topic-eventp
                                     fn-stxk-p fn-stxk-shapep
                                     fn-stxk-sequence))))

(defthm fn-th-topic-event-is-not-stxe
  (implies (fn-th-topic-eventp event)
           (not (fn-stxe-p event)))
  :hints (("Goal" :in-theory (enable fn-th-topic-eventp
                                     fn-stxe-p fn-stxe-shapep
                                     fn-stxe-sequence))))

(defthm fn-th-topic-event-is-not-stxa
  (implies (fn-th-topic-eventp event)
           (not (fn-stxa-p event)))
  :hints (("Goal" :in-theory (enable fn-th-topic-eventp
                                     fn-stxa-p fn-stxa-shapep
                                     fn-stxa-sequence))))
