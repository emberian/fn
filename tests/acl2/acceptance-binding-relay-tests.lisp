; PRF-1108 relay branch component: complete literal theorem witnesses.
(in-package "ACL2")
(include-book "../../books/acceptance-binding-relay")
(include-book "article-subject-tests")
(include-book "acceptance-binding-tests")

(defconst *abrt-msgid* '(60 114 101 108 97 121 64 97 114 116 105 99 108 101 46 105 110 118 97 108 105 100 62))

; Positive: nonempty original/relay variant, complete sole antecedent and
; first disjunct of the conclusion. The original bytes really differ.
(assert-event
 (and (fn-rcl-tombstonep (fn-rcl-tombstone-of *asjt-wire* *abrt-msgid*))
      (not (fn-rcl-tombstonep *asjt-wire*))
      (not (equal *asjt-other* *asjt-wire*))
      (fn-ab-p *abt-relay*)
      (equal (fn-abr-action *abt-relay* *asjt-other* '("g") *asjt-wire* '("g")) :duplicate)
      (equal (fn-abr-action *abt-relay* *asjt-other* '("g") *asjt-wire* '("g"))
             (fn-abr-action *abt-relay* *asjt-other* '("g")
              (fn-rcl-tombstone-of *asjt-wire* *abrt-msgid*) '("g")))))

; Changed protected bytes and changed groups are conflicts on both sides.
(assert-event
 (and (not (fn-rcl-tombstonep *asjt-wire*))
      (equal (fn-abr-action *abt-relay* *asjt-body-change* '("g") *asjt-wire* '("g")) :conflict)
      (equal (fn-abr-action *abt-relay* *asjt-body-change* '("g") *asjt-wire* '("g"))
             (fn-abr-action *abt-relay* *asjt-body-change* '("g")
              (fn-rcl-tombstone-of *asjt-wire* *abrt-msgid*) '("g")))
      (equal (fn-abr-action *abt-relay* *asjt-other* '("different") *asjt-wire* '("g")) :conflict)
      (equal (fn-abr-action *abt-relay* *asjt-other* '("different")
              (fn-rcl-tombstone-of *asjt-wire* *abrt-msgid*) '("g")) :conflict)))

; Hypothesis removal: a tombstone is not live article content. Reclaiming a
; tombstone AGAIN binds its marker bytes instead of the removed article.
(assert-event
 (let ((held (fn-rcl-tombstone-of *asjt-wire* *abrt-msgid*)))
   (and (fn-rcl-tombstonep held)
        (not (or
              (equal (fn-abr-action *abt-relay* *asjt-other* '("g") held '("g"))
                     (fn-abr-action *abt-relay* *asjt-other* '("g")
                      (fn-rcl-tombstone-of held *abrt-msgid*) '("g")))
              (and (fn-ab-p *abt-relay*)
                   (equal (fn-ab-profile *abt-relay*) :relay-v1)
                   (equal '("g") '("g"))
                   (fn-abr-collisionp *asjt-other* held)))))))

; Invalid bindings never silently select relay or D25. An explicit other
; profile is dispatched elsewhere, and never ORed with this branch.
(assert-event
 (and (equal (fn-abr-action nil *asjt-other* '("g") *asjt-wire* '("g")) :invalid-binding)
      (equal (fn-abr-action *abt-post* *asjt-other* '("g") *asjt-wire* '("g")) :unsupported-binding)
      (equal (fn-abr-action *abt-native* *asjt-other* '("g") *asjt-wire* '("g")) :unsupported-binding)))

; Collision realization satisfies the existing digest seam constraints. It
; is a mutation witness for the residual, not evidence about real BLAKE3.
(defun abrt-colliding-digest (x)
  (declare (xargs :guard t) (ignore x))
  (make-list 32 :initial-element 0))
(defattach fn-frame-digest abrt-colliding-digest)
(assert-event
 (and (not (fn-rcl-tombstonep *asjt-wire*))
      (fn-ab-p *abt-relay*)
      (equal (fn-ab-profile *abt-relay*) :relay-v1)
      (equal '("g") '("g"))
      (fn-abr-collisionp *asjt-body-change* *asjt-wire*)
      (equal (fn-abr-action *abt-relay* *asjt-body-change* '("g") *asjt-wire* '("g")) :conflict)
      (equal (fn-abr-action *abt-relay* *asjt-body-change* '("g")
              (fn-rcl-tombstone-of *asjt-wire* *abrt-msgid*) '("g")) :duplicate)))
(defattach fn-frame-digest fn-blake3)
