; The frozen relay-v1 branch and its exact reclaim residual. Component of
; PRF-1108; the served comparator is not switched by including this book.
(in-package "ACL2")
(include-book "acceptance-binding")
(include-book "store-reclaim")

(defun fn-abr-action (binding offered groups held held-groups)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-rcl-payload-profilep)))))
  (cond ((not (fn-ab-p binding)) :invalid-binding)
        ((not (equal (fn-ab-profile binding) :relay-v1)) :unsupported-binding)
        ((not (fn-rcl-payload-profilep offered)) :invalid-subject)
        ((not (equal groups held-groups)) :conflict)
        ((fn-rcl-tombstonep held)
         (if (equal (fn-asj-subject offered) (fn-rcl-tomb-article-subject held))
             :duplicate :conflict))
        (t (if (equal (fn-asj-project offered) (fn-asj-project held))
               :duplicate :conflict))))

; A difference of exact projections with one typed commitment. This names
; the residual rather than assuming digest injectivity. A-CRYPTO describes
; BLAKE3-256 generic collision work (~2^128), not exact removed bytes.
(defun fn-abr-collisionp (offered held)
  (declare (xargs :guard (and (fn-rcl-payload-profilep offered)
                            (fn-rcl-payload-profilep held))
                  :guard-hints (("Goal" :in-theory (enable fn-rcl-payload-profilep)))))
  (and (not (equal (fn-asj-project offered) (fn-asj-project held)))
       (equal (fn-asj-subject offered) (fn-asj-subject held))))

(defthm fn-abr-reclaim-preserves-decision-or-selected-collision
  (implies (not (fn-rcl-tombstonep held))
           (or (equal (fn-abr-action binding offered groups held held-groups)
                      (fn-abr-action binding offered groups
                       (fn-rcl-tombstone-of held msgid) held-groups))
               (and (fn-ab-p binding)
                    (equal (fn-ab-profile binding) :relay-v1)
                    (equal groups held-groups)
                    (fn-abr-collisionp offered held))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-abr-action fn-abr-collisionp)
                (fn-ab-p fn-ab-profile fn-rcl-payload-profilep
                 fn-asj-project fn-asj-subject fn-rcl-tombstonep
                 fn-rcl-tombstone-of fn-rcl-tomb-article-subject))
                  :use ((:instance fn-rcl-tombstone-of-fields (payload held))
                        (:instance fn-asj-subject-of-equal-projections-by-definition
                                   (w offered) (w2 held))))))

(in-theory (disable fn-abr-action fn-abr-collisionp))
