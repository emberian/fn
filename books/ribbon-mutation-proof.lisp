(in-package "ACL2")
(include-book "ribbon")

(local
 (defthm fn2-ribbon-common-prefix-injective
   (equal (equal (append prefix a) (append prefix b)) (equal a b))
   :hints (("Goal" :induct (append prefix a)))))

(defthm fn2-ribbon-integrity-distinguishes-pages
  (implies (and (fn2-ribbon-page-integrity-premise before after)
                (not (equal before after)))
           (not (equal (fn-blake3 (fn2-fc-covered :page before nil))
                       (fn-blake3 (fn2-fc-covered :page after nil)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-a-integrity-evidence-sound
                          (expected (fn2-fc-covered :page before nil))
                          (observed (fn2-fc-covered :page after nil))))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn2-ribbon-page-integrity-premise fn2-fc-covered
                         fn2-ribbon-common-prefix-injective
                         (:executable-counterpart equal)
                         (:executable-counterpart binary-append)
                         binary-append)))))
