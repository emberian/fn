; The signed keystone over the concrete entries called by the checkpoint host.
(in-package "ACL2")
(include-book "history-image-concrete")
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-his-events-proper
  (implies (fn-hp-events-okp h) (true-listp h))
  :hints (("Goal" :induct (fn-hp-events-okp h) :in-theory (enable fn-hp-events-okp)))))

(local
 (defthm fn-his-holdable-proper
  (implies (fn-hp-okp h salt) (true-listp h))
  :hints (("Goal" :in-theory (e/d (fn-hp-okp) (fn-hp-events-okp fn-hp-image))))))

(local
 (defthm fn-his-suffix-empty
  (equal (fn-hrc-sfx-list 0 0 c) nil)
  :hints (("Goal" :in-theory (enable fn-hrc-sfx-list)))))

(defthm fn-his-image-build-c-is-canonical
  (implies (and (fn-hrecs$cp fn-hrecs$c) (natp salt) (fn-hp-okp h salt))
           (let* ((res (fn-his-image-build-c h salt fn-hrecs$c)) (c2 (mv-nth 1 res)))
             (and (equal (mv-nth 0 res) :ok)
                  (fn-hrc-wfp c2) (fn-hrs-rel h c2)
                  (equal (fn-hrc-img c2) 1)
                  (equal (fn-hrc-nimg c2) (len h))
                  (equal (fn-hrc-lo c2) (fn-hrc-hi c2))
                  (equal (fn-hrc-salt c2) salt)
                  (equal (fn-hrc-lens c2) (fn-hp-lens h salt))
                  (equal (fn-hrc-starts c2) (fn-hp-starts h salt))
                  (equal (fn-hrc-npages c2) (fn-hp-npages h salt))
                  (equal (pgs-w-length (fn-hrc-pgs c2)) (* 2048 (fn-hp-npages h salt)))
                  (equal (pgs-v-length (fn-hrc-pgs c2)) (fn-hp-npages h salt))
                  (equal (pgs-d-length (fn-hrc-pgs c2)) (fn-hp-npages h salt))
                  (fn-his-all-dirty 0 (fn-hp-npages h salt) (nth *pgs-di* (fn-hrc-pgs c2))))))
  :hints (("Goal" :do-not-induct t
           :use (fn-hp-placement-ok-of-image
                 (:instance fn-his-image-build-pgs-is-canonical-image
                    (pgs-mem (fn-hrc-pgs (fn-his-build-begin salt fn-hrecs$c)))))
           :in-theory (e/d (fn-hrc-wfp fn-hrs-rel fn-hrs-img-ok fn-hrc-sfx-list)
                           (fn-his-image-build-c fn-his-image-build-pgs fn-his-build-begin
                            fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                            fn-hp-piw fn-hp-piw-caps-extend fn-hp-iw fn-hp-vhold fn-his-all-dirty
                            fn-hrecs$cp fn-hrc-fields fn-hrc-updaters adt-placement-ok nth adt-nth-0 adt-nth-1+))))
  :rule-classes nil)

(defthm fn-his-image-build-c-refuses-unholdable
  (implies (and (fn-hrecs$cp fn-hrecs$c) (natp salt) (not (fn-hp-okp h salt)))
           (let ((res (fn-his-image-build-c h salt fn-hrecs$c)))
             (and (not (equal (mv-nth 0 res) :ok))
                  (not (equal (fn-hrc-img (mv-nth 1 res)) 1)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-his-image-build-c-refines-pgs
                 (:instance fn-his-image-build-pgs-refuses-unholdable
                    (pgs-mem (fn-hrc-pgs (fn-his-build-begin salt fn-hrecs$c)))))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)
