(in-package "ACL2")
(include-book "connection-receiver-source")

(defthm fn-crx-accepted-association-is-readable
 (implies (equal (mv-nth 0 (fn-ich-rx-bind id holder origin segment))
                 :associated)
  (equal (fn-ich-rx-origin id holder
           (mv-nth 1 (fn-ich-rx-bind id holder origin segment)))
         (mv :current origin)))
 :hints (("Goal" :in-theory (enable fn-ich-rx-bind fn-ich-rx-origin
                                   fn-ich-row fn-omk-at fn-omk-widthp))))

(defthm fn-crx-bind-preserves-connection-custody
 (let ((next (mv-nth 1 (fn-ich-rx-bind id holder origin segment))))
  (and (equal (fn-ich-row token next) (fn-ich-row token segment))
       (equal (fn-ich-segment-id next) (fn-ich-segment-id segment))
       (equal (fn-ich-active next) (fn-ich-active segment))))
 :hints (("Goal" :in-theory (enable fn-ich-rx-bind fn-ich-row
                                   fn-omk-at fn-omk-widthp))))

(defthm fn-crx-current-turn-cannot-cross-connection
 (implies (fn-crx-turn-currentp issued id holder ticket capacity instance)
  (and (implies (not (equal other-id id))
                (not (fn-crx-turn-currentp issued other-id holder ticket capacity instance)))
       (implies (not (equal other-holder holder))
                (not (fn-crx-turn-currentp issued id other-holder ticket capacity instance)))
       (implies (not (equal other-ticket ticket))
                (not (fn-crx-turn-currentp issued id holder other-ticket capacity instance)))
       (implies (not (equal other-capacity capacity))
                (not (fn-crx-turn-currentp issued id holder ticket other-capacity instance)))
       (implies (not (equal other-instance instance))
                (not (fn-crx-turn-currentp issued id holder ticket capacity other-instance)))))
 :hints (("Goal" :in-theory (enable fn-crx-turn-currentp fn-crx-origin-currentp))))

(defthm fn-crx-revocation-blocks-new-acquisition
 (not (fn-crx-turn-currentp (fn-crx-revoke issued id holder)
                            id holder ticket capacity instance))
 :hints (("Goal" :in-theory (enable fn-crx-revoke fn-crx-turn-currentp
                                   fn-crx-origin-currentp fn-crx-originp
                                   fn-omk-at fn-omk-widthp))))
