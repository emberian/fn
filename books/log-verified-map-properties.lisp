; LB vmap membership and MOVE authorization; owner C.
; LC owns allocator/lifetime ID proofs; these use its unchanged predicate.
(in-package "ACL2")
(include-book "catalog-columns-served")
(include-book "lb-log-layout")


(defun fn-lb-vmap-keys-in-segs-p (keys log)
 (declare (xargs :guard (alistp (remove-equal nil (true-list-fix log))) :verify-guards nil))
 (if (consp keys)
  (and (consp (car keys)) (fn-lb-log-model-segment (caar keys) log)
       (fn-lb-vmap-keys-in-segs-p (cdr keys) log))
  t))

(verify-guards fn-lb-vmap-keys-in-segs-p)

(local (defthm fn-lb-authenticated-entry-has-segment
 (implies (fn-arx-entry-ok (fn-lb-entry-octets seg entry log)
                          (fn-lb-entry-protected-len seg entry log))
  (fn-lb-log-model-segment seg log))
 :hints (("Goal" :cases ((fn-lb-log-model-segment seg log))
  :in-theory (e/d (fn-lb-entry-octets fn-lb-entry-protected-len fn-arx-entry-ok)
   (fn-lb-log-model-segment fn-lb-log-model-read-range fn-blake3-stobj))))))

(local (defthm fn-lb-vmap-bits-put-index-frame
 (equal (fn-lb-vmap-index (fn-lb-vmap-bits-put key val fn-lb-vmap))
        (fn-lb-vmap-index fn-lb-vmap))
 :hints (("Goal" :in-theory (enable fn-lb-vmap-index fn-lb-vmap-bits-put)))))

(local (defthm fn-lb-vmap-bits-put-raw-index-frame
 (equal (nth *fn-lb-vmap-index* (fn-lb-vmap-bits-put key val fn-lb-vmap))
        (nth *fn-lb-vmap-index* fn-lb-vmap))
 :hints (("Goal" :use fn-lb-vmap-bits-put-index-frame
  :in-theory (e/d (fn-lb-vmap-index) (fn-lb-vmap-bits-put fn-lb-vmap-bits-put-index-frame))))))

(local (defthm fn-lb-vmap-mark-index-effect
 (equal (fn-lb-vmap-index (fn-lb-vmap-mark seg entry log fn-lb-vmap))
  (if (and (fn-arx-entry-ok (fn-lb-entry-octets seg entry log)
                           (fn-lb-entry-protected-len seg entry log))
           (not (fn-lb-verified-bit seg entry fn-lb-vmap)))
   (cons (cons seg entry) (fn-lb-vmap-index fn-lb-vmap))
   (fn-lb-vmap-index fn-lb-vmap)))
 :hints (("Goal" :in-theory (e/d (fn-lb-vmap-mark update-fn-lb-vmap-index fn-lb-vmap-index)
  (fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len fn-lb-verified-bit fn-lb-vmap-bits-put fn-lb-vmap-p))))))

(defthm fn-lb-vmap-mark-preserves-keys-in-segs
 (implies (fn-lb-vmap-keys-in-segs-p (fn-lb-vmap-index fn-lb-vmap) log)
  (fn-lb-vmap-keys-in-segs-p (fn-lb-vmap-index (fn-lb-vmap-mark seg entry log fn-lb-vmap)) log))
 :hints (("Goal" :in-theory (e/d (fn-lb-vmap-keys-in-segs-p)
  (fn-lb-vmap-index fn-lb-vmap-mark fn-arx-entry-ok fn-lb-entry-octets
   fn-lb-entry-protected-len fn-lb-verified-bit fn-lb-log-model-segment)))))

(defthm fn-lb-vmap-new-key-segment-is-in-log
 (implies (and (member-equal key (fn-lb-vmap-index (fn-lb-vmap-mark seg entry log fn-lb-vmap)))
               (not (member-equal key (fn-lb-vmap-index fn-lb-vmap))))
  (fn-lb-log-model-segment (car key) log))
 :hints (("Goal" :in-theory (e/d (member-equal)
  (fn-lb-vmap-index fn-lb-vmap-mark fn-arx-entry-ok fn-lb-entry-octets
   fn-lb-entry-protected-len fn-lb-verified-bit fn-lb-log-model-segment)))))

(local (defthm fn-lb-segment-allocated-when-found
 (implies (and (fn-lc-seg-ids-allocatedp log next-id exhaustedp)
               (fn-lb-log-model-segment seg log))
  (fn-lc-id-allocatedp seg next-id exhaustedp))
 :hints (("Goal" :induct (fn-lb-log-model-segment seg log)
  :in-theory (e/d (fn-lb-log-model-segment fn-lc-seg-ids-allocatedp) (fn-lc-id-allocatedp))))))

(defthm fn-lb-vmap-mark-preserves-segment-ids-below-next
 (implies (fn-lc-segment-ids-below-next next-id exhaustedp log (fn-lb-vmap-index fn-lb-vmap))
  (fn-lc-segment-ids-below-next next-id exhaustedp log
    (fn-lb-vmap-index (fn-lb-vmap-mark seg entry log fn-lb-vmap))))
 :hints (("Goal" :in-theory (e/d (fn-lc-segment-ids-below-next fn-lc-key-ids-allocatedp)
  (fn-lc-seg-ids-allocatedp fn-lc-id-allocatedp fn-lb-vmap-index fn-lb-vmap-mark
   fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len fn-lb-verified-bit
   fn-lb-log-model-segment)))))

(local (defthm fn-lb-vmap-bits-put-bit-effect
 (equal (fn-lb-verified-bit seg entry (fn-lb-vmap-bits-put key val fn-lb-vmap))
  (if (equal (cons seg entry) key) (equal val t) (fn-lb-verified-bit seg entry fn-lb-vmap)))
 :hints (("Goal" :in-theory (enable fn-lb-verified-bit fn-lb-vmap-bits-get fn-lb-vmap-bits-put hons-assoc-equal)))))

(local (defthm fn-lb-vmap-index-update-bit-frame
 (equal (fn-lb-verified-bit seg entry (update-fn-lb-vmap-index keys fn-lb-vmap))
        (fn-lb-verified-bit seg entry fn-lb-vmap))
 :hints (("Goal" :in-theory (enable fn-lb-verified-bit fn-lb-vmap-bits-get update-fn-lb-vmap-index)))))

(local (defthm fn-lb-vmap-raw-index-update-bit-frame
 (equal (fn-lb-verified-bit seg entry (update-nth *fn-lb-vmap-index* keys fn-lb-vmap))
        (fn-lb-verified-bit seg entry fn-lb-vmap))
 :hints (("Goal" :use fn-lb-vmap-index-update-bit-frame
  :in-theory (e/d (update-fn-lb-vmap-index)
   (fn-lb-verified-bit fn-lb-vmap-index-update-bit-frame))))))

(defthm fn-lb-vmap-mark-bit-effect
 (equal (fn-lb-verified-bit seg entry (fn-lb-vmap-mark oldseg oldentry log fn-lb-vmap))
  (if (and (equal (cons seg entry) (cons oldseg oldentry))
           (fn-arx-entry-ok (fn-lb-entry-octets oldseg oldentry log)
                            (fn-lb-entry-protected-len oldseg oldentry log)))
   t (fn-lb-verified-bit seg entry fn-lb-vmap)))
 :hints (("Goal" :in-theory (e/d (fn-lb-vmap-mark)
  (fn-lb-verified-bit fn-lb-vmap-bits-put fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len)))))

(defthm fn-lb-vmap-index-covers-lookup
 (implies (and (fn-lb-vmap-index-covers bits keys)
               (equal (cdr (hons-assoc-equal key bits)) t))
  (member-equal key keys))
 :hints (("Goal" :induct (fn-lb-vmap-index-covers bits keys)
  :in-theory (enable fn-lb-vmap-index-covers hons-assoc-equal))))

(local (defthm fn-lb-allocated-key-member
 (implies (and (fn-lc-key-ids-allocatedp keys next-id exhaustedp) (member-equal key keys))
  (fn-lc-id-allocatedp (car key) next-id exhaustedp))
 :hints (("Goal" :induct (fn-lc-key-ids-allocatedp keys next-id exhaustedp)
  :in-theory (e/d (fn-lc-key-ids-allocatedp member-equal) (fn-lc-id-allocatedp))))))

(defthm fn-lb-vmap-next-id-unmarked
 (implies (and (fn-lc-segment-ids-below-next next-id exhaustedp log (fn-lb-vmap-index fn-lb-vmap))
               (not exhaustedp)
               (fn-lb-vmap-index-covers (nth *fn-lb-vmap-bits* fn-lb-vmap) (fn-lb-vmap-index fn-lb-vmap)))
  (not (fn-lb-verified-bit next-id entry fn-lb-vmap)))
 :hints (("Goal" :use ((:instance fn-lb-vmap-index-covers-lookup
                        (bits (nth *fn-lb-vmap-bits* fn-lb-vmap))
                        (keys (fn-lb-vmap-index fn-lb-vmap)) (key (cons next-id entry)))
                      (:instance fn-lb-allocated-key-member
                        (keys (fn-lb-vmap-index fn-lb-vmap)) (key (cons next-id entry))))
  :in-theory (e/d (fn-lc-segment-ids-below-next fn-lc-id-allocatedp fn-lb-verified-bit fn-lb-vmap-bits-get)
   (fn-lc-key-ids-allocatedp fn-lc-seg-ids-allocatedp fn-lb-vmap-index-covers
    fn-lb-vmap-index hons-assoc-equal fn-lb-vmap-index-covers-lookup fn-lb-allocated-key-member)))))

(local (defthm fn-lb-next-id-has-no-segment
 (implies (fn-lc-seg-ids-allocatedp log next-id nil)
  (not (fn-lb-log-model-segment next-id log)))
 :hints (("Goal" :use ((:instance fn-lb-segment-allocated-when-found (seg next-id) (exhaustedp nil)))
  :in-theory (e/d (fn-lc-id-allocatedp)
   (fn-lb-segment-allocated-when-found fn-lc-seg-ids-allocatedp fn-lb-log-model-segment))))))

(local (defthm fn-lb-next-id-cannot-authenticate-before-allocation
 (implies (fn-lc-seg-ids-allocatedp log next-id nil)
  (not (fn-arx-entry-ok (fn-lb-entry-octets next-id entry log)
                        (fn-lb-entry-protected-len next-id entry log))))
 :hints (("Goal" :use ((:instance fn-lb-authenticated-entry-has-segment (seg next-id)))
  :in-theory (disable fn-lb-authenticated-entry-has-segment fn-lc-seg-ids-allocatedp
    fn-lb-log-model-segment fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len)))))

(defthm fn-lb-vmap-old-mark-cannot-mark-next-id
 (implies (and (fn-lc-segment-ids-below-next next-id exhaustedp oldlog (fn-lb-vmap-index fn-lb-vmap))
               (not exhaustedp)
               (fn-lb-vmap-index-covers (nth *fn-lb-vmap-bits* fn-lb-vmap) (fn-lb-vmap-index fn-lb-vmap)))
  (not (fn-lb-verified-bit next-id entry (fn-lb-vmap-mark oldseg oldentry oldlog fn-lb-vmap))))
 :hints (("Goal"
  :use ((:instance fn-lb-vmap-next-id-unmarked (log oldlog))
        (:instance fn-lb-authenticated-entry-has-segment (seg oldseg) (entry oldentry) (log oldlog))
        (:instance fn-lb-segment-allocated-when-found (seg oldseg) (log oldlog)))
  :in-theory (e/d (fn-lc-segment-ids-below-next fn-lc-id-allocatedp)
    (fn-lc-seg-ids-allocatedp fn-lc-key-ids-allocatedp fn-lb-vmap-index
     fn-lb-verified-bit fn-lb-vmap-mark fn-arx-entry-ok fn-lb-entry-octets
     fn-lb-entry-protected-len fn-lb-log-model-segment fn-lb-vmap-next-id-unmarked)))))

(defthm fn-lbc-retrieval-current-key-locality
 (let* ((selected (fn-lbc-select session kind args v fn-lbc))
        (i (cadr selected))
        (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)))
  (implies (equal (fn-lb-verified-bit (fn-loc-segment a b) (fn-loc-offset a b) map1)
                  (fn-lb-verified-bit (fn-loc-segment a b) (fn-loc-offset a b) map2))
   (equal (fn-lbc-retrieval session archive arts kind args server v log map1 fn-arena fn-lbc)
          (fn-lbc-retrieval session archive arts kind args server v log map2 fn-arena fn-lbc))))
 :hints (("Goal" :in-theory (e/d (fn-lbc-retrieval)
  (fn-lbc-select fn-lbc-selected-reads-entry-p fn-lbc-loc0 fn-lbc-loc1 fn-loc-segment fn-loc-offset
   fn-lb-verified-bit fn-lb-entry-octets fn-lb-entry-protected-len fn-arx-entry-ok
   fn-lb-unverified-refusal fn-lbc-resident-reply fn-nntp-single)))))

(defthm fn-lbc-move-to-next-id-old-mark-cannot-authorize
 (implies (and (fn-lc-segment-ids-below-next next-id exhaustedp oldlog (fn-lb-vmap-index fn-lb-vmap))
               (not exhaustedp)
               (fn-lb-vmap-index-covers (nth *fn-lb-vmap-bits* fn-lb-vmap) (fn-lb-vmap-index fn-lb-vmap))
               (fn-lbc-retrieval-reads-entry-p session archive arts kind args server v fn-lbc next-id entry))
  (and (not (fn-lb-verified-bit next-id entry (fn-lb-vmap-mark oldseg oldentry oldlog fn-lb-vmap)))
       (equal (fn-lbc-retrieval session archive arts kind args server v log
                  (fn-lb-vmap-mark oldseg oldentry oldlog fn-lb-vmap) fn-arena fn-lbc)
              (fn-lbc-retrieval session archive arts kind args server v log fn-lb-vmap fn-arena fn-lbc))))
 :hints (("Goal"
  :use ((:instance fn-lb-vmap-next-id-unmarked (log oldlog))
        (:instance fn-lb-vmap-old-mark-cannot-mark-next-id)
        (:instance fn-lbc-retrieval-current-key-locality
          (map1 (fn-lb-vmap-mark oldseg oldentry oldlog fn-lb-vmap)) (map2 fn-lb-vmap)))
  :in-theory (e/d (fn-lbc-retrieval-reads-entry-p)
    (fn-lb-vmap-mark-bit-effect fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len
     fn-lb-log-model-segment fn-lb-vmap-index fn-lb-vmap-next-id-unmarked fn-lb-vmap-old-mark-cannot-mark-next-id
     fn-lbc-retrieval-current-key-locality fn-lbc-retrieval fn-lbc-select
     fn-lbc-selected-reads-entry-p fn-lbc-loc0 fn-lbc-loc1 fn-loc-segment fn-loc-offset
     fn-lb-vmap-mark fn-lb-verified-bit fn-lc-segment-ids-below-next fn-lb-vmap-index-covers)))))
