; Charging the exact stored maximum under R and cache validity.
(in-package "ACL2")
(include-book "history-totals-carried")
(include-book "memory-model")
(local (in-theory (disable (tau-system))))
(local
 (defthm pin-fix-of-list
  (implies (true-listp x) (equal (true-list-fix x) x))
  :hints (("Goal" :in-theory (enable true-list-fix)))))
(local
 (defthm pin-high-of-update
  (equal (fn-mm-cfg-article-high (update-nth 15 (nfix high) (true-list-fix cfg)))
         (nfix high))
  :hints (("Goal" :in-theory (union-theories
    '(fn-mm-cfg-article-high fn-mm-nat pin-fix-of-list nth-update-nth
      true-listp-update-nth (:type-prescription true-list-fix) nfix natp
      car-cons cdr-cons (:type-prescription nfix)) (theory 'minimal-theory))))))
(local
 (defthm pin-large-covers-high
  (implies (<= (nfix octets) (nfix high))
   (<= (+ (* 2 (nfix octets)) *fn-cbud-reply-status-octets*)
       (fn-mm-large-reply profile (update-nth 15 (nfix high) (true-list-fix cfg)))))
  :hints (("Goal" :in-theory (union-theories
   '(fn-mm-large-reply fn-mm-served-article-octets pin-high-of-update max
     (:type-prescription nfix)) (theory 'minimal-theory))))))
(local
 (defthm pin-carried-covers-held
  (implies (and (equal fn-hist (fn-sf-records (fn-sn-files s)))
                (fn-adm-stored-most-cache-validp cache (fn-sf-records (fn-sn-files s)))
                (member-equal rec (fn-sf-records (fn-sn-files s))) (fn-held-p rec))
   (and (natp (fn-hist-stored-most-carried cache s fn-hist))
        (<= (nfix (fn-hf-octets (fn-held-facts rec)))
            (fn-hist-stored-most-carried cache s fn-hist))))
  :hints (("Goal" :use (fn-hist-stored-most-carried-is-the-extend
    (:instance fn-adm-stored-most-extend-of-a-valid-cache
       (records (fn-sf-records (fn-sn-files s))))
    (:instance fn-adm-stored-article-most-covers-held-member
       (records (fn-sf-records (fn-sn-files s))))
    (:instance fn-adm-stored-article-most-is-natural
       (records (fn-sf-records (fn-sn-files s)))))
   :in-theory (union-theories
    '((:type-prescription fn-adm-stored-article-most-is-natural))
    (theory 'minimal-theory))))))
(local (set-default-hints
 '((quote (:use (pin-carried-covers-held
    (:instance pin-large-covers-high
      (octets (fn-hf-octets (fn-held-facts rec)))
      (high (max (nfix pins) (fn-hist-stored-most-carried cache s fn-hist)))))
   :in-theory (union-theories '(max nfix natp (:type-prescription nfix))
                             (theory 'minimal-theory)))))))
(defthm fn-adm-pinned-cfg-charges-every-stored-article
  (implies (and (equal fn-hist (fn-sf-records (fn-sn-files s)))
                (fn-adm-stored-most-cache-validp cache (fn-sf-records (fn-sn-files s)))
                (member-equal rec (fn-sf-records (fn-sn-files s)))
                (fn-held-p rec))
           (<= (+ (* 2 (nfix (fn-hf-octets (fn-held-facts rec)))) *fn-cbud-reply-status-octets*)
               (fn-mm-large-reply profile
                 (update-nth 15 (max (nfix pins) (fn-hist-stored-most-carried cache s fn-hist)) (true-list-fix cfg))))))
(local (set-default-hints nil))
