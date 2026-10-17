; The deflate-pool requested removal (natp n) has no counterexample, even
; outside guards.  The proof keeps every conclusion conjunct and drops only the
; named premise.  Round 3 promoted it into the strengthened production
; statement.  This regression book retains its original independent proof
; evidence.  (Its store-budget-stored-post half left with the breaking cut.)
(in-package "ACL2")

(include-book "../../books/deflate-pool")

(local
  (defthm
    dksob-decode-nfix
    (equal (fn-pzd-decode dict c (nfix n)) (fn-pzd-decode dict c n))
    :hints
    (("Goal" :in-theory (e/d (fn-pzd-decode fn-pzd-answer fn-pzd-budget) (fn-zin-payload-with))))))

(local
  (defthm
    dksob-bufs-nfix
    (equal
      (fn-zpl-decode-bufs pool dict end (nfix n) c fn-zin-win fn-zin-tab fn-zin-out)
      (fn-zpl-decode-bufs pool dict end n c fn-zin-win fn-zin-tab fn-zin-out))
    :hints
    (("Goal" :in-theory (e/d (fn-zpl-decode-bufs fn-pzd-budget) (fn-zpl-payload-bufs))))))

(local
  (defthm
    dksob-no-natp-removal
    (implies
      (and (fn-cbor-octet-listp c) (fn-cbor-octet-listp dict))
      (let
        ((r (fn-zpl-decode-bufs nil dict (len c) n c fn-zin-win fn-zin-tab fn-zin-out))
          (d (fn-pzd-decode dict c n)))
        (and
          (equal (car (car r)) (car d))
          (implies (equal (car d) :ok) (equal (mv-nth 4 r) (cadr d)))
          (fn-zpl-pool-okp (mv-nth 1 r) (mv-nth 2 r)))))
    :hints
    (("Goal"
       :use
       ((:instance fn-zpl-decode-bufs-from-the-empty-pool (n (nfix n))))
       :in-theory
       (quote (dksob-decode-nfix dksob-bufs-nfix (:type-prescription nfix) natp)))
)))
