; These two requested removals have no counterexamples, even outside guards.
; Each proof keeps every conclusion conjunct and drops only the named premise.
; Production theorem statements are unchanged. This book does not register teeth.
(in-package "ACL2")

(include-book "../../books/deflate-pool")

(include-book "../../books/store-budget-stored-post")

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

(local
  (defthm
    dksob-snoc-append
    (equal (fn-oct-snoc xs x) (append xs (list x)))
    :hints
    (("Goal" :induct (fn-oct-snoc xs x) :in-theory (quote (fn-oct-snoc binary-append))))))

(local
  (defthm
    dksob-seal-append
    (equal (fn-arena-seal-list xs fn-arena) (append fn-arena (list xs)))
    :hints
    (("Goal" :in-theory (enable fn-arena-seal-list)))))

(local
  (defthm
    dksob-nth-append-left
    (implies (and (natp n) (< n (len xs))) (equal (nth n (append xs ys)) (nth n xs)))
    :hints
    (("Goal" :induct (nth n xs) :in-theory (enable nth binary-append)))))

(local
  (defthm
    dksob-row-survives
    (implies
      (fn-sbud-row-extent-okp h fn-arena)
      (fn-sbud-row-extent-okp h (fn-arena-seal-list xs fn-arena)))
    :hints
    (("Goal"
       :in-theory
       (enable
         fn-sbud-row-extent-okp
         fn-row-handle-inp
         fn-arena-count-is-len
         fn-arena-payload-len-is-len-nth))
)))

(local
  (defthm
    dksob-prepare-stages
    (implies
      (not (equal (fn-spc-prepare s row) s))
      (and
        (equal (fn-sf-records (fn-sn-files (fn-spc-prepare s row))) (fn-sf-records (fn-sn-files s)))
        (equal (fn-sf-record-candidate (fn-sn-files (fn-spc-prepare s row))) row)))
    :hints
    (("Goal"
       :in-theory
       (e/d
         (fn-spc-prepare fn-spc-stage-record)
         (fn-sn-statep
           fn-sn-record-bindsp
           fn-sn-prepare-node
           fn-sf-candidatep
           fn-cpe-projection-step)))
)))

(local
  (defthm
    dksob-nth-at-count
    (equal (nth (len a) (append a (list x))) x)
    :hints
    (("Goal" :induct (len a) :in-theory (enable nth binary-append)))))

(local
  (defthm
    dksob-rows-survive
    (implies
      (fn-sbud-rows-extents-okp rows fn-arena)
      (fn-sbud-rows-extents-okp rows (fn-arena-seal-list xs fn-arena)))
    :hints
    (("Goal"
       :induct
       (fn-sbud-rows-extents-okp rows fn-arena)
       :in-theory
       (e/d (fn-sbud-rows-extents-okp) (fn-sbud-row-extent-okp dksob-seal-append)))
)))

(local
  (defthm
    dksob-new-row
    (fn-sbud-rows-extents-okp
      (list (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
      (fn-arena-seal-list (fn-record-payload w) fn-arena))
    :hints
    (("Goal"
       :in-theory
       (e/d
         (fn-sbud-rows-extents-okp
           fn-sbud-row-extent-okp
           fn-row-handle-inp
           fn-intern-row-at
           fn-held-facts-of
           fn-arena-count-is-len
           fn-arena-payload-len-is-len-nth)
         (fn-held-p
           fn-held-context-of
           fn-hf-split-index
           fn-hf-body-lines-of
           fn-arena-payload-is-nth
           fn-arena-get-is-nth
           fn-arena-p-is-payload-listp)))
)))

(local
  (defthm
    dksob-no-recognizer-removal
    (implies
      (fn-sbud-store-extents-okp s fn-arena)
      (let*
        ((next (fn-psrv-store-prepare-next config s w (fn-arena-count fn-arena)))
          (after (if (equal next s) fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena))))
        (fn-sbud-store-extents-okp next after)))
    :hints
    (("Goal"
       :use
       ((:instance
          dksob-prepare-stages
          (row
            (fn-intern-row-at
              w
              (fn-sn-keyring s)
              (fn-sn-keyring-generation s)
              (fn-arena-count fn-arena))))
)
       :in-theory
       (e/d
         (fn-psrv-store-prepare-next
           fn-store-prepare-carried-next
           fn-pcar-spc-prepare-is-spc-prepare
           fn-sbud-store-extents-okp
           fn-sbud-files-extents-okp)
         (fn-spc-prepare
           fn-pcar-spc-prepare
           fn-intern-row-at
           fn-record-p
           fn-arena-seal-list
           dksob-seal-append
           dksob-prepare-stages
           fn-sbud-rows-extents-okp
           fn-arena-count-is-len
           fn-arena-payload-len-is-len-nth)))
)))
