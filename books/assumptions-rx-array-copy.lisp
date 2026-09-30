; A-RX-ARRAY-COPY / PRF-1150: conditional semantic boundary,
; not a proof of Common Lisp REPLACE.
(in-package "ACL2")

(defun fn-rxac-bytes-p (xs)
  (if (atom xs) (equal xs nil)
    (and (natp (car xs)) (< (car xs) 256)
         (fn-rxac-bytes-p (cdr xs)))))

(defun fn-rxac-copy-prefix (source destination count)
  (if (or (zp count) (atom source) (atom destination)) destination
    (cons (car source)
          (fn-rxac-copy-prefix (cdr source) (cdr destination) (1- count)))))

(defthm fn-rxac-copy-prefix-preserves-capacity
  (equal (len (fn-rxac-copy-prefix source destination count)) (len destination)))

(defthm fn-rxac-copy-prefix-preserves-outside
  (equal (nthcdr count (fn-rxac-copy-prefix source destination count))
         (nthcdr count destination))
  :hints (("Goal" :induct (fn-rxac-copy-prefix source destination count))))

(defun fn-rxac-domain-p (source-id destination-id source destination old-fill end stable)
  (and source-id destination-id (not (equal source-id destination-id))
       (equal stable t)
       (fn-rxac-bytes-p source) (fn-rxac-bytes-p destination)
       (natp old-fill) (<= old-fill (len destination))
       (natp end) (<= end (len source)) (<= end (len destination))))

; Observation: status, source identity, destination identity, source bytes,
; destination bytes, resulting fill, capacity, association, quarantined.
; The association names the already registered provider/carry/pool context.
; It is borrowed unchanged, not a host-created authority or capacity receipt.
(defun fn-rxac-observation-contract-p
  (observation source-id destination-id source destination old-fill end association outcome)
  (and (true-listp observation) (equal (len observation) 9)
       (equal (nth 0 observation) outcome)
       (equal (nth 1 observation) source-id)
       (equal (nth 2 observation) destination-id)
       (equal (nth 3 observation) source)
       (equal (nth 6 observation) (len destination))
       (equal (nth 7 observation) association)
       (case outcome
         (:copied
          (and (equal (nth 4 observation)
                      (fn-rxac-copy-prefix source destination end))
               (equal (nth 5 observation) end)
               (equal (nth 8 observation) nil)))
         (:not-invoked
          (and (equal (nth 4 observation) destination)
               (equal (nth 5 observation) old-fill)
               (equal (nth 8 observation) nil)))
         (:uncertain
          ; A partial copy or escaped fill may have changed bytes or fill.
          ; No rollback, successful publication, retry or refund follows.
          (and (fn-rxac-bytes-p (nth 4 observation))
               (equal (len (nth 4 observation)) (len destination))
               (natp (nth 5 observation))
               (<= (nth 5 observation) (len destination))
               (equal (nth 8 observation) t)))
         (otherwise nil))))

(defun fn-rxac-model-observe
  (source-id destination-id source destination old-fill end stable association outcome)
  (if (not (and (fn-rxac-domain-p source-id destination-id source destination old-fill end stable)
                (member-eq outcome '(:copied :not-invoked :uncertain))))
      (list :unavailable)
    (list outcome source-id destination-id source
        (if (equal outcome :copied)
            (fn-rxac-copy-prefix source destination end) destination)
        (if (equal outcome :copied) end old-fill)
        (len destination) association (equal outcome :uncertain))))

(encapsulate
 (((fn-assume-rxac-observe * * * * * * * * *) => *))
 (local
  (defun fn-assume-rxac-observe
    (source-id destination-id source destination old-fill end stable association outcome)
    (fn-rxac-model-observe source-id destination-id source destination
                           old-fill end stable association outcome)))
 (defthm fn-assume-rxac-observation-contract
   (implies
    (and (fn-rxac-domain-p source-id destination-id source destination old-fill end stable)
         (member-eq outcome '(:copied :not-invoked :uncertain)))
    (fn-rxac-observation-contract-p
     (fn-assume-rxac-observe source-id destination-id source destination
                            old-fill end stable association outcome)
     source-id destination-id source destination old-fill end association outcome))
   :rule-classes nil))

; The native subject will be fnn-owner-receiver-fill. Qualification additionally
; binds its generated nested UB8 backing, core-issued endpoints and installed
; token/instance to these identities. Unknown/partial failure must invoke the
; actual core fence before another consumer can observe the provider. This
; assumption gives no allocator, compiler-frame, GC or retained-debt bound.
