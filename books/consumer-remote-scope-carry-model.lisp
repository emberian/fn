; Proof-only complete same-pass query annotation. No observer runs on the
; served path; fn-crs-tick maintains the literal metadata during its pass.
(in-package "ACL2")
(include-book "consumer-remote-scope")
(include-book "consumer-progress-metadata")

(defun fn-crsc-invariant (s)
 (declare (xargs :guard t :verify-guards nil))
 (and (eq (fn-cp-nth 0 s) :remote-scope)
      (true-listp (fn-cp-nth 13 s)) (true-listp (fn-cp-nth 15 s))
      (equal (fn-cp-nth 14 s) (fn-caam-list-annotation (fn-cp-nth 13 s)))
      (equal (fn-cp-nth 16 s) (fn-caam-list-annotation (fn-cp-nth 15 s)))
      (implies (member-eq (fn-cp-nth 3 s) '(:served :closed :moderators :accept))
               (fn-scc-octet-listp (fn-cp-nth 0 (fn-cp-nth 6 s))))))

(local
 (defthm fn-crsc-wire-octets-are-canonical-octets
  (equal (fn-cbor-octet-listp xs) (fn-scc-octet-listp xs))
  :hints (("Goal" :induct (fn-cbor-octet-listp xs)
                   :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-scc-octet-listp fn-scc-octetp)))))

(local
 (defthm fn-crsc-name-is-canonical-octets
  (implies (fn-crs-namep xs) (fn-scc-octet-listp xs))
  :hints (("Goal" :in-theory (e/d (fn-crs-namep)
                      (fn-scc-octet-listp fn-cbor-octet-listp fn-record-group-name-octetsp fn-cbor-at-mostp))))))

(local
 (defthm fn-crsc-annotation-head
  (implies (consp xs)
   (equal (fn-cp-nth 1 (fn-caam-list-annotation xs)) (fn-scs-summary (car xs))))
  :hints (("Goal" :in-theory (enable fn-caam-list-annotation fn-cp-nth)))))

(local
 (defthm fn-crsc-annotation-tail
  (implies (consp xs)
   (equal (fn-cp-nth 2 (fn-caam-list-annotation xs)) (fn-caam-list-annotation (cdr xs))))
  :hints (("Goal" :in-theory (enable fn-caam-list-annotation fn-cp-nth)))))

(defthm fn-crs-begin-establishes-complete-query-annotation
 (implies (eq (fn-cp-nth 0 ingress) :authenticated)
          (fn-crsc-invariant (fn-cp-nth 1 (fn-crs-begin ingress generation config groups))))
 :hints (("Goal" :in-theory (enable fn-crs-begin fn-crs-state fn-crsc-invariant fn-cp-nth fn-caam-list-annotation))))

(defthm fn-crs-tick-preserves-complete-query-annotation
 (implies (and (fn-crsc-invariant s)
                (member-eq (fn-cp-nth 0 (fn-crs-tick s key g)) '(:yield :ready)))
          (fn-crsc-invariant (fn-cp-nth 1 (fn-crs-tick s key g))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-caam-list-cons-maintains-annotation
                   (head (fn-cp-nth 0 (fn-cp-nth 6 s)))
                   (tail (fn-cp-nth 13 s))
                   (head-carry (fn-scs-octets (len (fn-cp-nth 0 (fn-cp-nth 6 s)))))
                   (tail-metadata (fn-cp-nth 14 s)))
                 (:instance fn-caam-list-cons-maintains-annotation
                   (head (car (fn-cp-nth 13 s)))
                   (tail (fn-cp-nth 15 s))
                   (head-carry (fn-cp-nth 1 (fn-cp-nth 14 s)))
                   (tail-metadata (fn-cp-nth 16 s))))
          :in-theory (e/d (fn-crs-tick fn-crs-state fn-crsc-invariant fn-cp-nth
                           )
                           (fn-crs-namep fn-gac-readablep fn-gac-text-octets
                            fn-nntp-moderated-entryp fn-mod-entry-queue fn-mod-entry-moderators
                            fn-caam-list-annotation fn-caac-list-cons fn-scs-summary fn-scs-octets fn-scc-octet-listp
                            fn-nntp-octets-chars lexorder len)))))

(defthm fn-crs-finish-carries-exact-complete-query-annotation
 (implies (and (fn-crsc-invariant s)
                (equal (fn-cp-nth 1 s) key)
                (eq (fn-cp-nth 3 s) :ready))
  (let ((answer (fn-crs-finish s key)))
   (and (eq (fn-cp-nth 0 answer) :definition)
        (equal (fn-cp-nth 2 answer) (fn-caam-list-annotation (fn-cp-nth 1 answer)))
        (equal (fn-caac-list-carry (fn-cp-nth 2 answer)) (fn-scs-summary (fn-cp-nth 1 answer))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-caam-list-carry-is-exact (rows (fn-cp-nth 15 s))))
  :in-theory (e/d (fn-crsc-invariant fn-crs-finish fn-cp-nth)
                   (fn-caam-list-annotation fn-caac-list-carry fn-scs-summary)))))

(in-theory (disable fn-crsc-invariant))
