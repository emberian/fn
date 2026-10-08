; Queue domain preservation: both hypotheses carry observable information.
(in-package "ACL2")
(include-book "../../books/owner-submission-octets")
(include-book "../../books/injection-octets")
(include-book "injection-header-boundary-tests")
(include-book "post-art-take-domain-tests")

(defconst *oso-good-sub* (fn-own-sub-make 1 0 nil *phlt-decision* nil))
(defconst *oso-bad-owner* (fn-own-enqueue nil *patd-sub*))

(assert-event
 (and (fn-inj-injectedp *phlt-decision*)
      (consp (fn-own-sub-octets *oso-good-sub*))
      (fn-bch-octetsp (fn-own-sub-octets *oso-good-sub*))
      (fn-oso-ownerp nil)
      (not (fn-oso-ownerp *oso-bad-owner*))))

(defteeth fn-oso-enqueue-preserves
 :claim (((owner (fn-oso-ownerp o))
          (octets (fn-bch-octetsp (fn-own-sub-octets sub))))
         (fn-oso-ownerp (fn-own-enqueue o sub)))
 :subject fn-own-enqueue
 :witness ((o nil) (sub *oso-good-sub*))
 :breaks ((owner ((o *oso-bad-owner*) (sub *oso-good-sub*)))
          (octets ((o nil) (sub *patd-sub*))))
 :mutations
 ((lost-submission
   (:conclusion (and (fn-oso-ownerp (fn-own-enqueue o sub))
                     (not (consp (fn-own-queue (fn-own-enqueue o sub))))))
   ((o nil) (sub *oso-good-sub*))
   :fault "Dropping the queued article preserves the domain but loses the submission.")))

; The generator's payload is unchanged; the theorem does not normalize it.
(assert-event
 (and (fn-bch-octetsp (fn-inj-decision-octets *phlt-decision*))
      (equal (fn-psub-unpack-sub (fn-psub-pack-sub *oso-good-sub*))
             *oso-good-sub*)))
