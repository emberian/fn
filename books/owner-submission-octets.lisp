; fn: payload domain carried from admission through the submission queue.
(in-package "ACL2")
(include-book "owner-parse-carried")
(include-book "injection-octets")

; Logical invariants: no served operation executes this queue traversal.
(defun fn-oso-queuep (queue)
 (declare (xargs :guard t))
 (if (consp queue)
  (and (fn-bch-octetsp
         (fn-own-sub-octets (fn-psub-unpack-sub (car queue))))
       (fn-oso-queuep (cdr queue)))
  (null queue)))

(defun fn-oso-ownerp (o)
 (declare (xargs :guard t))
 (and (fn-oso-queuep (fn-own-queue o))
      (fn-bch-octetsp (fn-own-sub-octets (fn-own-inflight o)))))

(defthm fn-oso-queuep-of-append
 (implies (and (fn-oso-queuep x) (fn-oso-queuep y))
  (fn-oso-queuep (append x y)))
 :hints (("Goal" :induct (fn-oso-queuep x)
          :in-theory (union-theories '(fn-oso-queuep binary-append car-cons cdr-cons)
                                    (theory 'minimal-theory)))))

(defthm fn-oso-enqueue-preserves
 (implies (and (fn-oso-ownerp o) (fn-bch-octetsp (fn-own-sub-octets sub)))
  (fn-oso-ownerp (fn-own-enqueue o sub)))
 :hints (("Goal" :in-theory (union-theories
  '(fn-oso-ownerp fn-own-enqueue fn-own-queue-of-fn-own-make fn-own-inflight-of-fn-own-make
    fn-oso-queuep-of-append fn-ag-append fn-oso-queuep fn-psub-unpack-of-pack-sub
    car-cons cdr-cons (:executable-counterpart fn-oso-queuep))
   (theory 'minimal-theory)))))

(defthm fn-oso-take-preserves
 (implies (fn-oso-ownerp o) (fn-oso-ownerp (fn-own-take-submission o)))
 :hints (("Goal" :in-theory (union-theories
  '(fn-oso-ownerp fn-own-take-submission fn-own-queue-of-fn-own-make fn-own-inflight-of-fn-own-make
    fn-oso-queuep fn-own-sub-octets fn-own-sub-decision-of-fn-own-sub-make-author
    car-cons cdr-cons)
   (theory 'minimal-theory)))))


(defthm fn-oso-control-decision-octets
 (fn-bch-octetsp
  (fn-own-sub-octets
   (fn-own-sub-make-author id version mark
    (fn-own-control-decision cfg msgid groups octets) login account context)))
 :hints (("Goal" :use ((:instance fn-io-octet-recognizers (x octets)))
  :in-theory (union-theories
   '(fn-own-sub-octets fn-own-sub-decision-of-fn-own-sub-make-author
     fn-own-control-decision fn-peer-submissionp fn-peer-submission-shapep
     fn-peer-submission-peer fn-peer-submission-kind fn-peer-submission-msgid
     fn-peer-submission-octets fn-inj-refuse fn-inj-make-decision fn-inj-decision-octets
     fn-inj-nth fn-inj-car fn-inj-cdr fn-ag-car fn-ag-cdr
     true-listp len nfix zp car-cons cdr-cons
     (:executable-counterpart fn-bch-octetsp))
   (theory 'minimal-theory)))))

(defthm fn-oso-control-decision-octets-basic
 (fn-bch-octetsp
  (fn-own-sub-octets
   (fn-own-sub-make id version mark
    (fn-own-control-decision cfg msgid groups octets) context)))
 :hints (("Goal"
  :use ((:instance fn-oso-control-decision-octets (login nil) (account nil)))
  :in-theory (union-theories '(fn-own-sub-make fn-own-sub-make-author)
                            (theory 'minimal-theory)))))


(defthm fn-oso-control-submit-preserves
 (implies (fn-oso-ownerp o)
  (and (fn-oso-ownerp (fn-own-control-submit o msgid groups octets))
       (fn-oso-ownerp (fn-own-legacy-control-submit o msgid groups octets))))
 :hints (("Goal" :in-theory (union-theories
  '(fn-own-control-submit fn-own-legacy-control-submit
    fn-oso-enqueue-preserves fn-oso-control-decision-octets-basic)
  (theory 'minimal-theory)))))

(defthm fn-oso-taken-submission-octets
 (implies (fn-oso-ownerp o)
  (fn-bch-octetsp
   (fn-own-sub-octets (fn-own-inflight (fn-own-take-submission o)))))
 :hints (("Goal" :use ((:instance fn-oso-take-preserves))
  :in-theory (union-theories '(fn-oso-ownerp) (theory 'minimal-theory)))))
