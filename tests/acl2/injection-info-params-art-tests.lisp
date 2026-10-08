; Statement 3's injection member: the entire refinement and retained BODY.
(in-package "ACL2")
(include-book "../../books/injection-info-params-art")
(include-book "injection-header-boundary-tests")

(defconst *phlat-d*
  (fn-inj-make-decision
   (fn-inj-decision-status *phlt-decision*)
   (fn-inj-decision-reason *phlt-decision*)
   (fn-inj-decision-msgid *phlt-decision*)
   (fn-inj-decision-groups *phlt-decision*)
   (fn-art-of (fn-inj-decision-octets *phlt-decision*))))

(defteeth fn-ipp-with-params-art-refines
  :claim (((art (fn-art-headp a)))
          (and (equal (fn-art-octets (fn-ipp-with-params-art a msgid params))
                      (fn-ipp-with-params (fn-art-octets a) msgid params))
               (equal (fn-art-body (fn-ipp-with-params-art a msgid params))
                      (fn-art-body a))))
  :subject fn-ipp-with-params-art
  :witness ((a (fn-art-decision-payload *phlat-d*))
            (msgid (fn-inj-decision-msgid *phlt-decision*))
            (params *phlt-params*))
  :breaks
  ((art ((a (cons nil (fn-bch-pack (fn-inj-decision-octets *phlt-decision*))))
        (msgid (fn-inj-decision-msgid *phlt-decision*)) (params *phlt-params*))))
  :mutations
  ((empty-body
    (:conclusion (equal (fn-art-body (fn-ipp-with-params-art a msgid params)) 1))
    ((a (fn-art-decision-payload *phlat-d*))
     (msgid (fn-inj-decision-msgid *phlt-decision*)) (params *phlt-params*))
    :fault "Discarding BODY during the header rewrite replaces it with the empty sentinel.")))

; The configured complaints value supplies nonempty parameters through the
; served wrapper, so its equality is witnessed by an actual header change.
(defconst *phlat-cfg*
  (fn-cfg-make 1
   (fn-cfg-apply-delta (fn-cfg-empty-value) 1
    (fn-clock-observation 5 1700000000 2 t)
    (fn-cfg-set-policy "complaints-to" (phlt-o "abuse@example.org")))))
(defconst *phlat-body-only-d*
  (fn-inj-make-decision :injected nil (fn-inj-decision-msgid *phlt-decision*) nil
   (cons nil (fn-bch-pack (fn-inj-decision-octets *phlt-decision*)))))

(assert-event
 (and (fn-inj-injectedp *phlt-decision*)
      (equal (fn-ipp-complaints *phlat-cfg*) (phlt-o "abuse@example.org"))
      (not (equal (fn-ipp-injected-art *phlat-d* nil nil *phlat-cfg*)
                  (fn-art-decision-payload *phlat-d*)))))

(defteeth fn-ipp-injected-art-refines
  :claim (((art (fn-art-headp (fn-art-decision-payload d))))
          (let ((r (fn-ipp-injected-art d secret login cfg)))
            (and (equal (fn-art-octets r)
                        (fn-ipp-injected-octets (fn-art-decision-down d) secret login cfg))
                 (equal (fn-art-body r)
                        (fn-art-body (fn-art-decision-payload d))))))
  :subject fn-ipp-injected-art
  :witness ((d *phlat-d*) (secret nil) (login nil) (cfg *phlat-cfg*))
  :breaks ((art ((d *phlat-body-only-d*) (secret nil) (login nil) (cfg *phlat-cfg*))))
  :mutations
  ((empty-body
    (:conclusion
     (let ((r (fn-ipp-injected-art d secret login cfg)))
       (equal (fn-art-body r) 1)))
    ((d *phlat-d*) (secret nil) (login nil) (cfg *phlat-cfg*))
    :fault "The wrapper must retain the packed BODY rather than the empty sentinel.")))
