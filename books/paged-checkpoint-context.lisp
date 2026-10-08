; Tape metadata depends on three context fields, never the accumulated rows.
(in-package "ACL2")
(include-book "paged-checkpoint")

; fn-pck-context is shared from paged-checkpoint-intern-context.

(defun fn-pck-context-state (context)
  (declare (xargs :guard t))
  (if (equal context :bad) :bad
    (fn-ssr-state nil (fn-sco-at 0 context) (fn-sco-at 1 context)
                  (fn-sco-at 2 context))))

(defthm fn-pck-context-state-valid
  (implies (fn-ssr-statep st)
           (fn-ssr-statep (fn-pck-context-state (fn-pck-context st))))
  :hints (("Goal" :in-theory (enable fn-pck-context-state fn-pck-context
                                    fn-ssr-statep fn-ssr-state fn-ssr-at fn-sco-at))))

(local
 (defthm pck-context-equal-fields
  (implies (and (fn-ssr-statep a) (fn-ssr-statep b)
                (equal (fn-pck-context a) (fn-pck-context b)))
           (and (equal (fn-ssr-at 1 a) (fn-ssr-at 1 b))
                (equal (fn-ssr-at 2 a) (fn-ssr-at 2 b))
                (equal (fn-ssr-at 3 a) (fn-ssr-at 3 b))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pck-context fn-ssr-statep)))))

(defthm fn-pck-context-step-congruence
  (implies (and (fn-ssr-statep a) (fn-ssr-statep b)
                (equal (fn-pck-context a) (fn-pck-context b)))
           (and (equal (fn-pck-context (pck-ssr1 a w))
                       (fn-pck-context (pck-ssr1 b w)))
                (equal (fn-pck-meta w a) (fn-pck-meta w b))))
  :rule-classes nil
  :hints (("Goal" :use pck-context-equal-fields :in-theory
           (union-theories
            '(fn-pck-context pck-ssr1 fn-pck-meta fn-pck-row0
              fn-ssr-publish fn-ssr-state fn-ssr-at fn-ag-car fn-ag-cdr
              car-cons cdr-cons (:executable-counterpart zp)
              (:executable-counterpart binary-+))
            (theory 'minimal-theory)))))

; fn-pck-context-agreep is shared from paged-checkpoint-intern-context.

(defthm fn-pck-context-agree-step
  (implies (fn-pck-context-agreep a b)
           (fn-pck-context-agreep (pck-ssr1 a w) (pck-ssr1 b w)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-pck-context-agreep fn-pck-context pck-ssr1-bad
              (:executable-counterpart fn-ssr-statep)))
           :use (fn-pck-context-step-congruence
                 (:instance pck-ssr1-statep (st a))
                 (:instance pck-ssr1-statep (st b))))))

(defun pck-context-fold-ind (a b recs)
  (if (consp recs)
      (pck-context-fold-ind (pck-ssr1 a (car recs))
                            (pck-ssr1 b (car recs)) (cdr recs))
    (list a b)))

(defthm fn-pck-context-fold-congruence
  (implies (fn-pck-context-agreep a b)
           (fn-pck-context-agreep (fn-pck-st-of a recs) (fn-pck-st-of b recs)))
  :hints (("Goal" :induct (pck-context-fold-ind a b recs)
           :in-theory (e/d (fn-pck-st-of) (fn-pck-context-agreep pck-ssr1)))))

(defthm fn-pck-context-meta-congruence
  (implies (fn-pck-context-agreep a b)
           (equal (fn-pck-meta w a) (fn-pck-meta w b)))
  :hints (("Goal" :in-theory (enable fn-pck-context-agreep)
           :use fn-pck-context-step-congruence)))

(defthm fn-pck-context-state-agrees
  (implies (fn-ssr-statep st)
           (fn-pck-context-agreep (fn-pck-context-state (fn-pck-context st)) st))
  :hints (("Goal" :in-theory (enable fn-pck-context-agreep fn-pck-context-state
                                    fn-pck-context fn-ssr-state fn-ssr-statep
                                    fn-ssr-at fn-sco-at))))

(defthm fn-pck-context-enc-row-congruence
  (implies (fn-pck-context-agreep a b)
           (equal (fn-pck-enc-row w base a) (fn-pck-enc-row w base b)))
  :hints (("Goal" :use fn-pck-context-meta-congruence
           :in-theory (union-theories '(fn-pck-enc-row) (theory 'minimal-theory)))))

(local
 (defun pck-context-rows-ind (a b recs base)
  (if (consp recs)
      (pck-context-rows-ind (pck-ssr1 a (car recs)) (pck-ssr1 b (car recs))
                            (cdr recs) (+ base (fn-cpl-frame-octets (len (fn-pck-payload (car recs))))))
    (list a b base))))

(defthm fn-pck-context-rows-congruence
  (implies (fn-pck-context-agreep a b)
           (equal (fn-pck-rows-from recs base a) (fn-pck-rows-from recs base b)))
  :hints (("Goal" :induct (pck-context-rows-ind a b recs base)
           :in-theory (union-theories '(pck-context-rows-ind fn-pck-rows-from fn-pck-context-agree-step
                                        fn-pck-context-enc-row-congruence)
                                      (theory 'minimal-theory)))))

(defthm fn-pck-context-encodable-congruence
  (implies (fn-pck-context-agreep a b)
           (equal (fn-pck-sccb-listp recs a) (fn-pck-sccb-listp recs b)))
  :hints (("Goal" :induct (pck-context-fold-ind a b recs)
           :in-theory (e/d (fn-pck-sccb-listp)
                           (fn-pck-context-agreep fn-pck-meta pck-ssr1)))))
