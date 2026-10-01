; Proof-only actual OSM -> existing cold child initialization bridge.
; No served recognizer or alternate source walker.
(in-package "ACL2")
(include-book "snapshot-row-source-remap")
(include-book "snapshot-remap-cold-domain")
(include-book "snapshot-row-source-grammar")

(defun-nx fn-rccs-decoded-row-lineagep (source handle pool)
 (let* ((node (fn-omk-at 1 source)) (head (fn-hdc-car node))
        (composite (and (fn-omk-widthp head 2) (eq (fn-omk-at 0 head) :atom)
                        (eq (fn-omk-at 1 head) :hstxa))))
  (and (fn-omk-widthp source 2) (eq (fn-omk-at 0 source) :decoded)
       (natp handle) (fn-hrcur-cold-domainp node pool)
       (fn-hrcur-cold-domainp (fn-hdc-atom handle) pool)
       (implies composite
        (and (fn-odm-prefixp 3 node)
             (fn-odm-prefixp 5 (fn-odm-at 2 node)))))))

(local (defthm fn-rccs-ordinary-prefix-has-replacement-path
 (implies (fn-odm-prefixp 15 node) (fn-odm-prefixp 5 node))
 :hints (("Goal" :do-not-induct t :expand ((fn-odm-prefixp 15 node) (fn-odm-prefixp 14 (fn-hdc-cdr node)) (fn-odm-prefixp 13 (fn-hdc-cdr (fn-hdc-cdr node))) (fn-odm-prefixp 12 (fn-hdc-cdr (fn-hdc-cdr (fn-hdc-cdr node)))) (fn-odm-prefixp 11 (fn-hdc-cdr (fn-hdc-cdr (fn-hdc-cdr (fn-hdc-cdr node))))) (fn-odm-prefixp 5 node) (fn-odm-prefixp 4 (fn-hdc-cdr node)) (fn-odm-prefixp 3 (fn-hdc-cdr (fn-hdc-cdr node))) (fn-odm-prefixp 2 (fn-hdc-cdr (fn-hdc-cdr (fn-hdc-cdr node)))) (fn-odm-prefixp 1 (fn-hdc-cdr (fn-hdc-cdr (fn-hdc-cdr (fn-hdc-cdr node))))) (fn-odm-prefixp 0 (fn-hdc-cdr (fn-hdc-cdr (fn-hdc-cdr (fn-hdc-cdr (fn-hdc-cdr node))))))) :in-theory (enable fn-odm-prefixp)))))

; Caller must establish lineage from actual parsed/captured Store grammar;
; this NX predicate is never an executable preflight or readiness issuer.
(defthm fn-rccs-actual-row-source-preserves-decoded-domain
 (implies (fn-rccs-decoded-row-lineagep source handle pool)
  (let ((mapped (mv-nth 0 (fn-osm-row-source source handle))))
   (and (fn-omk-widthp mapped 2) (eq (fn-omk-at 0 mapped) :decoded)
        (fn-hrcur-cold-domainp (fn-omk-at 1 mapped) pool))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccd-actual-held-remap-preserves-cold-codec-domain
                   (node (fn-omk-at 1 source)))
        (:instance fn-rccd-actual-composite-remap-preserves-cold-codec-domain
                   (node (fn-omk-at 1 source))))
  :in-theory (e/d (fn-rccs-decoded-row-lineagep fn-osm-row-source fn-osm-node-held-headp fn-omk-at fn-omk-widthp) (fn-odm-held fn-odm-composite fn-odm-prefixp fn-hrcur-cold-domainp)))))

(local (defthm fn-rccs-widths-agree
 (equal (fn-omk-widthp x n) (fn-hrcur-widthp x n))
 :hints (("Goal" :induct (fn-omk-widthp x n)
  :in-theory (enable fn-omk-widthp fn-hrcur-widthp)))))
(local (defthm fn-rccs-first-field-is-car
 (equal (fn-omk-at 0 x) (car x))
 :hints (("Goal" :expand ((fn-omk-at 0 x)) :in-theory (enable fn-omk-at)))))
(local (defthm fn-rccs-second-field-is-cadr
 (equal (fn-omk-at 1 x) (cadr x))
 :hints (("Goal" :expand ((fn-omk-at 1 x) (fn-omk-at 0 (cdr x)))
  :in-theory (enable fn-omk-at)))))

(defthm fn-rccs-mapped-source-initializes-the-actual-cold-codec
 (implies (and (fn-rccs-decoded-row-lineagep source handle pool)
               (fn-scc-octet-listp pool))
  (let ((mapped (mv-nth 0 (fn-osm-row-source source handle))))
   (and (fn-hrcur-cold-invariantp
          (fn-hrcur-cold-begin mapped capture lease) pool)
        (equal (fn-hrcur-cold-rest
                 (fn-hrcur-cold-begin mapped capture lease) pool)
               (fn-scc-encode (fn-hdc-abstract (fn-omk-at 1 mapped) pool))))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-rccs-actual-row-source-preserves-decoded-domain
        (:instance fn-hrcur-cold-begin-establishes-invariant
         (source (mv-nth 0 (fn-osm-row-source source handle)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rccs-widths-agree fn-rccs-second-field-is-cadr fn-rccs-first-field-is-car)))))

(defthm fn-rccs-actual-typed-composite-establishes-remap-lineage
 (implies (and (fn-hstxa-p (fn-hdc-abstract node pool))
               (fn-hrcur-cold-domainp node pool) (fn-scc-octet-listp pool)
               (natp handle) (fn-hrcur-cold-domainp (fn-hdc-atom handle) pool))
  (fn-rccs-decoded-row-lineagep (list :decoded node) handle pool))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rccg-actual-typed-composite-has-decoded-remap-path)
  :in-theory (e/d (fn-rccs-decoded-row-lineagep fn-omk-at fn-omk-widthp)
                 (fn-hstxa-p fn-hdc-abstract fn-hrcur-cold-domainp
                  fn-odm-prefixp fn-odm-at)))))
