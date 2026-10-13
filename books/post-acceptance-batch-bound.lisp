; Batch POST bounds and the empty context v2 carried with the event.
(in-package "ACL2")
(include-book "post-context")
(include-book "records-concrete")

; The keyring codec's own maximum: magic, version, kind, four u32
; coordinates, profile, and snapshot (stx-keyring-records.lisp:12-49).
(defconst *fn-pbatch-max*
 (+ (len (fn-cbor-encode-argument 2 (len *fn-stxk-magic*))) (len *fn-stxk-magic*)
    (len (fn-cbor-encode-argument 0 *fn-stxk-version*))
    (len (fn-cbor-encode-argument 0 *fn-stxk-kind*))
    (* 4 (len (fn-cbor-encode-argument 0 *fn-cbor-max-uint*)))
    (len (fn-cbor-encode-argument 2 *fn-stxk-max-profile*)) *fn-stxk-max-profile*
    (len (fn-cbor-encode-argument 2 *fn-stxk-max-snapshot*)) *fn-stxk-max-snapshot*))

(defun fn-pctx-of-batch (row) (list (fn-rcon-store-event-txid row) nil nil 0 nil nil 0))
(defun fn-pbatch-rowp (row)
  (or (fn-store-retention-event-p row) (fn-stxk-p row) (fn-stxe-p row) (fn-cpe-eventp row) (fn-th-topic-eventp row)))

; These are the machine's two home-buffer terms, with the current K.
(defconst *fn-pbatch-post-home-max*
 (max (+ 42 (* 2 (fn-adm-acc-out-max)))
      (+ *fn-pctx-sufhead-max* (fn-adm-acc-out-max) 32)))
(defconst *fn-pbatch-context-octets*
 (len (fn-pctx-encode '(0 nil nil 0 nil nil 0))))

(defthm fn-pbatch-max-is-derived
 (equal *fn-pbatch-max* 65634) :rule-classes nil)
(defthm fn-pbatch-post-home-max-is-derived
 (equal *fn-pbatch-post-home-max* 6920) :rule-classes nil)
(defthm fn-pbatch-context-octets-is-derived
 (equal *fn-pbatch-context-octets* 33) :rule-classes nil)

(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm pbatch-cat-length-l
 (equal (len (fn-pctx-cat a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (fn-pctx-cat a b) :in-theory (union-theories '(fn-pctx-cat len) (theory 'ground-zero))))))
(local (defthm pbatch-uint-length-l
 (equal (len (fn-pctx-uint-be n width)) (nfix width))
 :hints (("Goal" :induct (fn-pctx-uint-be n width)
          :in-theory (set-difference-theories (union-theories '(fn-pctx-uint-be len nfix zp) (theory 'ground-zero)) '(ash logand))))))
(defthm fn-pbatch-context-encode-length
 (equal (len (fn-pctx-encode (fn-pctx-of-batch row))) *fn-pbatch-context-octets*)
 :hints (("Goal" :in-theory
   (union-theories '(fn-pctx-encode fn-pctx-of-batch fn-pctx-get fn-pctx-encode-field
                     fn-pctx-octets len (:executable-counterpart fn-cbor-octet-listp)
                     pbatch-cat-length-l pbatch-uint-length-l)
                   (theory 'ground-zero)))))
