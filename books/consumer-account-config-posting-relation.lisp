; Proof-only observation of the actual bounded configuration preparation.
; Mark 2 is the signing binding; every other row survives literally and in
; order. These folds are not validators on the served path.
(in-package "ACL2")
(include-book "consumer-account-config-preparation")

(defun fn-bcpo-policy-rows (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-n (car rows)) 2)
          (fn-bcpo-policy-rows (cdr rows))
        (cons (car rows) (fn-bcpo-policy-rows (cdr rows))))
    nil))

(defthm fn-bcpo-policy-rows-true-listp
  (true-listp (fn-bcpo-policy-rows rows))
  :rule-classes :type-prescription)

(local (defthm fn-bcpo-append-associative
  (equal (append (append a b) c) (append a (append b c)))))

(local (defthm fn-bcpo-revappend-append
  (equal (append (revappend a b) c) (revappend a (append b c)))))

; The projected final result at each actual cursor phase. Captured base
; accounts are included only before the scanner begins. New bindings are
; represented too, so no assumed all-mark-2 list hides a corrupt input.
(defun fn-bcpo-projected-result (s)
  (declare (xargs :guard t))
  (let ((bindings (fn-bcpo-policy-rows (fn-cp-nth 9 s)))
        (cursor (fn-bcpo-policy-rows (fn-cp-nth 11 s)))
        (reversed (fn-bcpo-policy-rows (fn-cp-nth 12 s)))
        (final (fn-bcpo-policy-rows (fn-cp-nth 14 s))))
    (case (fn-cp-nth 4 s)
      (:bindings-reverse
       (append (fn-bcpo-policy-rows
                (fn-cfg-accounts (fn-cfg-value (fn-cp-nth 2 s))))
               (revappend bindings final)))
      (:scan (append (revappend reversed cursor) final))
      (:restore (revappend reversed final))
      (:ready final)
      (otherwise nil))))

(defun fn-bcpo-base-relatedp (s)
  (declare (xargs :guard t))
  (and (member-eq (fn-cp-nth 4 s) '(:bindings-reverse :scan :restore :ready))
       (equal (fn-bcpo-projected-result s)
              (fn-bcpo-policy-rows
               (fn-cfg-accounts (fn-cfg-value (fn-cp-nth 2 s)))))))

(defthm fn-bcp-tick-preserves-nonbinding-row-projection
  (equal (fn-bcpo-projected-result (fn-cp-nth 1 (fn-bcp-tick s rowcarry)))
         (fn-bcpo-projected-result s))
  :hints (("Goal"
           :in-theory (e/d (fn-bcpo-projected-result fn-bcp-tick fn-bcp-with
                            fn-bcp-state fn-cp-nth fn-bcpo-policy-rows)
                           (fn-bcp-intent-lookup fn-caac-list-cons
                            fn-cfg-accounts fn-cfg-value fn-cfg-row-n
                            fn-cfg-row-a)))))

(defthm fn-bcp-tick-preserves-nonbinding-base-relation
  (implies (fn-bcpo-base-relatedp s)
           (fn-bcpo-base-relatedp (fn-cp-nth 1 (fn-bcp-tick s rowcarry))))
  :hints (("Goal"
           :in-theory (e/d (fn-bcpo-base-relatedp fn-bcp-tick fn-bcp-with
                            fn-bcp-state fn-cp-nth)
                           (fn-bcp-tick-preserves-nonbinding-row-projection
                            fn-bcpo-projected-result fn-bcpo-policy-rows
                            fn-bcp-intent-lookup fn-caac-list-cons
                            fn-cfg-accounts fn-cfg-value fn-cfg-row-n
                            fn-cfg-row-a))
           :use fn-bcp-tick-preserves-nonbinding-row-projection)))

(defthm fn-bcp-prepared-preserves-nonbinding-accounts
  (implies (and (fn-bcpo-base-relatedp s)
                (equal (fn-cp-nth 4 s) :ready))
           (equal
            (fn-bcpo-policy-rows
             (fn-cfg-accounts (fn-cfg-value
                               (fn-cp-nth 1 (fn-bcp-prepared s generation)))))
            (fn-bcpo-policy-rows
             (fn-cfg-accounts (fn-cfg-value (fn-cp-nth 2 s))))))
  :hints (("Goal" :in-theory
           (e/d (fn-bcpo-base-relatedp fn-bcpo-projected-result
                  fn-bcp-prepared fn-cfg-make fn-cfg-value-make-full
                  fn-cfg-accounts fn-cfg-value fn-cfg-ag-car fn-cfg-ag-cdr fn-cp-nth)
                (fn-bcpo-policy-rows)))))

(local
 (defthm fn-bcpo-valid-stage-builds-mark-two
  (implies (fn-cab-eventp event)
           (equal (fn-cfg-row-n
                    (fn-bcp-binding-row
                     (fn-cp-nth 3 (fn-cp-nth 4 event))
                     (fn-cp-nth 6 (fn-cp-nth 4 event)))) 2))
  :hints (("Goal"
           :use ((:instance fn-cbor-at-mostp-from-length
                   (xs (fn-cp-nth 6 (fn-cp-nth 4 event))) (bound 32)))
           :in-theory
           (e/d (fn-cab-eventp fn-cab-operationp fn-cac-fields-validp
                  fn-cac-fieldp fn-bcp-binding-row fn-cfg-row-make fn-cfg-row-n
                  fn-cfg-ag-car fn-cfg-ag-cdr fn-cp-nth)
                (fn-cbor-at-mostp fn-cbor-octet-listp fn-record-octets-string
                 fn-id-hex-octets fn-cp-idp fn-cac-u64p fn-cab-decisionp))))))

(defthm fn-bcp-stage-preserves-nonbinding-binding-projection
  (implies (equal (car (fn-bcp-stage s event)) :ok)
           (equal (fn-bcpo-policy-rows
                   (fn-cp-nth 9 (fn-cp-nth 1 (fn-bcp-stage s event))))
                  (fn-bcpo-policy-rows (fn-cp-nth 9 s))))
  :hints (("Goal" :in-theory
           (e/d (fn-bcp-stage fn-bcp-with fn-bcp-state fn-bcpo-policy-rows fn-cp-nth)
                (fn-bcp-binding-row fn-bcp-binding-row-carry fn-cait-put-octets
                 fn-caac-list-cons fn-cab-eventp fn-cfg-row-n)))))

(defthm fn-bcp-begin-has-no-nonbinding-new-rows
  (equal (fn-bcpo-policy-rows
           (fn-cp-nth 9 (fn-bcp-begin candidate base baseauthority))) nil)
  :hints (("Goal" :in-theory
           (enable fn-bcp-begin fn-bcp-state fn-cp-nth fn-bcpo-policy-rows))))

(defthm fn-bcp-seal-establishes-nonbinding-base-relation
  (implies (and (equal (fn-cp-nth 4 s) :collect)
                (equal (fn-bcpo-policy-rows (fn-cp-nth 9 s)) nil))
           (fn-bcpo-base-relatedp (fn-cp-nth 1 (fn-bcp-seal s))))
  :hints (("Goal" :in-theory
           (e/d (fn-bcp-seal fn-bcp-with fn-bcp-state fn-cp-nth
                  fn-bcpo-base-relatedp fn-bcpo-projected-result)
                (fn-cfg-accounts fn-cfg-value fn-bcpo-policy-rows)))))

; Actual configuration observers depend only on this projection. These
; equations permit policy reuse; they do not evaluate a fold on the host path.
(defthm fn-cfg-access-table-of-nonbinding-projection
  (equal (fn-cfg-access-table (fn-bcpo-policy-rows rows))
         (fn-cfg-access-table rows))
  :hints (("Goal" :induct (fn-bcpo-policy-rows rows)
           :in-theory (e/d (fn-bcpo-policy-rows fn-cfg-access-table
                            fn-cfg-access-rowp)
                           (fn-cfg-row-n)))))

(defthm fn-cfg-moderation-row-of-nonbinding-projection
  (equal (fn-cfg-moderation-row (fn-bcpo-policy-rows rows) name)
         (fn-cfg-moderation-row rows name))
  :hints (("Goal" :induct (fn-bcpo-policy-rows rows)
           :in-theory (e/d (fn-bcpo-policy-rows fn-cfg-moderation-row
                            fn-cfg-moderation-rowp)
                           (fn-cfg-row-n fn-cfg-row-a)))))

(defthm fn-cfg-moderator-logins-of-nonbinding-projection
  (equal (fn-cfg-moderator-logins (fn-bcpo-policy-rows rows) name)
         (fn-cfg-moderator-logins rows name))
  :hints (("Goal" :induct (fn-bcpo-policy-rows rows)
           :in-theory (e/d (fn-bcpo-policy-rows fn-cfg-moderator-logins
                            fn-cfg-moderator-rowp)
                           (fn-cfg-row-n fn-cfg-row-a fn-cfg-row-b)))))
