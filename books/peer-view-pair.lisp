; Identity comparison for the two exact C bodies exported together. A
; reader or importer supplies generated-layout field rows and an owned span.
(in-package "ACL2")
(include-book "identity")
(include-book "pool-ranges")
(fn2-book-layer :e)

(local (in-theory (disable fn2-fieldsp fn2-fields-wfp fn2-fields-rows
 fn2-fields-value fn2-fields-ref-off fn2-fields-ref-len fn2-pool-wfp fn2-pool-compare)))

; Compare two references decoded directly from the same owned input. The
; generated codecs establish the encoded bounds and set both Ref handles.
(defun fn2-peer-view-same-ref (a b slot gen kind owner generation fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :guard
                 (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp a) (< a (fn2-fields-rows fn2-fields)) (natp b) (< b (fn2-fields-rows fn2-fields))))
       nil)
      (n (fn2-fields-ref-len a fn2-fields))
      ((unless (and (posp n) (<= n 250) (equal n (fn2-fields-ref-len b fn2-fields))
                    (equal slot (fn2-fields-ref-slot a fn2-fields)) (equal gen (fn2-fields-ref-gen a fn2-fields))
                    (equal slot (fn2-fields-ref-slot b fn2-fields)) (equal gen (fn2-fields-ref-gen b fn2-fields))))
       nil)
      ((mv code cmp &) (fn2-pool-compare slot gen (fn2-fields-ref-off a fn2-fields) kind owner generation
                        slot gen (fn2-fields-ref-off b fn2-fields) kind owner generation n fn2-pool)))
  (and (eq code :ok) (eq cmp :equal))))
(in-theory (disable fn2-peer-view-same-ref))

; The keys have the same six scalar identity fields, Message-ID and digest.
; The named field pairs belong to the two generated layouts independently.
(defmacro fn2-peer-view-same (field)
 `(equal (fn2-fields-value (+ h ,(intern-in-package-of-symbol
             (concatenate 'string "*FN2-IDENTITY-HISTORY-ENTRY-FIELD-" (symbol-name field) "*") 'fn2)) fn2-fields)
         (fn2-fields-value (+ e ,(intern-in-package-of-symbol
             (concatenate 'string "*FN2-IDENTITY-EVIDENCE-ENTRY-FIELD-" (symbol-name field) "*") 'fn2)) fn2-fields)))

; An exported pair must name one content and stable evidence occurrence.
(defun fn2-peer-view-pair-identity-p (h e slot gen kind owner generation fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :guard
                 (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (and (natp h) (natp e)
      (<= (+ h *fn2-identity-history-entry-num-fields*) (fn2-fields-rows fn2-fields))
      (<= (+ e *fn2-identity-evidence-entry-num-fields*) (fn2-fields-rows fn2-fields))
      (fn2-peer-view-same namespace) (fn2-peer-view-same profile) (fn2-peer-view-same algorithm)
      (fn2-peer-view-same lineage) (fn2-peer-view-same domain) (fn2-peer-view-same incarnation)
      (equal (fn2-fields-value (+ h *fn2-identity-history-entry-field-evidence*) fn2-fields)
             (fn2-fields-value (+ e *fn2-identity-evidence-entry-field-occurrence*) fn2-fields))
      (equal *fn2-identity-evidence-kind-binding*
             (fn2-fields-value (+ e *fn2-identity-evidence-entry-field-kind*) fn2-fields))
      (fn2-peer-view-same-ref (+ h *fn2-identity-history-entry-field-name*)
       (+ e *fn2-identity-evidence-entry-field-name*) slot gen kind owner generation fn2-fields fn2-pool)
      (fn2-peer-view-same-ref (+ h *fn2-identity-history-entry-field-digest*)
       (+ e *fn2-identity-evidence-entry-field-digest*) slot gen kind owner generation fn2-fields fn2-pool)))
(in-theory (disable fn2-peer-view-pair-identity-p))
