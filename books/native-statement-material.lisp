; Public authoring boundary for the existing FN-Statement ML-DSA-65 suite.
; It reuses the enrolled stable principal. It is not FN-Authorship hybrid.
(in-package "ACL2")
(include-book "stx-lace")
(include-book "policy")
(include-book "native-hybrid-control")

(defun fn-nsm-plan (principal incarnation sequence kind group source)
 (declare (xargs :guard t :guard-hints
  (("Goal" :in-theory (e/d (fn-stmt-payloadp)
   (fn-native-hybrid-control-uint32 fn-stx-parse fn-stx-field fn-stx-payload-for
    fn-stx-authored-header fn-stx-b64-encode fn-stmt-headerp))))))
 (let* ((inc (fn-native-hybrid-control-uint32 incarnation))
        (seq (fn-native-hybrid-control-uint32 sequence))
        (article (fn-stx-parse source))
        (k (cond ((equal kind "article") :article)
                 ((equal kind "policy") :policy) (t nil))))
  (if (not (and (fn-prin-idp principal) (fn-record-uint32p inc)
                (fn-record-uint32p seq) k article (true-listp article)
                (not (fn-stx-field article)))) nil
   (let* ((initial (fn-stmt-make-header principal inc seq nil k (make-list 32 :initial-element 0)))
          (policy (if (and (eq k :policy) (stringp group))
                      (fn-pol-policy-encode
                       (fn-pol-make-policy (fn-record-string-octets group) nil (fn-article-body article))) nil))
          (payload (if (eq k :article) (fn-stx-payload-for article initial) policy))
          (authored (if (eq k :article) source
                     (append (fn-stx-authored-header (fn-article-fields article))
                      (append '(13 10) (fn-stx-b64-encode policy))))))
    (if (not (and (fn-stmt-payloadp payload) (consp payload)
                  (fn-cbor-octet-listp authored))) nil
     (let ((header (fn-stmt-make-header principal inc seq nil k (fn-stmt-payload-ref payload))))
      (if (fn-stmt-headerp header)
          (list header payload authored (fn-stmt-signing-preimage header)) nil)))))))

(defun fn-nsm-render (plan signature)
 (declare (xargs :guard t))
 (let* ((header (fn-ag-car plan))
        (payload (fn-ag-car (fn-ag-cdr plan)))
        (source (fn-ag-car (fn-ag-cdr (fn-ag-cdr plan))))
        (statement (fn-stmt-make header payload signature)))
  (if (not (and (fn-stmt-p statement) (fn-cbor-octet-listp source))) nil
   (append (fn-record-string-octets "FN-Statement: ")
    (append (fn-stx-header-value-parts header signature) (append '(13 10) source))))))

(defun fn-nsm-check-rendered (principal key plan signature)
 (declare (xargs :guard t))
 (let* ((bytes (fn-nsm-render plan signature))
        (article (fn-stx-parse bytes))
        (ring (list (cons principal key))))
  (and bytes article (fn-prin-keyringp ring)
       (let ((s (fn-stx-statement-of article)))
        (and (fn-stmt-p s) (equal (fn-stmt-creator s) principal)
             (fn-prin-verifiedp s ring))))))
(in-theory (disable fn-nsm-plan fn-nsm-render fn-nsm-check-rendered))
