; Streamed successful FETCH retains the exact nested port-reply wire schema.
; Only length words are emitted before the checked source windows arrive.
(in-package "ACL2")
(include-book "fnct-pool")
(local (in-theory (disable fn2-fields-rows fn2-fieldsp fn2-fields-wfp
                           fn2-poolp fn2-pool-wfp fn2-pool-rows)))
(make-event
 (let* ((fetch (cadr (assoc-eq 'fetch *fn2-fnct-results*)))
        (article (car fetch))
        (port *fn2-fnct-port-reply-layout*)
        (reason (cadr port)) (result (caddr port)))
  (if (not (and (equal (len fetch) 1) (eq (car article) 'article)
                (eq (caadr article) :octets32) (natp (cadadr article))
                (equal (len port) 3) (eq (caar port) 'class)
                (eq (car (cadar port)) :enum)
                (member-eq :accepted (caddr (cadar port)))
                (eq (car reason) 'reason) (eq (caadr reason) :octets16)
                (eq (car result) 'result) (eq (caadr result) :octets32)))
      (er soft 'fn2-cns-fetch-prefix-codec "FETCH and its port envelope must expose their declared length-prefixed fields.")
    (let* ((body-prefix (list (car port) '(reason-length :u16be)
                              '(result-length :u32be) '(article-length :u32be)))
           (prefix (append *fn2-fnct-header-layout* body-prefix)))
     (value `(progn
       (defconst *fn2-cns-fetch-accepted-class* ,(position-eq :accepted (caddr (cadar port))))
       (defconst *fn2-cns-fetch-wire-max* ,(cadadr article))
       (defconst *fn2-cns-fetch-result-prefix-octets* ,(fn2-layout-max-size '((article-length :u32be))))
       (defconst *fn2-cns-fetch-port-prefix-octets* ,(fn2-layout-max-size body-prefix))
       (defconst *fn2-cns-fetch-frame-prefix-octets* ,(fn2-layout-max-size prefix))
       (deflayout fn2-fnct-fetch-stream-prefix ',prefix)))))))

; Generate scalar writes from the emitted prefix's field order, rather than
; maintaining a second handwritten serializer or offsets.
(make-event
 (let ((bindings '((magic *fn2-fnct-magic*) (version *fn2-fnct-version*)
                    (kind *fn2-fnct-port-reply-kind*)
                    (length (+ article-bytes *fn2-cns-fetch-port-prefix-octets*))
                    (class *fn2-cns-fetch-accepted-class*) (reason-length 0)
                    (result-length (+ article-bytes *fn2-cns-fetch-result-prefix-octets*))
                    (article-length article-bytes))))
  (values '(*fn2-fnct-magic* *fn2-fnct-version* *fn2-fnct-port-reply-kind*
                  (+ article-bytes *fn2-cns-fetch-port-prefix-octets*)
                  0 0 (+ article-bytes *fn2-cns-fetch-result-prefix-octets*) article-bytes))
        (bindings (pairlis$ names values)))
  (value
   `(defun fn2-cns-fetch-stream-prefix (base article-bytes slot gen okind owner ownergen fn2-fields fn2-pool)
     (declare (xargs :stobjs (fn2-fields fn2-pool)
                     :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
     (if (not (and (natp base)
                   (<= (+ base *fn2-fnct-fetch-stream-prefix-num-fields*) (fn2-fields-rows fn2-fields))
                   (natp article-bytes) (<= article-bytes *fn2-cns-fetch-wire-max*)))
         (mv :bounds 0 fn2-fields fn2-pool)
       (let* ,(fn2-fnct-def-result-binds 'fn2-fnct-fetch-stream-prefix bindings)
        (mv-let (code end fn2-pool)
         (fn2-fnct-fetch-stream-prefix-encode base slot gen 0 okind owner ownergen fn2-fields fn2-pool)
         (mv code end fn2-fields fn2-pool)))))))
