; The streaming APPEND prefix is derived from the sole wire schema. It
; decodes metadata and the article's length word, never scans its body.
(in-package "ACL2")
(include-book "consumer-codec")
(make-event
 (let* ((row (fn2-fnct-word-row :append *fn2-fnct-codes*))
        (fields (caddr row)) (article (car (last fields))))
  (if (not (and (equal (car row) 11) (eq (car article) 'article)
                (eq (caadr article) :octets32) (natp (cadadr article))))
      (er soft 'fn2-cns-append-prefix-codec "APPEND must end in its declared octets32 article field.")
    (value `(progn
      (defconst *fn2-cns-append-wire-max* ,(cadadr article))
      (deflayout fn2-fnct-k4-append-prefix
        '((code :u8) ,@(butlast fields 1) (article-length :u32be))))))))
