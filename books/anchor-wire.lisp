; Executable bounded grammar for the deployed RoughTime v1 anchor response.
;
; The host owns UDP and cryptographic primitive observations.  This book owns
; the tagged-message grammar, bounds, required fields, little-endian values,
; canonical DELE/SREP binding and the anchor fields handed to books/anchor.

(in-package "ACL2")
(include-book "anchor")

(set-verify-guards-eagerness 0)

(defconst *fn-anchor-wire-max-response* 4096)
(defconst *fn-anchor-wire-max-tags* 32)
(defconst *fn-anchor-wire-max-path-nodes* 32)

(defconst *fn-anchor-wire-tag-sig* '(83 73 71 0))
(defconst *fn-anchor-wire-tag-nonc* '(78 79 78 67))
(defconst *fn-anchor-wire-tag-path* '(80 65 84 72))
(defconst *fn-anchor-wire-tag-srep* '(83 82 69 80))
(defconst *fn-anchor-wire-tag-cert* '(67 69 82 84))
(defconst *fn-anchor-wire-tag-indx* '(73 78 68 88))
(defconst *fn-anchor-wire-tag-dele* '(68 69 76 69))

(defun fn-anchor-wire-result-ok (value rest)
  (declare (xargs :guard t))
  (list :ok value rest))

(defun fn-anchor-wire-result-error (reason)
  (declare (xargs :guard t))
  (list :error reason))

(defun fn-anchor-wire-result-okp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :ok)))

(defun fn-anchor-wire-result-value (x)
  (declare (xargs :guard t))
  (if (consp (cdr x)) (car (cdr x)) nil))

(defun fn-anchor-wire-result-rest (x)
  (declare (xargs :guard t))
  (if (consp (cdr (cdr x))) (car (cdr (cdr x))) nil))

(defun fn-anchor-wire-result-reason (x)
  (declare (xargs :guard t))
  (if (and (consp x) (equal (car x) :error) (consp (cdr x)))
      (car (cdr x))
    nil))

(defun fn-anchor-wire-nth (n xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (zp (nfix n)) (car xs)
        (fn-anchor-wire-nth (1- (nfix n)) (cdr xs)))
    nil))

(defun fn-anchor-wire-split (n xs)
  (declare (xargs :guard t))
  (if (not (natp n))
      nil
    (if (zp n)
        (cons nil xs)
      (if (consp xs)
          (let ((rest (fn-anchor-wire-split (1- n) (cdr xs))))
            (and rest (cons (cons (car xs) (car rest)) (cdr rest))))
        nil))))

(defun fn-anchor-wire-le-value (octets factor)
  (declare (xargs :guard t))
  (if (consp octets)
      (+ (* (nfix factor) (nfix (car octets)))
         (fn-anchor-wire-le-value (cdr octets) (* 256 (nfix factor))))
    0))

(defun fn-anchor-wire-le32 (octets)
  (declare (xargs :guard t))
  (fn-anchor-wire-le-value octets 1))

(defun fn-anchor-wire-le64 (octets)
  (declare (xargs :guard t))
  (fn-anchor-wire-le-value octets 1))

(defun fn-anchor-wire-read-u32s (count octets values-rev)
  (declare (xargs :guard t))
  (if (not (natp count))
      (fn-anchor-wire-result-error :count)
    (if (zp count)
        (fn-anchor-wire-result-ok (reverse values-rev) octets)
      (let ((head (fn-anchor-wire-split 4 octets)))
        (if (not head)
            (fn-anchor-wire-result-error :truncated-offsets)
          (fn-anchor-wire-read-u32s
           (1- count) (cdr head)
           (cons (fn-anchor-wire-le32 (car head)) values-rev)))))))

(defun fn-anchor-wire-read-tags (count octets tags-rev)
  (declare (xargs :guard t))
  (if (not (natp count))
      (fn-anchor-wire-result-error :count)
    (if (zp count)
        (fn-anchor-wire-result-ok (reverse tags-rev) octets)
      (let ((head (fn-anchor-wire-split 4 octets)))
        (if (not head)
            (fn-anchor-wire-result-error :truncated-tags)
          (fn-anchor-wire-read-tags
           (1- count) (cdr head) (cons (car head) tags-rev)))))))

(defun fn-anchor-wire-tags-increasingp (tags previous have-previous)
  (declare (xargs :guard t))
  (if (atom tags)
      (null tags)
    (let ((value (fn-anchor-wire-le32 (car tags))))
      (and (or (not have-previous) (< (nfix previous) value))
           (fn-anchor-wire-tags-increasingp
            (cdr tags) value t)))))

(defun fn-anchor-wire-build-fields (tags ends previous body fields-rev)
  (declare (xargs :guard t))
  (if (atom tags)
      (if (and (null tags) (null ends) (null body))
          (fn-anchor-wire-result-ok (reverse fields-rev) nil)
        (fn-anchor-wire-result-error :field-count))
    (if (atom ends)
        (fn-anchor-wire-result-error :field-count)
      (let ((end (nfix (car ends))))
        (if (< end (nfix previous))
            (fn-anchor-wire-result-error :decreasing-offset)
          (let ((field (fn-anchor-wire-split (- end (nfix previous)) body)))
            (if (not field)
                (fn-anchor-wire-result-error :offset-outside-message)
              (fn-anchor-wire-build-fields
               (cdr tags) (cdr ends) end (cdr field)
               (cons (list (car tags) (car field)) fields-rev)))))))))

(defun fn-anchor-wire-parse-message-counted (count octets)
  (declare (xargs :guard t))
  (let ((offsets (fn-anchor-wire-read-u32s (1- (nfix count)) octets nil)))
    (if (not (fn-anchor-wire-result-okp offsets))
        offsets
      (let ((tags (fn-anchor-wire-read-tags
                   (nfix count) (fn-anchor-wire-result-rest offsets) nil)))
        (if (not (fn-anchor-wire-result-okp tags))
            tags
          (let* ((tag-values (fn-anchor-wire-result-value tags))
                 (body (fn-anchor-wire-result-rest tags)))
            (if (not (fn-anchor-wire-tags-increasingp tag-values 0 nil))
                (fn-anchor-wire-result-error :tag-order)
              (fn-anchor-wire-build-fields
               tag-values
               (append (fn-anchor-wire-result-value offsets)
                       (list (len body)))
               0 body nil))))))))

(defun fn-anchor-wire-parse-message (octets)
  (declare (xargs :guard t))
  (cond
   ((not (fn-cbor-at-mostp octets *fn-anchor-wire-max-response*))
    (fn-anchor-wire-result-error :message-length))
   ((not (fn-cbor-octet-listp octets))
    (fn-anchor-wire-result-error :not-octets))
   (t
    (let ((count-head (fn-anchor-wire-split 4 octets)))
      (if (not count-head)
          (fn-anchor-wire-result-error :truncated-count)
        (let ((count (fn-anchor-wire-le32 (car count-head))))
          (if (or (zp count) (< *fn-anchor-wire-max-tags* count))
              (fn-anchor-wire-result-error :tag-count)
            (fn-anchor-wire-parse-message-counted count (cdr count-head)))))))))

(defun fn-anchor-wire-has-fieldp (tag fields)
  (declare (xargs :guard t))
  (if (atom fields)
      nil
    (or (equal tag (fn-anchor-wire-nth 0 (car fields)))
        (fn-anchor-wire-has-fieldp tag (cdr fields)))))

(defun fn-anchor-wire-field (tag fields)
  (declare (xargs :guard t))
  (if (atom fields)
      nil
    (if (equal tag (fn-anchor-wire-nth 0 (car fields)))
        (fn-anchor-wire-nth 1 (car fields))
      (fn-anchor-wire-field tag (cdr fields)))))

(defun fn-anchor-wire-requiredp (tags fields)
  (declare (xargs :guard t))
  (if (atom tags)
      (null tags)
    (and (fn-anchor-wire-has-fieldp (car tags) fields)
         (fn-anchor-wire-requiredp (cdr tags) fields))))

(defun fn-anchor-wire-widthp (value width)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp value) (equal (len value) (nfix width))))

(defun fn-anchor-wire-parsed-anchor (parsed)
  (declare (xargs :guard t))
  (fn-anchor-wire-nth 0 parsed))

(defun fn-anchor-wire-parsed-path (parsed)
  (declare (xargs :guard t))
  (fn-anchor-wire-nth 1 parsed))

(defun fn-anchor-wire-parsed-index (parsed)
  (declare (xargs :guard t))
  (fn-anchor-wire-nth 2 parsed))

(defun fn-anchor-wire-parse-dele (octets)
  (declare (xargs :guard t))
  (let ((result (fn-anchor-wire-parse-message octets)))
    (if (not (fn-anchor-wire-result-okp result))
        (fn-anchor-wire-result-error :dele-message)
      (let ((fields (fn-anchor-wire-result-value result)))
        (if (not (fn-anchor-wire-requiredp
                  (list *fn-anchor-tag-pubk*
                        *fn-anchor-tag-mint*
                        *fn-anchor-tag-maxt*)
                  fields))
            (fn-anchor-wire-result-error :missing-dele-field)
          (let ((delegate (fn-anchor-wire-field *fn-anchor-tag-pubk* fields))
                (mint (fn-anchor-wire-field *fn-anchor-tag-mint* fields))
                (maxt (fn-anchor-wire-field *fn-anchor-tag-maxt* fields)))
            (if (not (and (fn-anchor-wire-widthp delegate
                                                     *fn-anchor-key-octets*)
                          (fn-anchor-wire-widthp mint 8)
                          (fn-anchor-wire-widthp maxt 8)))
                (fn-anchor-wire-result-error :dele-field)
              (fn-anchor-wire-result-ok
               (list delegate
                     (fn-anchor-wire-le64 mint)
                     (fn-anchor-wire-le64 maxt))
               nil))))))))

(defun fn-anchor-wire-parse-cert (octets)
  (declare (xargs :guard t))
  (let ((result (fn-anchor-wire-parse-message octets)))
    (if (not (fn-anchor-wire-result-okp result))
        (fn-anchor-wire-result-error :cert-message)
      (let ((fields (fn-anchor-wire-result-value result)))
        (if (not (fn-anchor-wire-requiredp
                  (list *fn-anchor-wire-tag-dele* *fn-anchor-wire-tag-sig*)
                  fields))
            (fn-anchor-wire-result-error :missing-cert-field)
          (let* ((signature
                  (fn-anchor-wire-field *fn-anchor-wire-tag-sig* fields))
                 (dele-octets
                  (fn-anchor-wire-field *fn-anchor-wire-tag-dele* fields))
                 (dele-result (fn-anchor-wire-parse-dele dele-octets)))
            (if (not (fn-anchor-wire-widthp signature *fn-anchor-sig-octets*))
                (fn-anchor-wire-result-error :cert-signature)
              (if (not (fn-anchor-wire-result-okp dele-result))
                  dele-result
                (let ((dele (fn-anchor-wire-result-value dele-result)))
                  (fn-anchor-wire-result-ok
                   (list signature dele-octets
                         (fn-anchor-wire-nth 0 dele)
                         (fn-anchor-wire-nth 1 dele)
                         (fn-anchor-wire-nth 2 dele))
                   nil))))))))))

(defun fn-anchor-wire-parse-srep (octets)
  (declare (xargs :guard t))
  (let ((result (fn-anchor-wire-parse-message octets)))
    (if (not (fn-anchor-wire-result-okp result))
        (fn-anchor-wire-result-error :srep-message)
      (let ((fields (fn-anchor-wire-result-value result)))
        (if (not (fn-anchor-wire-requiredp
                  (list *fn-anchor-tag-radi*
                        *fn-anchor-tag-midp*
                        *fn-anchor-tag-root*)
                  fields))
            (fn-anchor-wire-result-error :missing-srep-field)
          (let ((radius (fn-anchor-wire-field *fn-anchor-tag-radi* fields))
                (midpoint (fn-anchor-wire-field *fn-anchor-tag-midp* fields))
                (root (fn-anchor-wire-field *fn-anchor-tag-root* fields)))
            (if (not (and (fn-anchor-wire-widthp radius 4)
                          (fn-anchor-wire-widthp midpoint 8)
                          (fn-anchor-wire-widthp root *fn-anchor-root-octets*)))
                (fn-anchor-wire-result-error :srep-field)
              (fn-anchor-wire-result-ok
               (list (fn-anchor-wire-le32 radius)
                     (fn-anchor-wire-le64 midpoint)
                     root)
               nil))))))))

(defun fn-anchor-wire-parse-top (packet nonce)
  (declare (xargs :guard t))
  (let ((result (fn-anchor-wire-parse-message packet)))
    (if (not (fn-anchor-wire-result-okp result))
        result
      (let ((fields (fn-anchor-wire-result-value result)))
        (if (not (fn-anchor-wire-requiredp
                  (list *fn-anchor-wire-tag-sig*
                        *fn-anchor-wire-tag-nonc*
                        *fn-anchor-wire-tag-path*
                        *fn-anchor-wire-tag-srep*
                        *fn-anchor-wire-tag-cert*
                        *fn-anchor-wire-tag-indx*)
                  fields))
            (fn-anchor-wire-result-error :missing-top-field)
          (let* ((signature
                  (fn-anchor-wire-field *fn-anchor-wire-tag-sig* fields))
                 (carried-nonce
                  (fn-anchor-wire-field *fn-anchor-wire-tag-nonc* fields))
                 (path (fn-anchor-wire-field *fn-anchor-wire-tag-path* fields))
                 (srep (fn-anchor-wire-field *fn-anchor-wire-tag-srep* fields))
                 (cert (fn-anchor-wire-field *fn-anchor-wire-tag-cert* fields))
                 (index-octets
                  (fn-anchor-wire-field *fn-anchor-wire-tag-indx* fields))
                 (index (fn-anchor-wire-le32 index-octets))
                 (depth (floor (len path) *fn-anchor-root-octets*)))
            (if (not (and
                      (fn-anchor-wire-widthp signature *fn-anchor-sig-octets*)
                      (fn-anchor-wire-widthp carried-nonce
                                               *fn-anchor-nonce-octets*)
                      (equal carried-nonce nonce)
                      (fn-cbor-octet-listp path)
                      (equal (mod (len path) *fn-anchor-root-octets*) 0)
                      (<= (len path)
                          (* *fn-anchor-wire-max-path-nodes*
                             *fn-anchor-root-octets*))
                      (fn-anchor-wire-widthp index-octets 4)))
                (fn-anchor-wire-result-error :top-field)
              (if (not (< index (expt 2 depth)))
                  (fn-anchor-wire-result-error :index-depth)
                (fn-anchor-wire-result-ok
                 (list signature path index srep cert) nil)))))))))

(defun fn-anchor-wire-compose-response (top cert srep nonce key)
  (declare (xargs :guard t))
  (let* ((signature (fn-anchor-wire-nth 0 top))
         (path (fn-anchor-wire-nth 1 top))
         (index (fn-anchor-wire-nth 2 top))
         (srep-octets (fn-anchor-wire-nth 3 top))
         (delegation-signature (fn-anchor-wire-nth 0 cert))
         (dele-octets (fn-anchor-wire-nth 1 cert))
         (delegate (fn-anchor-wire-nth 2 cert))
         (mint (fn-anchor-wire-nth 3 cert))
         (maxt (fn-anchor-wire-nth 4 cert))
         (radius (fn-anchor-wire-nth 0 srep))
         (midpoint (fn-anchor-wire-nth 1 srep))
         (root (fn-anchor-wire-nth 2 srep))
         (anchor (fn-anchor key delegate mint maxt delegation-signature
                            midpoint radius nonce signature root)))
    (cond ((not (fn-anchor-p anchor))
           (fn-anchor-wire-result-error :anchor-fields))
          ((not (equal dele-octets (fn-anchor-dele-octets anchor)))
           (fn-anchor-wire-result-error :delegation-canonical))
          ((not (equal srep-octets (fn-anchor-srep-octets anchor)))
           (fn-anchor-wire-result-error :response-canonical))
          (t (fn-anchor-wire-result-ok (list anchor path index) nil)))))

(defun fn-anchor-wire-parse-response (packet nonce key)
  (declare (xargs :guard t))
  (if (not (and (fn-anchor-wire-widthp nonce *fn-anchor-nonce-octets*)
                (fn-anchor-wire-widthp key *fn-anchor-key-octets*)))
      (fn-anchor-wire-result-error :arguments)
    (let ((top-result (fn-anchor-wire-parse-top packet nonce)))
      (if (not (fn-anchor-wire-result-okp top-result))
          top-result
        (let* ((top (fn-anchor-wire-result-value top-result))
               (srep-result
                (fn-anchor-wire-parse-srep (fn-anchor-wire-nth 3 top)))
               (cert-result
                (fn-anchor-wire-parse-cert (fn-anchor-wire-nth 4 top))))
          (if (not (fn-anchor-wire-result-okp srep-result))
              srep-result
            (if (not (fn-anchor-wire-result-okp cert-result))
                cert-result
              (fn-anchor-wire-compose-response
               top
               (fn-anchor-wire-result-value cert-result)
               (fn-anchor-wire-result-value srep-result)
               nonce key))))))))

; The native caller's accepted tree shape.  Root equality remains the separate
; SHA-512 primitive observation passed to fn-anchor's one-nonce seam.
(defun fn-anchor-wire-single-leafp (parsed)
  (declare (xargs :guard t))
  (and (null (fn-anchor-wire-parsed-path parsed))
       (equal (fn-anchor-wire-parsed-index parsed) 0)))

(defthm fn-anchor-wire-compose-success-has-anchor
  (implies (fn-anchor-wire-result-okp
            (fn-anchor-wire-compose-response top cert srep nonce key))
           (fn-anchor-p
            (fn-anchor-wire-parsed-anchor
             (fn-anchor-wire-result-value
              (fn-anchor-wire-compose-response top cert srep nonce key)))))
  :hints (("Goal"
           :in-theory (enable fn-anchor-wire-compose-response
                              fn-anchor-wire-result-ok
                              fn-anchor-wire-result-error
                              fn-anchor-wire-result-okp
                              fn-anchor-wire-result-value
                              fn-anchor-wire-parsed-anchor))))

(defthm fn-anchor-wire-parse-success-has-anchor
  (implies (fn-anchor-wire-result-okp
            (fn-anchor-wire-parse-response packet nonce key))
           (fn-anchor-p
            (fn-anchor-wire-parsed-anchor
             (fn-anchor-wire-result-value
              (fn-anchor-wire-parse-response packet nonce key)))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-anchor-wire-parse-response)
                (fn-anchor-wire-parse-top
                 fn-anchor-wire-parse-srep
                 fn-anchor-wire-parse-cert
                 fn-anchor-wire-parse-dele
                 fn-anchor-wire-compose-response
                 fn-anchor-wire-result-okp
                 fn-anchor-wire-result-value
                 fn-anchor-wire-parsed-anchor
                 fn-anchor-wire-parse-message
                 fn-anchor-wire-parse-message-counted
                 fn-anchor-wire-build-fields
                 fn-anchor-wire-read-u32s
                 fn-anchor-wire-read-tags)))))

(deftheory fn-anchor-wire-vocabulary
  '((:d fn-anchor-wire-result-ok)
    (:d fn-anchor-wire-result-error)
    (:d fn-anchor-wire-result-okp)
    (:d fn-anchor-wire-result-value)
    (:d fn-anchor-wire-result-rest)
    (:d fn-anchor-wire-result-reason)
    (:d fn-anchor-wire-nth)
    (:d fn-anchor-wire-split)
    (:d fn-anchor-wire-le-value)
    (:d fn-anchor-wire-le32)
    (:d fn-anchor-wire-le64)
    (:d fn-anchor-wire-read-u32s)
    (:d fn-anchor-wire-read-tags)
    (:d fn-anchor-wire-tags-increasingp)
    (:d fn-anchor-wire-build-fields)
    (:d fn-anchor-wire-parse-message-counted)
    (:d fn-anchor-wire-has-fieldp)
    (:d fn-anchor-wire-field)
    (:d fn-anchor-wire-requiredp)
    (:d fn-anchor-wire-widthp)
    (:d fn-anchor-wire-parsed-anchor)
    (:d fn-anchor-wire-parsed-path)
    (:d fn-anchor-wire-parsed-index)
    (:d fn-anchor-wire-parse-message)
    (:d fn-anchor-wire-parse-dele)
    (:d fn-anchor-wire-parse-cert)
    (:d fn-anchor-wire-parse-srep)
    (:d fn-anchor-wire-parse-top)
    (:d fn-anchor-wire-compose-response)
    (:d fn-anchor-wire-parse-response)
    (:d fn-anchor-wire-single-leafp)
    fn-anchor-wire-compose-success-has-anchor
    fn-anchor-wire-parse-success-has-anchor))

(in-theory (disable fn-anchor-wire-vocabulary))
