; fn: the store's identity, asked of the running owner by one control request
; (Mini M4; planning/design/wire-grammar-2026-10-04.md section 5).
;
; `fn identity CONTROL' sends `fn-stid-request' (FNCT kind 24, the grammar
; *fn-wf-identity-request-grammar*) over the 0600 control socket; the owner
; answers `fn-stid-reply' (FNCT kind 25, *fn-wf-identity-reply-grammar*) from
;
;   * the genesis record its open read (books/store-genesis.lisp fn-gen-open's
;     verdict, which the host keeps as the global fn-store-genesis): format
;     word, node identity, schema digest, profile digest, and the creating
;     image's revision;
;   * its consumer state (books/consumer-position.lisp: (:consumer-state
;     HISTORY INCARNATION ...), NIL before the first bootstrap): history id
;     and incarnation, empty before a bootstrap;
;   * the running image's recorded source revision (host/native/io.lisp
;     fnn-checkpoint-revision; "unknown" on an image that records none);
;   * the digest of the exported grammar file this image renders
;     (books/wire-export.lisp *fn-wgx-file-digest*).
;
; The interpreter IS the codec: both frames are fn-wg-encode / fn-wg-decode
; at the family constants, so their round trips are fn-wg-decode-of-encode
; and fn-wg-encode-of-decode.  The client prints `fn-stid-line' and exits by
; `fn-stid-exit-class'.
;
; KEYSTONES
;   fn-stid-reply-of-a-genesis-decodes     for every genesis record the open
;     accepts (fn-gen-p), whatever the consumer state and running revision,
;     the reply the owner sends decodes, whole, to the accepted value that
;     carries that genesis's format, node, schema, profile and revision;
;   fn-stid-request-is-recognized          the request the client sends is the
;     one the owner recognizes, and nothing longer is.
;
; This book owns the prefix `fn-stid-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "wire-export")
(include-book "store-genesis")

; -----------------------------------------------------------------------------
; The request

(defun fn-stid-request ()
  (declare (xargs :guard t))
  (fn-wg-encode *fn-wf-identity-request-grammar* nil))

(defun fn-stid-request-p (octets)
  (declare (xargs :guard t))
  (let ((r (fn-wg-decode *fn-wf-identity-request-grammar* octets)))
    (and (fn-wg-okp r) (not (consp (fn-wg-rest r))))))

; -----------------------------------------------------------------------------
; The answer

(defconst *fn-stid-unknown* '(117 110 107 110 111 119 110)) ; "unknown"

; An id field: the consumer state's history or incarnation, or empty.
(defun fn-stid-id (x)
  (declare (xargs :guard t))
  (if (and (fn-cbor-octet-listp x) (<= (len x) 64)) x nil))

; A revision field: frame text (UTF-8, 1..512 octets), else "unknown".
(defun fn-stid-text (x)
  (declare (xargs :guard t))
  (if (and (consp x) (<= (len x) 512) (fn-wg-utf8p x)) x *fn-stid-unknown*))

(defun fn-stid-genesis-of (verdict)
  ; The genesis record of fn-gen-open's verdict (:genesis G TRAILER), or nil.
  (declare (xargs :guard t))
  (if (and (consp verdict) (equal (car verdict) :genesis) (consp (cdr verdict)))
      (cadr verdict)
    nil))

(defun fn-stid-value (verdict consumer-state running)
  (declare (xargs :guard t))
  (let ((g (fn-stid-genesis-of verdict)))
    (if (fn-gen-p g)
        (list :accepted
              (list (fn-gen-format g) (fn-gen-node g) (fn-gen-schema g)
                    (fn-gen-profile-digest g)
                    (fn-stid-id (fn-cp-nth 1 consumer-state))
                    (fn-stid-id (fn-cp-nth 2 consumer-state))
                    (fn-gen-revision g)
                    (fn-stid-text running)
                    *fn-wgx-file-digest*))
      (list :refused :no-genesis))))

(defun fn-stid-reply (verdict consumer-state running)
  (declare (xargs :guard t))
  (fn-wg-encode *fn-wf-identity-reply-grammar*
                (fn-stid-value verdict consumer-state running)))

; The client's read of a reply: the value, or nil for a frame that is not a
; whole identity reply.
(defun fn-stid-reply-read (octets)
  (declare (xargs :guard t))
  (let ((r (fn-wg-decode *fn-wf-identity-reply-grammar* octets)))
    (if (and (fn-wg-okp r) (not (consp (fn-wg-rest r)))) (fn-wg-value r) nil)))

; -----------------------------------------------------------------------------
; The line the client prints, and its exit class

(defun fn-stid-field (key octets hexp)
  ; " KEY=VALUE": VALUE the octets' hex, or the octets as text.
  (declare (xargs :guard t))
  (append (list 32) (fn-wgx-str key) (list 61)
          (if hexp (fn-wgx-hex octets) (true-list-fix octets))))

(defun fn-stid-line (value)
  ; ASCII except the two revisions, which are the image's recorded text.
  (declare (xargs :guard t))
  (let ((fields (if (consp value) (fn-wg-arg 1 value) nil)))
    (cond
     ((and (consp value) (equal (car value) :accepted))
      (append (fn-wgx-str "fn-store-identity-v1")
              (fn-stid-field "format" (fn-wg-arg 0 fields) nil)
              (fn-stid-field "node" (fn-wg-arg 1 fields) t)
              (fn-stid-field "schema" (fn-wg-arg 2 fields) t)
              (fn-stid-field "profile" (fn-wg-arg 3 fields) t)
              (fn-stid-field "history" (fn-wg-arg 4 fields) t)
              (fn-stid-field "incarnation" (fn-wg-arg 5 fields) t)
              (fn-stid-field "created-revision" (fn-wg-arg 6 fields) nil)
              (fn-stid-field "running-revision" (fn-wg-arg 7 fields) nil)
              (fn-stid-field "grammar" (fn-wg-arg 8 fields) t)))
     ((and (consp value) (equal (car value) :refused))
      (append (fn-wgx-str "fn-store-identity-refused-v1 ")
              (fn-wgx-str (if (symbolp (fn-wg-arg 1 value))
                              (string-downcase (symbol-name (fn-wg-arg 1 value)))
                            ""))))
     (t (fn-wgx-str "fn-store-identity-uncertain-v1 reply")))))

; :accepted, :refused, or :fenced for no readable reply (the client cannot
; know what the owner answered): the outcome classes of books/outcome-class.
(defun fn-stid-exit-class (value)
  (declare (xargs :guard t))
  (cond ((and (consp value) (equal (car value) :accepted)) :accepted)
        ((and (consp value) (equal (car value) :refused)) :refused)
        (t :fenced)))

; -----------------------------------------------------------------------------
; Keystones

(local (in-theory (disable fn-wg-decode fn-wg-encode fn-wg-valuep fn-wg-grammarp
                           fn-wg-delimitedp)))

(local
 (defthm fn-stid-utf8-of-gen-text
   (implies (fn-frame-textp x)
            (and (consp x) (<= (len x) 512) (fn-wg-utf8p x) (fn-cbor-octet-listp x)))
   :hints (("Goal" :in-theory (enable fn-frame-textp fn-wg-utf8p)))))

(defthm fn-stid-value-is-a-reply-value
  (fn-wg-valuep *fn-wf-identity-reply-grammar*
                (fn-stid-value verdict consumer-state running))
  :hints (("Goal" :in-theory (enable fn-wg-valuep fn-gen-p fn-stid-text fn-stid-id
                                     fn-wg-class-okp fn-gen-digest-fieldp))))
