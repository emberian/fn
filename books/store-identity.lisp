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
;     HISTORY INCARNATION ...), NIL before the first bootstrap): the arm
;     `unbootstrapped', or `bootstrapped' with the history id and incarnation
;     (never an empty field);
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
;   fn-stid-value-is-a-reply-value          whatever the open's verdict, the
;     consumer state and the running revision, what the owner answers is a
;     value of the reply grammar (so it decodes, whole, to itself:
;     fn-stid-reply-decodes);
;   fn-stid-reply-of-a-genesis-decodes     for every genesis record the open
;     accepts (fn-gen-p) and every consumer state fn-cp-statep accepts (or
;     none), the reply decodes, whole, to the accepted value that carries that
;     genesis's format, node, schema, profile and revision and that state's
;     history id and incarnation;
;   fn-stid-request-is-recognized          the request the client sends is the
;     one the owner recognizes, and nothing longer is.
;
; This book owns the prefix `fn-stid-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "wire-export")
(include-book "store-genesis")
(include-book "consumer-local-control") ; fn-ncl-absolute-pathp, the control path rule

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

; An identity field of the consumer state: 1..64 octets (fn-cp-idp's shape).
(defun fn-stid-idp (x)
  (declare (xargs :guard t))
  (and (consp x) (fn-cbor-octet-listp x) (<= (len x) 64)))

; The consumer arm: `unbootstrapped' before the first bootstrap (no state),
; `bootstrapped' with the history id and incarnation after it; nil for a
; state whose ids are not ids (never one fn-cp-statep accepts), which the
; owner refuses by name rather than print an empty field.
(defun fn-stid-consumer (consumer-state)
  (declare (xargs :guard t))
  (cond ((null consumer-state) (list :unbootstrapped nil))
        ((and (fn-stid-idp (fn-cp-nth 1 consumer-state))
              (fn-stid-idp (fn-cp-nth 2 consumer-state)))
         (list :bootstrapped (list (fn-cp-nth 1 consumer-state)
                                   (fn-cp-nth 2 consumer-state))))
        (t nil)))

; A revision field: frame text (UTF-8, 1..512 octets), else "unknown".
(defun fn-stid-text (x)
  (declare (xargs :guard t))
  (if (fn-frame-textp x) x *fn-stid-unknown*))

(defun fn-stid-genesis-of (verdict)
  ; The genesis record of fn-gen-open's verdict (:genesis G TRAILER), or nil.
  (declare (xargs :guard t))
  (if (and (consp verdict) (equal (car verdict) :genesis) (consp (cdr verdict)))
      (cadr verdict)
    nil))

(defun fn-stid-value (verdict consumer-state running)
  (declare (xargs :guard t))
  (let ((g (fn-stid-genesis-of verdict))
        (c (fn-stid-consumer consumer-state)))
    (cond ((not (fn-gen-p g)) (list :refused :no-genesis))
          ((not c) (list :refused :consumer-state))
          (t (list :accepted
                   (list (fn-gen-format g) (fn-gen-node g) (fn-gen-schema g)
                         (fn-gen-profile-digest g)
                         c
                         (fn-gen-revision g)
                         (fn-stid-text running)
                         *fn-wgx-file-digest*))))))

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

(defun fn-stid-consumer-fields (c)
  ; " consumer=unbootstrapped", or " consumer=bootstrapped history=HEX
  ; incarnation=HEX".
  (declare (xargs :guard t))
  (if (and (consp c) (equal (car c) :bootstrapped))
      (append (fn-wgx-str " consumer=bootstrapped")
              (fn-stid-field "history" (fn-wg-arg 0 (fn-wg-arg 1 c)) t)
              (fn-stid-field "incarnation" (fn-wg-arg 1 (fn-wg-arg 1 c)) t))
    (fn-wgx-str " consumer=unbootstrapped")))

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
              (fn-stid-consumer-fields (fn-wg-arg 4 fields))
              (fn-stid-field "created-revision" (fn-wg-arg 5 fields) nil)
              (fn-stid-field "running-revision" (fn-wg-arg 6 fields) nil)
              (fn-stid-field "grammar" (fn-wg-arg 7 fields) t)))
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

;; -----------------------------------------------------------------------------
; The client's verb: `fn identity CONTROL'

(defconst *fn-stid-usage*
  "usage: fn identity CONTROL (asks the running owner at the absolute control-socket path CONTROL who this store is: its format word, genesis node identity, schema and profile digests, consumer history id and incarnation, the creating and the running image's revisions, and the digest of the wire-grammar file the image renders; exit 0 accepted, 1 refused by name, 3 no reply the client can read)")

; (:run CONTROL) for exactly one absolute control-socket path (the consumer
; verbs' rule, fn-ncl-absolute-pathp), else (:usage).
(defun fn-stid-cli-plan (argv)
  (declare (xargs :verify-guards nil))
  (if (and (consp argv) (null (cdr argv)) (fn-ncl-absolute-pathp (car argv)))
      (list :run (car argv))
    (list :usage)))

(defun fn-stid-exit-code (value)
  (declare (xargs :guard t))
  (fn-outcome-code (fn-stid-exit-class value)))

; -----------------------------------------------------------------------------
; Keystones

(local (in-theory (disable fn-wg-decode fn-wg-encode fn-wg-valuep fn-wg-grammarp
                           fn-wg-delimitedp fn-gen-p fn-frame-textp fn-gen-digest-fieldp
                           fn-gen-format fn-gen-node fn-gen-schema fn-gen-profile-digest
                           fn-gen-revision)))

(local
 (defthm fn-stid-at-mostp-len
   (implies (fn-cbor-at-mostp x n) (<= (len x) (nfix n)))
   :rule-classes :linear))

; The genesis record's fields, as the reply's fields read them.
(local
 (defthm fn-stid-gen-fields
   (implies (fn-gen-p g)
            (and (fn-frame-textp (fn-gen-format g))
                 (fn-frame-textp (fn-gen-revision g))
                 (fn-gen-digest-fieldp (fn-gen-node g))
                 (fn-gen-digest-fieldp (fn-gen-schema g))
                 (fn-gen-digest-fieldp (fn-gen-profile-digest g))))
   :hints (("Goal" :in-theory (enable fn-gen-p fn-frame-values-okp fn-frame-field-okp
                                      fn-gen-format fn-gen-node fn-gen-schema
                                      fn-gen-profile-digest fn-gen-revision fn-gen-nth)))))

(local
 (defthm fn-stid-text-field
   (implies (fn-frame-textp x)
            (fn-wg-valuep '(:bytes 2 1 512 :utf8) x))
   :hints (("Goal" :in-theory (enable fn-wg-valuep-opener-bytes fn-frame-textp
                                      fn-wg-class-okp fn-wg-utf8p)))))

(local
 (defthm fn-stid-text-len
   (implies (fn-frame-textp x) (<= (len x) 512))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-frame-textp)))))

(local
 (defthm fn-stid-digest-field
   (implies (fn-gen-digest-fieldp x)
            (and (fn-wg-valuep '(:bytes 1 32 32 :any) x)
                 (equal (len x) 32)))
   :hints (("Goal" :in-theory (enable fn-wg-valuep-opener-bytes fn-gen-digest-fieldp
                                      fn-wg-class-okp)))))

(local
 (defthm fn-stid-text-of-running
   (fn-frame-textp (fn-stid-text x))
   :hints (("Goal" :in-theory (enable fn-frame-textp)))))

(local
 (defthm fn-stid-bytes-encode-len
   (implies (equal (fn-wg-op g) :bytes)
            (equal (len (fn-wg-encode g v)) (+ (nfix (fn-wg-arg 1 g)) (len v))))
   :hints (("Goal" :in-theory (enable fn-wg-encode-opener-bytes)))))

; The consumer arm: a value, and at most 131 octets.
(local
 (defthm fn-stid-consumer-field
   (implies (fn-stid-consumer cs)
            (and (fn-wg-valuep *fn-wf-identity-consumer-grammar* (fn-stid-consumer cs))
                 (<= (len (fn-wg-encode *fn-wf-identity-consumer-grammar*
                                        (fn-stid-consumer cs)))
                     131)))
   :hints (("Goal" :in-theory (enable fn-wg-valuep-opener-tag fn-wg-valuep-opener-seq
                                      fn-wg-valuep-opener-bytes fn-wg-encode-opener-tag
                                      fn-wg-encode-opener-seq fn-wg-encode-opener-bytes
                                      fn-wg-class-okp)))))

(local
 (defthm fn-stid-consumer-id-lens
   (and (<= (len (car (cadr (fn-stid-consumer cs)))) 64)
        (<= (len (cadr (cadr (fn-stid-consumer cs)))) 64))
   :rule-classes :linear))

(local (in-theory (disable fn-stid-consumer)))

; The accepted value, over abstract fields of the right shapes.
(local
 (defthm fn-stid-accepted-is-a-reply-value
   (implies (and (fn-frame-textp f) (fn-gen-digest-fieldp n) (fn-gen-digest-fieldp s)
                 (fn-gen-digest-fieldp p) (fn-stid-consumer cs)
                 (fn-frame-textp cr) (fn-frame-textp rr) (fn-gen-digest-fieldp d))
            (fn-wg-valuep *fn-wf-identity-reply-grammar*
                          (list :accepted (list f n s p (fn-stid-consumer cs) cr rr d))))
   :hints (("Goal" :in-theory (enable fn-wg-valuep-opener-frame fn-wg-valuep-opener-tag
                                      fn-wg-valuep-opener-seq fn-wg-encode-opener-tag
                                      fn-wg-encode-opener-seq)))))

(local
 (defthm fn-stid-grammar-digest-field
   (fn-gen-digest-fieldp *fn-wgx-file-digest*)
   :hints (("Goal" :in-theory (enable fn-gen-digest-fieldp)))))

(defthm fn-stid-value-is-a-reply-value
  (fn-wg-valuep *fn-wf-identity-reply-grammar*
                (fn-stid-value verdict consumer-state running))
  :hints (("Goal" :in-theory (disable fn-stid-accepted-is-a-reply-value)
                  :use ((:instance fn-stid-accepted-is-a-reply-value
                                   (f (fn-gen-format (fn-stid-genesis-of verdict)))
                                   (n (fn-gen-node (fn-stid-genesis-of verdict)))
                                   (s (fn-gen-schema (fn-stid-genesis-of verdict)))
                                   (p (fn-gen-profile-digest (fn-stid-genesis-of verdict)))
                                   (cs consumer-state)
                                   (cr (fn-gen-revision (fn-stid-genesis-of verdict)))
                                   (rr (fn-stid-text running))
                                   (d *fn-wgx-file-digest*))))))

; Whatever the owner answers decodes, whole, to itself (the generic round
; trip at the reply grammar).
(defthm fn-stid-reply-decodes
  (equal (fn-wg-decode *fn-wf-identity-reply-grammar*
                       (fn-stid-reply verdict consumer-state running))
         (fn-wg-ok (fn-stid-value verdict consumer-state running) nil))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-stid-reply fn-stid-value-is-a-reply-value
                                fn-wg-decode-of-encode-whole (:e fn-wg-grammarp))
                              (theory 'minimal-theory)))))

(defthm fn-stid-reply-read-of-reply
  (equal (fn-stid-reply-read (fn-stid-reply verdict consumer-state running))
         (fn-stid-value verdict consumer-state running))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-stid-reply-read fn-stid-reply-decodes fn-wg-okp fn-wg-ok
                                fn-wg-rest fn-wg-value (:e consp) car-cons cdr-cons)
                              (theory 'minimal-theory)))))

; KEYSTONE: a genesis the open accepts, and a consumer state the replay
; accepts or none, are answered with exactly their identity.
(defthm fn-stid-reply-of-a-genesis-decodes
  (implies (and (fn-gen-p g)
                (or (null cs) (fn-cp-statep cs)))
           (equal (fn-stid-reply-read (fn-stid-reply (list :genesis g trailer) cs running))
                  (list :accepted
                        (list (fn-gen-format g) (fn-gen-node g) (fn-gen-schema g)
                              (fn-gen-profile-digest g)
                              (if (null cs)
                                  (list :unbootstrapped nil)
                                (list :bootstrapped (list (fn-cp-nth 1 cs) (fn-cp-nth 2 cs))))
                              (fn-gen-revision g)
                              (fn-stid-text running)
                              *fn-wgx-file-digest*))))
  :hints (("Goal" :in-theory (e/d (fn-stid-value fn-stid-consumer fn-stid-genesis-of
                                   fn-stid-idp fn-cp-statep fn-cp-idp)
                                  (fn-stid-reply fn-stid-reply-read fn-stid-text)))))

; The request the client sends is the one the owner recognizes.
(defthm fn-stid-request-is-recognized
  (fn-stid-request-p (fn-stid-request)))
