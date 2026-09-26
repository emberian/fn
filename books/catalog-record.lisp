; fn: the held record (wave 5, lane catalog-slice, 2026-09-26; D33; the
; consolidation design section 1.1; gpt-6's answer to PKT-293, section 1 of
; planning/review-2026-09-26-gpt6-answers.md: two views over one tuple).
;
; Two views of one record.  The WIRE record is `fn-record-p'
; (books/records-shape.lisp): an octet-list payload, the codec's domain,
; unchanged by this book.  The HELD record is what the catalog stores and
; the served machine reads: the same eleven positions, read by the SAME
; positional accessors (`fn-record-sequence' .. `fn-record-stamp' are
; `mbe' selectors with guard t, so they read either view), with the payload
; position holding a natural, a HANDLE into the arena (books/payload-arena
; .lisp), and four positions after it:
;
;   11 facts     (octets body-start body-lines)   decided ONCE from the bytes at intern
;   12 context   (verdict delta generation)        decided at intern under the keyring in force
;   13 numbers   ((group . n) ...)                 assigned by the catalog's commit; nil before
;   14 withdrawn nil | (at . by)                   the version at which a cancel withdrew it
;
; Its recognizer is `fn-held-p', never `fn-record-p': the predicate that
; means "contains octets" is not reused to mean "contains an integer".
;
; ALPHA, the abstraction: `fn-held-wire-of' materializes a held record into
; the wire record it stands for, reading the bytes by handle.  INTERN, the
; one place bytes are read to build a held record: `fn-cat-intern-list'
; from a decoded wire record (the open), `fn-cat-intern' from the octet
; buffer (the prepare; the seal is `fn-arena-seal-buffer', no list is
; retained).  The theorem: alpha of intern is the identity on the wire.
;
; The byte facts are what OVER and the served reads walk the payload for
; today: the header/body boundary (`fn-nntp-split-article', books/nntp-
; session.lisp) and the body's CRLF line count (`fn-nov-body-line-count',
; books/nntp-responses.lisp); the equations with those definitions are
; `fn-hf-split-index-is-split-article' and `fn-hf-crlf-count-is-crlf-lines'.
; The context is what `fn-sn-finish' (books/store-node.lisp) computes from
; the bytes at completion: the statement verdict (`fn-stx-verdict-of-octets')
; and the identity delta (`fn-stx-delta', through `fn-sn-accepted-delta'),
; under the keyring and its generation.  Whether the keyring can change
; between the prepare that interns and the finish that consumes is the
; phase gate's theorem in books/catalog-commit.lisp, not this book's.

(in-package "ACL2")
(include-book "payload-arena")
(include-book "stx-lace")
(include-book "nntp-session")

; -----------------------------------------------------------------------------
; The byte facts.

; The index just past the first CRLFCRLF at or after position I, or nil.
(defun fn-hf-split-index (bytes i)
  (declare (xargs :guard (natp i)))
  (if (consp bytes)
      (if (and (eql (car bytes) 13)
               (consp (cdr bytes)) (eql (car (cdr bytes)) 10)
               (consp (cdr (cdr bytes))) (eql (car (cdr (cdr bytes))) 13)
               (consp (cdr (cdr (cdr bytes)))) (eql (car (cdr (cdr (cdr bytes)))) 10))
          (+ i 4)
        (fn-hf-split-index (cdr bytes) (+ i 1)))
    nil))

; The number of CRLF-terminated lines, or nil when the octets are not a
; well-formed line sequence (a bare CR, a bare LF, a NUL, or an unterminated
; tail): `fn-nntp-crlf-lines-aux' with its accumulators replaced by the one
; bit it decides on at the end.
(defun fn-hf-crlf-count (bytes inline)
  (declare (xargs :guard t))
  (if (consp bytes)
      (if (eql (car bytes) 13)
          (if (and (consp (cdr bytes)) (eql (car (cdr bytes)) 10))
              (let ((r (fn-hf-crlf-count (cdr (cdr bytes)) nil)))
                (if r (+ 1 r) nil))
            nil)
        (if (or (eql (car bytes) 10) (eql (car bytes) 0))
            nil
          (fn-hf-crlf-count (cdr bytes) t)))
    (if inline nil 0)))

(defthm fn-hf-split-index-type
  (implies (natp i)
           (or (null (fn-hf-split-index bytes i))
               (natp (fn-hf-split-index bytes i))))
  :rule-classes :type-prescription)

(defthm fn-hf-split-index-bound
  (implies (and (natp i) (fn-hf-split-index bytes i))
           (<= (fn-hf-split-index bytes i) (+ i (len bytes))))
  :rule-classes :linear)

(defthm fn-hf-crlf-count-type
  (or (null (fn-hf-crlf-count bytes inline))
      (natp (fn-hf-crlf-count bytes inline)))
  :rule-classes :type-prescription)

; The column OVER serves: the body's line count when the article splits
; and its body is well formed, else 0 (`fn-nov-body-line-count''s value).
(defun fn-hf-body-lines-of (bytes)
  (declare (xargs :guard (true-listp bytes)))
  (let ((s (fn-hf-split-index bytes 0)))
    (if s
        (let ((n (fn-hf-crlf-count (nthcdr s bytes) nil)))
          (if n n 0))
      0)))

(defun fn-hf-startp (x)
  (declare (xargs :guard t))
  (or (null x) (natp x)))

(fn-defrecord fn-hf
  :constructor (fn-hf-make octets body-start body-lines)
  :fields ((fn-hf-octets natp)
           (fn-hf-body-start fn-hf-startp)
           (fn-hf-body-lines natp))
  :recognizer fn-hf-p
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

(defun fn-held-facts-of (bytes)
  (declare (xargs :guard (true-listp bytes)))
  (fn-hf-make (len bytes) (fn-hf-split-index bytes 0) (fn-hf-body-lines-of bytes)))

(defthm fn-hf-p-of-held-facts-of
  (fn-hf-p (fn-held-facts-of bytes))
  :hints (("Goal" :in-theory (enable fn-hf-p fn-hf-internals))))

; -----------------------------------------------------------------------------
; The equations with the served machine's definitions (books/nntp-session).
; The split: `fn-nntp-split-article-aux' answers :ok exactly when a CRLFCRLF
; is found, and its body is the octets after it.

(defthm fn-hf-split-index-lower-bound
  (implies (and (natp i) (fn-hf-split-index bytes i))
           (<= (+ i 4) (fn-hf-split-index bytes i)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-hf-split-index))))

; The two recursions advance the index and the prefix together.
(local
 (defun fn-hf-split-ind (bytes i prefix-rev)
   (declare (xargs :measure (acl2-count bytes)))
   (if (consp bytes)
       (fn-hf-split-ind (cdr bytes) (+ i 1) (cons (car bytes) prefix-rev))
     (list i prefix-rev))))

(local
 (defthm fn-hf-split-article-aux-okp
   (equal (fn-nntp-split-okp (fn-nntp-split-article-aux bytes prefix-rev))
          (if (fn-hf-split-index bytes i) t nil))
   :rule-classes nil
   :hints (("Goal" :induct (fn-hf-split-ind bytes i prefix-rev)
            :in-theory (enable fn-nntp-split-article-aux fn-nntp-split-okp
                               fn-hf-split-index)))))

(local
 (defthm fn-hf-split-article-aux-body
   (implies (and (natp i) (fn-hf-split-index bytes i))
            (equal (fn-nntp-split-body (fn-nntp-split-article-aux bytes prefix-rev))
                   (nthcdr (- (fn-hf-split-index bytes i) i) bytes)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-hf-split-ind bytes i prefix-rev)
            :in-theory (enable fn-nntp-split-article-aux fn-nntp-split-body
                               fn-hf-split-index)))))

(defthm fn-hf-split-index-is-split-article
  (implies (fn-octet-listp bytes)
           (and (equal (fn-nntp-split-okp (fn-nntp-split-article bytes))
                       (if (fn-hf-split-index bytes 0) t nil))
                (implies (fn-hf-split-index bytes 0)
                         (equal (fn-nntp-split-body (fn-nntp-split-article bytes))
                                (nthcdr (fn-hf-split-index bytes 0) bytes)))))
  :hints (("Goal" :in-theory (enable fn-nntp-split-article)
           :use ((:instance fn-hf-split-article-aux-okp (i 0) (prefix-rev nil))
                 (:instance fn-hf-split-article-aux-body (i 0) (prefix-rev nil))))))

; The line count: the aux answers :ok exactly when the count is decided,
; and then with as many lines as lines-rev held plus the CRLFs.
(local
 (defun fn-hf-lines-ind (bytes line-rev lines-rev)
   (declare (xargs :measure (acl2-count bytes)))
   (if (consp bytes)
       (if (equal (car bytes) 13)
           (if (and (consp (cdr bytes)) (equal (car (cdr bytes)) 10))
               (fn-hf-lines-ind (cdr (cdr bytes)) nil (cons (reverse line-rev) lines-rev))
             (list line-rev lines-rev))
         (fn-hf-lines-ind (cdr bytes) (cons (car bytes) line-rev) lines-rev))
     (list line-rev lines-rev))))

(local
 (defthm fn-hf-crlf-lines-aux-okp
   (equal (equal (car (fn-nntp-crlf-lines-aux bytes line-rev lines-rev)) :ok)
          (if (fn-hf-crlf-count bytes (consp line-rev)) t nil))
   :rule-classes nil
   :hints (("Goal" :induct (fn-hf-lines-ind bytes line-rev lines-rev)
            :in-theory (enable fn-nntp-crlf-lines-aux fn-hf-crlf-count)))))

(local
 (defthm fn-hf-crlf-lines-aux-len
   (implies (fn-hf-crlf-count bytes (consp line-rev))
            (equal (len (car (cdr (fn-nntp-crlf-lines-aux bytes line-rev lines-rev))))
                   (+ (len lines-rev) (fn-hf-crlf-count bytes (consp line-rev)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-hf-lines-ind bytes line-rev lines-rev)
            :in-theory (enable fn-nntp-crlf-lines-aux fn-hf-crlf-count)))))

(defthm fn-hf-crlf-count-is-crlf-lines
  (implies (fn-octet-listp bytes)
           (and (equal (equal (car (fn-nntp-crlf-lines bytes)) :ok)
                       (if (fn-hf-crlf-count bytes nil) t nil))
                (implies (fn-hf-crlf-count bytes nil)
                         (equal (len (car (cdr (fn-nntp-crlf-lines bytes))))
                                (fn-hf-crlf-count bytes nil)))))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-lines)
           :use ((:instance fn-hf-crlf-lines-aux-okp (line-rev nil) (lines-rev nil))
                 (:instance fn-hf-crlf-lines-aux-len (line-rev nil) (lines-rev nil))))))

; `fn-nov-body-line-count' (books/nntp-responses.lisp) is this expression
; over `fn-nntp-split-article' and `fn-nntp-crlf-lines' with `fn-ng-len' for
; `len'; the column is its value by definition.
(local
 (defthm fn-hf-octet-listp-of-nthcdr
   (implies (fn-octet-listp bytes)
            (fn-octet-listp (nthcdr n bytes)))
   :hints (("Goal" :in-theory (enable fn-octet-listp nthcdr)))))

(defthm fn-hf-body-lines-of-is-nov-body-line-count-by-definition
  (implies (fn-octet-listp bytes)
           (equal (fn-hf-body-lines-of bytes)
                  (let ((split (fn-nntp-split-article bytes)))
                    (if (fn-nntp-split-okp split)
                        (let ((lines (fn-nntp-crlf-lines (fn-nntp-split-body split))))
                          (if (equal (car lines) :ok) (len (car (cdr lines))) 0))
                      0))))
  :hints (("Goal" :in-theory (e/d (fn-hf-body-lines-of)
                                  (fn-nntp-split-article fn-nntp-crlf-lines))
           :do-not-induct t
           :use ((:instance fn-hf-crlf-count-is-crlf-lines
                            (bytes (nthcdr (fn-hf-split-index bytes 0) bytes)))))))

; -----------------------------------------------------------------------------
; The context: what the finish decides from the bytes, decided at intern
; under the keyring and generation in force.

(defun fn-hc-anyp (x)
  (declare (xargs :guard t) (ignore x))
  t)

(fn-defrecord fn-hc
  :constructor (fn-hc-make verdict delta generation)
  :fields ((fn-hc-verdict fn-hc-anyp)
           (fn-hc-delta fn-hc-anyp)
           (fn-hc-generation natp))
  :recognizer fn-hc-p
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

(defun fn-held-context-of (bytes keyring generation)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (fn-hc-make (fn-stx-verdict-of-octets bytes keyring generation)
              (fn-stx-delta bytes keyring)
              generation))

(defthm fn-hc-p-of-held-context-of
  (implies (natp generation)
           (fn-hc-p (fn-held-context-of bytes keyring generation)))
  :hints (("Goal" :in-theory (enable fn-hc-p fn-hc-internals))))

; -----------------------------------------------------------------------------
; The held record.

(defun fn-held-numbersp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (consp (car x)) (posp (cdr (car x)))
         (fn-held-numbersp (cdr x)))))

(defun fn-held-withdrawnp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x) (natp (car x)) (natp (cdr x)))))

(fn-defrecord fn-held
  :constructor (fn-held-make sequence txid generation msgid payload groups
                             obligation-id content-subject release-evidence
                             charge stamp facts context numbers withdrawn)
  :fields ((fn-held-sequence fn-record-uint64p)
           (fn-held-txid fn-record-uint64p)
           (fn-held-generation fn-record-uint64p)
           (fn-held-msgid fn-record-msgidp)
           (fn-held-payload natp)
           (fn-held-groups fn-record-groups-validp)
           (fn-held-obligation-id fn-record-metadata-bytes-p)
           (fn-held-content-subject fn-record-metadata-bytes-p)
           (fn-held-release-evidence fn-record-metadata-bytes-p)
           (fn-held-charge fn-record-uint64p)
           (fn-held-stamp fn-record-stampp)
           (fn-held-facts fn-hf-p)
           (fn-held-context fn-hc-p)
           (fn-held-numbers fn-held-numbersp)
           (fn-held-withdrawn fn-held-withdrawnp))
  :recognizer fn-held-p
  :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

; The eleven wire positions are read by the wire accessors: one vocabulary
; (a held accessor rewrites to the wire one; the wire's rules then apply).
(defthm fn-held-accessors-are-the-wire-accessors
  (and (equal (fn-held-sequence h) (fn-record-sequence h))
       (equal (fn-held-txid h) (fn-record-txid h))
       (equal (fn-held-generation h) (fn-record-generation h))
       (equal (fn-held-msgid h) (fn-record-msgid h))
       (equal (fn-held-payload h) (fn-record-payload h))
       (equal (fn-held-groups h) (fn-record-groups h))
       (equal (fn-held-obligation-id h) (fn-record-obligation-id h))
       (equal (fn-held-content-subject h) (fn-record-content-subject h))
       (equal (fn-held-release-evidence h) (fn-record-release-evidence h))
       (equal (fn-held-charge h) (fn-record-charge h))
       (equal (fn-held-stamp h) (fn-record-stamp h)))
  :hints (("Goal" :in-theory (enable fn-record-internals fn-held-internals))))

; The recognizer executes (its field recognizers are the wire record's,
; all guard-verified); a list of held records; what a row of one satisfies.
(verify-guards fn-held-p)

(defun fn-held-listp (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      (null xs)
    (and (fn-held-p (car xs)) (fn-held-listp (cdr xs)))))

(defthm fn-held-listp-forward-true-listp
  (implies (fn-held-listp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defthm fn-held-p-of-nth-of-held-listp
  (implies (and (fn-held-listp xs) (natp i) (< i (len xs)))
           (fn-held-p (nth i xs))))

(defthm fn-held-listp-of-update-nth
  (implies (and (fn-held-listp xs) (fn-held-p h) (natp i) (< i (len xs)))
           (fn-held-listp (update-nth i h xs))))

(defthm fn-held-listp-of-append-one
  (implies (and (fn-held-listp xs) (fn-held-p h))
           (fn-held-listp (append xs (list h)))))

(defthm fn-held-p-fields
  (implies (fn-held-p h)
           (and (natp (fn-record-payload h))
                (fn-hf-p (fn-held-facts h))
                (fn-hc-p (fn-held-context h))
                (fn-held-numbersp (fn-held-numbers h))
                (fn-held-withdrawnp (fn-held-withdrawn h))))
  :hints (("Goal" :in-theory (enable fn-held-p))))

; -----------------------------------------------------------------------------
; ALPHA: the wire record a held record stands for, given its bytes.

(defun fn-held-wire (h payload)
  (declare (xargs :guard t))
  (fn-record-make (fn-record-sequence h) (fn-record-txid h)
                  (fn-record-generation h) (fn-record-msgid h) payload
                  (fn-record-groups h) (fn-record-obligation-id h)
                  (fn-record-content-subject h) (fn-record-release-evidence h)
                  (fn-record-charge h) (fn-record-stamp h)))

(defun fn-held-wire-of (h fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp (fn-record-payload h))
                              (< (fn-record-payload h) (fn-arena-count fn-arena)))))
  (fn-held-wire h (fn-arena-payload (fn-record-payload h) fn-arena)))

; On a wire record, replacing the payload by its own is the identity.
(defthm fn-held-wire-of-wire-record
  (implies (fn-record-shapep w)
           (equal (fn-held-wire w (fn-record-payload w)) w))
  :hints (("Goal" :in-theory (enable fn-held-wire))))

; -----------------------------------------------------------------------------
; INTERN.

; From a decoded wire record (the open): seal the payload, keep the handle.
(defun fn-cat-intern-list (w keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-record-p w) (fn-prin-keyringp keyring)
                              (natp generation))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let* ((bytes (fn-record-payload w))
         (h (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-list bytes fn-arena)))
    (mv (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                      (fn-record-generation w) (fn-record-msgid w) h
                      (fn-record-groups w) (fn-record-obligation-id w)
                      (fn-record-content-subject w) (fn-record-release-evidence w)
                      (fn-record-charge w) (fn-record-stamp w)
                      (fn-held-facts-of bytes)
                      (fn-held-context-of bytes keyring generation)
                      nil nil)
        fn-arena)))

; From the octet buffer (the prepare): the wire record W supplies the
; metadata, the buffer the bytes; the seal copies the buffer's cells and
; no list is retained.  The facts and the context are stated over the
; buffer's logical list; an exec that scans the buffer by index for the
; split and the line count is a later refinement of this definition.
(defun fn-cat-intern (w fn-octets keyring generation fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (let* ((bytes (fn-octets-list fn-octets))
         (h (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-buffer fn-octets fn-arena)))
    (mv (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                      (fn-record-generation w) (fn-record-msgid w) h
                      (fn-record-groups w) (fn-record-obligation-id w)
                      (fn-record-content-subject w) (fn-record-release-evidence w)
                      (fn-record-charge w) (fn-record-stamp w)
                      (fn-held-facts-of bytes)
                      (fn-held-context-of bytes keyring generation)
                      nil nil)
        fn-arena)))

; -----------------------------------------------------------------------------
; The intern's theorems.

; The interned record is a held record whose handle is the old count.
(defthm fn-held-p-of-intern-list
  (implies (and (fn-record-p w) (natp generation))
           (fn-held-p (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (enable fn-record-p fn-held-p fn-record-internals
                                     fn-held-internals fn-hf-p fn-hc-p))))

(defthm fn-intern-list-handle
  (equal (fn-record-payload (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena)))
         (fn-arena-count fn-arena))
  :hints (("Goal" :in-theory (enable fn-record-internals fn-held-internals))))

(defthm fn-intern-list-arena
  (equal (mv-nth 1 (fn-cat-intern-list w keyring generation fn-arena))
         (fn-arena-seal-list (fn-record-payload w) fn-arena)))

; The wire accessors of a held record built by the constructor.
(defthm fn-record-accessors-of-held-make
  (let ((h (fn-held-make sequence txid generation msgid payload groups
                         obligation-id content-subject release-evidence
                         charge stamp facts context numbers withdrawn)))
    (and (equal (fn-record-sequence h) sequence)
         (equal (fn-record-txid h) txid)
         (equal (fn-record-generation h) generation)
         (equal (fn-record-msgid h) msgid)
         (equal (fn-record-payload h) payload)
         (equal (fn-record-groups h) groups)
         (equal (fn-record-obligation-id h) obligation-id)
         (equal (fn-record-content-subject h) content-subject)
         (equal (fn-record-release-evidence h) release-evidence)
         (equal (fn-record-charge h) charge)
         (equal (fn-record-stamp h) stamp)
         (equal (fn-held-facts h) facts)
         (equal (fn-held-context h) context)
         (equal (fn-held-numbers h) numbers)
         (equal (fn-held-withdrawn h) withdrawn)))
  :hints (("Goal" :in-theory (enable fn-record-internals fn-held-internals))))

; KEYSTONE: alpha of intern is the identity on the wire record.  The sealed
; handle is the old count, which after the seal denotes the payload
; (fn-arena-seal-new-handle); the other ten positions are copied.
(defthm fn-cat-intern-list-materializes
  (implies (fn-record-shapep w)
           (mv-let (held fn-arena)
             (fn-cat-intern-list w keyring generation fn-arena)
             (equal (fn-held-wire-of held fn-arena) w)))
  :hints (("Goal" :in-theory (e/d (fn-held-wire fn-held-wire-of fn-cat-intern-list)
                                  (fn-arena-payload-is-nth fn-arena-count-is-len
                                   fn-arena-seal-list-is-append))
           :use ((:instance fn-arena-seal-new-handle (xs (fn-record-payload w)))))))

; The buffer intern is the list intern of the wire record whose payload is
; the buffer's list: the two entries build the same held record.  No
; hypothesis: both seals are the same append of the same list.
(defthm fn-cat-intern-is-intern-list
  (equal (fn-cat-intern w fn-octets keyring generation fn-arena)
         (fn-cat-intern-list (fn-held-wire w (fn-octets-list fn-octets))
                             keyring generation fn-arena))
  :hints (("Goal" :in-theory (enable fn-held-wire fn-cat-intern fn-cat-intern-list
                                     fn-arena-seal-buffer fn-arena-seal-list))))

(in-theory (disable fn-hf-split-index fn-hf-crlf-count fn-hf-body-lines-of
                    fn-held-facts-of fn-held-context-of fn-held-wire
                    fn-held-wire-of fn-cat-intern-list fn-cat-intern))
