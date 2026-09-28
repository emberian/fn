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
; phase gate's theorem of the commit book that follows this one (the
; continuation, PKT-585), not this book's.

(in-package "ACL2")
(include-book "held-record")
(include-book "payload-arena")
(include-book "stx-lace")
(include-book "nntp-session")
(include-book "control-authority")   ; fn-ctl-control-of: the control fact
(include-book "nov-fields")          ; fn-nov-header-content: the overview column
(include-book "reclaim-tombstone")   ; fn-rcl-tombstonep: the column's tombstone flag

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
;
; The executable is a loop (D27; lane line-stack, 2026-09-27): the count
; rides in ACC and every step is a tail call.  The recursion it replaces
; took one control-stack frame per LINE of the article at every intern (the
; committer's `fn-cat-intern'): a POST of 2,000,000 lines exhausted a 1 MiB
; stack and stopped the owner (tests.test_native_served_line_stack).
(defun fn-hf-crlf-count-onto (bytes inline acc)
  (declare (xargs :guard (natp acc)))
  (if (consp bytes)
      (if (eql (car bytes) 13)
          (if (and (consp (cdr bytes)) (eql (car (cdr bytes)) 10))
              (fn-hf-crlf-count-onto (cdr (cdr bytes)) nil (+ 1 acc))
            nil)
        (if (or (eql (car bytes) 10) (eql (car bytes) 0))
            nil
          (fn-hf-crlf-count-onto (cdr bytes) t acc)))
    (if inline nil acc)))

(defun fn-hf-crlf-count (bytes inline)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp bytes)
           (if (eql (car bytes) 13)
               (if (and (consp (cdr bytes)) (eql (car (cdr bytes)) 10))
                   (let ((r (fn-hf-crlf-count (cdr (cdr bytes)) nil)))
                     (if r (+ 1 r) nil))
                 nil)
             (if (or (eql (car bytes) 10) (eql (car bytes) 0))
                 nil
               (fn-hf-crlf-count (cdr bytes) t)))
         (if inline nil 0))
       :exec (fn-hf-crlf-count-onto bytes inline 0)))

(local
 (defthm fn-hf-crlf-count-onto-adds
   (implies (acl2-numberp acc)
            (equal (fn-hf-crlf-count-onto bytes inline acc)
                   (let ((r (fn-hf-crlf-count bytes inline)))
                     (if r (+ acc r) nil))))))

;  KEYSTONE (D27, constant stack at the intern).  The loop the host runs is
; the count the specification defines, on every argument.
(defthm fn-hf-crlf-count-onto-is-crlf-count
  (equal (fn-hf-crlf-count-onto bytes inline 0)
         (fn-hf-crlf-count bytes inline)))

(verify-guards fn-hf-crlf-count)

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

; The overview COLUMN (lane served-columns): from ONE parse result PARSED of
; BYTES, the five RFC 3977 section 8.3.2 fields exactly as the served OVER
; renders them (books/nov-fields.lisp fn-nov-header-content of the parsed
; view), each kept as a string (one character per octet: a column holds no
; octet list, D27), whether the parse succeeded under the same test
; fn-nov-overview makes, and whether the bytes are a reclaim tombstone.  A
; caller that already parsed passes its parse (store-intern-once, the POST's
; carried parse); fn-hnov-of parses.
(defun fn-hnov-field (view name)
  (declare (xargs :guard (fn-article-syntax-p view)))
  (fn-record-octets-string (fn-nov-header-content view name)))

(defun fn-hnov-parsed-okp (parsed)
  (declare (xargs :guard t))
  (and (true-listp parsed)
       (fn-article-result-okp parsed)
       (fn-article-syntax-p (fn-article-result-article parsed))))

(defun fn-hnov-of-parsed (bytes parsed)
  (declare (xargs :guard t))
  (let ((tomb (fn-rcl-tombstonep bytes)))
    (if (fn-hnov-parsed-okp parsed)
        (let ((view (fn-article-result-article parsed)))
          (fn-hnov-make tomb t
                        (fn-hnov-field view *fn-nov-subject-name*)
                        (fn-hnov-field view *fn-nov-from-name*)
                        (fn-hnov-field view *fn-nov-date-name*)
                        (fn-hnov-field view *fn-nov-message-id-name*)
                        (fn-hnov-field view *fn-nov-references-name*)))
      (fn-hnov-make tomb nil "" "" "" "" ""))))

(defun fn-hnov-of (bytes)
  (declare (xargs :guard t))
  (fn-hnov-of-parsed bytes (fn-article-parse bytes)))

(defthm fn-hnov-field-stringp
  (stringp (fn-hnov-field view name))
  :rule-classes :type-prescription)

(defthm fn-hnov-tombstonep-booleanp
  (booleanp (fn-rcl-tombstonep bytes))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-rcl-tombstonep))))

(defthm fn-hnov-p-of-hnov-of-parsed
  (fn-hnov-p (fn-hnov-of-parsed bytes parsed))
  :hints (("Goal" :in-theory (e/d (fn-hnov-p fn-hnov-internals fn-hnov-flagp)
                                  (fn-hnov-field fn-rcl-tombstonep fn-hnov-parsed-okp)))))

(defthm fn-hnov-p-of-hnov-of
  (fn-hnov-p (fn-hnov-of bytes))
  :hints (("Goal" :use ((:instance fn-hnov-p-of-hnov-of-parsed (parsed (fn-article-parse bytes))))
           :in-theory (e/d (fn-hnov-of) (fn-hnov-of-parsed fn-article-parse fn-hnov-p)))))

; Closed from here on: a proof that opens a row's facts sees the column as
; one term, never the parse (fn-held-p-of-intern-list and the intern's
; materialization opened it into the article grammar: 17 million steps).
(in-theory (disable fn-hnov-of fn-hnov-of-parsed fn-hnov-field fn-hnov-parsed-okp))

; The control position: the control vocabulary's three facts, then the
; overview column (books/held-record.lisp fn-hf-nov: the fourth element).
(defun fn-hf-control-with-nov (control nov)
  (declare (xargs :guard t))
  (list (fn-ctl-control-target control) (fn-ctl-control-keys control)
        (fn-ctl-control-locks control) nov))

(defthm fn-hf-control-with-nov-fields
  (and (equal (fn-ctl-control-target (fn-hf-control-with-nov c nov)) (fn-ctl-control-target c))
       (equal (fn-ctl-control-keys (fn-hf-control-with-nov c nov)) (fn-ctl-control-keys c))
       (equal (fn-ctl-control-locks (fn-hf-control-with-nov c nov)) (fn-ctl-control-locks c)))
  :hints (("Goal" :in-theory (enable fn-ctl-control-target fn-ctl-control-keys
                                     fn-ctl-control-locks fn-ctl-at))))

(defthm fn-hf-control-with-nov-true-listp
  (true-listp (fn-hf-control-with-nov c nov))
  :rule-classes :type-prescription)

(in-theory (disable fn-hf-control-with-nov))

(defun fn-held-facts-of (bytes)
  (declare (xargs :guard (true-listp bytes)))
  (fn-hf-make (len bytes) (fn-hf-split-index bytes 0) (fn-hf-body-lines-of bytes)
              (fn-hf-control-with-nov (fn-ctl-control-of bytes) (fn-hnov-of bytes))))

(defthm fn-hf-p-of-held-facts-of
  (fn-hf-p (fn-held-facts-of bytes))
  :hints (("Goal" :in-theory (e/d (fn-held-facts-of fn-hf-p fn-hf-internals fn-hf-startp)
                                  (fn-hnov-of fn-ctl-control-of)))))

; The column of a row's bytes is fn-hnov-of of them.
(defthm fn-hf-nov-of-held-facts-of
  (equal (fn-hf-nov (fn-held-facts-of bytes))
         (fn-hnov-of bytes))
  :hints (("Goal" :in-theory (e/d (fn-hf-internals fn-hf-control-with-nov) (fn-hnov-of)))))

; The control facts of a row's bytes are what the control vocabulary reads
; from them (books/control-authority.lisp fn-ctl-control-of-fields): the
; refresh that reads them from the row reads what it read from the octets.
(defthm fn-hf-control-of-held-facts-of
  (and (equal (fn-ctl-control-target (fn-hf-control (fn-held-facts-of bytes)))
              (fn-ctl-control-target (fn-ctl-control-of bytes)))
       (equal (fn-ctl-control-keys (fn-hf-control (fn-held-facts-of bytes)))
              (fn-ctl-control-keys (fn-ctl-control-of bytes)))
       (equal (fn-ctl-control-locks (fn-hf-control (fn-held-facts-of bytes)))
              (fn-ctl-control-locks (fn-ctl-control-of bytes))))
  :hints (("Goal" :in-theory (e/d (fn-hf-internals fn-held-facts-of)
                                  (fn-hnov-of fn-ctl-control-of fn-ctl-control-target
                                   fn-ctl-control-keys fn-ctl-control-locks)))))

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

(defun fn-held-context-of (bytes keyring generation)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (fn-hc-make (fn-stx-verdict-of-octets bytes keyring generation)
              (fn-stx-delta bytes keyring)
              generation))

(defthm fn-hc-p-of-held-context-of
  (implies (natp generation)
           (fn-hc-p (fn-held-context-of bytes keyring generation)))
  :hints (("Goal" :in-theory (enable fn-hc-p fn-hc-internals fn-hc-verdictp))))

(defun fn-held-wire-of (h fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp (fn-record-payload h))
                              (< (fn-record-payload h) (fn-arena-count fn-arena)))))
  (fn-held-wire h (fn-arena-payload (fn-record-payload h) fn-arena)))

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
                                     fn-held-internals fn-hf-p fn-hc-p
                                     fn-hf-startp fn-hc-verdictp))))

(defthm fn-intern-list-handle
  (equal (fn-record-payload (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena)))
         (fn-arena-count fn-arena))
  :hints (("Goal" :in-theory (enable fn-record-internals fn-held-internals))))

(defthm fn-intern-list-arena
  (equal (mv-nth 1 (fn-cat-intern-list w keyring generation fn-arena))
         (fn-arena-seal-list (fn-record-payload w) fn-arena)))

; fn-record-accessors-of-held-make: books/held-record.lisp (moved down, records-flip).

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

(in-theory (disable fn-hf-split-index fn-hf-crlf-count-onto fn-hf-crlf-count fn-hf-body-lines-of
                    fn-held-facts-of fn-held-context-of fn-held-wire
                    fn-held-wire-of fn-cat-intern-list fn-cat-intern))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:linear fn-hf-split-index-bound)))
