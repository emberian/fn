; fn: the received article parsed in place from the octet buffer (D27
; boundary 9; row Q2 of COMPLETE-BEFORE-6.6.0: PKT-026, PKT-034, PKT-187;
; lane d27-representation, 2026-09-29).
;
; Every owner entry that classifies a received article -- the posting
; policy's login gate (books/login-binding-live.lisp fn-lb-ocfg-gate), the
; C1 filing plan (books/peer-authored-accept.lisp fn-pa-filing-plan), the
; carrier form and the current plan (fn-pa-carrier-form, fn-pa-current-plan)
; -- takes the article as an octet list and runs fn-article-parse over it.
; The host held the article as a byte vector and consed one list per
; attempt (16 octets of heap an octet): for the gate on every served POST
; (host/native/owner.lisp fnn-owner-attempt-served) and for the four transit
; calls (fnn-owner-attempt-transit).  Here the article is the octet buffer
; (books/octets-stobj.lisp), filled once by the host, and the parse reads it
; by index.  No octet of the article is a cons cell except the header's
; lines (bounded by the profile's header limits, and the lines the logical
; view holds anyway) and, on the signed arm alone, the source the carrier
; field is decoded against (fn-hc-received-plan, whose value is that source).
;
; The twin's result is the reference parse's with the body LOCATED, not
; copied: fn-ars-parse-under answers (:ok (HEADER OFFSET FIELDS)) where the
; reference answers (:ok (HEADER BODY FIELDS)), OFFSET the index the body
; starts at, every error the same (fn-ars-of, the projection; a spec, no
; host path executes it).
;
; KEYSTONE fn-ars-parse-under-is-article-parse-under: over an octet list
; (the buffer's invariant, fn-octets-p) the twin is fn-ars-of the reference
; parse of the buffer's value, and fn-ars-body-is-located: the reference's
; body is the buffer's suffix at the twin's OFFSET.  The consumers the host
; calls (fn-ars-lb-ocfg-gate, fn-ars-filing-plan, fn-ars-carrier-form,
; fn-ars-current-plan; host/owner-host.lisp fn-owner-login-gate-buffer,
; fn-owner-control-filing-buffer, fn-owner-peer-carrier-form-buffer,
; fn-owner-peer-carrier-plan-buffer) are each equal to their reference over
; the buffer's value (the -is-reference theorems), so every keystone about
; the reference (books/login-binding.lisp, peer-authored-accept.lisp,
; control-classify.lisp) applies to the host's verdict.
;
; Not here: the signed arm's source as a buffer range (its digest is
; fn-frame-digest-buffer's shape, books/subject-id-buffer.lisp; the composite
; that keeps the source is PKT-743), and a header-parse cache across the
; four transit calls (each parses the header from the buffer: bounded by
; the profile's header limits, no body cons).

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "peer-authored-accept")
(include-book "login-binding-live")
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The projections (specifications).

; A line result with its REST located: (:ok LINE REST) becomes
; (:ok LINE (- N (len REST))), N the length of the list REST is a suffix of.
(defun fn-ars-line-of (r n)
  (declare (xargs :guard t))
  (if (and (consp r) (equal (car r) :ok) (consp (cdr r)) (consp (cddr r)))
      (list :ok (cadr r) (- (nfix n) (len (caddr r))))
    r))

; A parse result with its BODY located the same way.
(defun fn-ars-of (r n)
  (declare (xargs :guard t))
  (if (and (consp r) (equal (car r) :ok) (consp (cdr r)) (true-listp (cadr r)))
      (let ((a (cadr r)))
        (fn-article-ok
         (fn-article-make (fn-article-header a)
                          (- (nfix n) (len (fn-article-body a)))
                          (fn-article-fields a))))
    r))

(defthm fn-ars-of-okp
  (equal (fn-article-result-okp (fn-ars-of r n))
         (fn-article-result-okp r)))

(defthm fn-ars-of-fields
  (equal (fn-article-fields (fn-article-result-article (fn-ars-of r n)))
         (fn-article-fields (fn-article-result-article r))))

(defthm fn-ars-of-header
  (equal (fn-article-header (fn-article-result-article (fn-ars-of r n)))
         (fn-article-header (fn-article-result-article r))))

(defthm fn-ars-of-article-true-listp
  (equal (true-listp (fn-article-result-article (fn-ars-of r n)))
         (true-listp (fn-article-result-article r))))

(defthm fn-ars-of-error
  (implies (not (fn-article-result-okp r))
           (equal (fn-ars-of r n) r)))

; -----------------------------------------------------------------------------
; The line scanner: books/article.lisp fn-article-next-line-aux with the
; octet list replaced by an index into the buffer.  The line's octets are
; accumulated exactly as the reference accumulates them (a line is at most
; 998 octets, RFC 5322 section 2.1.1, and is the logical view's own value).

(defun fn-ars-next-line-aux (j line-rev left fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (<= j (fn-octets-len fn-octets))
                              (true-listp line-rev) (natp left))
                  :measure (nfix (- (fn-octets-len fn-octets) (nfix j)))))
  (if (or (not (natp j)) (>= j (fn-octets-len fn-octets)))
      (fn-article-error :missing-separator)
    (let ((o (fn-octets-get j fn-octets)))
      (if (equal o 13)
          (if (and (< (1+ j) (fn-octets-len fn-octets))
                   (equal (fn-octets-get (1+ j) fn-octets) 10))
              (list :ok (reverse line-rev) (+ 2 j))
            (fn-article-error :invalid-header))
        (if (equal o 10)
            (fn-article-error :invalid-header)
          (if (zp left)
              (fn-article-error :limit)
            (fn-ars-next-line-aux (1+ j) (cons o line-rev) (1- left)
                                  fn-octets)))))))

(defun fn-ars-next-line (j fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (<= j (fn-octets-len fn-octets)))))
  (fn-ars-next-line-aux j nil *fn-article-max-line-octets* fn-octets))

; The body's framing check (fn-article-body-crlfp) from an index.
(defun fn-ars-body-crlfp (j fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (<= j (fn-octets-len fn-octets)))
                  :measure (nfix (- (fn-octets-len fn-octets) (nfix j)))))
  (if (or (not (natp j)) (>= j (fn-octets-len fn-octets)))
      t
    (let ((o (fn-octets-get j fn-octets)))
      (if (equal o 13)
          (and (< (1+ j) (fn-octets-len fn-octets))
               (equal (fn-octets-get (1+ j) fn-octets) 10)
               (fn-ars-body-crlfp (+ 2 j) fn-octets))
        (and (not (equal o 10))
             (fn-ars-body-crlfp (1+ j) fn-octets))))))

; The parse loop: fn-article-parse-lines with OCTETS replaced by the index
; I; every other argument, test and result is the reference's.
(defun fn-ars-parse-lines (i limits lines-left header-bytes nfields
                             fields-rev current header-rev fn-octets)
  (declare (xargs :stobjs fn-octets
                  :measure (nfix lines-left)
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets))
                              (natp lines-left)
                              (natp header-bytes)
                              (natp nfields)
                              (true-listp fields-rev)
                              (or (null current)
                                  (fn-article-fieldp current))
                              (true-listp header-rev))
                  :verify-guards nil))
  (if (zp lines-left)
      (fn-article-error :header-lines-limit)
    (let ((next (fn-ars-next-line i fn-octets)))
      (if (not (fn-article-line-okp next))
          next
        (let ((line (fn-article-line-value next))
              (rest (fn-article-line-rest next)))
          (if (null line)
              (if (not (fn-ars-body-crlfp rest fn-octets))
                  (fn-article-error :invalid-header)
                (fn-article-ok
                 (fn-article-make
                  (reverse header-rev) rest
                  (fn-article-finish-fields fields-rev current))))
            (if (< (fn-article-limit-octets limits)
                   (+ header-bytes (len line) 2))
                (fn-article-error :header-octets-limit)
              (if (fn-article-wspp (car line))
                  (if (not current)
                      (fn-article-error :invalid-header)
                    (if (not (fn-article-fold-linep line))
                        (fn-article-error :invalid-header)
                      (fn-ars-parse-lines
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       nfields fields-rev (fn-article-add-fold current line)
                       (fn-article-header-rev-add-line header-rev line)
                       fn-octets)))
                (let ((field-result (fn-article-new-field line)))
                  (if (not (fn-article-line-okp field-result))
                      field-result
                    (if (<= (fn-article-limit-fields limits)
                            (+ (if current 1 0) (nfix nfields)))
                        (fn-article-error :header-fields-limit)
                      (fn-ars-parse-lines
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       (if current (+ 1 (nfix nfields)) nfields)
                       (if current (cons current fields-rev) fields-rev)
                       (fn-article-line-value field-result)
                       (fn-article-header-rev-add-line header-rev line)
                       fn-octets))))))))))))

; The parse the host calls: fn-article-parse-under over the whole buffer.
; The reference's two preflights are the buffer's: its length against the
; codec ceiling, and every cell an octet (fn-octets-p, the invariant).
(defun fn-ars-parse-under (limits fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (if (< *fn-article-max-octets* (fn-octets-len fn-octets))
      (fn-article-error :limit)
    (fn-ars-parse-lines 0 limits (1+ (fn-article-limit-lines limits))
                        0 0 nil nil nil fn-octets)))

(defun fn-ars-parse (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (fn-ars-parse-under *fn-article-ceiling-limits* fn-octets))

; -----------------------------------------------------------------------------
; The correspondence.

(local
 (defthm fn-ars-cdr-of-nthcdr
   (equal (cdr (nthcdr j xs)) (nthcdr (+ 1 (nfix j)) xs))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-ars-cddr-of-nthcdr
   (equal (cdr (cdr (nthcdr j xs))) (nthcdr (+ 2 (nfix j)) xs))))

(local
 (defthm fn-ars-consp-of-nthcdr
   (equal (consp (nthcdr j xs)) (< (nfix j) (len xs)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-ars-car-of-nthcdr
   (equal (car (nthcdr j xs)) (nth j xs))
   :hints (("Goal" :in-theory (enable nthcdr nth)))))

(local
 (defthm fn-ars-len-of-nthcdr
   (equal (len (nthcdr j xs)) (nfix (- (len xs) (nfix j))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm fn-ars-next-line-aux-is-reference
  (implies (natp j)
           (equal (fn-ars-next-line-aux j line-rev left fn-octets)
                  (fn-ars-line-of
                   (fn-article-next-line-aux (nthcdr j fn-octets) line-rev left)
                   (len fn-octets))))
  :hints (("Goal" :induct (fn-ars-next-line-aux j line-rev left fn-octets)
                  :in-theory (enable fn-article-next-line-aux))))

(defthm fn-ars-next-line-is-reference
  (implies (natp j)
           (equal (fn-ars-next-line j fn-octets)
                  (fn-ars-line-of (fn-article-next-line (nthcdr j fn-octets))
                                  (len fn-octets))))
  :hints (("Goal" :in-theory (enable fn-article-next-line))))

; The reference's rest is a suffix of its input, no longer than it.
(local
 (defthm fn-ars-reference-rest-len
   (implies (fn-article-line-okp (fn-article-next-line-aux ys lr left))
            (<= (len (fn-article-line-rest (fn-article-next-line-aux ys lr left)))
                (len ys)))
   :hints (("Goal" :in-theory (enable fn-article-next-line-aux)))
   :rule-classes :linear))

(local
 (defthm fn-ars-reference-rest-is-suffix
   (implies (fn-article-line-okp (fn-article-next-line-aux ys lr left))
            (equal (nthcdr (- (len ys)
                              (len (fn-article-line-rest
                                    (fn-article-next-line-aux ys lr left))))
                           ys)
                   (fn-article-line-rest (fn-article-next-line-aux ys lr left))))
   :hints (("Goal" :in-theory (enable fn-article-next-line-aux)
                   :induct (fn-article-next-line-aux ys lr left)))))

; Located in the buffer: the reference's rest is the buffer's suffix at the
; twin's index.
(local
 (defthm fn-ars-reference-rest-located
   (implies (and (natp j) (<= j (len fn-octets))
                 (fn-article-line-okp (fn-article-next-line (nthcdr j fn-octets))))
            (equal (nthcdr (- (len fn-octets)
                              (len (fn-article-line-rest
                                    (fn-article-next-line (nthcdr j fn-octets)))))
                           fn-octets)
                   (fn-article-line-rest (fn-article-next-line (nthcdr j fn-octets)))))
   :hints (("Goal" :in-theory (e/d (fn-article-next-line)
                                   (fn-ars-reference-rest-is-suffix))
                   :use ((:instance fn-ars-reference-rest-is-suffix
                                    (ys (nthcdr j fn-octets)) (lr nil)
                                    (left *fn-article-max-line-octets*)))))))

(defthm fn-ars-body-crlfp-is-reference
  (implies (natp j)
           (equal (fn-ars-body-crlfp j fn-octets)
                  (fn-article-body-crlfp (nthcdr j fn-octets))))
  :hints (("Goal" :induct (fn-ars-body-crlfp j fn-octets)
                  :in-theory (enable fn-article-body-crlfp))))

(defthm fn-ars-parse-lines-is-reference
  (implies (and (natp i) (<= i (len fn-octets)))
           (equal (fn-ars-parse-lines i limits lines-left header-bytes nfields
                                      fields-rev current header-rev fn-octets)
                  (fn-ars-of (fn-article-parse-lines
                              (nthcdr i fn-octets) limits lines-left header-bytes
                              nfields fields-rev current header-rev)
                             (len fn-octets))))
  :hints (("Goal" :induct (fn-ars-parse-lines i limits lines-left header-bytes
                                              nfields fields-rev current
                                              header-rev fn-octets)
                  :in-theory (e/d (fn-article-parse-lines)
                                  (fn-article-next-line fn-ars-next-line
                                   fn-article-new-field fn-article-add-fold
                                   fn-article-header-rev-add-line
                                   fn-article-finish-fields
                                   fn-article-body-crlfp fn-ars-body-crlfp
                                   fn-article-fold-linep fn-article-wspp
                                   fn-article-limit-octets
                                   fn-article-limit-fields)))))

(local
 (defthm fn-ars-at-mostp-is-len
   (equal (fn-cbor-at-mostp xs n) (<= (len xs) (nfix n)))
   :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))

; KEYSTONE.  The buffer's invariant is the one hypothesis: a cell that is
; not an octet is what the reference's preflight refuses and the buffer
; cannot hold.
(defthm fn-ars-parse-under-is-article-parse-under
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-parse-under limits fn-octets)
                  (fn-ars-of (fn-article-parse-under fn-octets limits)
                             (len fn-octets))))
  :hints (("Goal" :in-theory (e/d (fn-article-parse-under)
                                  (fn-article-parse-lines fn-ars-parse-lines
                                   fn-article-limit-lines)))))

(defthm fn-ars-parse-is-article-parse
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-parse fn-octets)
                  (fn-ars-of (fn-article-parse fn-octets) (len fn-octets))))
  :hints (("Goal" :in-theory (e/d (fn-article-parse)
                                  (fn-article-parse-under fn-ars-parse-under)))))

; The body located: the reference's body is the buffer's suffix at the
; twin's OFFSET (the reference's parse leaves the body as the rest after
; the separator line, a suffix of its input).
(local
 (defthm fn-ars-parse-lines-body-is-suffix
   (implies (and (true-listp octets)
                 (fn-article-result-okp
                  (fn-article-parse-lines octets limits lines-left header-bytes
                                          nfields fields-rev current header-rev)))
            (let ((body (fn-article-body
                         (fn-article-result-article
                          (fn-article-parse-lines octets limits lines-left
                                                  header-bytes nfields fields-rev
                                                  current header-rev)))))
              (and (<= (len body) (len octets))
                   (equal (nthcdr (- (len octets) (len body)) octets) body))))
   :hints (("Goal" :induct (fn-article-parse-lines octets limits lines-left
                                                   header-bytes nfields fields-rev
                                                   current header-rev)
                   :in-theory (e/d (fn-article-parse-lines)
                                   (fn-article-new-field fn-article-add-fold
                                    fn-article-header-rev-add-line
                                    fn-article-finish-fields
                                    fn-article-body-crlfp
                                    fn-article-fold-linep fn-article-wspp
                                    fn-article-limit-octets
                                    fn-article-limit-fields))))))

(defthm fn-ars-body-is-located
  (implies (and (fn-octets-p fn-octets)
                (fn-article-result-okp (fn-ars-parse-under limits fn-octets)))
           (equal (nthcdr (fn-article-body
                           (fn-article-result-article
                            (fn-ars-parse-under limits fn-octets)))
                          fn-octets)
                  (fn-article-body
                   (fn-article-result-article
                    (fn-article-parse-under fn-octets limits)))))
  :hints (("Goal" :in-theory (e/d (fn-article-parse-under)
                                  (fn-article-parse-lines fn-ars-parse-lines
                                   fn-article-limit-lines
                                   fn-ars-parse-under-is-article-parse-under))
                  :use ((:instance fn-ars-parse-under-is-article-parse-under)))))

; -----------------------------------------------------------------------------
; Guards.

(defthm fn-ars-next-line-aux-index
  (implies (and (natp j)
                (fn-article-line-okp (fn-ars-next-line-aux j line-rev left fn-octets)))
           (and (natp (fn-article-line-rest
                       (fn-ars-next-line-aux j line-rev left fn-octets)))
                (<= (fn-article-line-rest
                     (fn-ars-next-line-aux j line-rev left fn-octets))
                    (len fn-octets))))
  :hints (("Goal" :induct (fn-ars-next-line-aux j line-rev left fn-octets)
                  :in-theory (disable fn-ars-next-line-aux-is-reference)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((fn-ars-next-line-aux j line-rev left fn-octets)))
                 :rewrite))

(defthm fn-ars-next-line-aux-true-listp
  (implies (true-listp line-rev)
           (true-listp (fn-article-line-value
                        (fn-ars-next-line-aux j line-rev left fn-octets))))
  :hints (("Goal" :induct (fn-ars-next-line-aux j line-rev left fn-octets)
                  :in-theory (disable fn-ars-next-line-aux-is-reference))))

(verify-guards fn-ars-parse-lines
  :hints (("Goal"
           :in-theory
           (e/d (fn-ars-next-line)
                (fn-ars-next-line-aux fn-ars-next-line-aux-is-reference
                 fn-article-new-field fn-article-split-colon-aux
                 fn-article-line-value fn-article-line-rest
                 fn-article-add-fold fn-article-header-rev-add-line
                 fn-article-finish-fields fn-ars-body-crlfp)))))
(verify-guards fn-ars-parse-under)
(verify-guards fn-ars-parse)

; -----------------------------------------------------------------------------
; The consumers the host calls, each its reference with fn-article-parse
; replaced by the buffer parse, and each proved equal to it.

(local (in-theory (disable fn-ars-parse fn-ars-parse-under fn-article-parse
                           fn-article-parse-under fn-ars-of)))

; books/peer-authored-accept.lisp fn-pa-carrier-kind.
(defun fn-ars-carrier-kind (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((parsed (fn-ars-parse fn-octets)))
    (if (not (fn-article-result-okp parsed))
        :invalid
      (let ((article (fn-article-result-article parsed)))
        (if (not (true-listp article)) :invalid
          (if (equal (fn-hc-count-name
                      *fn-hc-name* (fn-article-fields article)) 0)
              :absent
            :present))))))

(defthm fn-ars-carrier-kind-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-carrier-kind fn-octets)
                  (fn-pa-carrier-kind fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-pa-carrier-kind) (fn-hc-count-name)))))

; books/control-classify.lisp fn-ctl-classify-octets.
(defun fn-ars-classify-octets (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((parsed (fn-ars-parse fn-octets)))
    (if (fn-article-result-okp parsed)
        (fn-ctl-classify (fn-article-result-article parsed))
      :unparsed)))

(local
 (defthm fn-ars-of-keeps-classify
   (equal (fn-ctl-classify (fn-article-result-article (fn-ars-of r n)))
          (fn-ctl-classify (fn-article-result-article r)))
   :hints (("Goal" :in-theory (e/d (fn-ctl-classify) (fn-ctl-classify-fields))))))

(defthm fn-ars-classify-octets-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-classify-octets fn-octets)
                  (fn-ctl-classify-octets fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-classify-octets) (fn-ctl-classify)))))

; books/peer-authored-accept.lisp fn-pa-filing-plan (C1; host
; fn-owner-control-filing-buffer).
(defun fn-ars-filing-plan (groups domain fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((classified (fn-ars-classify-octets fn-octets)))
    (cond ((and (consp classified) (eq (car classified) :malformed))
           (list :refused :control-malformed))
          ((and (consp classified) (eq (car classified) :control))
           (let ((group (fn-ctl-filing-group (cadr classified))))
             (if (fn-ctl-memberp group domain)
                 (list :file (list (fn-record-string-octets group)))
               (list :refused :control-not-filed))))
          (t (list :file groups)))))

(defthm fn-ars-filing-plan-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-filing-plan groups domain fn-octets)
                  (fn-pa-filing-plan fn-octets groups domain)))
  :hints (("Goal" :in-theory (e/d (fn-pa-filing-plan)
                                  (fn-ctl-classify-octets fn-ars-classify-octets
                                   fn-ctl-filing-group fn-ctl-memberp
                                   fn-record-string-octets)))))

; books/peer-authored-accept.lisp fn-pa-carrier-form (host
; fn-owner-peer-carrier-form-buffer).  The signed arm decodes the carrier
; field against the source through fn-hc-received-plan over the buffer's
; value (fn-octets-list: the one list this book builds, on that arm only,
; and the source is that plan's value).
(defun fn-ars-carrier-form (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-ars-carrier-kind
                                          fn-hc-received-plan)))))
  (let ((kind (fn-ars-carrier-kind fn-octets)))
    (if (eq kind :absent) :absent
      (if (eq kind :invalid) (list :refused :article)
        (let ((parsed (fn-hc-received-plan (fn-octets-list fn-octets))))
          (if (not (fn-hc-okp parsed))
              (list :refused :carrier)
            (let ((value (fn-hc-value parsed)))
              (if (not (and (true-listp value) (equal (len value) 2)))
                  (list :refused :carrier-shape)
                (let ((carrier (cadr value)))
                  (if (not (and (true-listp carrier)
                                (equal (len carrier) 3)))
                      (list :refused :carrier-shape)
                    (list :ok (car value) (car carrier) (cadr carrier)
                          (caddr carrier))))))))))))

(defthm fn-ars-carrier-form-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-carrier-form fn-octets)
                  (fn-pa-carrier-form fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-pa-carrier-form)
                                  (fn-pa-carrier-kind fn-ars-carrier-kind
                                   fn-hc-received-plan fn-hc-okp fn-hc-value)))))

; books/peer-authored-accept.lisp fn-pa-current-plan (host
; fn-owner-peer-carrier-plan-buffer).
(defun fn-ars-current-plan (snapshots carried transitp fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((form (fn-ars-carrier-form fn-octets)))
    (if (not (and (consp form) (eq (car form) :ok))) form
      (let* ((source (nth 1 form))
             (principal (nth 2 form))
             (keys (nth 3 form))
             (signatures (nth 4 form))
             (current (fn-hl-current-for-principal
                       principal snapshots))
             (generation (if (fn-stxk-p current)
                             (fn-stxk-keyring-generation current) nil))
             (enrolled (fn-hl-current-enrollment
                        generation snapshots)))
        (cond ((and (true-listp enrolled)
                    (equal (len enrolled) 3)
                    (equal (car enrolled) current)
                    (equal (cadr enrolled) principal)
                    (equal (caddr enrolled) keys))
               (list :ok source principal keys signatures
                     current generation))
              ((and (null current)
                    (fn-pa-carriesp principal carried))
               (list :carried source principal keys signatures))
              ((and transitp
                    (fn-pa-revoked-tombstonep current generation
                                              principal keys snapshots))
               (list :revoked source principal keys signatures
                     current generation))
              (t (list :refused :local-enrollment)))))))

(defthm fn-ars-current-plan-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-current-plan snapshots carried transitp fn-octets)
                  (fn-pa-current-plan fn-octets snapshots carried transitp)))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan)
                                  (fn-pa-carrier-form fn-ars-carrier-form
                                   fn-hl-current-for-principal fn-stxk-p
                                   fn-stxk-keyring-generation
                                   fn-hl-current-enrollment fn-pa-carriesp
                                   fn-pa-revoked-tombstonep)))))

; books/login-binding.lisp fn-lb-gate, fn-lb-owner-gate and
; books/login-binding-live.lisp fn-lb-ocfg-gate (host
; fn-owner-login-gate-buffer).
(defun fn-ars-lb-gate (login bindings policyp fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((bound (and policyp (fn-lb-binding login bindings))))
    (if (not bound)
        (list :pass login nil)
      (let ((form (fn-ars-carrier-form fn-octets)))
        (cond ((equal form :absent) (list :refused :login-unsigned login))
              ((and (consp form) (equal (car form) :ok))
               (if (equal (nth 2 form) bound)
                   (list :pass login bound)
                 (list :refused :login-not-bound login)))
              (t (list :pass login bound)))))))

(defthm fn-ars-lb-gate-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-lb-gate login bindings policyp fn-octets)
                  (fn-lb-gate fn-octets login bindings policyp)))
  :hints (("Goal" :in-theory (e/d (fn-lb-gate)
                                  (fn-pa-carrier-form fn-ars-carrier-form
                                   fn-lb-binding)))))

(defun fn-ars-lb-owner-gate (o cfg bindings fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-ars-lb-gate (fn-lb-inflight-login o) bindings (fn-lb-policy-onp cfg)
                  fn-octets))

(defthm fn-ars-lb-owner-gate-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-lb-owner-gate o cfg bindings fn-octets)
                  (fn-lb-owner-gate o cfg bindings fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-lb-owner-gate)
                                  (fn-lb-gate fn-ars-lb-gate
                                   fn-lb-inflight-login fn-lb-policy-onp)))))

; THE FUNCTION THE HOST CALLS for the served POST's login gate.
(defun fn-ars-lb-ocfg-gate (oc fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-ars-lb-owner-gate (fn-ocfg-owner oc) (fn-ocfg-config oc)
                        (fn-lb-conn-bindings oc (fn-lb-inflight-id (fn-ocfg-owner oc)))
                        fn-octets))

(defthm fn-ars-lb-ocfg-gate-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-lb-ocfg-gate oc fn-octets)
                  (fn-lb-ocfg-gate oc fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-lb-ocfg-gate)
                                  (fn-lb-owner-gate fn-ars-lb-owner-gate
                                   fn-ocfg-owner fn-ocfg-config
                                   fn-lb-conn-bindings fn-lb-inflight-id)))))
