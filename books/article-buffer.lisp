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
(include-book "peer-carriage")
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
              (if (or (not (fn-ars-body-crlfp rest fn-octets))
                      (not (fn-article-field-closedp current)))
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
                   (if (not (fn-article-field-closedp current))
                       (fn-article-error :invalid-header)
                    (if (<= (fn-article-limit-fields limits)
                            (+ (if current 1 0) (nfix nfields)))
                        (fn-article-error :header-fields-limit)
                      (fn-ars-parse-lines
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       (if current (+ 1 (nfix nfields)) nfields)
                       (if current (cons current fields-rev) fields-rev)
                       (fn-article-line-value field-result)
                       (fn-article-header-rev-add-line header-rev line)
                       fn-octets)))))))))))))

(defun fn-ars-parse-lines-acc (i limits lines-left header-bytes nfields
                             fields-rev cur header-rev fn-octets)
  (declare (xargs :stobjs fn-octets
                  :measure (nfix lines-left)
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets))
                              (natp lines-left)
                              (natp header-bytes)
                              (natp nfields)
                              (true-listp fields-rev)
                              (or (null cur)
                                  (fn-article-open-fieldp cur))
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
              (if (or (not (fn-ars-body-crlfp rest fn-octets))
                      (not (fn-article-open-field-closedp cur)))
                  (fn-article-error :invalid-header)
                (fn-article-ok
                 (fn-article-make
                  (reverse header-rev) rest
                  (fn-article-finish-fields fields-rev (and cur (fn-article-close-field cur))))))
            (if (< (fn-article-limit-octets limits)
                   (+ header-bytes (len line) 2))
                (fn-article-error :header-octets-limit)
              (if (fn-article-wspp (car line))
                  (if (not cur)
                      (fn-article-error :invalid-header)
                    (if (not (fn-article-fold-linep line))
                        (fn-article-error :invalid-header)
                      (fn-ars-parse-lines-acc
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       nfields fields-rev (fn-article-add-fold-open cur line)
                       (fn-article-header-rev-add-line header-rev line)
                       fn-octets)))
                (let ((field-result (fn-article-new-field line)))
                  (if (not (fn-article-line-okp field-result))
                      field-result
                   (if (not (fn-article-open-field-closedp cur))
                       (fn-article-error :invalid-header)
                    (if (<= (fn-article-limit-fields limits)
                            (+ (if cur 1 0) (nfix nfields)))
                        (fn-article-error :header-fields-limit)
                      (fn-ars-parse-lines-acc
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       (if cur (+ 1 (nfix nfields)) nfields)
                       (if cur (cons (fn-article-close-field cur) fields-rev) fields-rev)
                       (fn-article-open-field (fn-article-line-value field-result))
                       (fn-article-header-rev-add-line header-rev line)
                       fn-octets)))))))))))))

; The parse the host calls: fn-article-parse-under over the whole buffer.
; The reference's two preflights are the buffer's: its length against the
; codec ceiling, and every cell an octet (fn-octets-p, the invariant).
(defun fn-ars-parse-under (limits fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (if (< *fn-article-max-octets* (fn-octets-len fn-octets))
      (fn-article-error :limit)
    (mbe :logic (fn-ars-parse-lines 0 limits (1+ (fn-article-limit-lines limits))
                                  0 0 nil nil nil fn-octets)
         :exec (fn-ars-parse-lines-acc 0 limits (1+ (fn-article-limit-lines limits))
                                      0 0 nil nil nil fn-octets))))

(defun fn-ars-parse (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (fn-ars-parse-under *fn-article-ceiling-limits* fn-octets))

; -----------------------------------------------------------------------------
; The correspondence.

; The nthcdr facts the correspondences read (no std/lists book: the farm's
; system books certify std/lists/rev only).
(local
 (defthm fn-ars-nthcdr-of-zero
   (equal (nthcdr 0 xs) xs)
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-ars-cdr-of-nthcdr
   (implies (natp j)
            (equal (cdr (nthcdr j xs)) (nthcdr (+ 1 j) xs)))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-ars-cddr-of-nthcdr
   (implies (natp j)
            (equal (cdr (cdr (nthcdr j xs))) (nthcdr (+ 2 j) xs)))
   :hints (("Goal" :use ((:instance fn-ars-cdr-of-nthcdr)
                         (:instance fn-ars-cdr-of-nthcdr (j (+ 1 j))))
                   :in-theory (disable fn-ars-cdr-of-nthcdr)))))

; arithmetic/top leaves (< (+ -1 j) n) and (< j (+ 1 n)) as two terms; the
; induction hypothesis meets the goal only through this shift.
(local
 (defthm fn-ars-lt-minus-one
   (implies (and (integerp j) (integerp n))
            (equal (< (+ -1 j) n) (< j (+ 1 n))))
   :hints (("Goal" :cases ((< (+ -1 j) n))))))

(local
 (defthm fn-ars-consp-of-nthcdr
   (implies (natp j)
            (equal (consp (nthcdr j xs)) (< j (len xs))))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-ars-car-of-nthcdr
   (implies (natp j)
            (equal (car (nthcdr j xs)) (nth j xs)))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr nth)))))

(local
 (defthm fn-ars-len-of-nthcdr
   (implies (natp j)
            (equal (len (nthcdr j xs)) (nfix (- (len xs) j))))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-ars-nthcdr-of-nthcdr
   (implies (and (natp i) (natp j))
            (equal (nthcdr i (nthcdr j xs)) (nthcdr (+ i j) xs)))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr)))))

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
   ; The accessors stay closed here: the instance and the linear rule are
   ; stated over fn-article-line-rest, not its caddr.
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-article-next-line)
                                   (fn-ars-reference-rest-is-suffix
                                    fn-article-line-rest fn-article-line-okp
                                    fn-article-next-line-aux nthcdr))
                   :use ((:instance fn-ars-reference-rest-is-suffix
                                    (ys (nthcdr j fn-octets)) (lr nil)
                                    (left *fn-article-max-line-octets*)))))))

(defthm fn-ars-body-crlfp-is-reference
  (implies (natp j)
           (equal (fn-ars-body-crlfp j fn-octets)
                  (fn-article-body-crlfp (nthcdr j fn-octets))))
  :hints (("Goal" :induct (fn-ars-body-crlfp j fn-octets)
                  :in-theory (enable fn-article-body-crlfp))))

; The line result's three faces, as the parse loop reads them: the same
; verdict as the reference's, the same line, and the rest located (the
; reference's rest IS the buffer's suffix at the twin's index).
(defthm fn-ars-next-line-okp
  (implies (natp j)
           (equal (fn-article-line-okp (fn-ars-next-line j fn-octets))
                  (fn-article-line-okp (fn-article-next-line (nthcdr j fn-octets))))))

(defthm fn-ars-next-line-error
  (implies (and (natp j)
                (not (fn-article-line-okp (fn-article-next-line (nthcdr j fn-octets)))))
           (equal (fn-ars-next-line j fn-octets)
                  (fn-article-next-line (nthcdr j fn-octets)))))

(defthm fn-ars-next-line-value
  (implies (natp j)
           (equal (fn-article-line-value (fn-ars-next-line j fn-octets))
                  (fn-article-line-value (fn-article-next-line (nthcdr j fn-octets))))))

; An :ok line result has its three positions.
(local
 (defthm fn-ars-reference-ok-shape
   (implies (fn-article-line-okp (fn-article-next-line-aux ys lr left))
            (and (consp (cdr (fn-article-next-line-aux ys lr left)))
                 (consp (cddr (fn-article-next-line-aux ys lr left)))))
   :hints (("Goal" :in-theory (enable fn-article-next-line-aux)
                   :induct (fn-article-next-line-aux ys lr left)))))

(defthm fn-ars-next-line-rest-natp
  (implies (and (natp j)
                (fn-article-line-okp (fn-ars-next-line j fn-octets)))
           (natp (fn-article-line-rest (fn-ars-next-line j fn-octets))))
  :hints (("Goal" :use ((:instance fn-ars-reference-rest-len
                                   (ys (nthcdr j fn-octets)) (lr nil)
                                   (left *fn-article-max-line-octets*)))
                  :in-theory (e/d (fn-article-next-line
                                   fn-ars-next-line-aux-is-reference
                                   fn-article-line-okp fn-article-line-rest)
                                  (fn-ars-reference-rest-len))))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-ars-next-line-rest-bound
  (implies (and (natp j)
                (fn-article-line-okp (fn-ars-next-line j fn-octets)))
           (<= (fn-article-line-rest (fn-ars-next-line j fn-octets))
               (len fn-octets)))
  :hints (("Goal" :use ((:instance fn-ars-reference-rest-len
                                   (ys (nthcdr j fn-octets)) (lr nil)
                                   (left *fn-article-max-line-octets*)))
                  :in-theory (e/d (fn-article-next-line
                                   fn-ars-next-line-aux-is-reference
                                   fn-article-line-okp fn-article-line-rest)
                                  (fn-ars-reference-rest-len))))
  :rule-classes (:rewrite :linear))

(defthm fn-ars-next-line-rest-located
  (implies (and (natp j) (<= j (len fn-octets))
                (fn-article-line-okp (fn-article-next-line (nthcdr j fn-octets))))
           (equal (fn-article-line-rest (fn-article-next-line (nthcdr j fn-octets)))
                  (nthcdr (fn-article-line-rest (fn-ars-next-line j fn-octets))
                          fn-octets)))
  :hints (("Goal" :use ((:instance fn-ars-reference-rest-located))
                  :in-theory (e/d (fn-article-next-line
                                   fn-ars-next-line-aux-is-reference
                                   fn-article-line-okp fn-article-line-rest)
                                  (fn-ars-reference-rest-located)))))

(local (in-theory (disable fn-ars-next-line-aux-is-reference
                           fn-ars-next-line-is-reference)))

; The two verdict readers are one test; the loop's proof names this rule
; and the rest of the book keeps it closed (fn-ars-of-okp reads the twin's).
(local
 (defthm fn-ars-result-okp-is-line-okp
   (equal (fn-article-result-okp r) (fn-article-line-okp r))))

(defthm fn-ars-line-okp-of-error
  (not (fn-article-line-okp (fn-article-error c))))

(defthm fn-ars-of-ok-located
  (implies (and (natp k) (<= k (len fn-octets)))
           (equal (fn-ars-of (fn-article-ok (fn-article-make h (nthcdr k fn-octets) f))
                             (len fn-octets))
                  (fn-article-ok (fn-article-make h k f))))
  :hints (("Goal" :in-theory (enable fn-ars-of))))

; The parse loop reads a line result only through its accessors, which
; stay closed here so that the facets above are what the loop's proof sees.
(local (in-theory (disable fn-article-line-okp fn-article-line-value
                           fn-article-line-rest fn-article-result-okp)))

(defthm fn-ars-parse-lines-is-reference
  (implies (and (natp i) (<= i (len fn-octets)))
           (equal (fn-ars-parse-lines i limits lines-left header-bytes nfields
                                      fields-rev current header-rev fn-octets)
                  (fn-ars-of (fn-article-parse-lines
                              (nthcdr i fn-octets) limits lines-left header-bytes
                              nfields fields-rev current header-rev)
                             (len fn-octets))))
  ; The loop's own induction, both loops opened once a step, and only the
  ; facets: no arithmetic, no accessor opens (the two bodies are the same
  ; text, so each step is the facets' rewrites and nothing else).
  :hints (("Goal" :induct (fn-ars-parse-lines i limits lines-left header-bytes
                                              nfields fields-rev current
                                              header-rev fn-octets)
                  :expand ((:free (limits lines-left header-bytes nfields
                                    fields-rev current header-rev)
                                  (fn-ars-parse-lines i limits lines-left
                                                      header-bytes nfields
                                                      fields-rev current
                                                      header-rev fn-octets))
                           (:free (limits lines-left header-bytes nfields
                                    fields-rev current header-rev)
                                  (fn-article-parse-lines
                                   (nthcdr i fn-octets) limits lines-left
                                   header-bytes nfields fields-rev current
                                   header-rev)))
                  :in-theory (union-theories
                              '(fn-ars-next-line-okp fn-ars-next-line-error
                                fn-ars-next-line-value
                                fn-ars-next-line-rest-natp
                                fn-ars-next-line-rest-bound
                                fn-ars-next-line-rest-located
                                fn-ars-body-crlfp-is-reference
                                fn-ars-of-error fn-ars-result-okp-is-line-okp
                                fn-ars-line-okp-of-error fn-ars-of-ok-located
                                natp-compound-recognizer
                                (:induction fn-ars-parse-lines))
                              (theory 'minimal-theory)))))

(local (in-theory (disable fn-ars-result-okp-is-line-okp)))

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
; twin's OFFSET.  The reference's parse leaves the body as the rest after
; the separator line, a suffix of its input (fn-ars-suffixp: the suffix of
; XS with R's length is R), and every line's rest is a suffix of the input.
(defun fn-ars-suffixp (r xs)
  ; A specification (no host path executes it): nthcdr's guard wants a list.
  (declare (xargs :guard t :verify-guards nil))
  (equal (nthcdr (nfix (- (len xs) (len r))) xs) r))

(local
 (defthm fn-ars-suffixp-reflexive
   (fn-ars-suffixp xs xs)))

(local
 (defthm fn-ars-suffixp-len
   (implies (fn-ars-suffixp r xs)
            (<= (len r) (len xs)))
   :rule-classes :forward-chaining))

; The chain with the suffixes as eliminable variables: a suffix's defining
; equation mentions its own length, so the prover never substitutes it.
(local
 (defthm fn-ars-suffixp-chain
   (implies (and (natp i) (natp j)
                 (equal (nthcdr j xs) b) (equal (nthcdr i b) a))
            (equal (nthcdr (+ i j) xs) a))
   :hints (("Goal" :in-theory (disable nthcdr)))))

(local
 (defthm fn-ars-suffixp-transitive
   (implies (and (fn-ars-suffixp a b) (fn-ars-suffixp b c))
            (fn-ars-suffixp a c))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-ars-suffixp) (nthcdr fn-ars-nthcdr-of-nthcdr))
                   :use ((:instance fn-ars-suffixp-len (r a) (xs b))
                         (:instance fn-ars-suffixp-len (r b) (xs c))
                         (:instance fn-ars-suffixp-chain
                                    (i (- (len b) (len a)))
                                    (j (- (len c) (len b)))
                                    (xs c)))))))

(local
 (defthm fn-ars-next-line-rest-suffixp
   (implies (fn-article-line-okp (fn-article-next-line ys))
            (fn-ars-suffixp (fn-article-line-rest (fn-article-next-line ys)) ys))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-ars-suffixp fn-article-next-line)
                                   (fn-ars-reference-rest-is-suffix
                                    fn-ars-reference-rest-len
                                    fn-article-line-rest fn-article-line-okp
                                    fn-article-next-line-aux nthcdr))
                   :use ((:instance fn-ars-reference-rest-is-suffix
                                    (ys ys) (lr nil) (left *fn-article-max-line-octets*))
                         (:instance fn-ars-reference-rest-len
                                    (ys ys) (lr nil) (left *fn-article-max-line-octets*)))))))

(local (in-theory (disable fn-ars-suffixp)))

(local
 (defthm fn-ars-parse-lines-body-is-suffix
   (implies (fn-article-result-okp
             (fn-article-parse-lines octets limits lines-left header-bytes
                                     nfields fields-rev current header-rev))
            (fn-ars-suffixp
             (fn-article-body
              (fn-article-result-article
               (fn-article-parse-lines octets limits lines-left header-bytes
                                       nfields fields-rev current header-rev)))
             octets))
   :hints (("Goal" :induct (fn-article-parse-lines octets limits lines-left
                                                   header-bytes nfields fields-rev
                                                   current header-rev)
                   :expand ((:free (limits lines-left header-bytes nfields
                                     fields-rev current header-rev)
                                   (fn-article-parse-lines
                                    octets limits lines-left header-bytes
                                    nfields fields-rev current header-rev)))
                   :in-theory (union-theories
                               '(fn-ars-suffixp-reflexive fn-ars-suffixp-transitive
                                 fn-ars-next-line-rest-suffixp
                                 fn-ars-result-okp-is-line-okp
                                 fn-ars-line-okp-of-error
                                 fn-article-ok fn-article-make
                                 fn-article-result-article fn-article-body
                                 car-cons cdr-cons
                                 (:induction fn-article-parse-lines))
                               (theory 'minimal-theory))))))

; An :ok parse carries its article.
(local
 (defthm fn-ars-parse-lines-ok-shape
   (implies (fn-article-result-okp
             (fn-article-parse-lines octets limits lines-left header-bytes
                                     nfields fields-rev current header-rev))
            (let ((r (fn-article-parse-lines octets limits lines-left header-bytes
                                             nfields fields-rev current header-rev)))
              (and (consp (cdr r)) (true-listp (cadr r)))))
   :hints (("Goal" :induct (fn-article-parse-lines octets limits lines-left
                                                   header-bytes nfields fields-rev
                                                   current header-rev)
                   :expand ((:free (limits lines-left header-bytes nfields
                                     fields-rev current header-rev)
                                   (fn-article-parse-lines
                                    octets limits lines-left header-bytes
                                    nfields fields-rev current header-rev)))
                   :in-theory (union-theories
                               '(fn-ars-result-okp-is-line-okp
                                 fn-ars-line-okp-of-error
                                 fn-article-ok fn-article-make
                                 car-cons cdr-cons
                                 (:induction fn-article-parse-lines))
                               (theory 'minimal-theory))))))

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
  :hints (("Goal" :in-theory (e/d (fn-article-parse-under fn-ars-of fn-ars-suffixp
                                   fn-article-result-okp fn-article-result-article
                                   fn-article-body)
                                  (fn-article-parse-lines fn-ars-parse-lines
                                   fn-article-limit-lines fn-ars-suffixp-len
                                   fn-ars-parse-under-is-article-parse-under))
                  :use ((:instance fn-ars-parse-under-is-article-parse-under)
                        (:instance fn-ars-parse-lines-body-is-suffix
                                   (octets fn-octets)
                                   (lines-left (1+ (fn-article-limit-lines limits)))
                                   (header-bytes 0) (nfields 0) (fields-rev nil)
                                   (current nil) (header-rev nil))
                        (:instance fn-ars-parse-lines-ok-shape
                                   (octets fn-octets)
                                   (lines-left (1+ (fn-article-limit-lines limits)))
                                   (header-bytes 0) (nfields 0) (fields-rev nil)
                                   (current nil) (header-rev nil))
                        (:instance fn-ars-suffixp-len
                                   (r (fn-article-body
                                       (fn-article-result-article
                                        (fn-article-parse-lines
                                         fn-octets limits
                                         (1+ (fn-article-limit-lines limits))
                                         0 0 nil nil nil))))
                                   (xs fn-octets))))))

; -----------------------------------------------------------------------------
; Guards: the loop's obligations beyond the reference's are the next index
; (the rest facets); the line's shape is the reference's
; (fn-article-next-line-value-listp, fn-article-guard-backchaining).

(local
 (defthm fn-ars-fold-line-listp
   (implies (fn-article-fold-linep line) (true-listp line))
   :hints (("Goal" :in-theory (enable fn-article-fold-linep
                                     fn-article-header-bytes-true-listp)))
   :rule-classes :forward-chaining))

; The executed buffer loop carries the same visible-value flag as the list
; accumulator. This refinement preserves the exact verdict, header, body offset
; and fields while closing a long field by a single flag test.
(defthm fn-ars-parse-lines-acc-is-parse-lines
  (implies (or (null cur) (fn-article-open-fieldp cur))
           (equal (fn-ars-parse-lines-acc i limits lines-left header-bytes nfields
                                        fields-rev cur header-rev fn-octets)
                  (fn-ars-parse-lines i limits lines-left header-bytes nfields
                                    fields-rev (and cur (fn-article-close-field cur))
                                    header-rev fn-octets)))
  :hints (("Goal" :induct (fn-ars-parse-lines-acc i limits lines-left header-bytes
                                                 nfields fields-rev cur header-rev fn-octets)
                  :do-not '(generalize fertilize eliminate-destructors)
                  :in-theory (e/d (fn-ars-parse-lines fn-ars-parse-lines-acc
                                   fn-article-close-add-fold-open
                                   fn-article-add-fold-open-fieldp)
                                  (fn-article-close-field fn-article-add-fold-open
                                      fn-article-open-field fn-article-open-fieldp
                                      fn-article-add-fold fn-article-new-field
                                      fn-ars-next-line fn-article-header-rev-add-line
                                      fn-article-finish-fields fn-ars-body-crlfp
                                      fn-article-line-okp fn-article-line-value
                                      fn-article-line-rest fn-article-fold-linep
                                      fn-article-make fn-article-ok fn-article-error
                                      fn-article-wspp fn-article-limit-octets
                                      fn-article-limit-fields fn-article-field-closedp
                                      fn-article-open-field-closedp)))))

(verify-guards fn-ars-parse-lines
  :hints (("Goal"
           :in-theory
           (e/d (fn-article-guard-backchaining)
                (fn-ars-next-line fn-ars-next-line-aux fn-ars-body-crlfp
                 fn-article-next-line fn-article-next-line-aux
                 fn-article-new-field fn-article-split-colon-aux
                 fn-article-add-fold fn-article-header-rev-add-line
                 fn-article-finish-fields fn-article-body-crlfp)))))
(verify-guards fn-ars-parse-lines-acc
  :hints (("Goal" :in-theory
           (e/d (fn-article-guard-backchaining)
                (fn-ars-next-line fn-ars-next-line-aux
                 fn-article-next-line fn-article-next-line-aux
                 fn-article-new-field fn-article-line-value fn-article-line-rest
                 fn-article-add-fold-open fn-article-close-field fn-article-open-field
                 fn-article-open-fieldp fn-article-open-field-closedp
                 fn-article-header-rev-add-line fn-article-finish-fields
                 fn-ars-body-crlfp)))))
(verify-guards fn-ars-parse-under)
(verify-guards fn-ars-parse)

; -----------------------------------------------------------------------------
; The consumers the host calls, each its reference with fn-article-parse
; replaced by the buffer parse, and each proved equal to it.

(local (in-theory (disable fn-ars-parse fn-ars-parse-under fn-article-parse
                           fn-article-parse-under fn-ars-of
                           fn-article-result-article fn-article-fields
                           fn-article-header fn-article-body)))

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

; books/peer-carriage.lisp fn-pcb-transit-verdict (host
; fn-owner-transit-verdict-buffer; lane sweep-ops, S002): the verdict the
; service log records for every transit attempt.  On the unsigned arm (the
; carrier form :absent: every served POST without a carrier) it is decided
; from the buffer, with no list of the article; on a present carrier it is
; the reference over the buffer's value (the signed arm's events carry the
; article as a list anyway: PKT-743).
(defun fn-ars-transit-verdict (snapshots carried transitp ed ml fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (equal (fn-ars-carrier-form fn-octets) :absent)
      :unsigned
    (fn-pcb-transit-verdict (fn-octets-list fn-octets) snapshots carried
                            transitp ed ml)))

; A carrier-absent article is the unsigned arm of the transit verdict, on
; and off transit.
(defthm fn-pcb-transit-verdict-of-an-absent-carrier
  (implies (equal (fn-pa-carrier-form received) :absent)
           (equal (fn-pcb-transit-verdict received snapshots carried
                                          transitp ed ml)
                  :unsigned))
  :hints (("Goal" :in-theory (e/d (fn-pcb-transit-verdict
                                   fn-pcb-admission-verdict
                                   fn-pa-current-plan)
                                  (fn-pa-carrier-form fn-pcb-refusal-class
                                   fn-pcb-revoked-principalp)))))

; KEYSTONE for the host line.
(defthm fn-ars-transit-verdict-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-ars-transit-verdict snapshots carried transitp ed ml
                                          fn-octets)
                  (fn-pcb-transit-verdict fn-octets snapshots carried
                                          transitp ed ml)))
  :hints (("Goal" :in-theory (e/d (fn-oct-list-is-identity)
                                  (fn-ars-carrier-form fn-pa-carrier-form
                                   fn-pcb-transit-verdict)))))
