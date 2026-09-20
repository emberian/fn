; fn: the statement verdict -- what a receiving node concludes about an
; article's FN-Statement from the received bytes and its own keyring.
;
; specs/substrate-transport.md section 1.5 and SUB-002.  Three outcomes and
; no fourth: :verified, :unverified, :absent.  The verdict is NEVER a
; refusal.  An article whose statement is missing, malformed, unverifiable or
; signed by a principal this node does not know is still accepted, stored
; byte-exact and relayed unchanged; what it loses is authority.
;
; The peer is not an argument.  fn-stx-verdict takes the parsed article, this
; node's keyring and the keyring's generation, and nothing else: no peer
; identity, no session, no Path, no clock.  A verdict without the generation
; it was computed under is not reproducible, so the generation is carried in
; the verdict record and rendered in the reader's line.
;
; What :verified means, exactly, and the grounding theorem in
; books/stx-invariants.lisp says it mechanically: this principal signed these
; bytes, under the key this node holds for it.  It does not mean the claim is
; true, the principal is who they say, or the node approves.  Unforgeability
; and collision resistance are A-CRYPTO and are not proved anywhere in fn.
;
; The reader exposure (section 5) is one function here, fn-stx-verified-item,
; which renders the HDR :fn-verified metadata item.  It is rendered from the
; recorded verdict, never recomputed per query.  The one-line hook the HDR
; command needs is a board CHANGE against books/nntp-responses.lisp; no nntp
; book is edited by this lane.

(in-package "ACL2")
(include-book "stx-carrier")
(include-book "principal")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The verdict record: (token detail generation).

(defconst *fn-stx-verdicts* '(:verified :unverified :absent))

(defun fn-stx-make-verdict (token detail generation)
  (declare (xargs :guard t))
  (list token detail generation))
(defun fn-stx-verdict-token (v)
  (declare (xargs :guard t))
  (if (consp v) (car v) nil))
(defun fn-stx-verdict-detail (v)
  (declare (xargs :guard t))
  (if (and (consp v) (consp (cdr v))) (car (cdr v)) nil))
(defun fn-stx-verdict-generation (v)
  (declare (xargs :guard t))
  (if (and (consp v) (consp (cdr v)) (consp (cdr (cdr v)))) (car (cdr (cdr v))) nil))

(defthm fn-stx-verdict-token-of-fn-stx-make-verdict
  (equal (fn-stx-verdict-token (fn-stx-make-verdict token detail generation))
         token))
(defthm fn-stx-verdict-detail-of-fn-stx-make-verdict
  (equal (fn-stx-verdict-detail (fn-stx-make-verdict token detail generation))
         detail))
(defthm fn-stx-verdict-generation-of-fn-stx-make-verdict
  (equal (fn-stx-verdict-generation (fn-stx-make-verdict token detail generation))
         generation))

(in-theory (disable (:d fn-stx-make-verdict) (:d fn-stx-verdict-token)
                    (:d fn-stx-verdict-detail) (:d fn-stx-verdict-generation)))

; -----------------------------------------------------------------------------
; The statement an article carries, if any.  A function of the article alone:
; no keyring, no peer.  NIL when there is no field, when the field does not
; decode, or when the header's ref does not bind the payload THIS receiver
; projected out of the received bytes.

(defun fn-stx-field (article)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (if (mbe :logic (not (fn-article-syntax-p article)) :exec nil)
      nil
    (fn-article-get-header article *fn-stx-statement-name*)))

(defun fn-stx-statement-of (article)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (let ((f (fn-stx-field article)))
    (if (not (consp f))
        nil
      (let ((d (fn-stx-parse-header (fn-article-field-unfolded-value f))))
        (if (not (fn-stx-okp d))
            nil
          (fn-stx-reattach (fn-stx-val d) (fn-stx-val2 d)
                           (fn-stx-payload-for article (fn-stx-val d))))))))

(defthm fn-stx-reattach-is-a-statement
  (implies (fn-stx-reattach header signature payload)
           (fn-stmt-p (fn-stx-reattach header signature payload)))
  :hints (("Goal" :in-theory (enable (:d fn-stx-reattach)))))

(defthm fn-stx-statement-of-is-a-statement
  (implies (fn-stx-statement-of article)
           (fn-stmt-p (fn-stx-statement-of article))))

; -----------------------------------------------------------------------------
; The verdict.

(defun fn-stx-verdict (article keyring generation)
  (declare (xargs :guard (and (fn-article-syntax-p article)
                              (fn-prin-keyringp keyring))
                  :guard-hints (("Goal" :in-theory (disable fn-stx-statement-of)))))
  (let ((f (fn-stx-field article)))
    (if (not (consp f))
        (fn-stx-make-verdict :absent :no-field generation)
      (let ((d (fn-stx-parse-header (fn-article-field-unfolded-value f))))
        (if (not (fn-stx-okp d))
            (fn-stx-make-verdict :unverified :malformed generation)
          (let ((s (fn-stx-reattach (fn-stx-val d) (fn-stx-val2 d)
                                    (fn-stx-payload-for article (fn-stx-val d)))))
            (if (not s)
                (fn-stx-make-verdict :unverified :ref-mismatch generation)
              (if (fn-prin-verifiedp s keyring)
                  (fn-stx-make-verdict :verified (fn-stmt-creator s) generation)
                (fn-stx-make-verdict :unverified :signature generation)))))))))

; -----------------------------------------------------------------------------
; Rendering the HDR :fn-verified metadata item (section 5).
;
; Three tokens, one per member of *fn-stx-verdicts*, never a boolean and
; never two outcomes collapsed into one token.  The principal id is hex, the
; keyring generation decimal.  The policy term of the design's sample line is
; packet S4's and is not rendered here.

(defun fn-stx-hex-digit (n)
  (declare (xargs :guard t))
  (let ((k (nfix n)))
    (cond ((< k 10) (+ 48 k))
          ((< k 16) (+ 87 k))
          (t 48))))

(defun fn-stx-hex-octets (octets)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable floor mod)))))
  (if (consp octets)
      (cons (fn-stx-hex-digit (floor (nfix (car octets)) 16))
            (cons (fn-stx-hex-digit (mod (nfix (car octets)) 16))
                  (fn-stx-hex-octets (cdr octets))))
    nil))

(defun fn-stx-decimal-rev (n)
  (declare (xargs :guard (natp n)
                  :measure (nfix n)
                  :hints (("Goal" :in-theory (disable floor mod)))))
  (if (zp n)
      nil
    (cons (+ 48 (mod n 10)) (fn-stx-decimal-rev (floor n 10)))))

(defun fn-stx-decimal-octets (n)
  (declare (xargs :guard t))
  (if (and (natp n) (< 0 n))
      (revappend (fn-stx-decimal-rev n) nil)
    '(48)))

(defconst *fn-stx-token-verified* '(118 101 114 105 102 105 101 100))
(defconst *fn-stx-token-unverified*
  '(117 110 118 101 114 105 102 105 101 100))
(defconst *fn-stx-token-absent* '(97 98 115 101 110 116))
(defconst *fn-stx-token-keyring* '(107 101 121 114 105 110 103))
(defconst *fn-stx-token-no-field* '(110 111 45 102 105 101 108 100))
(defconst *fn-stx-token-malformed* '(109 97 108 102 111 114 109 101 100))
(defconst *fn-stx-token-ref-mismatch*
  '(114 101 102 45 109 105 115 109 97 116 99 104))
(defconst *fn-stx-token-signature*
  '(115 105 103 110 97 116 117 114 101))
(defconst *fn-stx-token-unknown* '(117 110 107 110 111 119 110))

(defun fn-stx-reason-token (detail)
  (declare (xargs :guard t))
  (cond ((equal detail :malformed) *fn-stx-token-malformed*)
        ((equal detail :ref-mismatch) *fn-stx-token-ref-mismatch*)
        ((equal detail :signature) *fn-stx-token-signature*)
        ((equal detail :no-field) *fn-stx-token-no-field*)
        (t *fn-stx-token-unknown*)))

(defun fn-stx-keyring-suffix (generation)
  (declare (xargs :guard t))
  (append '(32) (append *fn-stx-token-keyring*
                        (append '(32) (fn-stx-decimal-octets generation)))))

(defun fn-stx-verified-item (verdict)
  (declare (xargs :guard t))
  (let ((token (fn-stx-verdict-token verdict))
        (detail (fn-stx-verdict-detail verdict))
        (generation (fn-stx-verdict-generation verdict)))
    (cond ((equal token :verified)
           (append *fn-stx-token-verified*
                   (append '(32)
                           (append (fn-stx-hex-octets detail)
                                   (fn-stx-keyring-suffix generation)))))
          ((equal token :unverified)
           (append *fn-stx-token-unverified*
                   (append '(32)
                           (append (fn-stx-reason-token detail)
                                   (fn-stx-keyring-suffix generation)))))
          (t
           (append *fn-stx-token-absent*
                   (append '(32) (fn-stx-reason-token detail)))))))

; Printability is what the HDR renderer needs of this item: every octet is a
; printable US-ASCII character, so no rendering can carry CR, LF or NUL into
; a response line.  books/nntp-legacy.lisp's cleanliness theorems discharge
; against this (board CHANGE w7/substrate-s1).
(defun fn-stx-printablep (octets)
  (declare (xargs :guard t))
  (if (consp octets)
      (and (integerp (car octets))
           (<= 32 (car octets))
           (<= (car octets) 126)
           (fn-stx-printablep (cdr octets)))
    (null octets)))

(defthm fn-stx-printablep-of-append
  (equal (fn-stx-printablep (append a b))
         (and (fn-stx-printablep a) (fn-stx-printablep b))))

(defthm fn-stx-hex-octets-are-printable
  (fn-stx-printablep (fn-stx-hex-octets octets))
  :hints (("Goal" :in-theory (disable floor mod))))

(defthm fn-stx-decimal-rev-is-printable
  (fn-stx-printablep (fn-stx-decimal-rev n))
  :hints (("Goal" :in-theory (disable floor mod))))

(defthm fn-stx-printablep-of-revappend
  (implies (and (fn-stx-printablep a) (fn-stx-printablep b))
           (fn-stx-printablep (revappend a b))))

(defthm fn-stx-decimal-octets-are-printable
  (fn-stx-printablep (fn-stx-decimal-octets n)))

(defthm fn-stx-verified-item-is-printable
  (fn-stx-printablep (fn-stx-verified-item verdict)))

(defthm fn-stx-verified-item-is-non-empty
  (consp (fn-stx-verified-item verdict)))

; Three outcomes stay distinct all the way out (D13): the rendered item
; begins with a different token for each member of *fn-stx-verdicts*, so no
; rendering collapses :unverified and :absent.
(defthm fn-stx-verified-item-separates-the-three-outcomes
  (and (equal (fn-stx-verified-item (fn-stx-make-verdict :verified detail generation))
              (append *fn-stx-token-verified*
                      (append '(32)
                              (append (fn-stx-hex-octets detail)
                                      (fn-stx-keyring-suffix generation)))))
       (equal (fn-stx-verified-item (fn-stx-make-verdict :unverified detail generation))
              (append *fn-stx-token-unverified*
                      (append '(32)
                              (append (fn-stx-reason-token detail)
                                      (fn-stx-keyring-suffix generation)))))
       (equal (fn-stx-verified-item (fn-stx-make-verdict :absent detail generation))
              (append *fn-stx-token-absent*
                      (append '(32) (fn-stx-reason-token detail)))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

(in-theory (disable (:d fn-stx-field) (:d fn-stx-statement-of) (:d fn-stx-verdict)
                    (:d fn-stx-hex-digit) (:d fn-stx-hex-octets)
                    (:d fn-stx-decimal-rev) (:d fn-stx-decimal-octets)
                    (:d fn-stx-reason-token) (:d fn-stx-keyring-suffix)
                    (:d fn-stx-verified-item) (:d fn-stx-printablep)))
