; fn: XFN-ZARTICLE served (NNT-055, lane compress-5;
; docs/extensions/nntp-compress-dict.md "Negotiation").  Prefix `fn-zar-'.
;
;   XFN-ZARTICLE <message-id> <b3-hex> [<b3-hex> ...]
;
; The peer lists the full BLAKE3 digests of the dictionaries it holds.  When
; the store holds the article's payload compressed under a dictionary the
; peer listed, the answer is the block AS IT IS STORED, never decoded here:
;
;   229 <b3-hex> <N> <CLEN>        then the block C, escaped and cut into
;                                  lines (books/nntp-compress-dict.lisp
;                                  fn-zdn-body-lines), dot-stuffed, ".".
;
; N is the payload's length, CLEN is C's.  Otherwise the answer is exactly
; what ARTICLE <message-id> answers by Message-ID
; (fn-nntp-msgid-retrieval-indexed): 220 and the article, 430, and so on.
; A withdrawn identifier and a syntax error are the protocol table's arms
; (books/protocol-table.lisp row XFN-ZARTICLE); this book is its :model.
;
; KEYSTONES:
;   fn-zar-decide-stored-denotes   a stored answer names a digest the peer
;                                  listed, and C decodes under that digest's
;                                  dictionary to the article's octets
;                                  (A-ARENA-STORED, books/assumptions-stored)
;   fn-zar-decide-complete         a payload stored under a listed
;                                  dictionary is always answered stored
;   fn-zdn-body-round-trip         (books/nntp-compress-dict) the receiver's
;                                  join and unescape give C back

(in-package "ACL2")
(include-book "nntp-compress-dict")
(include-book "assumptions-stored")
(include-book "nntp-responses")

(defconst *fn-zar-bound* 4294967296) ; the frame's u32 fields (payload-lz-record)

; The store's answer for ARTICLE's payload, when it is held compressed, with
; C octets and both lengths u32 (the frame's fields: a longer one cannot be
; stored compressed).  nil otherwise.
(defun fn-zar-stored (article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((p (and (consp article) (fn-article-payload article))))
    (if (and (natp p) (< p (fn-arena-count fn-arena)))
        (let ((s (fn-arena-stored p fn-arena)))
          (if (and (true-listp s) (equal (len s) 3)
                   (fn-octet-listp (cadr s))
                   (natp (caddr s)) (< (caddr s) *fn-zar-bound*)
                   (< (len (cadr s)) *fn-zar-bound*))
              s
            nil))
      nil)))

(defun fn-zar-initial (digest n clen)
  (declare (xargs :guard t))
  (append (fn-nntp-string-octets "229 ") (fn-zdn-hex digest)
          (list 32) (fn-nntp-decimal-field (nfix n))
          (list 32) (fn-nntp-decimal-field (nfix clen))))

(defun fn-zar-article (token index)
  ; The article TOKEN names in the pinned Message-ID trie INDEX, as the ARTICLE
  ; retrieval finds it (fn-nntp-msgid-retrieval-indexed).
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-octet-listp token)
      (fn-midx-lookup (fn-nntp-token-string token) index)
    nil))

; The stored answer decodes to the article's octets (A-ARENA-STORED).
(defthm fn-zar-stored-denotes
  (let ((s (fn-zar-stored article fn-arena)))
    (implies s
             (and (fn-octet-listp (cadr s))
                  (equal (fn-lzr-lz-value (car s) (cadr s) (caddr s))
                         (fn-nntp-article-bytes article fn-arena)))))
  :hints (("Goal" :in-theory (enable fn-nntp-article-bytes fn-nntp-payload-bytes))))

; The decision: :syntax, (:stored DIGEST C N), or (:decoded TOKEN).
(defun fn-zar-decide (args index fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((req (fn-zdn-request args)))
    (if (equal req :syntax)
        :syntax
      (let* ((token (cadr req))
             (article (fn-zar-article token index))
             (s (fn-zar-stored article fn-arena))
             (ch (fn-zdn-choose s (true-list-fix (caddr req)))))
        (if (equal (car ch) :stored)
            (list :stored (cadr ch) (cadr s) (caddr s))
          (list :decoded token))))))

;; The line is checked, not assumed: printable ASCII, "229 " first, at most
;; 510 octets.  It is 4 + 64 + 2 + at most 20 octets of hex and digits
;; whenever the digest is a shipped one, so the check never fails in
;; composition; if it did, the answer would be the decoded one.
;; (books/nntp-pinned-effects.lisp: it implies the response grammar's
;; initial line, fn-zar-line-okp-is-an-initial-line.)
(defun fn-zar-printablep (line)
  (declare (xargs :guard t))
  (if (consp line)
      (and (integerp (car line)) (<= 32 (car line)) (<= (car line) 126)
           (fn-zar-printablep (cdr line)))
    (null line)))

(defun fn-zar-line-okp (initial)
  (declare (xargs :guard t))
  (and (fn-zar-printablep initial)
       (<= (+ (len initial) 2) *fn-nntp-max-response-octets*)
       (equal (take 4 initial) (list 50 50 57 32))))

(defun fn-zar-command (session archive index args fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((d (fn-zar-decide args index fn-arena)))
    (if (equal d :syntax)
        (fn-nntp-single session (fn-proto-text * :syntax))
      (let ((initial (and (equal (car d) :stored)
                          (fn-zar-initial (nth 1 d) (nth 3 d) (len (nth 2 d))))))
        (if (and (equal (car d) :stored) (fn-zar-line-okp initial))
            (fn-nntp-multi-octets session initial (fn-zdn-body-lines (nth 2 d)))
          (fn-nntp-msgid-retrieval-indexed
           session archive index :article
           (if (equal (car d) :stored) (cadr (fn-zdn-request args)) (cadr d))
           fn-arena))))))

; -----------------------------------------------------------------------------
; KEYSTONES.

(defthm fn-zar-decide-stored-denotes
  (let ((d (fn-zar-decide args index fn-arena))
        (article (fn-zar-article (cadr (fn-zdn-request args)) index)))
    (implies (equal (car d) :stored)
             (and (not (equal (fn-zdn-request args) :syntax))
                  (member-equal (nth 1 d) (caddr (fn-zdn-request args)))
                  (fn-octet-listp (nth 2 d))
                  (equal (fn-lzr-lz-value (fn-zdn-dict-of-digest (nth 1 d)) (nth 2 d) (nth 3 d))
                         (fn-nntp-article-bytes article fn-arena)))))
  :hints (("Goal" :in-theory (disable fn-zdn-request fn-zdn-choose fn-zar-article
                                      fn-zar-stored fn-zdn-digest-of-dict
                                      fn-zdn-dict-of-digest fn-zdn-choose-stored-only-shared
                                      fn-zar-stored-denotes)
           :use ((:instance fn-zar-stored-denotes
                            (article (fn-zar-article (cadr (fn-zdn-request args)) index)))
                 (:instance fn-zdn-choose-stored-only-shared
                            (stored (fn-zar-stored
                                     (fn-zar-article (cadr (fn-zdn-request args)) index)
                                     fn-arena))
                            (digests (true-list-fix (caddr (fn-zdn-request args)))))))))

(local (defthm fn-zar-member-true-list-fix
  (iff (member-equal x (true-list-fix l)) (member-equal x l))))

(defthm fn-zar-decide-complete
  (let* ((req (fn-zdn-request args))
         (s (fn-zar-stored (fn-zar-article (cadr req) index) fn-arena)))
    (implies (and (not (equal req :syntax))
                  s
                  (fn-zdn-digest-of-dict (car s))
                  (member-equal (fn-zdn-digest-of-dict (car s)) (caddr req)))
             (equal (fn-zar-decide args index fn-arena)
                    (list :stored (fn-zdn-digest-of-dict (car s)) (cadr s) (caddr s)))))
  :hints (("Goal" :in-theory (disable fn-zdn-request fn-zar-stored fn-zar-article
                                      fn-zdn-digest-of-dict fn-zdn-choose
                                      fn-zdn-choose-complete)
           :use ((:instance fn-zdn-choose-complete
                            (stored (fn-zar-stored (fn-zar-article (cadr (fn-zdn-request args))
                                                                   index)
                                                   fn-arena))
                            (digests (true-list-fix (caddr (fn-zdn-request args)))))))))

(in-theory (disable fn-zar-decide fn-zar-article fn-zar-stored fn-zar-initial fn-zar-line-okp))
