; Witnesses and teeth for books/nntp-zarticle (PRF-993, NNT-055; lane
; compress-7).  The fn-zar- keystones are stated over A-ARENA-STORED's
; constrained fn-arena-stored (books/assumptions-stored.lisp), which the
; prover cannot run.  Here a test attachment answers it the way the host's
; extent read does for a compressed extent -- (DICT C N) with C a DEFLATE
; stream over baseline 1 -- and ACL2 admits the attachment only after
; proving A-ARENA-STORED's constraint of it.  Every witness below is an
; assert-event executed through that attachment: fn-zar-decide itself runs,
; over a sealed arena and the pinned Message-ID trie ARTICLE uses.
;
; The attachment is a test realiser, not the host's: what it shows is that
; the keystones' antecedents are reachable together and each retained
; hypothesis is load-bearing, not that host/native/extent.lisp answers the
; constraint (that is the assumption's content).
(in-package "ACL2")
(include-book "../../books/nntp-zarticle")
(include-book "must-fail-checked")

;; A DEFLATE stored block (RFC 1951 3.2.4): BFINAL 1, BTYPE 00, LEN, NLEN.
(defun zat-stored-block (p)
  (declare (xargs :guard (and (true-listp p) (< (len p) 65536))))
  (let ((n (len p)))
    (list* 1 (mod n 256) (floor n 256) (mod (- 65535 n) 256) (floor (- 65535 n) 256) p)))

;; An article of 140 octets, and the 60-octet raw DEFLATE stream zlib 1.3
;; makes of it with baseline 1 as the preset dictionary (level 9, wbits
;; -15): its back-references reach into the dictionary.
(defconst *zat-p*
  (append (fn-nntp-string-octets "Subject: hello") (list 13 10)
          (fn-nntp-string-octets "From: a@b.example") (list 13 10)
          (fn-nntp-string-octets "Newsgroups: fn.test") (list 13 10 13 10)
          (fn-nntp-string-octets
           "Since this command provides the same functionality as LIST, because the message.")
          (list 13 10)))
(defconst *zat-c* '(131 95 222 154 145 10 12 2 94 46 200 121 90 137 14 73 176 42 6 227 248 44 72 245 197 203 21 12 189 32 14 105 167 34 236 82 32 68 80 192 250 22 144 1 29 96 61 4 170 214 117 144 199 229 97 213 46 208 209 0))

(assert-event (and (equal (len *zat-p*) 140) (equal (len *zat-c*) 60)
                   (equal (fn-lzr-lz-value *fn-lzd-baseline-1* *zat-c* 140) *zat-p*)))

(defun zat-block-of (p)
  (declare (xargs :guard (and (true-listp p) (< (len p) 65536))))
  (if (equal p *zat-p*) *zat-c* (zat-stored-block p)))

;; The test realiser: H's payload as (baseline 1, its block, its length),
;; answered only when the block decodes to the payload -- the host's
;; commit check (books/payload-lz-record.lisp) at a test scale.
(defun zat-arena-stored (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (and (natp h) (< h (fn-arena-count fn-arena)))
      (let ((p (fn-arena-payload h fn-arena)))
        (if (and (true-listp p) (< (len p) 65536))
            (let ((s (list *fn-lzd-baseline-1* (zat-block-of p) (len p))))
              (if (equal (ec-call (fn-lzr-lz-value (car s) (cadr s) (caddr s))) p) s nil))
          nil))
    nil))

(defattach (fn-arena-stored zat-arena-stored)
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-count))))

;; MUTATION (not a reachable state): a realiser that answers a block which
;; decodes to something else is refused -- the constraint has teeth.
(defun zat-arena-stored-lying (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (and (natp h) (< h (fn-arena-count fn-arena)))
      (list *fn-lzd-baseline-1* *zat-c* 140)
    nil))

(must-fail-checked
 (defattach (fn-arena-stored zat-arena-stored-lying)
   :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-count))))
 :unchecked "defattach admits a realiser only by proving A-ARENA-STORED's constraint of it; the assert-event below shows the constraint is false for this one")

(defun zat-lying-at-hi ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let* ((fn-arena (fn-arn-seal-many (list (fn-nntp-string-octets "hi")) fn-arena))
             (s (zat-arena-stored-lying 0 fn-arena)))
        (mv (list s (fn-arena-payload 0 fn-arena)) fn-arena))
      r)))

(assert-event
 (let ((s (car (zat-lying-at-hi))) (payload (cadr (zat-lying-at-hi))))
   (and s
        (equal payload (fn-nntp-string-octets "hi"))
        (not (equal (fn-lzr-lz-value (car s) (cadr s) (caddr s)) payload)))))

;; The fixture: one article, handle 0, in the pinned trie ARTICLE reads.
(defconst *zat-mid* (fn-nntp-string-octets "<a@b.example>"))
(defconst *zat-article* (fn-make-article "<a@b.example>" 0 '("fn.test") nil nil nil))
(defconst *zat-index* (fn-midx-build (list *zat-article*)))
(defconst *zat-d1* *fn-lzd-baseline-1-blake3*)
(defconst *zat-other* (make-list 32 :initial-element 7))

;; (DECISION STORED BYTES REQ) for ARGS over an arena holding PAYLOADS.  The
;; runs are functions, not constants: a defconst may not call an attachment.
(defun zat-run (payloads args)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let* ((fn-arena (fn-arn-seal-many payloads fn-arena))
             (req (fn-zdn-request args))
             (article (fn-zar-article (cadr req) *zat-index*)))
        (mv (list (fn-zar-decide args *zat-index* fn-arena)
                  (fn-zar-stored article fn-arena)
                  (fn-nntp-article-bytes article fn-arena)
                  req)
            fn-arena))
      r)))

(defun zat-both () (declare (xargs :verify-guards nil)) (zat-run (list *zat-p*)
                              (list *zat-mid* (fn-zdn-hex *zat-other*) (fn-zdn-hex *zat-d1*))))
(defun zat-without () (declare (xargs :verify-guards nil)) (zat-run (list *zat-p*) (list *zat-mid* (fn-zdn-hex *zat-other*))))
(defun zat-unknown () (declare (xargs :verify-guards nil)) (zat-run (list *zat-p*)
                                 (list (fn-nntp-string-octets "<z@b.example>")
                                       (fn-zdn-hex *zat-d1*))))
(defun zat-plain () (declare (xargs :verify-guards nil)) (zat-run (list (fn-nntp-string-octets "hi")) ; stored-block path
                               (list *zat-mid* (fn-zdn-hex *zat-d1*))))

;; KEYSTONES fn-zar-decide-stored-denotes and fn-zar-decide-complete,
;; reachable: the request parses, the article is held compressed under
;; baseline 1, whose digest the peer listed (second of two); every
;; antecedent holds, the decision is (:stored D1 C 140), D1 is listed, C is
;; octets, and C decodes against D1's shipped dictionary to the article's
;; octets as ARTICLE reads them.
(assert-event
 (let* ((d (nth 0 (zat-both))) (s (nth 1 (zat-both))) (bytes (nth 2 (zat-both)))
        (req (nth 3 (zat-both))))
   (and (not (equal req :syntax))
        s
        (fn-zdn-digest-of-dict (car s))
        (member-equal (fn-zdn-digest-of-dict (car s)) (caddr req))
        (equal (car d) :stored)
        (equal d (list :stored (fn-zdn-digest-of-dict (car s)) (cadr s) (caddr s)))
        (equal d (list :stored *zat-d1* *zat-c* 140))
        (member-equal (nth 1 d) (caddr req))
        (fn-octet-listp (nth 2 d))
        (equal bytes *zat-p*)
        (equal (fn-lzr-lz-value (fn-zdn-dict-of-digest (nth 1 d)) (nth 2 d) (nth 3 d))
               bytes))))

;; The same keystones over the stored-block (BTYPE 00) answer of another
;; article: still stored, still decoding to the article's octets.
(assert-event
 (let ((d (nth 0 (zat-plain))))
   (and (equal (car d) :stored)
        (equal (nth 2 d) (zat-stored-block (fn-nntp-string-octets "hi")))
        (equal (fn-lzr-lz-value (fn-zdn-dict-of-digest (nth 1 d)) (nth 2 d) (nth 3 d))
               (nth 2 (zat-plain)))
        (equal (nth 2 (zat-plain)) (fn-nntp-string-octets "hi")))))

;; fn-zar-decide-complete WITHOUT the membership hypothesis: the request
;; parses, the article is held compressed and its dictionary has a shipped
;; digest (the retained hypotheses hold), the peer did not list it, and the
;; decision is not stored: it is ARTICLE's decoded answer.
(assert-event
 (let* ((d (nth 0 (zat-without))) (s (nth 1 (zat-without))) (req (nth 3 (zat-without))))
   (and (not (equal req :syntax))
        s
        (fn-zdn-digest-of-dict (car s))
        (not (member-equal (fn-zdn-digest-of-dict (car s)) (caddr req)))
        (not (equal d (list :stored (fn-zdn-digest-of-dict (car s)) (cadr s) (caddr s))))
        (equal d (list :decoded *zat-mid*)))))

;; fn-zar-decide-complete WITHOUT the stored-answer hypothesis: the request
;; parses and lists D1, the Message-ID names no article, the store has no
;; stored answer, and the decision is decoded (ARTICLE's 430 path).
(assert-event
 (let* ((d (nth 0 (zat-unknown))) (s (nth 1 (zat-unknown))) (req (nth 3 (zat-unknown))))
   (and (not (equal req :syntax))
        (member-equal *zat-d1* (caddr req))
        (null s)
        (not (equal (car d) :stored))
        (equal (car d) :decoded))))

;; fn-zar-decide-stored-denotes WITHOUT its hypothesis (car d = :stored):
;; a decoded decision, whose digest position is not one the peer listed.
(assert-event
 (let* ((d (nth 0 (zat-without))) (req (nth 3 (zat-without))))
   (and (not (equal (car d) :stored))
        (not (member-equal (nth 1 d) (caddr req))))))
