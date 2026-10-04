; fn: the ARTICLE tariff read from the ROW the factory serves (lane tariff2,
; 2026-10-04; planning/design/tariff-2026-10-04.md Q3, "The first slice").
;
; books/output-tariff-article.lisp prices an extent length ELEN.  This book
; reads that length the way the ARTICLE row's factory reaches its octets
; (books/protocol-served-table.lisp, the "ARTICLE" row): the number and
; current forms through the catalog's number table (fn-cat-group-number), the
; Message-ID form through its Message-ID column (fn-cat-msgid-seqs), and the
; octets' length as the arena's payload length -- one field read, nothing
; realized (books/payload-arena.lisp fn-arena-payload-len-is-len-nth).
;
; VERSION-FREE.  The preview runs before the factory and does not know which
; view the factory's step will read at (a repin can move it).  A number names
; at most one row and never another (catalog-logic.lisp: the number table is
; append-only), so the number form prices that row whatever the view; the
; served reply is that row's octets or a short line, never another row's.
; The Message-ID form prices the LONGEST row carrying the Message-ID, since
; the view picks the newest visible one.  Both are upper bounds at every view
; and exact where the factory serves the row
; (fn-tariff-article-prices-the-served-row).
;
; THE XREF FORM.  With an Xref server configured, the row's compatibility
; form (books/served-catalog.lisp fn-rcompat-retrieval-cat) answers over the
; stored octets with an Xref line prepended, and its exec may render the
; stored octets a second time (nntp-reader-compat.lisp
; fn-rcompat-article-reply-exec).  Its charge is the length of one render
; of the longer payload plus one of the stored one, folded into one
; length by the tariff's affine figure (fn-tariff-article-octets-of-two-renders).
;
; Every other reply of the row (no group, no such article, withdrawn,
; reclaimed, syntax) is one short line, priced at ELEN 0 when no row is
; named; a named row prices its length even when the factory then answers a
; short line (an upper bound, never under).

(in-package "ACL2")
(include-book "output-tariff-article")
(include-book "served-catalog")
(include-book "article-stream-server")

; The length of the octets a payload denotes, as fn-nntp-payload-bytes reads
; them: a handle's arena length, an inline payload's own length.
(defun fn-tariff-article-payload-elen (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (natp p)
      (if (< p (fn-arena-count fn-arena)) (fn-arena-payload-len p fn-arena) 0)
    (len p)))

(defthm fn-tariff-article-payload-elen-is-len
  (equal (fn-tariff-article-payload-elen p fn-arena)
         (len (fn-nntp-payload-bytes p fn-arena)))
  :hints (("Goal" :in-theory (enable fn-nntp-payload-bytes))))

; The Xref line the compatibility form prepends to the row's article, with
; its CRLF; 0 when it prepends none.
(defun fn-tariff-article-xref-octets (server article)
  (declare (xargs :guard t))
  (let ((pairs (fn-xref-pairs article)))
    (if (consp pairs) (+ 2 (len (fn-xref-field server pairs))) 0)))

(defthm fn-tariff-article-served-payload-within-xref
  (<= (len (fn-rcompat-served-payload-of-bytes server article bytes))
      (+ (len bytes) (fn-tariff-article-xref-octets server article)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-rcompat-served-payload-of-bytes))))

; One row's charge: its length, or with an Xref server the two renders of
; the compatibility form folded into one length.
(defun fn-tariff-article-seq-charge (s server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (if (and (natp s) (< s (fn-cat-count fn-cat)))
      (let ((e (fn-tariff-article-payload-elen (fn-record-payload (fn-cat-at s fn-cat)) fn-arena)))
        (if server
            (+ (* 2 e) (fn-tariff-article-xref-octets server (fn-cat-row-article s fn-arena fn-cat)) 146)
          e))
    0))

(defun fn-tariff-article-seqs-charge (seqs server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (if (consp seqs)
      (max (fn-tariff-article-seq-charge (car seqs) server fn-arena fn-cat)
           (fn-tariff-article-seqs-charge (cdr seqs) server fn-arena fn-cat))
    0))

(defun fn-tariff-article-number-charge (group n server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (fn-tariff-article-seq-charge (fn-cat-group-number group n fn-cat) server fn-arena fn-cat))

(defun fn-tariff-article-msgid-charge (msgid server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (fn-tariff-article-seqs-charge (fn-cat-msgid-seqs msgid fn-cat) server fn-arena fn-cat))

; The row's charge by form, in the row's own tests: no argument (current),
; one number, one Message-ID; anything else names no row.
(defun fn-tariff-article-row-charge (session args server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let ((group (fn-nntp-session-group session)))
    (cond ((null args)
           (if group
               (fn-tariff-article-number-charge group (fn-nntp-session-current session)
                                                server fn-arena fn-cat)
             0))
          ((not (and (consp args) (null (cdr args)))) 0)
          ((fn-nntp-number-tokenp (car args))
           (if group
               (fn-tariff-article-number-charge group (fn-nntp-decimal-value (car args))
                                                server fn-arena fn-cat)
             0))
          ((fn-nntp-message-id-tokenp (car args))
           (fn-tariff-article-msgid-charge (fn-nntp-token-string (car args))
                                           server fn-arena fn-cat))
          (t 0))))

; The producer.  PREVIEW is fn-ocap-preview's (:preview NEXT :article
; TOKENS), TOKENS the first command's tokens with its keyword; AS the
; connection's authenticated session and CONFIG its pinned configuration.
; The reader session and the Xref server are the factory's own projections
; (books/nntp-auth.lisp fn-auth-view-session; books/article-stream-server.lisp
; fn-asto-server-candidate-is-original-server).
(defun fn-tariff-article-server (config)
  (declare (xargs :guard t))
  (let ((server (fn-asto-server-candidate config)))
    (if (fn-xref-serverp server) server nil)))

(defun fn-tariff-article-preview (preview as config fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let* ((tokens (fn-ocap-at 3 preview))
         (args (if (consp tokens) (cdr tokens) nil))
         (session (fn-post-session-base
                   (fn-peer-session-base (fn-auth-view-session as config)))))
    (fn-tariff-article-descriptor
     (fn-tariff-article-row-charge session args (fn-tariff-article-server config)
                                   fn-arena fn-cat))))

; ---------------------------------------------------------------------------
; What the charge is a bound of.

(local
 (defthm fn-tariff-article-row-article-bytes
   (implies (and (natp s) (< s (fn-cat-count fn-cat)))
            (equal (len (fn-nntp-article-bytes (fn-cat-row-article s fn-arena fn-cat) fn-arena))
                   (fn-tariff-article-payload-elen (fn-record-payload (fn-cat-at s fn-cat)) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-cat-row-article fn-nntp-article-bytes)
                                   (fn-tariff-article-payload-elen))))))

(defthm fn-tariff-article-nil-bytes
  (equal (len (fn-nntp-article-bytes nil fn-arena)) 0)
  :hints (("Goal" :in-theory (enable fn-nntp-article-bytes fn-nntp-payload-bytes))))

; KEYSTONE (the number and current forms): at EVERY view, the octets the
; factory's number finder serves are exactly the length the producer read,
; or none.
(defthm fn-tariff-article-prices-the-served-row
  (equal (len (fn-nntp-article-bytes (fn-scat-number-article group n v fn-arena fn-cat) fn-arena))
         (if (fn-scat-number-article group n v fn-arena fn-cat)
             (fn-tariff-article-number-charge group n nil fn-arena fn-cat)
           0))
  :hints (("Goal" :in-theory (e/d (fn-scat-number-article fn-cnx-view-seq)
                                  (fn-cat-row-article fn-tariff-article-payload-elen)))))

; The view's choice among the rows carrying a Message-ID is within their
; maximum (the newest visible is one of them, or none).
(defthm fn-tariff-article-last-visible-within-charge
  (<= (fn-tariff-article-seq-charge (fn-cat-view-last-visible seqs v fn-cat) nil fn-arena fn-cat)
      (fn-tariff-article-seqs-charge seqs nil fn-arena fn-cat))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-cat-view-last-visible seqs v fn-cat)
           :in-theory (e/d (fn-cat-view-last-visible fn-tariff-article-seq-charge)
                           (fn-tariff-article-payload-elen fn-tariff-article-payload-elen-is-len
                            fn-cat-row-article fn-tariff-article-xref-octets)))))

(defthm fn-tariff-article-scat-msgid-unfold
  (equal (fn-scat-msgid-article msgid v fn-arena fn-cat)
         (if (fn-cat-view-last-visible (fn-cat-msgid-seqs msgid fn-cat) v fn-cat)
             (fn-cat-row-article (fn-cat-view-last-visible (fn-cat-msgid-seqs msgid fn-cat) v fn-cat)
                                 fn-arena fn-cat)
           nil))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-scat-msgid-article))))
(defthm fn-tariff-article-seq-charge-of-row
  (implies (and (natp s) (< s (fn-cat-count fn-cat)))
           (equal (fn-tariff-article-seq-charge s nil fn-arena fn-cat)
                  (fn-tariff-article-payload-elen (fn-record-payload (fn-cat-at s fn-cat)) fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-tariff-article-seq-charge))))
(defthm fn-tariff-article-seq-charge-of-nil
  (equal (fn-tariff-article-seq-charge nil server fn-arena fn-cat) 0)
  :hints (("Goal" :in-theory '(fn-tariff-article-seq-charge natp (:executable-counterpart integerp)))))

; KEYSTONE (the Message-ID form): at EVERY view, the octets the factory's
; Message-ID finder serves are within the charge the producer read.
(defthm fn-tariff-article-prices-the-served-msgid
  (<= (len (fn-nntp-article-bytes (fn-scat-msgid-article msgid v fn-arena fn-cat) fn-arena))
      (fn-tariff-article-msgid-charge msgid nil fn-arena fn-cat))
  :rule-classes :linear
  :hints (("Goal" :in-theory (union-theories '(fn-tariff-article-msgid-charge fn-tariff-article-nil-bytes
                                               fn-tariff-article-row-article-bytes
                                               fn-tariff-article-seq-charge-of-nil)
                                             (theory 'minimal-theory))
           :use ((:instance fn-tariff-article-scat-msgid-unfold)
                 (:instance fn-tariff-article-last-visible-within-charge
                            (seqs (fn-cat-msgid-seqs msgid fn-cat)))
                 (:instance fn-scat-last-visible-in-range
                            (seqs (fn-cat-msgid-seqs msgid fn-cat)))
                 (:instance fn-tariff-article-seq-charge-of-row
                            (s (fn-cat-view-last-visible (fn-cat-msgid-seqs msgid fn-cat) v fn-cat)))))))

; The Xref form's two renders: the served payload (stored + Xref line) and
; the stored one, within one render of the folded length.
(defthm fn-tariff-article-octets-of-two-renders
  (implies (and (natp e) (natp x))
           (<= (+ (fn-tariff-article-octets (+ e x)) (fn-tariff-article-octets e))
               (fn-tariff-article-octets (+ (* 2 e) x 146))))
  :rule-classes nil)
