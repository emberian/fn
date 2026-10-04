; Cached NOV row references for byte quanta (Q5c/J1, PRF-1066).
; The runtime constructor copies only a fixed number of references.  It
; never converts a cached header string or concatenates a complete row.
; This older constructor still materializes numerical fields. The mixed
; piece constructor replaces that setup with resumable decimal phases.
(in-package "ACL2")
(include-book "nov-byte-window")
(include-book "served-columns")
(include-book "nntp-effects")

(local (in-theory (disable fn-nntp-decimal-field fn-nntp-decimal fn-record-string-octets)))

(defun fn-nbw-column-pieces (number facts octets)
  (declare (xargs :guard t))
  (let ((nov (fn-hf-nov facts)))
    (list (fn-nntp-decimal-field number) '(9)
          (fn-hnov-subject nov) '(9)
          (fn-hnov-from nov) '(9)
          (fn-hnov-date nov) '(9)
          (fn-hnov-msgid nov) '(9)
          (fn-hnov-references nov) '(9)
          (fn-nntp-decimal octets) '(9)
          (fn-nntp-decimal (fn-hf-body-lines facts)) '(13 10))))

(local
 (defthm fn-nbw-octet-listp-is-cbor
   (equal (fn-cbor-octet-listp bytes) (fn-octet-listp bytes))
   :hints (("Goal" :induct (fn-octet-listp bytes)
                   :in-theory (enable fn-octet-listp fn-octetp
                                      fn-cbor-octet-listp fn-cbor-octetp)))))

(defthm fn-nbw-column-pieces-have-shape
  (implies (fn-hnov-p (fn-hf-nov facts))
           (fn-nbw-piecesp (fn-nbw-column-pieces number facts octets)))
  :hints (("Goal" :in-theory (enable fn-nbw-column-pieces fn-nbw-piecesp
                                     fn-hnov-p fn-hnov-internals))))

; The abstraction of the runtime references is exactly the existing NOV
; row, including CRLF.  Expansion is theorem vocabulary, never runtime.
(defthm fn-nbw-column-pieces-are-complete-row
  (implies (and (fn-hnov-p (fn-hf-nov facts))
                (fn-hnov-ok (fn-hf-nov facts)))
           (equal (fn-nbw-remaining
                   (fn-nbw-column-pieces number facts
                                         (fn-nntp-article-length article fn-arena)) 0)
                  (append (fn-nov-line number (fn-scol-nov-overview article facts fn-arena))
                          '(13 10))))
  :hints (("Goal" :in-theory
           (e/d (fn-nbw-column-pieces fn-nbw-remaining fn-scol-nov-overview
                 fn-nov-line fn-nntp-append-pieces fn-nov-subject fn-nov-from
                 fn-nov-date fn-nov-msgid fn-nov-references fn-nov-bytes fn-nov-lines
                 fn-hnov-p fn-hnov-internals)
                (fn-nntp-article-length fn-nntp-decimal fn-nntp-decimal-field
                 fn-record-string-octets)))))

(local
 (defthm fn-nbw-ok-column-has-facts
   (implies (fn-hnov-ok (fn-hf-nov facts)) facts)
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-hf-nov fn-hnov-ok)))))

; The maintained column relation F ties this constructor's row to the
; actual immutable article bytes.  It does not assert that every legacy
; row has a cache: missing-cache hydration remains a separate obligation.
(defthm fn-nbw-column-pieces-refine-article-row
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (equal facts (fn-scol-facts article fn-cat))
                (fn-hnov-ok (fn-hf-nov facts)))
           (equal (fn-nbw-remaining
                   (fn-nbw-column-pieces number facts
                                         (fn-nntp-article-length article fn-arena)) 0)
                  (append (fn-nov-line number (fn-nov-overview article fn-arena))
                          '(13 10))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-nbw-column-pieces-are-complete-row)
                        (:instance fn-scol-facts-are-the-bytes-facts)
                        (:instance fn-hnov-p-of-hnov-of
                                   (bytes (fn-nntp-article-bytes article fn-arena)))
                        (:instance fn-scol-nov-overview-of-bytes-facts))
                  :in-theory (disable fn-nbw-column-pieces-are-complete-row
                                      fn-scol-facts-are-the-bytes-facts
                                      fn-scol-nov-overview-of-bytes-facts
                                      fn-hnov-p-of-hnov-of fn-scol-okp fn-scol-facts
                                      fn-hf-nov fn-hnov-p fn-nntp-article-bytes fn-hnov-of
                                      fn-nbw-column-pieces fn-nbw-remaining
                                      fn-nov-line fn-scol-nov-overview
                                      fn-nov-overview fn-held-facts-of))))
