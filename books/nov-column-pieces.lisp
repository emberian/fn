; Fixed reference capture into the mixed NOV formatter, PRF-1066 component.
(in-package "ACL2")
(include-book "nov-column-window")
(include-book "nov-piece-window")

(defun fn-npw-column-pieces (number facts octets)
  (declare (xargs :guard t))
  (let ((nov (fn-hf-nov facts)))
    (list (fn-nntp-decimal-field number) '(9)
          (fn-hnov-subject nov) '(9)
          (fn-hnov-from nov) '(9)
          (fn-hnov-date nov) '(9)
          (fn-hnov-msgid nov) '(9)
          (fn-hnov-references nov) '(9)
          (list :decimal (nfix octets) nil) '(9)
          (list :decimal (nfix (fn-hf-body-lines facts)) nil) '(13 10))))

(local
 (defthm fn-npw-nntp-string-octets-agree
   (equal (fn-record-string-octets-aux chars)
          (fn-nntp-string-octets-aux chars))
   :hints (("Goal" :induct (fn-record-string-octets-aux chars)
                   :in-theory (enable fn-record-string-octets-aux
                                      fn-nntp-string-octets-aux)))))

(local
 (defthm fn-npw-nntp-octets-are-cbor
   (equal (fn-cbor-octet-listp bytes) (fn-octet-listp bytes))
   :hints (("Goal" :induct (fn-octet-listp bytes)
                   :in-theory (enable fn-octet-listp fn-octetp
                                      fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-npw-octet-piece
   (implies (fn-octet-listp bytes)
            (and (fn-npw-partp bytes fn-arena)
                 (equal (fn-npw-part-bytes bytes pos fn-arena) bytes)))
   :hints (("Goal" :in-theory (enable fn-octet-listp fn-octetp
                                      fn-npw-partp fn-npw-part-bytes)))))

(defthm fn-npw-column-pieces-have-shape
  (implies (fn-hnov-p (fn-hf-nov facts))
           (fn-npw-piecesp (fn-npw-column-pieces number facts octets) fn-arena))
  :hints (("Goal" :in-theory
           (e/d (fn-npw-column-pieces fn-npw-piecesp fn-npw-partp
                 fn-hnov-p fn-hnov-internals)
                (fn-nntp-decimal-field)))))

; Natural metadata is rendered in full, independently of any codec width.
; Capturing it allocates a fixed number of references; digit production is
; charged later by fn-npw-tick. The initial article number retains the
; existing bounded NNTP number renderer.
(defthm fn-npw-column-pieces-refine-column
  (implies (and (fn-hnov-p (fn-hf-nov facts))
                (natp octets) (natp (fn-hf-body-lines facts)))
           (equal (fn-npw-remaining (fn-npw-column-pieces number facts octets) 0 fn-arena)
                  (fn-nbw-remaining (fn-nbw-column-pieces number facts octets) 0)))
  :hints (("Goal" :in-theory
           (e/d (fn-npw-column-pieces fn-npw-remaining fn-npw-part-bytes
                 fn-nbw-column-pieces fn-nbw-remaining fn-nntp-decimal
                 fn-nntp-decimal-rev fn-hnov-p fn-hnov-internals)
                (fn-nntp-decimal-field fn-record-string-octets
                 explode-nonnegative-integer)))))

(defthm fn-npw-column-pieces-are-complete-row
  (implies (and (fn-hnov-p (fn-hf-nov facts))
                (fn-hnov-ok (fn-hf-nov facts))
                (natp (fn-hf-body-lines facts)))
           (equal (fn-npw-remaining
                   (fn-npw-column-pieces number facts
                     (fn-nntp-article-length article fn-arena)) 0 fn-arena)
                  (append (fn-nov-line number (fn-scol-nov-overview article facts fn-arena))
                          '(13 10))))
  :hints (("Goal" :use ((:instance fn-npw-column-pieces-refine-column
                                   (octets (fn-nntp-article-length article fn-arena)))
                        (:instance fn-nbw-column-pieces-are-complete-row))
                  :in-theory (disable fn-npw-column-pieces fn-npw-remaining
                                      fn-nbw-column-pieces fn-nbw-remaining
                                      fn-npw-column-pieces-refine-column
                                      fn-nbw-column-pieces-are-complete-row
                                      fn-nov-line fn-scol-nov-overview))))
