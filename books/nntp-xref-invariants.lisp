;; fn: the served Xref field is clean and the dispatcher renders it (R3,
;; PRF-206).  The definitions and the pair keystones are books/nntp-xref.lisp;
;; this book adds what needs the overview's clean-line vocabulary
;; (books/nntp-overview.lisp, which includes the dispatcher).

(in-package "ACL2")
(include-book "nntp-overview")
(include-book "nntp-xref")

(local (in-theory (enable fn-nov-vocabulary
    fn-nntp-xref-server fn-nntp-listing-server fn-xref-serverp fn-xref-wordp
    fn-xref-pairs fn-xref-field fn-nov-served-line fn-nov-served-lines-numbered
    fn-nov-served-suffixes fn-nov-append-each fn-nntp-over-range-served
    fn-nntp-over-current-served fn-nntp-over-msgid-served
    fn-nntp-list-overview-fmt-served)))

(defthm fn-xref-octets-are-clean
  (implies (fn-xref-octetsp bytes) (fn-nov-clean-fieldp bytes)))

(defthm fn-xref-server-octets-are-clean
  (implies (fn-xref-server-octetsp bytes) (fn-nov-clean-fieldp bytes)))

(defthm fn-xref-pairs-of-groups-are-words
  (implies (member-equal m (fn-xref-pairs-of ms article))
           (fn-xref-wordp (fn-nntp-string-octets (car m))))
  :hints (("Goal" :in-theory (disable fn-xref-wordp fn-nntp-string-octets
                                      fn-nntp-article-number))))

(defun fn-xref-pair-listp (pairs)
  (declare (xargs :guard t))
  (if (consp pairs)
      (and (consp (car pairs))
           (fn-xref-wordp (fn-nntp-string-octets (car (car pairs))))
           (fn-xref-pair-listp (cdr pairs)))
    t))

(defthm fn-xref-pairs-of-is-a-pair-list
  (fn-xref-pair-listp (fn-xref-pairs-of ms article))
  :hints (("Goal" :in-theory (disable fn-xref-wordp fn-nntp-string-octets
                                      fn-nntp-article-number))))

(defthm fn-nov-clean-field-of-append
  (implies (and (fn-nov-clean-fieldp x) (fn-nov-clean-fieldp y))
           (fn-nov-clean-fieldp (append x y))))

(defthm fn-xref-locations-are-clean
  (implies (fn-xref-pair-listp pairs)
           (fn-nov-clean-fieldp (fn-xref-locations pairs)))
  :hints (("Goal" :in-theory (disable fn-nntp-string-octets
                                      fn-nntp-decimal-field))))

; No field of the Xref text can split the line or the overview record: it
; carries no TAB, CR, LF or NUL.
(defthm fn-xref-field-is-clean
  (implies (fn-xref-serverp server)
           (fn-nov-clean-fieldp (fn-xref-field server (fn-xref-pairs article))))
  :hints (("Goal" :in-theory (disable fn-xref-locations fn-xref-pairs-of fn-xref-server-octetsp))))

(defthm fn-nov-served-line-is-a-clean-line
  (implies (and (fn-nov-overviewp over)
                (or (null server) (fn-xref-serverp server)))
           (fn-nov-clean-linep (fn-nov-served-line number over server article)))
  :hints (("Goal" :in-theory (disable fn-nov-line fn-xref-field fn-xref-serverp
                                      fn-xref-pairs))))

(defthm fn-nov-served-lines-numbered-are-clean
  (implies (or (null server) (fn-xref-serverp server))
           (fn-nov-clean-line-listp
            (fn-nov-served-lines-numbered numbers nidx trie server fn-arena)))
  :hints (("Goal" :in-theory (disable fn-nov-overview fn-nov-served-line
                                      fn-gidx-nidx-number-article
                                      fn-rcl-tombstonep fn-xref-serverp))))

(defthm fn-nov-fmt-xref-lines-are-clean
  (fn-nov-clean-line-listp (fn-nov-fmt-octet-lines *fn-nov-fmt-xref-lines*)))

