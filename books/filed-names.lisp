; fn: the NNTP string-octet length is the record string-octet length, shared
; by the two proofs that a filed article's Newsgroups groups are the source's
; (books/filed-groups.lisp, packet 2, and books/filed-stored.lisp, P4-3).
; Each includer includes this book locally, so neither rule reaches a third
; book.  Kept apart from books/filed-parse.lisp, whose world does not carry
; the NNTP string definitions.
(in-package "ACL2")

(include-book "nntp-syntax")
(include-book "records-shape")

(defthm o1n-nntp-string-octets-aux-is-record
  (equal (fn-nntp-string-octets-aux chars) (fn-record-string-octets-aux chars))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux fn-record-string-octets-aux))))

(defthm o1n-nntp-string-octets-is-record
  (equal (fn-nntp-string-octets x) (fn-record-string-octets x))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets fn-record-string-octets))))
