; fn: the tariff of the ARTICLE family (lane tariff, 2026-10-04;
; planning/design/tariff-2026-10-04.md Q3 and "The first slice").
;
; The tariff of a served read is a function of the ROW the factory serves
; (its extent length ELEN, read by the factory's own lookup:
; books/output-tariff-article-row.lisp) composed with the REPRESENTATION's
; cost model.  In the current representation the exec reply of
; fn-nntp-article-response-of-bytes (books/nntp-responses.lisp) is built in
; two passes of one cons cell per reply octet (fn-nntp-response-block-rev
; onto an accumulator, then revappend), and the extent is realized whole
; into the host's verified cache (host/native/extent.lisp
; fn-durable-realize-octets); so the resident octets of ARTICLE n are
;
;   2 * *fn-tariff-cons-octets* * (initial line + 2*ELEN + 3)  +  ELEN
;
; the first term the two spines (cumulative conses, the collector unmodelled:
; a cell is charged when consed, never credited when collected), the second
; the cache entry.  This is a logical-constructor tariff times a measured
; layout constant; it does NOT price the collector's copy, native vectors,
; the session update or the lookup's own cells (named in the packet's D).
; It is produced by ACL2 from the row, never declared by an operator.
;
; The descriptor is the family generator's (books/output-tariff-family.lisp
; fn-tariff-descriptor): a price the descriptor cannot carry is refused by
; name, never saturated (D27).

(in-package "ACL2")
(include-book "output-command-admission")

; SBCL x86-64: a cons cell is two 8-octet words.  A measured layout constant
; of the trusted base (the *fn-cost-contracts* convention), stated, not
; derived here.
(defconst *fn-tariff-cons-octets* 16)

; "220 " + a decimal number (at most 20 digits of a u64) + " " + a
; Message-ID (at most *fn-record-max-msgid* octets) + " article follows" +
; CRLF: the bound of fn-nntp-retrieval-initial's line.
(defconst *fn-tariff-article-initial-octets*
  (+ 4 20 1 *fn-record-max-msgid* 16 2))

; The reply's octets: the initial line, every line dot-stuffed and
; CRLF-terminated (at most one added octet a line, so within 2*ELEN), and
; the terminating ".\r\n".
(defun fn-tariff-article-reply-octets (elen)
  (declare (xargs :guard (natp elen)))
  (+ *fn-tariff-article-initial-octets* (* 2 elen) 3))

(defun fn-tariff-article-octets (elen)
  (declare (xargs :guard (natp elen)))
  (+ (* 2 *fn-tariff-cons-octets* (fn-tariff-article-reply-octets elen))
     elen))

(defthm fn-tariff-article-octets-natp
  (implies (natp elen) (natp (fn-tariff-article-octets elen)))
  :rule-classes :type-prescription)

; HEAD and BODY answer one section of the same octets through the same
; exec (fn-nntp-response-block-rev over the section, then revappend), with
; an initial line no longer than ARTICLE's, so ARTICLE's figure bounds them.
; STAT answers the initial line alone, but its exec realizes the octets
; once to tell a reclaimed article (fn-nntp-article-response-of-bytes
; reads them before the kind test): the line's two spines and the extent.
(defun fn-tariff-stat-octets (elen)
  (declare (xargs :guard (natp elen)))
  (+ (* 2 *fn-tariff-cons-octets* *fn-tariff-article-initial-octets*) elen))

(defthm fn-tariff-stat-octets-natp
  (implies (natp elen) (natp (fn-tariff-stat-octets elen)))
  :rule-classes :type-prescription)

(defthm fn-tariff-stat-within-article
  (implies (natp elen)
           (<= (fn-tariff-stat-octets elen) (fn-tariff-article-octets elen)))
  :rule-classes :linear)
