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
; It is produced by ACL2 from the row, never declared by an operator, and
; `fn-ocap-admit-preview' consumes it exactly as any descriptor.
;
; The descriptor is `(:tariff :article OCTETS)' (books/output-command-
; admission.lisp fn-ocap-tariffp); an ELEN the descriptor cannot carry is
; refused by name (:unrepresentable), never saturated (D27).

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

; Every ELEN below this bound gives an OCTETS below 2^64, the descriptor's
; domain; an extent is a u64 length, so the bound is the descriptor's, not a
; ceiling on stored data.
(defconst *fn-tariff-article-elen-max* (expt 2 56))

(defun fn-tariff-article-descriptor (elen)
  (declare (xargs :guard t))
  (if (and (natp elen) (< elen *fn-tariff-article-elen-max*))
      (list :tariff :article (fn-tariff-article-octets elen))
    (list :unrepresentable :article)))

(defthm fn-tariff-article-octets-natp
  (implies (natp elen) (natp (fn-tariff-article-octets elen)))
  :rule-classes :type-prescription)

(defthm fn-tariff-article-descriptor-is-a-tariff
  (implies (and (natp elen) (< elen *fn-tariff-article-elen-max*))
           (fn-ocap-tariffp (fn-tariff-article-descriptor elen))))

; KEYSTONE (charge-before-effect at the gate): over an :article preview the
; produced descriptor is admitted EXACTLY when its octets are within the
; capacity, and then the held prefix is the preview's own; any other word
; is a refusal.  Both directions, so an unaffordable article is refused by
; name and an affordable one is never refused for its price.
(defthm fn-tariff-article-admits-exactly-within-capacity
  (implies (and (natp elen) (< elen *fn-tariff-article-elen-max*)
                (fn-ocap-previewp preview)
                (equal (fn-ocap-at 2 preview) :article)
                (natp capacity) (< capacity 18446744073709551616))
           (equal (fn-ocap-admit-preview preview (fn-tariff-article-descriptor elen) capacity)
                  (if (<= (fn-tariff-article-octets elen) capacity)
                      (list :hold (fn-ocap-at 1 preview) :article)
                    (list :refused :output-tariff-unaffordable :article)))))

; An unrepresentable length is refused by name, never held.
(defthm fn-tariff-article-unrepresentable-is-refused
  (implies (not (and (natp elen) (< elen *fn-tariff-article-elen-max*)))
           (equal (fn-ocap-at 0 (fn-ocap-admit-preview preview (fn-tariff-article-descriptor elen) capacity))
                  :refused)))
