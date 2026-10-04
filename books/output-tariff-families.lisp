; fn: the priced command families, one row each (lane tariff3, 2026-10-04;
; planning/design/tariff-2026-10-04.md Q3, the families in the packet's
; order).  books/output-tariff-family.lisp generates the producer the host
; calls (fn-tariff-family-preview), its keystone and one instance per row;
; tools/cost_obligations.py counts the rows (the ratchet).
;
; The retrieval rows read the ROW their factory serves, by the factory's own
; lookup (books/output-tariff-article-row.lisp fn-tariff-article-row-charge:
; the number, current and Message-ID forms; the Xref form's two renders),
; whatever the kind: ARTICLE, HEAD, BODY and STAT name the same row
; (books/protocol-served-table.lisp, one finder per form for the four).
; The figures are books/output-tariff-article.lisp's: HEAD and BODY within
; ARTICLE's, STAT the initial line and the realized extent.

(in-package "ACL2")
(include-book "output-tariff-family")
(include-book "output-tariff-article-row")

(def-family-tariffs
  :context ((tokens (fn-ocap-at 3 preview))
            (args (if (consp tokens) (cdr tokens) nil))
            (session (fn-post-session-base
                      (fn-peer-session-base (fn-auth-view-session as config))))
            (server (fn-tariff-article-server config)))
  :rows ((:article (fn-tariff-article-octets
                    (nfix (fn-tariff-article-row-charge session args server fn-arena fn-cat))))
         (:head (fn-tariff-article-octets
                 (nfix (fn-tariff-article-row-charge session args server fn-arena fn-cat))))
         (:body (fn-tariff-article-octets
                 (nfix (fn-tariff-article-row-charge session args server fn-arena fn-cat))))
         (:stat (fn-tariff-stat-octets
                 (nfix (fn-tariff-article-row-charge session args server fn-arena fn-cat))))))
