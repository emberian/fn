; Witnesses and teeth for the widened XFNCATCHUP quantum (root ruling
; 2026-10-06, lane tariff4): the quantum charges the RENDERED record
; (`fn-cu-record-cost' in books/peer-catchup-serve.lisp) -- header line,
; body lines and CRLF framing, exactly the wire's octets -- so a batch of
; the smallest framable articles still charges every record's header and
; framing, and a round of them completes: every batch yields (NEXT moves
; past FROM), nothing deadlocks, and the single-record exception carries
; the record the quantum alone would refuse.
;
; The smallest article the view can serve has a 4-octet payload, CRLF CRLF:
; one empty header line, one empty body line, split-ok.  A zero-byte
; payload is never served at all (`fn-nntp-split-article' answers :error,
; so `fn-nntp-article-framedp' fails); the old charge's dishonesty was the
; uncharged header and framing of every SERVED record -- 41 of this
; record's 45 octets, an 11x undercharge of the wire at the minimum, worse
; for shorter msgids relative to payload -- not a servable zero-byte
; record.
(in-package "ACL2")
(include-book "../../books/peer-catchup-serve")
(include-book "arena-lift")

; The smallest framable payload (4 octets) and a one-line-body variant (8).
(defconst *cz-tiny-bytes* '(13 10 13 10))
(defconst *cz-small-bytes* '(104 13 10 13 10 98 13 10))

; The arena: handles 0..2 hold tiny, tiny, small.
(defconst *cz-arena* (list *cz-tiny-bytes* *cz-tiny-bytes* *cz-small-bytes*))

(defconst *cz-t1* (fn-make-article "<t1@example.invalid>" 0 '("fn.test")
                                   (list (cons "fn.test" 1)) t 842000000))
(defconst *cz-t2* (fn-make-article "<t2@example.invalid>" 1 '("fn.test")
                                   (list (cons "fn.test" 2)) t 842000001))
(defconst *cz-s1* (fn-make-article "<s1@example.invalid>" 2 '("fn.test")
                                   (list (cons "fn.test" 3)) t 842000002))
;; Newest first, as the view holds them.
(defconst *cz-articles* (list *cz-s1* *cz-t2* *cz-t1*))
(defconst *cz-state*
  (fn-make-state '("fn.test") (list (cons "fn.test" 3)) *cz-articles* 3 nil nil))
(defconst *cz-view* (list *cz-s1* *cz-t2* *cz-t1*))
(defconst *cz-groups* '("fn.test"))

; The tiny article is served (the antecedent is real: arts, group, framed).
(bpr-lift fn-cu-servedp 3)
(assert-event (in-arena-fn-cu-servedp *cz-arena* *cz-t1* *cz-groups* *cz-view*))
(assert-event (in-arena-fn-cu-servedp *cz-arena* *cz-s1* *cz-groups* *cz-view*))

; The rendered record of the smallest framable article: 45 octets -- 2
; ("R ") + 20 (the msgid) + 1 (space) + 16 (the count's hex) + 2 (the
; header line's CRLF) + 4 (the payload's own two empty lines).  The old
; charge read 4; the charge is the wire now
; (`fn-cu-rendered-records-are-the-charge').
(bpr-lift fn-cu-record-cost 1)
(assert-event (equal (in-arena-fn-cu-record-cost *cz-arena* *cz-t1*) 45))
(assert-event (< 0 (in-arena-fn-cu-record-cost *cz-arena* *cz-t1*)))

; LIVENESS (the root's condition): a round of the smallest articles
; completes.  Quantum 1 -- no record fits, not even one alone -- and every
; batch still serves exactly its one record (the first is always taken) and
; yields: NEXT moves past FROM at every position below the end, and at the
; end the round is done.  The charge is positive per record, so the
; positions advance on the entries themselves, never on a quantum that
; never fills.
(defun cz-select (articles from groups arts quantum fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (next served) (fn-cu-select articles from groups arts quantum fn-arena)
    (list next served)))
(bpr-lift cz-select 5)
(assert-event (equal (in-arena-cz-select *cz-arena* *cz-articles* 0 *cz-groups*
                                          *cz-view* 1)
                     (list 1 (list *cz-t1*))))
(assert-event (equal (in-arena-cz-select *cz-arena* *cz-articles* 1 *cz-groups*
                                          *cz-view* 1)
                     (list 2 (list *cz-t2*))))
(assert-event (equal (in-arena-cz-select *cz-arena* *cz-articles* 2 *cz-groups*
                                          *cz-view* 1)
                     (list 3 (list *cz-s1*))))
(assert-event (equal (in-arena-cz-select *cz-arena* *cz-articles* 3 *cz-groups*
                                          *cz-view* 1)
                     (list 3 nil)))

; The bound arm of `fn-cu-select-stays-within-the-quantum' (restated over
; rendered octets): quantum 90 admits exactly the two tiny records (45 +
; 45 = 90, the boundary is inclusive) and stops at the small one.
(assert-event (equal (in-arena-cz-select *cz-arena* *cz-articles* 0 *cz-groups*
                                          *cz-view* 90)
                     (list 2 (list *cz-t1* *cz-t2*))))
; The exception arm: at quantum 1 the 45-octet record exceeds it and the
; batch is that one record alone, whole, never cut.
(bpr-lift fn-cu-octets-of 1)
(assert-event (equal (in-arena-fn-cu-octets-of *cz-arena* (list *cz-t1*)) 45))
