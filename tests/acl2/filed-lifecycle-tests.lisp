; Witnesses and teeth for books/filed-lifecycle: the reclaim-aware history
; invariant FN-O1-FILES-INVP through the owner's lifecycle beyond the Store
; transitions (those are books/filed-history's, witnessed in
; filed-history-tests).  Every keystone has an instance with a RECLAIMED
; article (a tombstoned record, FN-RCLP-TOMBSTONED) among the history for
; which every hypothesis holds, the conclusion holds, and the old all-filed
; predicate FN-O1-RECORDS-FILEDP is NIL; the checked mutation (the conclusion
; with the tombstone disjunct dropped, OTF-FILES-FILED-ONLY-INVP) is false of
; it.  The teeth: an unfiled non-tombstone record (*otf-bad*, or the swapped
; record *p4-swap* that recovery accepts), a handle the release names, a
; composite whose stxa article is not its held article.
;
; Hypotheses the first statement draft carried, dropped because no instance
; has one failing alone with a false conclusion (the instances below are the
; evidence: each asserts the conclusion with the hypothesis failing):
;   K3: the interned row is not :bad; the prepare of :bad stages nothing.
;   K4: the rebuilt owner is not :fault; the swap over a fault is an empty Store.
;   K5a: the full replay is not :bad and the open is not :fault; a failed open
;        has no Store, and the empty Store is invariant.
;   K5b: the open is not :fault: likewise.
; K5b keeps (true-listp ws) and the intern of the whole journal not :bad, which
; the cited equality with the full recover needs.  The stobj recognizers
; (fn-arena-p) are true of every live arena; fn-sf-record-valuesp (K7) has no
; runtime removal witness: a catalog loaded from a non-record row is not a live
; fn-cat.
(in-package "ACL2")
(include-book "filed-history-tests")   ; *otf-good*, *otf-z*, *otf-bad*, the signed composites, the mixed Store
(include-book "filed-catalog-tests")   ; *p3-w0*, *p5-z1*, *p4-swap*, p4-open, p5-served-run
(include-book "arena-lift")
(include-book "must-fail-checked")

; --------------------------------------------------------------------------
; Fixtures: Stores holding a committed record, reserved again.
(defun fl-wire-n (n msgid payload groups)
  (fn-record-make n n n msgid payload groups (concatenate 'string "fl-pin-" msgid) "otf-content" "otf-release" 2 841000000))
; a Store with W0 as its one record (arena: W0 at handle 0)
(defun fl-one-store (w0 fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-hrt-events (list w0) nil 0 fn-arena)
    (mv (fn-sit-reserve (fn-sn-finish (fn-sn-test-publish (fn-sn-prepare *sn-reserved* (car rows))))) fn-arena)))
(defconst *fl-w1* (fl-wire-n 1 "<w2@b.example>" (otf-src "fn.test,fn.letters") '("fn.letters")))
(defconst *fl-z1* (fn-rclp-tombstoned *fl-w1*))
(defconst *fl-u1* (fl-wire-n 1 "<w2@b.example>" (otf-src "fn.letters") '("fn.test")))

(defconst *fl-sg1* (otf-sig-record 1 (otf-sig-src 1 "example,other")))
(defconst *fl-sz1* (fn-rclp-tombstoned *fl-sg1*))
(defconst *fl-sb1* (otf-sig-record 1 (otf-sig-src 1 "other")))
(defconst *fl-sg2* (otf-sig-record 2 (otf-sig-src 2 "example,other")))
(defconst *fl-sz2* (fn-rclp-tombstoned *fl-sg2*))
(defconst *fl-sb2* (otf-sig-record 2 (otf-sig-src 2 "other")))

; K6 has no hypothesis (positional in every instance above); fn-sf-record-valuesp has no
; runtime removal witness: a catalog loaded from a non-record row is not a live fn-cat.
