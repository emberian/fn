; Teeth for books/body-chunks.lisp and books/body-chunks-span.lisp (lane
; chunked-body, B6).  Each keystone: a reachable positive witness asserting
; its antecedent and conclusion, and one hypothesis-removal witness per
; hypothesis (the retained ones hold, the omitted one fails, the conclusion
; fails).  The span append is run on the live buffer.

(in-package "ACL2")
(include-book "../../books/body-chunks-span")

(defun bcht-repeat (n x)
  (declare (xargs :guard (natp n)))
  (make-list n :initial-element x))

; A body of three lines: 700 octets, 3 octets, empty; each CR LF.
(defconst *bcht-lines* (list (bcht-repeat 700 97) (bcht-repeat 3 98) nil))
(defconst *bcht-octets* (fn-bch-join *bcht-lines*))
(defconst *bcht-store* (fn-bch-of *bcht-octets*))

; -----------------------------------------------------------------------------
; fn-bch-unpack-of-pack (hypothesis: an octet list).

(assert-event (and (fn-bch-octetsp '(0 255 13 10 0))
                   (equal (fn-bch-unpack (fn-bch-pack '(0 255 13 10 0))) '(0 255 13 10 0))))
; Trailing zero octets survive (the sentinel digit).
(assert-event (equal (fn-bch-unpack (fn-bch-pack '(1 0 0 0))) '(1 0 0 0)))
; Hypothesis removal: 300 is not an octet, and it does not come back.
(assert-event (and (not (fn-bch-octetsp '(300)))
                   (not (equal (fn-bch-unpack (fn-bch-pack '(300))) '(300)))))

; -----------------------------------------------------------------------------
; fn-bch-octets-of-push-list (hypotheses: a well-formed store, octets).

(assert-event (and (fn-bch-wfp *bcht-store*)
                   (fn-bch-octetsp *bcht-octets*)
                   (equal (fn-bch-octets *bcht-store*) *bcht-octets*)
                   (equal (fn-bch-count *bcht-store*) 1)
                   (equal (fn-bch-length *bcht-store*) (len *bcht-octets*))))
; Hypothesis removal (well-formed): a tail claiming 3 octets packing 1.
(defconst *bcht-bad* (fn-bch-make 0 3 (fn-bch-pack '(7)) nil))
(assert-event (and (not (fn-bch-wfp *bcht-bad*))
                   (not (equal (fn-bch-octets (fn-bch-push-list *bcht-bad* '(1 2)))
                               (append (fn-bch-octets *bcht-bad*) '(1 2))))))
; Hypothesis removal (octets): 256 is kept as 0.
(assert-event (and (fn-bch-wfp *bcht-store*)
                   (not (fn-bch-octetsp '(256)))
                   (not (equal (fn-bch-octets (fn-bch-push-list *bcht-store* '(256)))
                               (append (fn-bch-octets *bcht-store*) '(256))))))

; -----------------------------------------------------------------------------
; fn-bch-wf-is-of-octets (canonicity; hypothesis: well formed).

(assert-event (and (fn-bch-wfp *bcht-store*)
                   (equal (fn-bch-of (fn-bch-octets *bcht-store*)) *bcht-store*)))
; Hypothesis removal: a store with a short block holds the same octets as a
; canonical one but is not it.
(defconst *bcht-short-block* (fn-bch-make 1 0 1 (list (fn-bch-pack '(1 2 3)))))
(assert-event (and (not (fn-bch-wfp *bcht-short-block*))
                   (not (equal (fn-bch-of (fn-bch-octets *bcht-short-block*))
                               *bcht-short-block*))))

; -----------------------------------------------------------------------------
; fn-bch-lines-of-join (hypothesis: no line holds an LF) and the store's lines.

(assert-event (and (fn-bch-clean-linesp *bcht-lines*)
                   (equal (cdr (fn-bch-split-onto *bcht-octets* nil nil))
                          (revappend *bcht-lines* nil))
                   (equal (fn-bch-lines-rev *bcht-store*) (revappend *bcht-lines* nil))))
; A CR inside a line is kept; only the one before the LF goes.
(assert-event (equal (fn-bch-lines-rev (fn-bch-of (fn-bch-join '((13 13)))))
                     '((13 13))))
; Hypothesis removal: a line holding an LF splits in two.
(assert-event (and (not (fn-bch-clean-linesp '((1 10 2))))
                   (not (equal (cdr (fn-bch-split-onto (fn-bch-join '((1 10 2))) nil nil))
                               '((1 10 2))))))

; -----------------------------------------------------------------------------
; fn-bchs-push-span-is-push-list (no hypothesis), on the live buffer: spans
; crossing block boundaries, from a store with a partial tail, from an empty
; one, and from a store whose tail is malformed (the per-octet fallback).

(defun bcht-span-in (s xs i k fn-octets)
  (declare (xargs :stobjs fn-octets :mode :program))
  (let ((fn-octets (fn-octets-from-list xs fn-octets)))
    (mv (fn-bchs-push-span s i k fn-octets) fn-octets)))

(defun bcht-span (s xs i k)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets) (bcht-span-in s xs i k fn-octets)
      r)))

(defconst *bcht-buffer*
  (append (bcht-repeat 1100 120) '(13 10) (bcht-repeat 40 0) (bcht-repeat 30 255)))

(assert-event (equal (bcht-span (fn-bch-empty) *bcht-buffer* 0 (len *bcht-buffer*))
                     (fn-bch-push-list (fn-bch-empty) *bcht-buffer*)))
(assert-event (let ((s (fn-bch-of (bcht-repeat 300 7))))
                (equal (bcht-span s *bcht-buffer* 5 1160)
                       (fn-bch-push-list s (take 1155 (nthcdr 5 *bcht-buffer*))))))
(assert-event (equal (bcht-span *bcht-bad* *bcht-buffer* 0 9)
                     (fn-bch-push-list *bcht-bad* (take 9 *bcht-buffer*))))
(assert-event (let ((s (fn-bch-of (bcht-repeat 511 7))))
                (and (equal (fn-bch-tail-len s) 511)
                     (equal (bcht-span s *bcht-buffer* 0 1)
                            (fn-bch-push-list s (take 1 *bcht-buffer*)))
                     (equal (fn-bch-count (bcht-span s *bcht-buffer* 0 1)) 1))))
; The octets of the span append (the abstraction through the keystone).
(assert-event (let ((s (fn-bch-of (bcht-repeat 300 7))))
                (equal (fn-bch-octets (bcht-span s *bcht-buffer* 0 (len *bcht-buffer*)))
                       (append (bcht-repeat 300 7) *bcht-buffer*))))
