; fn: teeth for books/wire-span.lisp (REP-012, PRF-181).
;
; What this book is evidence FOR.  fn-wire-feed-span consumes a range of the
; octet buffer by span; its KEYSTONE fn-wire-feed-span-is-feed-bytes says the
; index scan (its :exec) equals feeding the range's bytes one at a time through
; fn-wire-feed-byte (its :logic), and fn-wire-span-fold-is-feed-proper says
; that byte feed is fn-wire-feed-proper over the slice.  So the span over
; [i, end) of the buffer is exactly the reference machine over those octets:
; the article it frames, the dot-unstuffing, the line and body limits and the
; refusals are the reference's, whatever the read boundaries.
;
; The witnesses run the executable path on a live local buffer, the way the
; host runs it, and cross two reads with a line split at the boundary and a
; dot-stuffed line.  The must-fails remove a guard hypothesis and show the
; keystone equality no longer holds.

(in-package "ACL2")
(include-book "../../books/wire-span")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it may reach is guard-verified.

(assert-event
 (equal (list (symbol-class 'fn-wire-feed-span (w state))
              (symbol-class 'fn-wire-span-fold (w state)))
        '(:common-lisp-compliant :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The article machine over a range: a dot-stuffed line and a line split across
; two reads.  The body bytes are "..hi\r\n.\r\n": the wire line "..hi"
; unstuffs to ".hi", and the "." line ends the body, so the article is the one
; line (46 104 105).

(defconst *wst-limit-line* 64)
(defconst *wst-limit-body* 4096)
(defconst *wst-article0*
  (fn-wire-result-state
   (fn-wire-begin-article
    (fn-wire-initial-state *wst-limit-line* *wst-limit-body*))))
(assert-event (equal (fn-wire-state-mode *wst-article0*) :article))

(defconst *wst-body* '(46 46 104 105 13 10 46 13 10))

; The reference over the whole list, from the same article state.
(defconst *wst-reference* (fn-wire-feed-proper *wst-article0* *wst-body*))

; One read: the span over the whole buffer equals the reference (state and
; events), and yields the article event whose body is the unstuffed line.
(defun wst-one-read (fn-octets)
  (declare (xargs :stobjs fn-octets))
  (let* ((fn-octets (fn-octets-from-list *wst-body* fn-octets))
         (r (fn-wire-feed-span *wst-article0* 0 (fn-octets-len fn-octets) fn-octets)))
    (mv (list (equal (fn-wsp-state r) (fn-wire-result-state *wst-reference*))
              (equal (fn-wsp-events r) (fn-wire-result-events *wst-reference*))
              (fn-wsp-events r)
              (fn-wsp-next r))
        fn-octets)))

(defun wst-one-read-value ()
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (wst-one-read fn-octets) v)))

(assert-event
 (equal (wst-one-read-value)
        (list t t (list (fn-wire-article-event (list (list 46 104 105)))) 9)))

; Two reads with the line split at the boundary: the "..hi\r\n" line is cut
; after "..h" (index 3), so the first span carries a partial line and the
; second resumes it.  Composing the two spans equals the one-read span, hence
; the reference: the read boundary does not change what is framed.
(defun wst-two-reads (fn-octets)
  (declare (xargs :stobjs fn-octets))
  (let* ((fn-octets (fn-octets-from-list *wst-body* fn-octets))
         (end (fn-octets-len fn-octets))
         (r1 (fn-wire-feed-span *wst-article0* 0 3 fn-octets))
         (r2 (fn-wire-feed-span (fn-wsp-state r1) (fn-wsp-next r1) end fn-octets)))
    (mv (list (equal (fn-wsp-state r2) (fn-wire-result-state *wst-reference*))
              (append (fn-wsp-events r1) (fn-wsp-events r2))
              (fn-wsp-next r1)
              (fn-wsp-next r2))
        fn-octets)))

(defun wst-two-reads-value ()
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (wst-two-reads fn-octets) v)))

(assert-event
 (equal (wst-two-reads-value)
        (list t
              (list (fn-wire-article-event (list (list 46 104 105))))
              3 9)))

; -----------------------------------------------------------------------------
; A line over the line limit closes the wire with :line-overlimit, at the same
; octet as the reference: the span carries the limit by subtraction, not by a
; recognizer.  Line limit 3, a line of four ordinary bytes.

(defconst *wst-tight*
  (fn-wire-result-state (fn-wire-begin-article (fn-wire-initial-state 3 4096))))
(defconst *wst-long-line* '(65 66 67 68 13 10))

(defun wst-overlimit (fn-octets)
  (declare (xargs :stobjs fn-octets))
  (let* ((fn-octets (fn-octets-from-list *wst-long-line* fn-octets))
         (r (fn-wire-feed-span *wst-tight* 0 (fn-octets-len fn-octets) fn-octets)))
    (mv (list (equal (fn-wire-state-mode (fn-wsp-state r)) :closed)
              (fn-wsp-events r))
        fn-octets)))

(defun wst-overlimit-value ()
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (wst-overlimit fn-octets) v)))

(assert-event
 (equal (wst-overlimit-value)
        (list t (list (fn-wire-reject-event :line-overlimit)))))

; The same input under the reference closes the same way: the span refusal is
; the reference refusal.
(assert-event
 (equal (fn-wire-state-mode
         (fn-wire-result-state (fn-wire-feed-proper *wst-tight* *wst-long-line*)))
        :closed))

; -----------------------------------------------------------------------------
; Teeth for the keystone fn-wire-feed-span-is-feed-bytes: one must-fail per
; guard hypothesis, showing the scan/fold equality fails without it.

; Without (fn-octets-p fn-octets): the scan reads cells the fold's byte model
; does not, so the two disagree on a non-octet "buffer".
(must-fail
 (defthm wst-keystone-needs-octets-p
   (implies (and (fn-wire-fast-statep wire-state)
                 (natp i) (natp end)
                 (<= end (fn-octets-len fn-octets)))
            (equal (fn-wire-span-scan wire-state i end fn-octets)
                   (fn-wire-span-fold wire-state i end fn-octets)))))

; Without (<= end (fn-octets-len fn-octets)): a range past the buffer's end is
; not decided by the scan the way the fold's guard requires.
(must-fail
 (defthm wst-keystone-needs-range-within-buffer
   (implies (and (fn-wire-fast-statep wire-state)
                 (fn-octets-p fn-octets)
                 (natp i) (natp end))
            (equal (fn-wire-span-scan wire-state i end fn-octets)
                   (fn-wire-span-fold wire-state i end fn-octets)))))

; Without (fn-wire-fast-statep wire-state): the scan's per-byte execution
; invariant is what makes it the fold; drop it and the equality is unproved.
(must-fail
 (defthm wst-keystone-needs-fast-statep
   (implies (and (fn-octets-p fn-octets)
                 (natp i) (natp end)
                 (<= end (fn-octets-len fn-octets)))
            (equal (fn-wire-span-scan wire-state i end fn-octets)
                   (fn-wire-span-fold wire-state i end fn-octets)))))
