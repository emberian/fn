; fn: the wire machine over a span of the octet buffer (D27; REP-012; PRF-181).
;
; The served read hands the wire machine one socket observation.  Until this
; book that observation was a list of octets consumed one cons at a time
; (books/wire.lisp fn-wire-feed-byte: a new eight-cell state per byte, the
; byte consed onto the reversed line, after a per-read coerce of the socket
; vector to a 512-element list), which is where a 32 KiB POST spent 59 percent
; of its CPU and 635 consed bytes per payload octet
; (planning/evidence/rep-wave-d-2026-09-25.md section 1.2).  Here the
; observation is a range [i, end) of the octet buffer (books/octets-stobj.lisp),
; filled once from the socket vector by the host, and the wire machine reads it
; in place: no octet of the read is a cons cell.
;
; fn-wire-feed-span is the fold of fn-wire-feed-byte over the range's bytes,
; read from the buffer by index (fn-octets-get), until the first byte that
; yields an event (fn-wire-span-fold).  Its correspondence is the KEYSTONE
; fn-wire-feed-span-is-feed-proper (through fn-wire-span-fold-is-feed-proper):
; the range's (state, events) is fn-wire-feed-proper over the slice
; (fn-oct-slice-list i next), the reference byte machine on exactly those
; octets.  The state the span leaves is the reference's (fn-wire-make-state:
; the partial line as line-rev, the body as its lines), so no theorem over
; fn-wire-statep or the served connection changes, and the big saving is at
; the served layer (books/served-span.lisp fn-scar-feed-span rebuilds the
; ten-field connection once per framed event, not once per byte).  Reducing
; the remaining per-byte wire-state rebuild to a per-line index scan (the next
; CRLF by fn-oct-line-end, the line limit by subtraction) is PKT-479.
;
; Called from books/served-span.lisp fn-scar-feed-span, which
; host/owner-host.lisp fn-owner-chunk-span reaches from
; host/native/owner.lisp fnn-owner-handle-chunk.

(in-package "ACL2")
(include-book "wire")
(include-book "octets-stobj")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The span result: (state events next), NEXT the index after the last byte
; fed.  Total selectors, as the wire's own records.

(defun fn-wsp-make (wire-state events next)
  (declare (xargs :guard t))
  (list wire-state events next))

(defun fn-wsp-state (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car x))

(defun fn-wsp-events (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr x)))

(defun fn-wsp-next (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr (fn-wire-ag-cdr x))))

(defthm fn-wsp-state-of-fn-wsp-make
  (equal (fn-wsp-state (fn-wsp-make wire-state events next)) wire-state))

(defthm fn-wsp-events-of-fn-wsp-make
  (equal (fn-wsp-events (fn-wsp-make wire-state events next)) events))

(defthm fn-wsp-next-of-fn-wsp-make
  (equal (fn-wsp-next (fn-wsp-make wire-state events next)) next))

(in-theory (disable (:d fn-wsp-make) (:d fn-wsp-state) (:d fn-wsp-events)
                    (:d fn-wsp-next)))

; -----------------------------------------------------------------------------
; The logical span step: the byte feed, one byte at a time, until the first
; byte that yields an event or the end of the range.

(defun fn-wire-span-fold (wire-state i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep wire-state)
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))
                  :verify-guards nil))
  (if (or (not (natp i)) (not (natp end)) (>= i end))
      (fn-wsp-make wire-state nil (nfix i))
    (let ((r (fn-wire-feed-byte wire-state (fn-octets-get i fn-octets))))
      (if (consp (fn-wire-result-events r))
          (fn-wsp-make (fn-wire-result-state r) (fn-wire-result-events r) (+ 1 i))
        (fn-wire-span-fold (fn-wire-result-state r) (+ 1 i) end fn-octets)))))

(defthm fn-wire-span-fold-preserves-fast-statep
  (implies (fn-wire-fast-statep wire-state)
           (fn-wire-fast-statep
            (fn-wsp-state (fn-wire-span-fold wire-state i end fn-octets))))
  :hints (("Goal" :induct (fn-wire-span-fold wire-state i end fn-octets)
           :in-theory (disable fn-wire-feed-byte fn-wire-fast-statep))))

(verify-guards fn-wire-span-fold
  :hints (("Goal" :in-theory (disable fn-wire-feed-byte fn-wire-fast-statep))))

(defthm fn-wire-span-fold-next-is-natural
  (natp (fn-wsp-next (fn-wire-span-fold wire-state i end fn-octets)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-wire-span-fold wire-state i end fn-octets)
           :in-theory (disable fn-wire-feed-byte))))

(defthm fn-wire-span-fold-next-bounds
  (implies (and (natp i) (natp end) (< i end))
           (and (< i (fn-wsp-next (fn-wire-span-fold wire-state i end fn-octets)))
                (<= (fn-wsp-next (fn-wire-span-fold wire-state i end fn-octets))
                    end)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-wire-span-fold wire-state i end fn-octets)
           :in-theory (disable fn-wire-feed-byte))))

(defthm fn-wire-span-fold-next-at-least
  (implies (natp i)
           (<= i (fn-wsp-next (fn-wire-span-fold wire-state i end fn-octets))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-wire-span-fold wire-state i end fn-octets)
           :in-theory (disable fn-wire-feed-byte))))

; The fold's (state, events) is the fixed-mode composition helper over the
; bytes it consumed: fn-wire-feed-proper on the slice [i, next).  With the
; fold stopping at the first event, every earlier byte contributed none.
(local
 (defthm fn-wire-span-slice-open
   (implies (and (natp i) (natp n) (< i n))
            (equal (fn-oct-slice-list i n fn-octets)
                   (cons (fn-octets-get i fn-octets)
                         (fn-oct-slice-list (1+ i) n fn-octets))))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-wire-feed-proper-closed-is-noop
   (implies (equal (fn-wire-state-mode wire-state) :closed)
            (equal (fn-wire-feed-proper wire-state octets)
                   (fn-wire-make-result wire-state nil)))
   :hints (("Goal" :in-theory (enable fn-wire-feed-proper)))))

(local
 (defthm fn-wire-span-feed-byte-without-event-keeps-open
   (implies (and (not (equal (fn-wire-state-mode wire-state) :closed))
                 (not (consp (fn-wire-result-events (fn-wire-feed-byte wire-state byte)))))
            (not (equal (fn-wire-state-mode
                         (fn-wire-result-state (fn-wire-feed-byte wire-state byte)))
                        :closed)))
   :hints (("Goal" :in-theory (enable fn-wire-feed-byte fn-wire-after-line fn-wire-close)))))

(local
 (defthm fn-wire-span-feed-byte-events-are-a-true-list
   (true-listp (fn-wire-result-events (fn-wire-feed-byte wire-state byte)))
   :hints (("Goal" :in-theory (enable fn-wire-feed-byte fn-wire-after-line fn-wire-close)))))

(local
 (defthm fn-wire-span-feed-proper-rebuilds
   (equal (fn-wire-make-result
           (fn-wire-result-state (fn-wire-feed-proper wire-state octets))
           (fn-wire-result-events (fn-wire-feed-proper wire-state octets)))
          (fn-wire-feed-proper wire-state octets))
   :hints (("Goal" :expand ((fn-wire-feed-proper wire-state octets))
            :in-theory (enable fn-wire-make-result fn-wire-result-state
                               fn-wire-result-events fn-wire-ag-car fn-wire-ag-cdr)))))

(defthm fn-wire-span-fold-is-feed-proper
  (implies (and (natp i) (natp end) (<= i end)
                (not (equal (fn-wire-state-mode wire-state) :closed)))
           (equal (fn-wire-feed-proper
                   wire-state
                   (fn-oct-slice-list
                    i (fn-wsp-next (fn-wire-span-fold wire-state i end fn-octets))
                    fn-octets))
                  (fn-wire-make-result
                   (fn-wsp-state (fn-wire-span-fold wire-state i end fn-octets))
                   (fn-wsp-events (fn-wire-span-fold wire-state i end fn-octets)))))
  :hints (("Goal" :induct (fn-wire-span-fold wire-state i end fn-octets)
           :in-theory (e/d (fn-wire-feed-proper)
                           (fn-wire-feed-byte fn-wire-fast-statep)))
          ("Subgoal *1/2" :in-theory (e/d (fn-wire-feed-proper fn-oct-slice-list)
                                          (fn-wire-feed-byte fn-wire-fast-statep)))))

; -----------------------------------------------------------------------------
; The host-called entry.  Its logic and its execution are both the byte fold
; over the buffer's range: no octet of the read is a cons cell (the socket
; vector is read in place by fn-octets-get), and books/served-span.lisp
; dispatches once per framed event rather than once per byte.  Its
; correspondence is fn-wire-span-fold-is-feed-proper above: the range's
; (state, events) is fn-wire-feed-proper over the slice, the reference byte
; machine on exactly those octets.  Removing the remaining per-byte wire-state
; rebuild (a per-line index scan) is PKT-479.

(defun fn-wire-feed-span (wire-state i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep wire-state)
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))))
  (fn-wire-span-fold wire-state i end fn-octets))

(defthm fn-wire-feed-span-preserves-fast-statep
  (implies (fn-wire-fast-statep wire-state)
           (fn-wire-fast-statep
            (fn-wsp-state (fn-wire-feed-span wire-state i end fn-octets)))))

(defthm fn-wire-feed-span-next-is-natural
  (natp (fn-wsp-next (fn-wire-feed-span wire-state i end fn-octets)))
  :rule-classes :type-prescription)

(defthm fn-wire-feed-span-next-bounds
  (implies (and (natp i) (natp end) (< i end))
           (and (< i (fn-wsp-next (fn-wire-feed-span wire-state i end fn-octets)))
                (<= (fn-wsp-next (fn-wire-feed-span wire-state i end fn-octets))
                    end)))
  :rule-classes :linear)

(defthm fn-wire-feed-span-is-feed-proper
  (implies (and (natp i) (natp end) (<= i end)
                (not (equal (fn-wire-state-mode wire-state) :closed)))
           (equal (fn-wire-feed-proper
                   wire-state
                   (fn-oct-slice-list
                    i (fn-wsp-next (fn-wire-feed-span wire-state i end fn-octets))
                    fn-octets))
                  (fn-wire-make-result
                   (fn-wsp-state (fn-wire-feed-span wire-state i end fn-octets))
                   (fn-wsp-events (fn-wire-feed-span wire-state i end fn-octets)))))
  :hints (("Goal" :use ((:instance fn-wire-span-fold-is-feed-proper)))))

(defthm fn-wire-feed-span-is-span-fold
  (equal (fn-wire-feed-span wire-state i end fn-octets)
         (fn-wire-span-fold wire-state i end fn-octets))
  :hints (("Goal" :in-theory (enable fn-wire-feed-span))))

(in-theory (disable fn-wire-feed-span))
