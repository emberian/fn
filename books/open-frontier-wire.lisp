; fn -- the open's events fold over WIRE events (row S1 item 4, lane
; limits-live-5).
;
; The open folds the next transaction id over the events it decodes, a chunk
; at a time, before it interns them (host/native/io.lisp
; fnn-recover-suffix-intern and fnn-recover-log, host/store-open-host.lisp,
; host/store-write-host.lisp).  That fold was a program-mode host function
; (fn-store-log-next-txid-of-events, host/store-host.lisp) reading
; fn-rcon-wire-event-txid; the frontier PRF-937 proves admits every replayed
; history (books/open-frontier.lisp fn-ofr-replay-ok-frontier-admits) folds
; fn-store-event-txid over the ROWS the replay reads.  This book is the fold
; the host now calls, and the two theorems that join it to the replay's:
;   fn-ofw-wire-next-is-the-rows-next (KEYSTONE): the fold over the wire
;     events is fn-ofr-events-next over the rows fn-intern-events makes of
;     them, for every keyring, generation and arena, whenever the intern
;     succeeds (books/store-intern.lisp fn-intern-events-keep-coordinates:
;     a row's txid is its wire event's);
;   fn-ofw-wire-next-of-append: the fold over a concatenation is the fold of
;     the second over the first's, so folding chunk by chunk is the fold over
;     the whole suffix.

(in-package "ACL2")
(include-book "open-frontier")
(include-book "records-concrete")
(include-book "store-intern")

(defun fn-ofw-wire-next (events acc)
  (declare (xargs :guard t))
  (if (consp events)
      (fn-ofw-wire-next
       (cdr events)
       (let ((txid (fn-rcon-wire-event-txid (car events))))
         (if (natp txid) (max (nfix acc) (+ 1 txid)) (nfix acc))))
    (nfix acc)))

; The fold both sides reduce to: over the coordinates' txids (the third of
; each (KIND SEQUENCE TXID GENERATION)).
(defun fn-ofw-coordinates-next (cs acc)
  (declare (xargs :guard t))
  (if (consp cs)
      (fn-ofw-coordinates-next
       (cdr cs)
       (let ((txid (and (consp (car cs)) (consp (cdar cs)) (consp (cddar cs))
                        (caddr (car cs)))))
         (if (natp txid) (max (nfix acc) (+ 1 txid)) (nfix acc))))
    (nfix acc)))

(defthm fn-ofw-wire-next-is-coordinates-next
  (equal (fn-ofw-wire-next events acc)
         (fn-ofw-coordinates-next (fn-wire-coordinates events) acc))
  :hints (("Goal" :induct (fn-ofw-wire-next events acc)
           :in-theory (e/d (fn-ofw-wire-next fn-ofw-coordinates-next
                            fn-wire-coordinates fn-rcon-wire-event-txid-is-wire-event-txid)
                           (fn-rcon-wire-event-txid fn-wire-event-txid
                            fn-wire-event-kind fn-wire-event-sequence
                            fn-wire-event-generation)))))

(defthm fn-ofw-rows-next-is-coordinates-next
  (equal (fn-ofr-events-next rows acc)
         (fn-ofw-coordinates-next (fn-row-coordinates rows) acc))
  :hints (("Goal" :induct (fn-ofr-events-next rows acc)
           :in-theory (e/d (fn-ofr-events-next fn-ofw-coordinates-next fn-row-coordinates)
                           (fn-store-event-txid fn-store-event-kind
                            fn-store-event-sequence fn-store-event-generation)))))

; KEYSTONE (row S1 item 4, PRF-976).  The host's events fold is the replay's
; frontier fold over the rows the intern makes of the same events.
(defthm fn-ofw-wire-next-is-the-rows-next
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                            :bad)))
           (equal (fn-ofw-wire-next ws acc)
                  (fn-ofr-events-next (mv-nth 0 (fn-intern-events ws keyring generation
                                                                  fn-arena))
                                      acc)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-intern-events-keep-coordinates))
           :in-theory (disable fn-intern-events fn-intern-events-keep-coordinates
                               fn-ofw-wire-next fn-ofr-events-next))))

(defthm fn-ofw-wire-next-of-append
  (equal (fn-ofw-wire-next (append a b) acc)
         (fn-ofw-wire-next b (fn-ofw-wire-next a acc)))
  :hints (("Goal" :induct (fn-ofw-wire-next a acc)
           :in-theory (e/d (fn-ofw-wire-next)
                           (fn-rcon-wire-event-txid fn-ofw-wire-next-is-coordinates-next)))))

(defthm fn-ofw-wire-next-natp
  (natp (fn-ofw-wire-next events acc))
  :rule-classes :type-prescription)

(defthm fn-ofw-wire-next-at-least
  (<= (nfix acc) (fn-ofw-wire-next events acc))
  :rule-classes :linear)

(in-theory (disable fn-ofw-wire-next fn-ofw-coordinates-next))
