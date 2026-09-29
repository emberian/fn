; fn: a served read's cold line -- the per-line answer after a cold abort
; (lane composed-owner-3, 2026-09-29; row A4 of
; build/coordinator/COMPLETE-BEFORE-6.6.0.md, option (c), approved by the
; coordinator 2026-09-29 02:10Z).
;
; The served read span (host/owner-host.lisp fn-owner-chunk-span-at over
; fn-mca-read-span) is PURE over its stobjs: its owner is installed only
; after it returns.  So the host runs it with the extent realizer in a no-I/O
; mode (host/native/extent.lisp *fnn-extent-no-io*): a payload extent that
; is not in the realizer's cache aborts the span, nothing of it is kept, and
; the host re-runs the span ONE LINE at a time (the line's end is ACL2's,
; fn-oct-line-end; a wire may be split anywhere, fn-wire-scan-is-span-fold).
; Lines that are warm are answered in order, each its own read.  The line
; that faults cold has its extent read OUTSIDE the owner mutex; the read
; waits for it at most the declared dependency deadline
; (books/owner-time-bars.lisp fn-otb-dependency-step, `read-dependency-ms',
; 5,000 ms by default).  Answered in time, the line is re-run warm.  Past the
; deadline the line is answered by THIS book: RFC 3977 section 3.2.1's 403
; (fn-otb-unavailable-line: temporarily unavailable, never 430 or 423), the
; whole line consumed, and the session unchanged -- the connection's wire
; returns to the start of a line in command mode (its limits kept: a line
; that began in an earlier read is consumed with the rest of it) and nothing
; else of the owner moves.  The lines after it proceed as they would have:
; pipelined commands are answered in order (RFC 3977 section 3.5).
;
; Warm reads pay nothing for this: the per-line re-run happens only after a
; cold abort, and the no-I/O mode is a test of the realizer's cache that the
; warm path makes anyway (a hit is a hit).
;
; Command mode only.  A cold payload read is made only by a command
; (ARTICLE, HEAD, BODY): a line inside an article's body never reads one.
; A connection not in command mode is not this book's (the result is nil and
; the host treats it as a store fault).

(in-package "ACL2")

(include-book "owner-article-slots")
(include-book "owner-time-bars")

; The wire at the start of a line in command mode, with W's limits.
(defun fn-ocln-line-state (w)
  (declare (xargs :guard t))
  (fn-wire-make-state :command nil 0 nil nil 0
                      (fn-wire-state-line-limit w)
                      (fn-wire-state-body-limit w)))

(defun fn-ocln-conn-at-line (c)
  (declare (xargs :guard t))
  (update-nth 3 (fn-ocln-line-state (fn-own-conn-wire c)) (true-list-fix c)))

(defun fn-ocln-commandp (oc id)
  (declare (xargs :guard t))
  (let ((c (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
    (and c (eq (fn-wire-state-mode (fn-own-conn-wire c)) :command) t)))

(defun fn-ocln-owner-at-line (oc id)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (c (fn-own-find-conn id (fn-own-conns o))))
    (if c
        (fn-ocfg-with-owner
         oc (fn-own-set-conns o (fn-own-replace-conn (fn-ocln-conn-at-line c)
                                                     (fn-own-conns o))))
      oc)))

; The result over [I, END): the 403 reply, the span consumed, the owner OC
; with ID's wire at the start of a line.
(defun fn-ocln-unavailable-result (oc id i end since now limit)
  (declare (xargs :guard t))
  (fn-own-tls-make-result (nfix (- (nfix end) (nfix i)))
                          (list (fn-nntp-reply-effect
                                 (fn-otb-unavailable-line since now limit)))
                          (fn-ocln-owner-at-line oc id)
                          nil))

; THE FUNCTION THE HOST CALLS (host/owner-host.lisp
; fn-owner-unavailable-line-at, from host/native/owner.lisp
; fnn-owner-handle-chunk-read once fn-otb-dependency-step answers
; :unavailable): the line of the octet buffer that begins at I, answered 403.
(defun fn-ocln-unavailable-span (oc id i since now limit fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))))
  (if (fn-ocln-commandp oc id)
      (fn-ocln-unavailable-result oc id i (fn-oct-line-end i fn-octets)
                                  since now limit)
    nil))

; -----------------------------------------------------------------------------
; The theorems.

(local
 (defthm fn-ocln-line-end-bounds
   (implies (and (natp i) (<= i (fn-octets-len fn-octets)))
            (and (<= i (fn-oct-line-end i fn-octets))
                 (<= (fn-oct-line-end i fn-octets) (fn-octets-len fn-octets))
                 (implies (< i (fn-octets-len fn-octets))
                          (< i (fn-oct-line-end i fn-octets)))))
   :hints (("Goal" :in-theory (enable fn-oct-line-end)))
   :rule-classes :linear))

(local
 (defthm fn-ocln-line-end-natp
   (implies (and (natp i) (<= i (fn-octets-len fn-octets)))
            (natp (fn-oct-line-end i fn-octets)))
   :hints (("Goal" :in-theory (enable fn-oct-line-end)))
   :rule-classes :type-prescription))

(local
 (defthm fn-ocln-ocfg-owner-of-with-owner
   (equal (fn-ocfg-owner (fn-ocfg-with-owner oc o)) o)
   :hints (("Goal" :in-theory (enable fn-ocfg-owner fn-ocfg-with-owner fn-ocfg-make)))))

(local
 (defthm fn-ocln-conns-of-set-conns
   (equal (fn-own-conns (fn-own-set-conns o conns)) conns)
   :hints (("Goal" :in-theory (enable fn-own-conns fn-own-set-conns fn-own-make)))))

;; KEYSTONE (PRF-933).  A cold line past its deadline is answered by name
;; and leaves the session as it was.  For a connection in command mode, the
;; host's call answers the line that begins at I -- exactly the octets up to
;; and including its LF (fn-oct-line-end), at least one when any remain --
;; with ONE reply, time-bars' 403 (fn-otb-unavailable-line: not 430, not
;; 423), and the owner is OC with only that connection's wire returned to
;; the start of a line in command mode (its line and body limits kept).
;; Every other part of the connection -- its session, its pin, its
;; configuration -- and every other connection are OC's.
(defthm fn-ocln-a-cold-line-is-answered-unavailable
  (implies (and (natp i) (<= i (fn-octets-len fn-octets))
                (fn-ocln-commandp oc id))
           (let* ((r (fn-ocln-unavailable-span oc id i since now limit fn-octets))
                  (o (fn-ocfg-owner oc))
                  (c (fn-own-find-conn id (fn-own-conns o)))
                  (reply (cadr (car (fn-own-tls-result-effects r)))))
             (and (equal (fn-own-tls-result-consumed r)
                         (- (fn-oct-line-end i fn-octets) i))
                  (implies (< i (fn-octets-len fn-octets))
                           (< 0 (fn-own-tls-result-consumed r)))
                  (equal (fn-own-tls-result-effects r)
                         (list (list :reply (fn-otb-unavailable-line since now limit))))
                  (equal (list (nth 0 reply) (nth 1 reply) (nth 2 reply)) '(52 48 51))
                  (equal (fn-own-tls-result-owner r)
                         (fn-ocfg-with-owner
                          oc (fn-own-set-conns
                              o (fn-own-replace-conn
                                 (update-nth 3 (fn-ocln-line-state (fn-own-conn-wire c))
                                             (true-list-fix c))
                                 (fn-own-conns o)))))
                  (equal (fn-wire-state-mode (fn-ocln-line-state (fn-own-conn-wire c)))
                         :command))))
  :hints (("Goal" :use ((:instance fn-otb-a-late-page-is-unavailable-never-absent
                                   (completed nil)))
           :in-theory (e/d (fn-ocln-unavailable-span fn-ocln-unavailable-result
                            fn-ocln-owner-at-line fn-ocln-conn-at-line
                            fn-ocln-commandp fn-own-tls-make-result
                            fn-own-tls-result-consumed fn-own-tls-result-effects
                            fn-own-tls-result-owner fn-nntp-reply-effect)
                           (fn-otb-a-late-page-is-unavailable-never-absent
                            fn-oct-line-end fn-otb-unavailable-line)))))

;; A connection not in command mode is not answered here.
(defthm fn-ocln-unavailable-span-outside-command-mode-by-definition
  (implies (not (fn-ocln-commandp oc id))
           (equal (fn-ocln-unavailable-span oc id i since now limit fn-octets) nil))
  :hints (("Goal" :in-theory (enable fn-ocln-unavailable-span))))

(in-theory (disable fn-ocln-unavailable-span fn-ocln-unavailable-result
                    fn-ocln-owner-at-line fn-ocln-conn-at-line fn-ocln-commandp
                    fn-ocln-line-state))
