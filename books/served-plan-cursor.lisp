; served-plan-cursor.lisp -- the render plan's cursor quantum: the host's
; continuation of a served OVER/XOVER range (lane join-f2-13, 2026-09-29;
; PKT-733 (4), D27, PRF-1020).
;
; A served step answers an OVER/XOVER range with one CURSOR effect
; (:over-cursor CUR) (books/served-catalog.lisp fn-nntp-over-range-ovw), and
; books/served-plan.lisp's windows stop in front of it (fn-splan-fill's
; :cursor status; fn-splan-at-cursorp).  This book is the plan's step at a
; cursor and its proof:
;   fn-splan-cursor-step (p w fn-arena fn-cat) -> (mv status p')
;     the host-called subject (host/native/owner.lisp fnn-owner-cursor-step,
;     under the owner mutex, one quantum of the connection's scheduling
;     class; host/native/mux.lisp fnn-mux-flush re-feeds it): one
;     fn-ovw-step of the plan's first cursor (at most W numbers probed, at
;     most W NOV lines built: books/over-window.lisp
;     fn-ovw-step-window-at-most-w), whose octets replace the cursor as a
;     reply effect followed by the cursor that remains, if any.  Status :ok,
;     or :malformed (the plan's cursor is not one: a core fault, as a
;     non-octet reply effect is).
;   fn-splan-cursor-window (override) -> W: ACL2's quantum
;     (*fn-splan-cursor-window*); a developer image's FN_NATIVE_OVER_WINDOW
;     selector overrides it (the natives run the 100k range under a small
;     one).
; The list model of the host's loop (fnn-mux-flush: render a window off the
; mutex, write it; at a cursor run its quantum under the mutex; again):
;   fn-splan-cw-drain (p w wl n fn-arena fn-cat): N rounds, each a cursor
;     quantum (at a cursor) or a window of W octets.
;   fn-splan-cw-remaining (p wl fn-arena fn-cat): what the plan owes with
;     every cursor read as its run (fn-ovw-run: the steps until the cursor
;     is NIL).
; KEYSTONE fn-splan-cw-drain-is-the-expanded-reply: once the loop is done,
; the octets written are fn-served-reply-octets of the step's effects
; EXPANDED (books/served-catalog.lisp fn-ovw-expand: what the chain
; equations of books/served-catalog-chain.lisp are stated modulo), for every
; window size W, every quantum WL and however the socket paced the windows,
; provided every cursor in the effects is FRESH (fn-splan-fresh-cursorp: the
; arm's, its status line owed; fn-nntp-over-range-ovw-emits-a-fresh-cursor,
; and fn-ovw-cursor-effect has that one call site).  With
; fn-ovw-run-is-over-range-cat the loop writes, for an OVER/XOVER range,
; exactly the unbounded reader's reply (fn-splan-cw-octets-of-the-arm,
; fn-splan-cw-drain-of-the-arm-is-the-unbounded-reply).
; The plan's invariant between quanta (fn-splan-cw-okp: every cursor in it
; is a cursor) is established by the arm's effects and kept by both kinds
; of round; a quantum of such a plan is never :malformed
; (fn-splan-cursor-step-of-okp-is-ok).
; The pin: a cursor's V is the connection's pinned view (the session's,
; held while the plan lives: the mux steps no connection whose plan is
; live), so a commit or a withdrawal between quanta changes no quantum
; (over-window's fn-ovw-step-of-commit-pinned, -of-withdraw-pinned).  Seals
; and reclaim between quanta: over-window's header (open).

(in-package "ACL2")
(include-book "served-plan")
(include-book "over-window")

(local (in-theory (disable (tau-system))))

; served-plan repeats the cursor effect's shape (it sits below the catalog).
(defthm fn-splan-cursor-effectp-is-ovw-by-definition
  (equal (fn-splan-cursor-effectp e) (fn-ovw-cursor-effectp e))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ovw-cursor-effectp))))

; -----------------------------------------------------------------------------
; The quantum

; At most this many numbers probed, this many NOV lines built, per hold of
; the owner mutex (fn-ovw-step-window-at-most-w).
(defconst *fn-splan-cursor-window* 256)

(defun fn-splan-cursor-window (override)
  (declare (xargs :guard t))
  (if (posp override) override *fn-splan-cursor-window*))

(defthm fn-splan-cursor-window-posp
  (posp (fn-splan-cursor-window override))
  :rule-classes (:rewrite :type-prescription))

; -----------------------------------------------------------------------------
; The step: the first cursor of REST, stepped once

(defun fn-splan-rest-cursor-step (rest w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                  :verify-guards nil))
  (if (consp rest)
      (if (fn-splan-cursor-effectp (car rest))
          (let ((cur (car (cdr (car rest)))))
            (if (and (consp cur) (fn-ovw-cursorp cur))
                (mv-let (octets next)
                  (fn-ovw-step cur w fn-arena fn-cat)
                  (mv :ok (cons (fn-nntp-reply-effect octets)
                                (if next
                                    (cons (fn-ovw-cursor-effect next) (cdr rest))
                                  (cdr rest)))))
              (mv :malformed rest)))
        (mv-let (status rest2)
          (fn-splan-rest-cursor-step (cdr rest) w fn-arena fn-cat)
          (mv status (cons (car rest) rest2))))
    (mv :ok rest)))

(verify-guards fn-splan-rest-cursor-step
  :hints (("Goal" :in-theory (disable fn-ovw-step fn-ovw-cursorp))))

; The host-called subject.
(defun fn-splan-cursor-step (p w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)))
  (mv-let (status rest)
    (fn-splan-rest-cursor-step (fn-splan-rest p) w fn-arena fn-cat)
    (mv status (cons (fn-splan-cur p) rest))))

; -----------------------------------------------------------------------------
; The list model: what a plan owes with every cursor read as its run

(defun fn-splan-cw-octets (rest wl fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (consp rest)
      (append (if (fn-splan-cursor-effectp (car rest))
                  (fn-ovw-run (car (cdr (car rest))) wl fn-arena fn-cat)
                (fn-srb-effect-octets (car rest)))
              (fn-splan-cw-octets (cdr rest) wl fn-arena fn-cat))
    nil))

(defun fn-splan-cw-remaining (p wl fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (append (fn-splan-cur p) (fn-splan-cw-octets (fn-splan-rest p) wl fn-arena fn-cat)))

; N rounds of the host's loop: a quantum at a cursor, else a window of W.
(defun fn-splan-cw-drain (p w wl n fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil :measure (nfix n)))
  (if (zp n)
      (mv :ok nil p)
    (if (fn-splan-at-cursorp p)
        (mv-let (status p2)
          (fn-splan-cursor-step p wl fn-arena fn-cat)
          (if (equal status :ok)
              (fn-splan-cw-drain p2 w wl (- n 1) fn-arena fn-cat)
            (mv status nil p)))
      (mv-let (status octets p2)
        (fn-splan-take (fn-splan-cur p) (fn-splan-rest p) w)
        (if (equal status :ok)
            (mv-let (status2 more p3)
              (fn-splan-cw-drain p2 w wl (- n 1) fn-arena fn-cat)
              (mv status2 (append octets more) p3))
          (mv status octets p2))))))

; =============================================================================
; Theorems

(local
 (defthm fn-splan-cw-append-assoc
   (equal (append (append x y) z) (append x (append y z)))))

(local
 (defthm fn-splan-cw-reply-octets-step
   (equal (fn-served-reply-octets (cons e effects))
          (append (fn-srb-effect-octets e) (fn-served-reply-octets effects)))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets)))))

(local
 (defthm fn-splan-cw-effect-octets-of-reply-effect
   (equal (fn-srb-effect-octets (fn-nntp-reply-effect octets)) octets)
   :hints (("Goal" :in-theory (enable fn-nntp-reply-effect)))))

(local
 (defthm fn-splan-cw-cursor-effectp-of-reply-effect
   (not (fn-splan-cursor-effectp (fn-nntp-reply-effect octets)))
   :hints (("Goal" :in-theory (enable fn-nntp-reply-effect)))))

(local
 (defthm fn-splan-cw-cursor-effect-shape
   (and (fn-splan-cursor-effectp (fn-ovw-cursor-effect cur))
        (equal (car (cdr (fn-ovw-cursor-effect cur))) cur))
   :hints (("Goal" :in-theory (enable fn-ovw-cursor-effect)))))

; A window followed by what its continuation owes is what the plan owed
; (the cursors read as their runs); a window stops in front of a cursor.
(defthm fn-splan-take-is-a-cw-prefix
  (equal (append (mv-nth 1 (fn-splan-take cur rest k))
                 (fn-splan-cur (mv-nth 2 (fn-splan-take cur rest k)))
                 (fn-splan-cw-octets (fn-splan-rest (mv-nth 2 (fn-splan-take cur rest k)))
                                     wl fn-arena fn-cat))
         (append cur (fn-splan-cw-octets rest wl fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-splan-take cur rest k)
           :in-theory (e/d (fn-splan-take) (fn-ovw-run)))))

; A quantum keeps what the plan owes: the cursor's run is its step's octets
; followed by the run of the cursor that remains (fn-ovw-run unfolds).
(defthm fn-splan-rest-cursor-step-keeps-cw-octets
  (implies (equal (mv-nth 0 (fn-splan-rest-cursor-step rest wl fn-arena fn-cat)) :ok)
           (equal (fn-splan-cw-octets (mv-nth 1 (fn-splan-rest-cursor-step rest wl fn-arena fn-cat))
                                      wl fn-arena fn-cat)
                  (fn-splan-cw-octets rest wl fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-splan-rest-cursor-step rest wl fn-arena fn-cat)
           :in-theory (disable fn-ovw-step fn-ovw-cursorp fn-ovw-run)
           :expand ((fn-ovw-run (car (cdr (car rest))) wl fn-arena fn-cat)))))

(defthm fn-splan-cursor-step-keeps-cw-remaining
  (implies (equal (mv-nth 0 (fn-splan-cursor-step p wl fn-arena fn-cat)) :ok)
           (equal (fn-splan-cw-remaining (mv-nth 1 (fn-splan-cursor-step p wl fn-arena fn-cat))
                                         wl fn-arena fn-cat)
                  (fn-splan-cw-remaining p wl fn-arena fn-cat)))
  :hints (("Goal" :in-theory (disable fn-splan-rest-cursor-step))))

(defthm fn-splan-cw-drain-is-a-prefix
  (equal (append (mv-nth 1 (fn-splan-cw-drain p w wl n fn-arena fn-cat))
                 (fn-splan-cw-remaining (mv-nth 2 (fn-splan-cw-drain p w wl n fn-arena fn-cat))
                                        wl fn-arena fn-cat))
         (fn-splan-cw-remaining p wl fn-arena fn-cat))
  :hints (("Goal" :induct (fn-splan-cw-drain p w wl n fn-arena fn-cat)
           :in-theory (disable fn-splan-take fn-splan-cursor-step fn-splan-cur fn-splan-rest
                               fn-splan-at-cursorp fn-ovw-run))))

(defthm fn-splan-cw-drain-octets-true-listp
  (true-listp (mv-nth 1 (fn-splan-cw-drain p w wl n fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-splan-cw-drain p w wl n fn-arena fn-cat)
           :in-theory (disable fn-splan-take fn-splan-cursor-step fn-ovw-run))))

(local
 (defthm fn-splan-cw-rest-donep-owes-nothing
   (implies (fn-splan-rest-donep rest)
            (equal (fn-splan-cw-octets rest wl fn-arena fn-cat) nil))
   :hints (("Goal" :in-theory (disable fn-ovw-run)))))

(defthm fn-splan-donep-implies-cw-nothing-remains
  (implies (fn-splan-donep p)
           (equal (fn-splan-cw-remaining p wl fn-arena fn-cat) nil)))

(defthm fn-splan-of-effects-cw-remaining
  (equal (fn-splan-cw-remaining (fn-splan-of-effects effects) wl fn-arena fn-cat)
         (fn-splan-cw-octets effects wl fn-arena fn-cat)))

; -----------------------------------------------------------------------------
; Fresh cursors: the arm's (its status line owed) read as their runs are
; what the expansion says they stand for.

(defun fn-splan-fresh-cursorp (cur)
  (declare (xargs :guard t))
  (and (consp cur) (true-listp cur)
       (equal cur (fn-ovw-cursor (nth 0 cur) (nth 1 cur) (nth 2 cur) (nth 3 cur) (nth 4 cur) t))
       (natp (nth 1 cur)) (natp (nth 2 cur)) (natp (nth 3 cur))))

(defun fn-splan-fresh-effectsp (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (and (or (not (fn-splan-cursor-effectp (car effects)))
               (fn-splan-fresh-cursorp (car (cdr (car effects)))))
           (fn-splan-fresh-effectsp (cdr effects)))
    t))

(defthm fn-splan-fresh-run-is-cursor-octets
  (implies (fn-splan-fresh-cursorp cur)
           (equal (fn-ovw-run cur wl fn-arena fn-cat)
                  (fn-ovw-cursor-octets cur fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ovw-run-is-reply
                            (group (nth 0 cur)) (k (nth 1 cur)) (top (nth 2 cur))
                            (v (nth 3 cur)) (legacyp (nth 4 cur)) (owedp t) (w wl)))
           :in-theory (e/d (fn-ovw-cursor-octets)
                           (fn-ovw-run fn-ovw-run-is-reply fn-ovw-lines fn-ovw-reply)))))

(defthm fn-splan-cw-octets-is-the-expanded-reply
  (implies (fn-splan-fresh-effectsp effects)
           (equal (fn-splan-cw-octets effects wl fn-arena fn-cat)
                  (fn-served-reply-octets (fn-ovw-expand effects fn-arena fn-cat))))
  :hints (("Goal" :induct (fn-splan-fresh-effectsp effects)
           :in-theory (e/d (fn-ovw-expand fn-ovw-cursor-effectp)
                           (fn-ovw-run fn-ovw-cursor-octets fn-splan-fresh-cursorp)))))

; KEYSTONE.  Whatever the window size W, the quantum WL and the N rounds
; the socket paced, once the plan is done the loop wrote the reply the
; served machine decided, with every cursor expanded.
(defthm fn-splan-cw-drain-is-the-expanded-reply
  (implies (and (fn-splan-fresh-effectsp effects)
                (fn-splan-donep
                 (mv-nth 2 (fn-splan-cw-drain (fn-splan-of-effects effects) w wl n fn-arena fn-cat))))
           (equal (mv-nth 1 (fn-splan-cw-drain (fn-splan-of-effects effects) w wl n fn-arena fn-cat))
                  (fn-served-reply-octets (fn-ovw-expand effects fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-splan-cw-drain fn-splan-cw-remaining fn-splan-donep
                               fn-splan-of-effects fn-splan-cw-drain-is-a-prefix
                               fn-splan-donep-implies-cw-nothing-remains
                               fn-splan-of-effects-cw-remaining fn-splan-cw-octets
                               fn-splan-fresh-effectsp)
           :use ((:instance fn-splan-cw-drain-is-a-prefix (p (fn-splan-of-effects effects)))
                 (:instance fn-splan-donep-implies-cw-nothing-remains
                            (p (mv-nth 2 (fn-splan-cw-drain (fn-splan-of-effects effects)
                                                            w wl n fn-arena fn-cat))))
                 (:instance fn-splan-cw-drain-octets-true-listp (p (fn-splan-of-effects effects)))
                 (:instance fn-splan-of-effects-cw-remaining)
                 (:instance fn-splan-cw-octets-is-the-expanded-reply)))))

; -----------------------------------------------------------------------------
; The arm: its one cursor is fresh, and the loop writes the unbounded
; reader's reply.

(defthm fn-nntp-over-range-ovw-emits-a-fresh-cursor
  (implies (natp v)
           (fn-splan-fresh-effectsp (cdr (fn-nntp-over-range-ovw session v token legacyp fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-ovw fn-ovw-start fn-ovw-cursor
                                   fn-ovw-cursor-effect fn-nntp-make-result fn-nntp-reply-effect)
                                  (fn-nntp-parse-range fn-cat-group-next fn-ovw-status)))))

(local
 (defthm fn-splan-cw-reply-octets-of-one-listp
   (implies (true-listp x)
            (equal (fn-served-reply-octets (list (fn-nntp-reply-effect x))) x))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets fn-nntp-reply-effect)))))

(local
 (defthm fn-splan-cw-reply-octets-true-listp
   (true-listp (fn-served-reply-octets effects))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets)))))

(defthm fn-splan-cw-octets-of-the-arm
  (implies (natp v)
           (equal (fn-splan-cw-octets (cdr (fn-nntp-over-range-ovw session v token legacyp fn-cat))
                                      wl fn-arena fn-cat)
                  (fn-served-reply-octets
                   (cdr (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-splan-cw-octets-is-the-expanded-reply
                                        fn-nntp-over-range-ovw-emits-a-fresh-cursor
                                        fn-ovw-cursor-effect-expands-to-run
                                        fn-ovw-run-is-over-range-cat
                                        fn-splan-cw-reply-octets-of-one-listp
                                        fn-splan-cw-reply-octets-true-listp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-ovw-cursor-effect-expands-to-run (w wl))
                 (:instance fn-ovw-run-is-over-range-cat (w wl))))))

(defthm fn-splan-cw-drain-of-the-arm-is-the-unbounded-reply
  (implies (and (natp v)
                (fn-splan-donep
                 (mv-nth 2 (fn-splan-cw-drain
                            (fn-splan-of-effects
                             (cdr (fn-nntp-over-range-ovw session v token legacyp fn-cat)))
                            w wl n fn-arena fn-cat))))
           (equal (mv-nth 1 (fn-splan-cw-drain
                             (fn-splan-of-effects
                              (cdr (fn-nntp-over-range-ovw session v token legacyp fn-cat)))
                             w wl n fn-arena fn-cat))
                  (fn-served-reply-octets
                   (cdr (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-splan-cw-drain-is-the-expanded-reply
                                        fn-nntp-over-range-ovw-emits-a-fresh-cursor
                                        fn-splan-cw-octets-is-the-expanded-reply
                                        fn-splan-cw-octets-of-the-arm)
                                      (theory 'minimal-theory))
           :use ((:instance fn-splan-cw-drain-is-the-expanded-reply
                            (effects (cdr (fn-nntp-over-range-ovw session v token legacyp fn-cat))))
                 (:instance fn-splan-cw-octets-is-the-expanded-reply
                            (effects (cdr (fn-nntp-over-range-ovw session v token legacyp fn-cat))))))))

; -----------------------------------------------------------------------------
; The plan's invariant between quanta: every cursor in it is a cursor.
; Established by the arm's effects, kept by both kinds of round; a quantum
; of such a plan is never :malformed.

(defun fn-splan-cw-rest-okp (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (and (or (not (fn-splan-cursor-effectp (car rest)))
               (and (consp (car (cdr (car rest))))
                    (fn-ovw-cursorp (car (cdr (car rest))))))
           (fn-splan-cw-rest-okp (cdr rest)))
    t))

(defun fn-splan-cw-okp (p)
  (declare (xargs :guard t))
  (fn-splan-cw-rest-okp (fn-splan-rest p)))

(defthm fn-splan-fresh-effectsp-is-cw-okp
  (implies (fn-splan-fresh-effectsp effects)
           (fn-splan-cw-okp (fn-splan-of-effects effects)))
  :hints (("Goal" :in-theory (enable fn-ovw-cursor fn-ovw-cursorp))))

(local
 (defthm fn-splan-cw-step-next-is-consp
   (implies (mv-nth 1 (fn-ovw-step cur w fn-arena fn-cat))
            (consp (mv-nth 1 (fn-ovw-step cur w fn-arena fn-cat))))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovw-cursor)
                                   (fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))))))

(defthm fn-splan-rest-cursor-step-of-okp
  (implies (fn-splan-cw-rest-okp rest)
           (and (equal (mv-nth 0 (fn-splan-rest-cursor-step rest wl fn-arena fn-cat)) :ok)
                (fn-splan-cw-rest-okp (mv-nth 1 (fn-splan-rest-cursor-step rest wl fn-arena fn-cat)))))
  :hints (("Goal" :induct (fn-splan-rest-cursor-step rest wl fn-arena fn-cat)
           :in-theory (disable fn-ovw-step fn-ovw-cursorp))))

(defthm fn-splan-cursor-step-of-okp-is-ok
  (implies (fn-splan-cw-okp p)
           (and (equal (mv-nth 0 (fn-splan-cursor-step p wl fn-arena fn-cat)) :ok)
                (fn-splan-cw-okp (mv-nth 1 (fn-splan-cursor-step p wl fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (disable fn-splan-rest-cursor-step))))

(defthm fn-splan-take-keeps-cw-okp
  (implies (fn-splan-cw-rest-okp rest)
           (fn-splan-cw-rest-okp (fn-splan-rest (mv-nth 2 (fn-splan-take cur rest k)))))
  :hints (("Goal" :induct (fn-splan-take cur rest k)
           :in-theory (e/d (fn-splan-take) (fn-ovw-cursorp)))))

(in-theory (disable fn-splan-cursor-window fn-splan-rest-cursor-step fn-splan-cursor-step
                    fn-splan-cw-octets fn-splan-cw-remaining fn-splan-cw-drain
                    fn-splan-fresh-cursorp fn-splan-fresh-effectsp
                    fn-splan-cw-rest-okp fn-splan-cw-okp))
