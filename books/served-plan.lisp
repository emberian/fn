; fn: a served step's reply as an immutable RENDER PLAN, pulled in windows off
; the owner mutex (wave 5, lane owner-scheduler, 2026-09-26; D27; HST-023;
; PRF-248; gpt-6's consolidation review section 7: "immutable read/render
; plans produced against pinned views, and I/O execution that consumes those
; plans").
;
; A served step answers with EFFECTS (books/served.lisp); its reply is
; `fn-served-reply-octets' of them.  Until this book the octets were written
; into the live octet buffer UNDER the owner mutex (books/served-reply-buffer
; fn-served-reply-to-buffer, PRF-192) and copied out before the mutex was
; released: a 3 MiB ARTICLE held every other connection for the whole walk.
;
; The effects are an immutable ACL2 value whose reply octets are pointers into
; the connection's pinned archive; nothing mutates them after the step.  So
; the step's result IS the render plan: `fn-splan-of-effects' wraps it, and
; the I/O thread renders it AFTER the mutex is released, into its own buffer
; (never the live `fn-octets'), at most W octets per call
; (`fn-splan-window'), writing each window to the socket before it asks for
; the next.  A plan is (CUR . REST): CUR the octets left of the reply effect
; being rendered, REST the effects not yet started.
;
;   fn-splan-of-effects (effects) -> plan
;   fn-splan-window     (plan w fn-octets) -> (mv status plan' fn-octets)
;                        status :ok, or :malformed (a reply effect that is not
;                        octets: the host faults, as it faulted on a non-octet
;                        reply before)
;   fn-splan-donep      (plan) -> whether nothing remains
;
; The keystones (PRF-248):
;   fn-splan-window-is-a-prefix-of-the-reply: the window's octets (the
;     buffer's range [0, len)) followed by what the continuation still owes
;     are exactly what the plan owed, and the window is at most W octets
;     (both unconditional: a window that meets a non-octet stops in front of
;     it and leaves it in the continuation); under :ok a window of a plan
;     that is not done writes at least one octet (the loop progresses).
;   fn-splan-windows-are-the-reply: over the list model of the same loop, the
;     concatenation of the windows of a plan built from EFFECTS, once the
;     plan is done, is `fn-served-reply-octets' of EFFECTS: the bytes the I/O
;     thread writes are the bytes the served machine decided, whatever W and
;     however the socket paced the windows.
; The host line: host/native/owner.lisp fnn-owner-render-next calls
; fn-splan-window with the connection's render buffer; fnn-owner-write-plan
; loops it until fn-splan-donep.

(in-package "ACL2")
(include-book "served-reply-buffer")

; -----------------------------------------------------------------------------
; The plan

(defun fn-splan-of-effects (effects)
  (declare (xargs :guard t))
  (cons nil effects))

(defun fn-splan-cur (p)
  (declare (xargs :guard t))
  (if (consp p) (car p) nil))

(defun fn-splan-rest (p)
  (declare (xargs :guard t))
  (if (consp p) (cdr p) nil))

(defthm fn-splan-cur-of-cons
  (equal (fn-splan-cur (cons a b)) a))

(defthm fn-splan-rest-of-cons
  (equal (fn-splan-rest (cons a b)) b))

; What the plan still owes (the specification; not executed by the host).
(defun fn-splan-remaining (p)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-splan-cur p) (fn-served-reply-octets (fn-splan-rest p))))

(defun fn-splan-rest-donep (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (and (atom (fn-srb-effect-octets (car rest)))
           (fn-splan-rest-donep (cdr rest)))
    t))

(defun fn-splan-donep (p)
  (declare (xargs :guard t))
  (and (atom (fn-splan-cur p))
       (fn-splan-rest-donep (fn-splan-rest p))))

; The next window's size, ACL2's decision for the host (host/native/owner.lisp
; fnn-owner-render-next asks it before every fn-splan-window): the remaining
; octets of the effect the window starts in.  A materialized effect (an octet
; list the arm built inside the step) is rendered whole, because holding its
; list while the socket drains costs sixteen octets per octet where the
; rendered vector costs one; a fixed window bounds a window only over an
; effect that points into the pinned view (the design's section 3.3; no such
; kind yet).  Zero exactly when the plan is done, so the host's loop
; progresses (fn-splan-window-size-is-positive-until-done with the prefix
; keystone's progress conjunct).
(defun fn-splan-rest-head-len (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (if (consp (fn-srb-effect-octets (car rest)))
          (len (fn-srb-effect-octets (car rest)))
        (fn-splan-rest-head-len (cdr rest)))
    0))

(defun fn-splan-window-size (p)
  (declare (xargs :guard t))
  (if (consp (fn-splan-cur p))
      (len (fn-splan-cur p))
    (fn-splan-rest-head-len (fn-splan-rest p))))

(local
 (defthm fn-splan-rest-head-len-positive-iff-not-done
   (iff (posp (fn-splan-rest-head-len rest))
        (not (fn-splan-rest-donep rest)))))

(local
 (defthm fn-splan-len-posp-of-consp
   (implies (consp x) (posp (len x)))
   :hints (("Goal" :expand ((len x))))))

(defthm fn-splan-window-size-is-positive-until-done
  (iff (posp (fn-splan-window-size p))
       (not (fn-splan-donep p)))
  :hints (("Goal" :in-theory (disable posp fn-splan-rest-donep fn-splan-rest-head-len)
           :use ((:instance fn-splan-rest-head-len-positive-iff-not-done
                            (rest (fn-splan-rest p)))
                 (:instance fn-splan-len-posp-of-consp (x (fn-splan-cur p)))))))

; -----------------------------------------------------------------------------
; One window into the buffer: up to K octets appended at the fill point.

(defun fn-splan-fill (cur rest k fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (natp k)
                  :measure (+ (acl2-count cur) (acl2-count rest))))
  (cond ((zp k) (mv :ok (cons cur rest) fn-octets))
        ((consp cur)
         (if (fn-cbor-octetp (car cur))
             (let ((fn-octets (fn-octets-append-octet (car cur) fn-octets)))
               (fn-splan-fill (cdr cur) rest (- k 1) fn-octets))
           (mv :malformed (cons cur rest) fn-octets)))
        ((consp rest)
         (fn-splan-fill (fn-srb-effect-octets (car rest)) (cdr rest) k fn-octets))
        (t (mv :ok (cons nil nil) fn-octets))))

; The host-called subject: clear the buffer, then one window.
(defun fn-splan-window (p w fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp w)))
  (let ((fn-octets (fn-octets-clear fn-octets)))
    (fn-splan-fill (fn-splan-cur p) (fn-splan-rest p) w fn-octets)))

; -----------------------------------------------------------------------------
; The list model of the same loop: (mv status octets plan').

(defun fn-splan-take (cur rest k)
  (declare (xargs :guard (natp k)
                  :measure (+ (acl2-count cur) (acl2-count rest))))
  (cond ((zp k) (mv :ok nil (cons cur rest)))
        ((consp cur)
         (if (fn-cbor-octetp (car cur))
             (mv-let (status octets p)
               (fn-splan-take (cdr cur) rest (- k 1))
               (mv status (cons (car cur) octets) p))
           (mv :malformed nil (cons cur rest))))
        ((consp rest)
         (fn-splan-take (fn-srb-effect-octets (car rest)) (cdr rest) k))
        (t (mv :ok nil (cons nil nil)))))

; N windows of W, concatenated.
(defun fn-splan-drain (p w n)
  (declare (xargs :guard (and (natp w) (natp n)) :measure (nfix n)))
  (if (zp n)
      (mv :ok nil p)
    (mv-let (status octets p2)
      (fn-splan-take (fn-splan-cur p) (fn-splan-rest p) w)
      (if (equal status :ok)
          (mv-let (status2 more p3)
            (fn-splan-drain p2 w (- n 1))
            (mv status2 (append octets more) p3))
        (mv status octets p2)))))

; =============================================================================
; Theorems

(local (in-theory (disable fn-cbor-octetp)))

(local
 (defthm fn-splan-reply-octets-step
   (equal (fn-served-reply-octets (cons e effects))
          (append (fn-srb-effect-octets e) (fn-served-reply-octets effects)))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets)))))

(local
 (defthm fn-splan-append-assoc
   (equal (append (append x y) z) (append x (append y z)))))

; The stobj loop is the list loop: same status, same continuation, and the
; buffer's value is what it held followed by the window's octets.
(defthm fn-splan-fill-is-take
  (and (equal (mv-nth 0 (fn-splan-fill cur rest k fn-octets))
              (mv-nth 0 (fn-splan-take cur rest k)))
       (equal (mv-nth 1 (fn-splan-fill cur rest k fn-octets))
              (mv-nth 2 (fn-splan-take cur rest k))))
  :hints (("Goal" :induct (fn-splan-fill cur rest k fn-octets))))

(defthm fn-splan-fill-buffer-is-take-octets
  (implies (true-listp fn-octets)
           (equal (mv-nth 2 (fn-splan-fill cur rest k fn-octets))
                  (append fn-octets (mv-nth 1 (fn-splan-take cur rest k)))))
  :hints (("Goal" :induct (fn-splan-fill cur rest k fn-octets))))

(local
 (defthm fn-splan-take-of-len
   (implies (true-listp x) (equal (take (len x) x) x))))

(defthm fn-splan-take-octets-are-octets
  (and (true-listp (mv-nth 1 (fn-splan-take cur rest k)))
       (fn-cbor-octet-listp (mv-nth 1 (fn-splan-take cur rest k))))
  :hints (("Goal" :induct (fn-splan-take cur rest k))))

(defthm fn-splan-take-at-most-k
  (<= (len (mv-nth 1 (fn-splan-take cur rest k))) (nfix k))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-splan-take cur rest k))))

; The window followed by what the continuation owes is what the plan owed.
(defthm fn-splan-take-is-a-prefix
  ; Unconditional: a window that stops at a non-octet leaves it, and
  ; everything after it, in the continuation.  Stated in the plan's
  ; accessor vocabulary (what `fn-splan-remaining' of the continuation
  ; unfolds to), so the keystones below match it with the accessors closed.
  (equal (append (mv-nth 1 (fn-splan-take cur rest k))
                 (fn-splan-cur (mv-nth 2 (fn-splan-take cur rest k)))
                 (fn-served-reply-octets (fn-splan-rest (mv-nth 2 (fn-splan-take cur rest k)))))
         (append cur (fn-served-reply-octets rest)))
  :hints (("Goal" :induct (fn-splan-take cur rest k))))

; A window of a plan that owes something writes something.
(defthm fn-splan-take-progresses
  (implies (and (posp k)
                (equal (mv-nth 0 (fn-splan-take cur rest k)) :ok)
                (consp (append cur (fn-served-reply-octets rest))))
           (consp (mv-nth 1 (fn-splan-take cur rest k))))
  :hints (("Goal" :induct (fn-splan-take cur rest k))))

(local
 (defthm fn-splan-rest-donep-iff
   (iff (fn-splan-rest-donep rest)
        (not (consp (fn-served-reply-octets rest))))
))

(defthm fn-splan-donep-iff-nothing-remains
  (iff (fn-splan-donep p) (not (consp (fn-splan-remaining p)))))

(defthm fn-splan-of-effects-remaining
  (equal (fn-splan-remaining (fn-splan-of-effects effects))
         (fn-served-reply-octets effects)))

; A window of no size writes nothing and moves nothing.
(defthm fn-splan-take-of-no-window
  (implies (not (posp k))
           (equal (fn-splan-take cur rest k) (list :ok nil (cons cur rest))))
  :hints (("Goal" :in-theory (enable fn-splan-take))))

; The continuation of a window is a plan (a cons), whatever the status.
(defthm fn-splan-take-continuation-is-a-plan
  (consp (mv-nth 2 (fn-splan-take cur rest k)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-splan-take cur rest k) :in-theory (enable fn-splan-take))))

(local
 (defthm fn-splan-len-zero-is-atom
   (equal (equal (len x) 0) (atom x))))

; -----------------------------------------------------------------------------
; KEYSTONE 1: one window, on the buffer the host writes from.

(defthm fn-splan-window-is-a-prefix-of-the-reply
  (let* ((r (fn-splan-window p w fn-octets))
         (status (mv-nth 0 r))
         (p2 (mv-nth 1 r))
         (buf (mv-nth 2 r)))
    (and (<= (fn-octets-len buf) (nfix w))
         (equal (append (fn-oct-slice-list 0 (fn-octets-len buf) buf)
                        (fn-splan-remaining p2))
                (fn-splan-remaining p))
         (implies (and (equal status :ok) (posp w) (not (fn-splan-donep p)))
                  (posp (fn-octets-len buf)))))
  :hints (("Goal" :in-theory (e/d (fn-oct-len-is-len fn-oct-slice-list-is-take-nthcdr)
                                  (fn-splan-take fn-splan-fill fn-splan-donep
                                   fn-splan-cur fn-splan-rest))
           :use ((:instance fn-splan-take-progresses
                            (cur (fn-splan-cur p)) (rest (fn-splan-rest p)) (k w))
                 (:instance fn-splan-donep-iff-nothing-remains)))))

; A malformed plan leaves the continuation where the fault is and the host
; faults; nothing but a non-octet in a reply effect stops a window.
(defthm fn-splan-take-status
  (member-equal (mv-nth 0 (fn-splan-take cur rest k)) '(:ok :malformed))
  :hints (("Goal" :induct (fn-splan-take cur rest k) :in-theory (enable fn-splan-take))))

(defthm fn-splan-window-status
  (member-equal (mv-nth 0 (fn-splan-window p w fn-octets)) '(:ok :malformed))
  :hints (("Goal" :in-theory (e/d (fn-splan-window)
                                  (fn-splan-take fn-splan-fill member-equal
                                   fn-splan-cur fn-splan-rest
                                   fn-splan-fill-is-take fn-splan-take-status))
           :use ((:instance fn-splan-fill-is-take
                            (cur (fn-splan-cur p)) (rest (fn-splan-rest p)) (k w)
                            (fn-octets (fn-octets-clear fn-octets)))
                 (:instance fn-splan-take-status
                            (cur (fn-splan-cur p)) (rest (fn-splan-rest p)) (k w))))))

; -----------------------------------------------------------------------------
; KEYSTONE 2: all the windows are the reply.

(defthm fn-splan-drain-is-a-prefix
  (equal (append (mv-nth 1 (fn-splan-drain p w n))
                 (fn-splan-remaining (mv-nth 2 (fn-splan-drain p w n))))
         (fn-splan-remaining p))
  :hints (("Goal" :induct (fn-splan-drain p w n)
           :in-theory (disable fn-splan-take fn-splan-cur fn-splan-rest))))

(defthm fn-splan-drain-octets-true-listp
  (true-listp (mv-nth 1 (fn-splan-drain p w n)))
  :hints (("Goal" :induct (fn-splan-drain p w n)
           :in-theory (disable fn-splan-take))))

(local
 (defthm fn-splan-reply-octets-true-listp
   (true-listp (fn-served-reply-octets effects))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets)))))

(defthm fn-splan-remaining-true-listp
  (true-listp (fn-splan-remaining p)))

(defthm fn-splan-windows-are-the-reply
  ; KEYSTONE (PRF-248).  Whatever the window size W and however many windows N
  ; the socket took, once the plan is done the octets written are the reply
  ; the served machine decided.
  ; The one hypothesis: the loop ran until the plan was done (a plan that
  ; met a non-octet is never done: the octet stays in its continuation).
  (implies (fn-splan-donep (mv-nth 2 (fn-splan-drain (fn-splan-of-effects effects) w n)))
           (equal (mv-nth 1 (fn-splan-drain (fn-splan-of-effects effects) w n))
                  (fn-served-reply-octets effects)))
  :hints (("Goal" :in-theory (disable fn-splan-drain fn-splan-remaining fn-splan-donep
                                      fn-splan-of-effects fn-splan-drain-is-a-prefix
                                      fn-splan-donep-iff-nothing-remains
                                      fn-splan-of-effects-remaining)
           :use ((:instance fn-splan-drain-is-a-prefix (p (fn-splan-of-effects effects)))
                 (:instance fn-splan-donep-iff-nothing-remains
                            (p (mv-nth 2 (fn-splan-drain (fn-splan-of-effects effects) w n))))
                 (:instance fn-splan-remaining-true-listp
                            (p (mv-nth 2 (fn-splan-drain (fn-splan-of-effects effects) w n))))
                 (:instance fn-splan-of-effects-remaining)))))

; -----------------------------------------------------------------------------
; The served step's typed result (adapter-retirement-2's ServedStep fence,
; PKT-616 (b): the shape that lane named (:served-step WORD REPLY ...), here
; with the PLAN's effects in the reply slot; its own book was reverted at
; batch AQ, so this is the one definition heading to dev).
; host/owner-host.lisp fn-owner-chunk-span returns one instead of six
; globals; host/native/owner.lisp fnn-owner-handle-chunk checks the shape
; once (fn-splan-step-p) and reads it through the accessors.
;   (:served-step EFFECTS CLOSEP STARTTLSP SUBMITTEDP CONSUMED REFUSAL-LINES EXPOSURE-CLOSE)

(defun fn-splan-step-make (effects closep starttlsp submittedp consumed refusal-lines
                                   exposure-close)
  (declare (xargs :guard t))
  (list :served-step effects (and closep t) (and starttlsp t) (and submittedp t)
        (nfix consumed) refusal-lines exposure-close))

(defun fn-splan-step-p (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 8) (eq (car x) :served-step)
       (true-listp (nth 1 x))
       (booleanp (nth 2 x)) (booleanp (nth 3 x)) (booleanp (nth 4 x))
       (natp (nth 5 x)) (true-listp (nth 6 x))
       (or (null (nth 7 x)) (fn-cbor-octet-listp (nth 7 x)))))

(defun fn-splan-step-effects (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 1 x))
(defun fn-splan-step-closep (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 2 x))
(defun fn-splan-step-starttlsp (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 3 x))
(defun fn-splan-step-submittedp (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 4 x))
(defun fn-splan-step-consumed (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 5 x))
(defun fn-splan-step-refusal-lines (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 6 x))
(defun fn-splan-step-exposure-close (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 7 x))

(defthm fn-splan-step-make-is-a-step
  (implies (and (true-listp effects) (true-listp refusal-lines)
                (or (null exposure-close) (fn-cbor-octet-listp exposure-close)))
           (fn-splan-step-p (fn-splan-step-make effects closep starttlsp submittedp consumed
                                                refusal-lines exposure-close))))

(defthm fn-splan-step-accessors-of-make
  (and (equal (fn-splan-step-effects (fn-splan-step-make e c s u n r x)) e)
       (equal (fn-splan-step-closep (fn-splan-step-make e c s u n r x)) (and c t))
       (equal (fn-splan-step-starttlsp (fn-splan-step-make e c s u n r x)) (and s t))
       (equal (fn-splan-step-submittedp (fn-splan-step-make e c s u n r x)) (and u t))
       (equal (fn-splan-step-consumed (fn-splan-step-make e c s u n r x)) (nfix n))
       (equal (fn-splan-step-refusal-lines (fn-splan-step-make e c s u n r x)) r)
       (equal (fn-splan-step-exposure-close (fn-splan-step-make e c s u n r x)) x)))

; The reply plan of a step: its effects, then the drain's completion reply,
; the redeem reply and the exposure close, each as a reply effect when
; present.  The order is the one the host wrote before this book
; (fnn-owner-handle-chunk: reply, completion, redeem, close).
(defun fn-splan-reply-effect-if (octets)
  (declare (xargs :guard t))
  (if (consp octets) (list (list :reply octets)) nil))

(defun fn-splan-step-plan (step completion redeem)
  (declare (xargs :guard (fn-splan-step-p step)))
  (fn-splan-of-effects
   (append (fn-splan-step-effects step)
           (fn-splan-reply-effect-if completion)
           (fn-splan-reply-effect-if redeem)
           (fn-splan-reply-effect-if (fn-splan-step-exposure-close step)))))

(local
 (defthm fn-splan-reply-octets-of-reply-effect-if
   (implies (true-listp octets)
            (equal (fn-served-reply-octets (fn-splan-reply-effect-if octets)) octets))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets)))))

; What the step's plan owes: the step's reply, then the three tails.
(defthm fn-splan-step-plan-remaining
  (implies (and (true-listp completion) (true-listp redeem)
                (true-listp (fn-splan-step-exposure-close step)))
           (equal (fn-splan-remaining (fn-splan-step-plan step completion redeem))
                  (append (fn-served-reply-octets (fn-splan-step-effects step))
                          completion redeem (fn-splan-step-exposure-close step))))
  :hints (("Goal" :in-theory (e/d (fn-served-reply-octets-of-append)
                                  (fn-splan-reply-effect-if fn-splan-step-effects
                                   fn-splan-step-exposure-close)))))

(in-theory (disable fn-splan-window fn-splan-fill fn-splan-take fn-splan-drain
                    fn-splan-step-p fn-splan-step-make fn-splan-step-plan))
