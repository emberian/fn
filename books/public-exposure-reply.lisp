; fn: the exposure's observation of a served step, without building its reply
; (PRF-161; exposure-reply-size, PKT-481).
;
; After every served step `fn-exp-observe' (books/public-exposure.lisp)
; reads two facts of the reply the step rendered: whether it sent any octet,
; and how many of its replies begin "481 " at a line start (RFC 4643 section
; 2.3.2's authentication-failed answer).  Until this book the host handed it
; `(fn-served-reply-octets effects)': a second copy of the whole reply, which
; `fn-exp-481-count' then walked with one control-stack frame per octet, so
; the served ARTICLE of a 2 MiB article exhausted the control stack inside
; `fn-owner-chunk' and stopped the owner (qual-dfa810fc; the backtrace is
; planning/evidence/exposure-reply-size/cause-backtrace.txt).
;
; The subject the host calls is `fn-exp-observe-effects'
; (host/owner-host.lisp fn-owner-exposure-observe, from fn-owner-chunk, from
; host/native/owner.lisp fnn-owner-handle-chunk).  Its logical definition IS
; `fn-exp-observe' of the step's reply octets, so every theorem of PRF-161
; about `fn-exp-observe' is a theorem about what the host runs
; (`fn-exp-observe-effects-unfolds').  Its executable is one scan of the
; effect list: no octet is copied and the stack is constant.  The scan is a
; five-state recognizer of "481 " at a line start that carries its state
; across effects, since a reply split between two effects is one stream on
; the wire.
;
; Keystones: fn-exp-481-scan-counts-the-481-replies (the recognizer is
; fn-exp-481-count), fn-exp-effects-scan-is-the-reply-scan (the scan over
; effects is the scan over the concatenated reply), and the guard proof of
; fn-exp-observe-effects (its executable is its definition), stated as
; fn-exp-observe-effects-is-the-observation-of-the-reply.
; Teeth: tests/acl2/public-exposure-reply-tests.lisp.
;
; This book owns the prefix `fn-exp-' with books/public-exposure.lisp.

(in-package "ACL2")
(include-book "public-exposure")

; -----------------------------------------------------------------------------
; The recognizer
;
; State 0: not at a line start; 1: at a line start; 2, 3, 4: at a line start
; and "4", "48", "481" read since.  A space in state 4 is one 481 reply.

(defun fn-exp-481-next (st c)
  (declare (xargs :guard t))
  (cond ((equal c 10) 1)
        ((and (equal st 1) (equal c 52)) 2)
        ((and (equal st 2) (equal c 56)) 3)
        ((and (equal st 3) (equal c 49)) 4)
        (t 0)))

(defun fn-exp-481-scan (octets st acc)
  (declare (xargs :guard (natp acc)))
  (if (consp octets)
      (fn-exp-481-scan (cdr octets) (fn-exp-481-next st (car octets))
                       (if (and (equal st 4) (equal (car octets) 32))
                           (+ 1 acc)
                         acc))
    (cons acc st)))

; What state ST has read since the line start, and whether it is at one.
(defun fn-exp-481-read (st)
  (declare (xargs :guard t))
  (cond ((equal st 2) '(52))
        ((equal st 3) '(52 56))
        ((equal st 4) '(52 56 49))
        (t nil)))

(defun fn-exp-481-at (st)
  (declare (xargs :guard t))
  (and (member-equal st '(1 2 3 4)) t))

(local
 (defthm fn-exp-481-count-of-cons
   (equal (fn-exp-481-count (cons a x) at)
          (+ (if (and at (equal a 52)
                      (equal (fn-exp-at 0 x) 56)
                      (equal (fn-exp-at 1 x) 49)
                      (equal (fn-exp-at 2 x) 32))
                 1 0)
             (fn-exp-481-count x (equal a 10))))
   :hints (("Goal" :expand ((fn-exp-481-count (cons a x) at)
                            (fn-exp-at 1 (cons a x))
                            (fn-exp-at 2 (cons a x))
                            (fn-exp-at 3 (cons a x)))))))

(local
 (defthm fn-exp-481-count-of-atom
   (implies (not (consp x))
            (equal (fn-exp-481-count x at) 0))))

(local
 (defthm fn-exp-at-0
   (equal (fn-exp-at 0 x) (if (consp x) (car x) nil))))

(local
 (defthm fn-exp-at-of-cons-positive
   (implies (posp i)
            (equal (fn-exp-at i (cons a x)) (fn-exp-at (1- i) x)))))

(local
 (defthm fn-exp-481-scan-matches-count
   (implies (acl2-numberp acc)
            (equal (car (fn-exp-481-scan octets st acc))
                   (+ acc (fn-exp-481-count (append (fn-exp-481-read st) octets)
                                            (fn-exp-481-at st)))))
   :hints (("Goal" :induct (fn-exp-481-scan octets st acc)
            :in-theory (e/d (fn-exp-481-scan) (fn-exp-481-count))))))

; Keystone: from a line start, the recognizer counts exactly the 481
; replies fn-exp-481-count counts, on every argument.
(defthm fn-exp-481-scan-counts-the-481-replies
  (equal (car (fn-exp-481-scan octets 1 0))
         (fn-exp-481-count octets t)))

(defthm fn-exp-481-scan-of-atom
  (implies (not (consp octets))
           (equal (fn-exp-481-scan octets st acc) (cons acc st))))

(defthm fn-exp-481-scan-of-append
  (equal (fn-exp-481-scan (append x y) st acc)
         (fn-exp-481-scan y (cdr (fn-exp-481-scan x st acc))
                          (car (fn-exp-481-scan x st acc)))))

; -----------------------------------------------------------------------------
; The scan over a step's effects

; The octets one effect contributes to the reply: fn-served-reply-octets'
; own selection (books/served.lisp).
(defun fn-exp-effect-reply (effect)
  (declare (xargs :guard t))
  (if (and (consp effect)
           (equal (car effect) :reply)
           (consp (cdr effect)))
      (car (cdr effect))
    nil))

(defthm fn-served-reply-octets-by-fn-exp-effect-reply
  (implies (consp effects)
           (equal (fn-served-reply-octets effects)
                  (append (fn-exp-effect-reply (car effects))
                          (fn-served-reply-octets (cdr effects))))))

(defthm fn-served-reply-octets-of-atom
  (implies (not (consp effects))
           (equal (fn-served-reply-octets effects) nil)))

; (ACC ST . ANSWERED): the 481 count, the recognizer's state, and whether any
; octet was sent.
(defun fn-exp-effects-scan (effects st acc answered)
  (declare (xargs :guard (natp acc)))
  (if (consp effects)
      (let* ((octets (fn-exp-effect-reply (car effects)))
             (r (fn-exp-481-scan octets st acc)))
        (fn-exp-effects-scan (cdr effects) (cdr r) (car r)
                             (or answered (consp octets))))
    (list* acc st answered)))

(defthm fn-exp-effects-scan-shape
  (and (consp (fn-exp-effects-scan effects st acc answered))
       (consp (cdr (fn-exp-effects-scan effects st acc answered)))))

(defthm fn-exp-481-scan-count-natp
  (implies (natp acc)
           (natp (car (fn-exp-481-scan octets st acc))))
  :rule-classes :type-prescription)

(local
 (defthm fn-exp-481-scan-count-natp-rewrite
   (implies (natp acc)
            (natp (car (fn-exp-481-scan octets st acc))))))

(verify-guards fn-exp-effects-scan)

(local
 (defthm consp-of-append-is-either
   (equal (consp (append x y)) (or (consp x) (consp y)))))

; Keystone: the scan over the effects is the recognizer over the reply the
; step writes, and ANSWERED is whether that reply is non-empty.
(defthm fn-exp-effects-scan-is-the-reply-scan
  (let ((r (fn-exp-effects-scan effects st acc answered))
        (s (fn-exp-481-scan (fn-served-reply-octets effects) st acc)))
    (and (equal (car r) (car s))
         (equal (cadr r) (cdr s))
         (equal (cddr r)
                (or answered (consp (fn-served-reply-octets effects))))))
  :hints (("Goal" :induct (fn-exp-effects-scan effects st acc answered)
           :in-theory (e/d (fn-served-reply-octets-by-fn-exp-effect-reply)
                           (fn-served-reply-octets fn-exp-481-scan
                            fn-exp-effect-reply)))))

; -----------------------------------------------------------------------------
; The subject the host calls

(defun fn-exp-observe-effects (xs lim id now effects consumed subject submitted)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (e/d (fn-exp-observe)
                                           (fn-exp-observe-facts
                                            fn-exp-effects-scan
                                            fn-exp-481-scan
                                            fn-served-reply-octets))
                    :use ((:instance fn-exp-effects-scan-is-the-reply-scan
                                     (st 1) (acc 0) (answered nil))
                          (:instance fn-exp-481-scan-counts-the-481-replies
                                     (octets (fn-served-reply-octets effects))))))))
  (mbe :logic (fn-exp-observe xs lim id now (fn-served-reply-octets effects)
                              consumed subject submitted)
       :exec (let ((r (fn-exp-effects-scan effects 1 0 nil)))
               (fn-exp-observe-facts xs lim id now (if (cddr r) t nil) (car r)
                                     consumed subject submitted))))

; The name the ledger cites for "the subject is fn-exp-observe of the
; reply": every PRF-161 theorem about fn-exp-observe applies to the host's
; call through this equation.
(defthm fn-exp-observe-effects-unfolds
  (equal (fn-exp-observe-effects xs lim id now effects consumed subject submitted)
         (fn-exp-observe xs lim id now (fn-served-reply-octets effects)
                         consumed subject submitted)))

; Keystone (the executable is the observation of the reply): what the host
; runs -- the facts computed by the scan, with no reply built -- is
; fn-exp-observe of the octets the step writes.  The decisions are unchanged.
(defthm fn-exp-observe-effects-is-the-observation-of-the-reply
  (let ((r (fn-exp-effects-scan effects 1 0 nil)))
    (equal (fn-exp-observe-facts xs lim id now (if (cddr r) t nil) (car r)
                                 consumed subject submitted)
           (fn-exp-observe xs lim id now (fn-served-reply-octets effects)
                           consumed subject submitted)))
  :hints (("Goal" :in-theory (e/d (fn-exp-observe)
                                  (fn-exp-observe-facts fn-exp-effects-scan
                                   fn-exp-481-scan fn-served-reply-octets))
           :use ((:instance fn-exp-effects-scan-is-the-reply-scan
                            (st 1) (acc 0) (answered nil))
                 (:instance fn-exp-481-scan-counts-the-481-replies
                            (octets (fn-served-reply-octets effects)))))))

(in-theory (disable fn-exp-observe-effects))
