; fn: the named host assumptions of the runtime contract
; (books/runtime-contract.lisp), as constrained functions (AGENTS.md: a named
; assumption is an encapsulate with a local witness, and the theorems that use
; it mention it).
;
; The contract checks the host's discipline where it can (a completion that
; matches no outstanding use is discarded, T6; a malformed one is reported as
; (:failed :malformed-completion)); what it cannot check is what the host did
; outside the state it is handed.  Two things:
;
;   A-HOST-LANDS      what an :in completion reports is in the buffer.
;   A-HOST-COMPLETES  every submitted action is completed exactly once.

(in-package "ACL2")
(include-book "runtime-contract")

; -----------------------------------------------------------------------------
; A-HOST-LANDS.  "When the host delivers a completion (kind id inc op (:done n))
; or (... (:short n)) of an :in action (:recv, :pread) whose handle is
; (h g off len), the N octets the operation produced are
; (fn-assume-host-input op n), and before delivering it the host wrote exactly
; them at cells [off, off + n) of buffer H, by `fn-rtc-st-splice', and changed
; nothing else of the layer state, while the buffer was :in-leased."
;
; Theorems that take it: `fn-rtc-host-landing-is-the-contract-step'
; (books/runtime-contract-landing.lisp), the executable step after the host's
; landing as the contract's step on the completion that carries the
; operation's octets.  The landing's own facts (it keeps the invariant and is
; invisible to every machine) are proved there for EVERY octet list, so they
; need no assumption; only the identity of the octets with the operation's
; does.

(encapsulate
  (((fn-assume-host-input * *) => *))

  (local (defun fn-rtc-zeros (n)
           (if (zp n) nil (cons 0 (fn-rtc-zeros (- n 1))))))

  (local (defthm fn-rtc-zeros-facts
           (and (fn-cbor-octet-listp (fn-rtc-zeros n))
                (equal (len (fn-rtc-zeros n)) (nfix n)))))

  (local (defun fn-assume-host-input (op n)
           (declare (ignore op))
           (fn-rtc-zeros n)))

  (defthm fn-assume-host-input-is-n-octets
    (and (fn-cbor-octet-listp (fn-assume-host-input op n))
         (equal (len (fn-assume-host-input op n)) (nfix n)))))

; -----------------------------------------------------------------------------
; A-HOST-COMPLETES.  "The host delivers exactly one completion for every
; submitted action other than :cancel."  Over a host trace -- the actions the
; layer emitted, in order -- `(fn-assume-host-completions actions)' is the
; completions the host returned after them; every non-:cancel action's key
; (kind id inc op) is the key of exactly one of them.
;
; Theorems that take it: none yet.  With T4 (only its own completion ends a
; use) and T13 (the last completion retires a draining slot) it bounds how long
; a stuck action pins its slot and its buffer: the instance's deadline plus the
; host's completion of the cancel.  The liveness theorem that states this over
; traces is landing 2's (the transaction machine's uncertainty path).

;; The number of completions in EVENTS whose key is KEY.
(defun fn-rtc-count-key (key events)
  (declare (xargs :guard t))
  (if (consp events)
      (+ (if (equal (fn-rtc-key (car events)) key) 1 0)
         (fn-rtc-count-key key (cdr events)))
    0))

(defun fn-rtc-completion-listp (events)
  (declare (xargs :guard t))
  (if (consp events)
      (and (fn-rtc-completionp (car events))
           (fn-rtc-completion-listp (cdr events)))
    (null events)))

; An action the host must complete: a well-formed action other than :cancel.
(defun fn-rtc-completable-p (a)
  (declare (xargs :guard t))
  (and (fn-rtc-actionp a) (not (eq (fn-rtc-get 0 a) :cancel))))

(defun fn-rtc-completable-key-p (key actions)
  (declare (xargs :guard t))
  (if (consp actions)
      (or (and (fn-rtc-completable-p (car actions))
               (equal (fn-rtc-key (car actions)) key))
          (fn-rtc-completable-key-p key (cdr actions)))
    nil))

; The witness: the host cancels every action, once per key.
(defun fn-rtc-cancel-all (actions)
  (declare (xargs :guard t))
  (if (consp actions)
      (if (and (fn-rtc-completable-p (car actions))
               (not (fn-rtc-completable-key-p (fn-rtc-key (car actions)) (cdr actions))))
          (cons (append (fn-rtc-key (car actions)) (list '(:cancelled)))
                (fn-rtc-cancel-all (cdr actions)))
        (fn-rtc-cancel-all (cdr actions)))
    nil))

(encapsulate
  (((fn-assume-host-completions *) => *))

  (local (defun fn-assume-host-completions (actions)
           (fn-rtc-cancel-all actions)))

  (local (defthm fn-rtc-key-of-cancelled
           (equal (fn-rtc-key (append (fn-rtc-key a) (list '(:cancelled))))
                  (fn-rtc-key a))))

  (local (defthm fn-rtc-count-key-of-cancel-all
           (equal (fn-rtc-count-key key (fn-rtc-cancel-all actions))
                  (if (fn-rtc-completable-key-p key actions) 1 0))
           :hints (("Goal" :in-theory (disable fn-rtc-completable-p fn-rtc-key)))))

  (local (defthm fn-rtc-completable-key-p-of-member
           (implies (and (member-equal a actions) (fn-rtc-completable-p a))
                    (fn-rtc-completable-key-p (fn-rtc-key a) actions))
           :hints (("Goal" :in-theory (disable fn-rtc-completable-p fn-rtc-key)))))

  (defthm fn-assume-host-completes-every-action
    (implies (and (member-equal a actions)
                  (fn-rtc-actionp a)
                  (not (equal (fn-rtc-get 0 a) :cancel)))
             (equal (fn-rtc-count-key (fn-rtc-key a) (fn-assume-host-completions actions))
                    1))
    :hints (("Goal" :in-theory (disable fn-rtc-key fn-rtc-actionp))))

  (defthm fn-assume-host-completions-are-completions
    (fn-rtc-completion-listp (fn-assume-host-completions actions))))
