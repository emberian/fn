; RFC 9171 section 4.3.1: Lifetime is milliseconds. The pinned ION helper
; tests/ltp/fn_ltp_send.c decimal_ttl accepts whole seconds in [1, INT_MAX/1000].
; This is the helper representation, not a bound on stored workflow lifetime.
(in-package "ACL2")

(defun fn-bpit-helper-seconds (lifetime)
  (declare (xargs :guard t))
  (if (not (posp lifetime)) nil
    (let ((seconds (floor lifetime 1000)))
      (if (and (<= 1 seconds) (<= seconds 2147483)
               (equal (* 1000 seconds) lifetime))
          seconds
        nil))))

; The actual host-called conversion cannot shorten or round a lifetime and
; always supplies the pinned helper's supported integer range.
(defthm fn-bpit-helper-seconds-preserves-lifetime
  (implies (fn-bpit-helper-seconds lifetime)
           (let ((seconds (fn-bpit-helper-seconds lifetime)))
             (and (integerp seconds) (<= 1 seconds) (<= seconds 2147483)
                  (equal (* 1000 seconds) lifetime))))
  :hints (("Goal" :in-theory (enable fn-bpit-helper-seconds))))
