; Exact shared state definitions extracted from current owner-host/recovery.
; No owner validity is recomputed here and no supplied readiness flag exists.
(in-package "ACL2")
(include-book "owner-config-state")
(include-book "owner-state-accessors")
(include-book "state-globals")
(include-book "public-exposure")
(include-book "owner-credits")
(include-book "heap-store-figure")

; fn-owner-config moved unchanged to owner-config-state.

(defun fn-owner-install-served-effects (effects state)
  (declare (xargs :stobjs state :guard t))
  (let* ((state (f-put-global 'fn-owner-effects effects state))
         (state (f-put-global 'fn-owner-output nil state))
         (state (f-put-global 'fn-owner-closep (fn-served-closingp effects) state))
         ; RFC 4642 section 2.2.2: the host owes a TLS handshake.  The book
         ; decided it (fn-auth-starttls, books/nntp-auth.lisp); this reads
         ; its answer off the effect list, exactly as the close is read.
         (state (f-put-global 'fn-owner-starttlsp
                              (if (fn-served-starttlsp effects) t nil) state))
         (state (f-put-global 'fn-owner-submittedp
                              (if (fn-served-submission effects) t nil) state)))
    state))

(defun fn-owner-reader-views (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-reader-views state)
      (f-get-global 'fn-owner-reader-views state)
    nil))

(defun fn-owner-auth (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-auth state)
      (f-get-global 'fn-owner-auth state)
    (fn-auth-open-config)))

(defun fn-owner-exposure-state (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-exposure state)
      (f-get-global 'fn-owner-exposure state)
    (fn-exp-initial)))

(defun fn-owner-exposure-publicp (state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-owner-exposure-public state)
       (f-get-global 'fn-owner-exposure-public state)))

(defun fn-owner-exposure-now (fn-owner-st)
  (declare (xargs :stobjs (fn-owner-st) :guard (fn-owner-boundp fn-owner-st)))
  (fn-clock-monotonic (fn-own-clock (fn-owner-core fn-owner-st))))

(defun fn-owner-credit-reserve (state)
  (declare (xargs :stobjs state :guard t))
  (let ((r (and (boundp-global 'fn-owner-credit-reserve state)
                (f-get-global 'fn-owner-credit-reserve state))))
    (if (posp r) r (fn-heap-article-reserve-octets nil))))

(defun fn-owner-credits (state)
  (declare (xargs :stobjs state :guard t))
  (let ((l (and (boundp-global 'fn-owner-credits state)
                (f-get-global 'fn-owner-credits state))))
    (or l (fn-mca-default (fn-owner-credit-reserve state)))))

(defun fn-owner-put-credits (l state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-credits l state))
