; Required durable current-C query dimension. This is policy/representation
; compatibility, never an allocation grant or a retained-source issuer.
(in-package "ACL2")
(include-book "consumer-remote-codec")
(include-book "consumer-remote-event-codec")
(include-book "consumer-remote-reply")
(include-book "config")

(defconst *fn-crp-limit-slot* "max-consumer-query-groups")

(defun fn-crp-event-ceiling (groups)
 (declare (xargs :guard t))
 ; FNCE4 fixed header, four counted IDs and one uint16+name per group.
 (+ 38 (* 4 *fn-cp-max-id*) (* (+ 2 *fn-record-max-group-name*) (nfix groups))))

(defun fn-crp-policy-verdict (groups record-ceiling)
 (declare (xargs :guard t))
 (cond ((not (and (posp groups) (fn-cp-uintp groups))) '(:refused :consumer-query-count))
       ((or (not (fn-frame-spec-listp (fn-cr-spec groups)))
            (< *fn-frame-max-payload* (fn-frame-specs-width (fn-cr-spec groups))))
        '(:refused :consumer-query-fncr-width))
       ((or (not (natp record-ceiling)) (< record-ceiling (fn-crp-event-ceiling groups)))
        '(:refused :consumer-query-record-width))
       ((not (fn-crr-profilep record-ceiling)) '(:refused :consumer-query-reply-width))
       (t (list :query-policy groups (fn-cr-read-bound groups)
                 (fn-crp-event-ceiling groups) record-ceiling))))

; Fixed6 cursor: tag, captured current-source key, borrowed current limit
; tail, installed Store record ceiling, phase, decided policy. The actual
; installed owner source must retain/revalidate every borrowed child.
(defun fn-crp-state (key rows record-ceiling phase policy)
 (declare (xargs :guard t))
 (list :query-policy-cursor key rows record-ceiling phase policy))

(defun fn-crp-begin (key rows record-ceiling)
 (declare (xargs :guard t))
 (list :yield (fn-crp-state key rows record-ceiling :lookup nil)))

(defun fn-crp-tick (s current-key current-record-ceiling)
 (declare (xargs :guard t))
 (let ((key (fn-cp-nth 1 s)) (rows (fn-cp-nth 2 s))
       (record-ceiling (fn-cp-nth 3 s)) (phase (fn-cp-nth 4 s)))
  (cond ((or (not (equal key current-key)) (not (equal record-ceiling current-record-ceiling)))
         '(:refused :query-policy-source-changed))
        ((eq phase :ready) (list :ready s))
        ((not (eq phase :lookup)) '(:refused :query-policy-phase))
        ((not (consp rows)) '(:unavailable :consumer-query-limit))
        ((equal (fn-cfg-limit-slot (car rows)) *fn-crp-limit-slot*)
         (let ((policy (fn-crp-policy-verdict (fn-cfg-limit-value (car rows)) record-ceiling)))
          (if (eq (fn-cp-nth 0 policy) :query-policy)
              (list :ready (fn-crp-state key nil record-ceiling :ready policy)) policy)))
        (t (list :yield (fn-crp-state key (cdr rows) record-ceiling :lookup nil))))))

(defun fn-crp-finish (s current-key current-record-ceiling)
 (declare (xargs :guard t))
 (if (or (not (equal (fn-cp-nth 1 s) current-key))
          (not (equal (fn-cp-nth 3 s) current-record-ceiling)))
     '(:refused :query-policy-source-changed)
  (if (eq (fn-cp-nth 4 s) :ready) (fn-cp-nth 5 s) '(:refused :query-policy-incomplete))))

; Emit the existing typed C delta; normal current-C durable publication and
; its atomic account/config collector own acceptance. Unsupported values are
; refused before an operator producer may propose the delta.
(defun fn-crp-config-proposal (groups record-ceiling)
 (declare (xargs :guard t))
 (let ((policy (fn-crp-policy-verdict groups record-ceiling)))
  (if (eq (fn-cp-nth 0 policy) :query-policy)
      (list :config-proposal (fn-cfg-set-limit *fn-crp-limit-slot* groups)) policy)))

; A current C row and an admitted Store profile do not establish the selected
; host array/index representation. No genuine installed descriptor exists
; yet; runtime-operation source/role publication remains the union's issuer.
(defun fn-crp-runtime-verdict (policy)
 (declare (xargs :guard t))
 (if (eq (fn-cp-nth 0 policy) :query-policy)
     '(:unavailable :consumer-query-runtime-representation) policy))

(in-theory (disable fn-crp-event-ceiling fn-crp-policy-verdict fn-crp-state
                    fn-crp-begin fn-crp-tick fn-crp-finish fn-crp-config-proposal fn-crp-runtime-verdict))
