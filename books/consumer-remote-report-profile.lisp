; Two required CURRENT-C policy rows, captured from ONE configured generation.
; No default, StoreR/queryG substitution, physical allowance or profile edit.
(in-package "ACL2")
(include-book "consumer-remote-collection")
(include-book "config")

(defconst *fn-crcol-items-slot* "max-remote-report-items")
(defconst *fn-crcol-octets-slot* "max-remote-report-octets")

(defun fn-crcol-policy-verdict (items bytes)
 (declare (xargs :guard t))
 (if (fn-crcol-profilep items bytes) (list :report-policy items bytes)
     '(:refused :remote-report-policy-unsupported)))

; Fixed7 key,generation,current-C row tail,first item bound,first byte bound,
; phase. The owner owes retained/current configuration custody, not a keyshape.
(defun fn-crcol-policy-state (key generation rows items bytes phase)
 (declare (xargs :guard t))
 (list :report-policy-cursor key generation rows items bytes phase))

(defun fn-crcol-policy-begin (key generation rows)
 (declare (xargs :guard t))
 (list :yield (fn-crcol-policy-state key generation rows nil nil :lookup)))

(defun fn-crcol-policy-tick (s key generation)
 (declare (xargs :guard t))
 (let* ((rows (fn-cp-nth 3 s)) (items (fn-cp-nth 4 s)) (bytes (fn-cp-nth 5 s))
        (phase (fn-cp-nth 6 s)))
  (cond ((not (and (equal key (fn-cp-nth 1 s)) (equal generation (fn-cp-nth 2 s))))
         '(:refused :remote-report-policy-source-changed))
        ((eq phase :ready) (list :ready s))
        ((not (eq phase :lookup)) '(:refused :remote-report-policy-phase))
        ((and items bytes)
         (let ((verdict (fn-crcol-policy-verdict items bytes)))
          (if (eq (fn-cp-nth 0 verdict) :report-policy)
              (list :ready (fn-crcol-policy-state key generation nil items bytes :ready)) verdict)))
        ((not (consp rows)) '(:refused :remote-report-limit-missing))
        (t
         (let* ((row (car rows)) (slot (fn-cfg-limit-slot row)) (value (fn-cfg-limit-value row)))
          (list :yield (fn-crcol-policy-state key generation (cdr rows)
           (if (and (null items) (equal slot *fn-crcol-items-slot*)) value items)
           (if (and (null bytes) (equal slot *fn-crcol-octets-slot*)) value bytes) :lookup)))))))

(defun fn-crcol-policy-finish (s key generation)
 (declare (xargs :guard t))
 (cond ((not (and (equal key (fn-cp-nth 1 s)) (equal generation (fn-cp-nth 2 s))))
        '(:refused :remote-report-policy-source-changed))
       ((not (eq (fn-cp-nth 6 s) :ready)) '(:refused :remote-report-policy-incomplete))
       (t (fn-crcol-policy-verdict (fn-cp-nth 4 s) (fn-cp-nth 5 s)))))

; Operator proposals use the existing typed C :limit schema, never change the
; immutable persisted pool/profile format. Actual durable C publication owns
; acceptance; a served reader captures both rows from its ONE current value.
(defun fn-crcol-config-proposals (items bytes)
 (declare (xargs :guard t))
 (let ((verdict (fn-crcol-policy-verdict items bytes)))
  (if (eq (fn-cp-nth 0 verdict) :report-policy)
   (list :config-proposals (fn-cfg-set-limit *fn-crcol-items-slot* items)
                           (fn-cfg-set-limit *fn-crcol-octets-slot* bytes)) verdict)))

(defun fn-crcol-runtime-verdict (policy)
 (declare (xargs :guard t))
 (if (eq (fn-cp-nth 0 policy) :report-policy)
     '(:unavailable :remote-report-runtime-representation) policy))

(in-theory (disable fn-crcol-policy-verdict fn-crcol-policy-state fn-crcol-policy-begin
 fn-crcol-policy-tick fn-crcol-policy-finish fn-crcol-config-proposals fn-crcol-runtime-verdict))
