(in-package "ACL2")
(include-book "../../books/stx-keyring-size-reader")
(include-book "../../books/statement-attach")

(defun fn-stxks-test-items ()
 (declare (xargs :guard t))
 '((:bytes 102 110 45 101) (:uint . 0) (:uint . 3)
   (:uint . 0) (:uint . 1) (:uint . 0) (:uint . 1)
   (:bytes 112) (:bytes 42 43)))

; Reachable positive: complete paired output + whole materialized row size.
(assert-event
 (let ((wire (fn-stmt-encode-items (fn-stxks-test-items))))
  (mv-let (result carry) (fn-stxks-decode wire)
   (and (fn-stmt-okp result)
        (equal result (fn-stxk-decode-exact wire))
        (equal (fn-stmt-value result) '(0 1 0 1 (112) (42 43)))
        (equal carry (fn-scs-summary (fn-stmt-value result)))
        (fn-scs-carryp carry)))))

; Every-budget refusal behavior remains exact, independently of default profile.
(assert-event
 (mv-let (result sizes) (fn-stmt-decode-items-sized-bounded 9 '(255) 0 65536)
  (and (equal result (fn-stmt-decode-items-bounded 9 '(255) 0 65536))
       (equal result '(:error :limit)) (null sizes))))
(assert-event
 (mv-let (result carry) (fn-stxks-decode '(255))
  (and (equal result (fn-stxk-decode-exact '(255)))
       (not (fn-stmt-okp result)) (null carry))))

; Hypothesis removal: correct other counts, incorrect profile count.
(assert-event
 (let* ((items (fn-stxks-test-items)) (p 2) (s 2)
        (row (fn-stmt-value (fn-stxk-of-items items))))
  (and (fn-stxk-items-p items)
       (not (equal p (len (cdr (nth 7 items)))))
       (equal s (len (cdr (nth 8 items))))
       (not (equal (fn-stxks-row-carry items p s) (fn-scs-summary row))))))
; Hypothesis removal: correct other counts, incorrect snapshot count.
(assert-event
 (let* ((items (fn-stxks-test-items)) (p 1) (s 3)
        (row (fn-stmt-value (fn-stxk-of-items items))))
  (and (fn-stxk-items-p items)
       (equal p (len (cdr (nth 7 items))))
       (not (equal s (len (cdr (nth 8 items)))))
       (not (equal (fn-stxks-row-carry items p s) (fn-scs-summary row))))))
; Corrupted metadata-domain fixture, logical evaluation outside served guards.
(assert-event
 (let* ((items (cons '(:bytes 0) (cdr (fn-stxks-test-items))))
        (p 1) (s 2) (row (fn-stmt-value (fn-stxk-of-items items))))
  (and (not (fn-stxk-items-p items))
       (equal p (len (cdr (nth 7 items))))
       (equal s (len (cdr (nth 8 items))))
       (not (equal (fn-stxks-row-carry items p s) (fn-scs-summary row))))))
