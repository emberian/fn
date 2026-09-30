(in-package "ACL2")
(include-book "../../books/consumer-remote-event-buffer")

; Fixtures execute the concrete local stobj. They do not supply production
; allocation authority or stand in for the installed Store operation.
(defun fn-crevbt-step (s key extent prefix)
 (declare (xargs :guard (fn-cbor-octet-listp prefix)))
 (with-local-stobj fn-octets
  (mv-let (answer bytes fn-octets)
   (let ((fn-octets (fn-octets-from-list prefix fn-octets)))
    (mv-let (answer fn-octets) (fn-crevb-step s key extent fn-octets)
     (mv answer (fn-octets-list fn-octets) fn-octets)))
   (list answer bytes))))

(defconst *crevbt-event*
 '(:consumer 1 2 3 (:remote-register (99) (112) (99) 1 2 1 ((97) (98)) (65))))
(defconst *crevbt-key* '(:current 1 2 3))

; Unconditional boundary positive checks complete result and complete effect.
(assert-event
 (let* ((s (cadr (fn-crev-begin *crevbt-event* 2 6 *crevbt-key* 48)))
        (actual (fn-crevbt-step s *crevbt-key* 48 nil)))
  (and (eq (car (car actual)) :yield)
       (mv-let (answer bytes) (fn-crevb-reference s *crevbt-key* 48 nil)
        (equal actual (list answer bytes)))
       (equal (cadr actual) (fn-crev-header *crevbt-event* 2)))))
; Concrete three-chunk assembly reaches terminal with exactly reference bytes.
(assert-event
 (let* ((s (cadr (fn-crev-begin *crevbt-event* 2 6 *crevbt-key* 48)))
        (a (fn-crevbt-step s *crevbt-key* 48 nil))
        (b (fn-crevbt-step (cadar a) *crevbt-key* 48 (cadr a)))
        (c (fn-crevbt-step (cadar b) *crevbt-key* 48 (cadr b)))
        (d (fn-crevbt-step (cadar c) *crevbt-key* 48 (cadr c))))
  (and (equal (car d) '(:encoded))
       (equal (cadr d) (fn-crev-encode-reference *crevbt-event*))
       (equal (fn-crev-decode-exact (cadr d)) (list :ok *crevbt-event*)))))
; Refusal witnesses affirm exact unchanged buffer effects.
(assert-event
 (let* ((s (cadr (fn-crev-begin *crevbt-event* 2 6 *crevbt-key* 48)))
        (prefix '(9 8)))
  (and (equal (fn-crevbt-step s '(:current 1 2 4) 50 prefix)
              (list '(:refused :consumer-source-changed) prefix))
       (equal (fn-crevbt-step s *crevbt-key* 1 prefix)
              (list '(:refused :remote-event-extent) prefix)))))
; Corrupted cursor: oversized/invalid header refuses before buffer write.
(assert-event
 (let* ((s (fn-crev-state *crevbt-key* '((97)) 1 3 nil '(999) :header)))
  (equal (fn-crevbt-step s *crevbt-key* 100 '(7))
         (list '(:refused :remote-event-chunk) '(7)))))
