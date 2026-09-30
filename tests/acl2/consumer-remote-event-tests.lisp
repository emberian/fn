(in-package "ACL2")
(include-book "../../books/consumer-remote-event-model")

(defconst *crevt-event*
 '(:consumer 8 9 10 (:remote-register (99) (112) (99) 1 2 1 ((97) (98)) (65))))
(defconst *crevt-key* '(:remote-current 1 2))
(defun fn-crevt-run (fuel s key)
 (declare (xargs :guard (natp fuel) :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) '(:yield)
  (let ((next (fn-crev-tick s key)))
   (if (eq (car next) :chunk)
       (let ((rest (fn-crevt-run (1- fuel) (fn-cp-nth 2 next) key)))
        (if (eq (car rest) :encoded)
            (list :encoded (append (fn-cp-nth 1 next) (fn-cp-nth 1 rest))) rest))
     next))))

; Includes a exact FNCE4 decode/encode and old-family separation.
(assert-event
 (let* ((charge (+ (fn-crev-header-charge *crevt-event* 2) 6))
        (start (fn-crev-begin *crevt-event* 2 6 *crevt-key* charge))
        (encoded (fn-crevt-run 8 (fn-cp-nth 1 start) *crevt-key*)))
  (and (fn-crev-headp *crevt-event*) (eq (car start) :yield)
       (equal encoded (list :encoded (fn-crev-encode-reference *crevt-event*)))
       (equal (len (fn-cp-nth 1 encoded)) charge)
       (equal (fn-crev-decode-exact (fn-cp-nth 1 encoded)) (list :ok *crevt-event*))
       (equal (fn-crev-decode-exact (update-nth 4 2 (fn-cp-nth 1 encoded))) '(:error :remote-version))
       (equal (fn-crev-begin *crevt-event* 2 6 *crevt-key* (1- charge)) '(:refused :record-budget))
       (equal (fn-crev-tick (fn-cp-nth 1 start) '(changed)) '(:refused :consumer-source-changed)))))

;@positive fn-crev-chunk-is-exact-residual-encoding
;@positive fn-crev-tick-preserves-exact-remaining-measures
(assert-event
 (let* ((s (fn-cp-nth 1 (fn-crev-begin *crevt-event* 2 6 *crevt-key* 300)))
        (next (fn-crev-tick s *crevt-key*)))
  (and (fn-crevm-measurep s) (eq (car next) :chunk)
       (equal (append (fn-cp-nth 1 next) (fn-crevm-residual (fn-cp-nth 2 next)))
              (fn-crevm-residual s))
       (fn-crevm-measurep (fn-cp-nth 2 next)))))
;@hypothesis-removal fn-crev-chunk-is-exact-residual-encoding chunk-result
(assert-event
 (let ((s (fn-cp-nth 1 (fn-crev-begin *crevt-event* 2 6 *crevt-key* 300))))
  (and (not (eq (car (fn-crev-tick s '(changed))) :chunk))
       (not (equal (append (true-list-fix (fn-cp-nth 1 (fn-crev-tick s '(changed))))
                           (fn-crevm-residual (fn-cp-nth 2 (fn-crev-tick s '(changed)))))
                    (fn-crevm-residual s))))))
;@hypothesis-removal fn-crev-tick-preserves-exact-remaining-measures maintained-measures
; Corrupted cursor charge; one bounded chunk is emitted, but no completion
; may be accepted after the residual wire debt differs from the exact query.
(assert-event
 (let* ((s (fn-crev-state *crevt-key* '((97) (98)) 2 7 nil nil :groups))
        (next (fn-crev-tick s *crevt-key*)))
  (and (not (fn-crevm-measurep s)) (eq (car next) :chunk)
       (not (fn-crevm-measurep (fn-cp-nth 2 next))))))
;@hypothesis-removal fn-crev-tick-preserves-exact-remaining-measures chunk-result
(assert-event
 (let* ((s (fn-crev-state *crevt-key* '((97)) 1 3 nil nil :groups))
        (next (fn-crev-tick s '(changed))))
  (and (fn-crevm-measurep s) (not (eq (car next) :chunk))
       (not (fn-crevm-measurep (fn-cp-nth 2 next))))))
;@positive fn-crev-encoded-has-no-residual-octets
(assert-event
 (let* ((s (fn-crev-state *crevt-key* nil 0 0 '(98) nil :groups))
        (next (fn-crev-tick s *crevt-key*)))
  (and (eq (car next) :encoded) (equal (fn-crevm-residual s) nil))))
;@hypothesis-removal fn-crev-encoded-has-no-residual-octets encoded-result
(assert-event
 (let* ((s (fn-crev-state *crevt-key* '((97)) 1 3 nil nil :groups))
        (next (fn-crev-tick s *crevt-key*)))
  (and (not (eq (car next) :encoded)) (not (equal (fn-crevm-residual s) nil)))))
