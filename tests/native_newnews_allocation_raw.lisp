;;; Actual native counterpart/registered-creator discrimination. Not a proof
;;; or a whole-plan allocation tariff; source-loaded warnings stay in the log.
(in-package "ACL2")
(require :sb-posix)
(require :sb-bsd-sockets)

(defun fnout-load-host-forms (path wanted)
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof) until (eq form :eof)
            when (and (consp form)
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval form)
                 (setf missing (remove (list (car form) (cadr form)) missing :test #'equal))))
    (when missing (error "output custody host forms missing: ~s" missing))))

(fnout-load-host-forms "host/native/io.lisp"
 '((define-condition fnn-store-error) (define-condition fnn-store-fault)
   (define-condition fnn-entry-guard-fault) (defun fnn-fault)
   (defun fnn-counterpart) (defun fnn-install-raw-dispatch)
   (defun fnn-dispatch-function) (defun fnn-guard-conjuncts)
   (defun fnn-entry-guard-spec) (defun fnn-entry-guard-describe)
   (defun fnn-entry-guard) (defun fnn-call) (defun fnn-core)))
(defvar *fnn-dispatch-counterpart* nil)
(defvar *fnn-raw-dispatch* (make-hash-table :test 'eq))
(defvar *fnn-startup-creators* (make-hash-table :test 'eq))
(defvar *fnn-entry-guard-specs* (make-hash-table :test 'eq))
(defvar *fn-entry-guard-kinds* nil)
(fnn-install-raw-dispatch :report nil)


; The actual generated producer and plan entries, using the normal selected
; counterparts. Fixture construction precedes each allocation measurement.
(setq *fnn-dispatch-counterpart* t)
(dolist (name '(fn-nntp-newnews-response-stream fn-splan-of-effects
                fn-splan-cursor-step fn-splan-donep))
 (unless (eq (fnn-dispatch-function name) (fnn-counterpart name))
  (error "NEWNEWS probe route mismatch: ~s" name)))
(let* ((a (fn-make-article "<a@x>" '(13 10 13 10 65) '("fn.test")
                           '(("fn.test" . 1)) 1 5))
       (b (fn-make-article "<b@x>" '(13 10 13 10 66) '("fn.other")
                           '(("fn.other" . 1)) 2 6))
       (groups '("fn.g0" "fn.g1" "fn.g2" "fn.g3" "fn.g4" "fn.g5"
                 "fn.g6" "fn.g7" "fn.g8" "fn.g9" "fn.test"))
       (archive (fn-make-state groups nil (list b a) 0 nil nil))
       (args (list (fn-nntp-string-octets "fn.test")
                   (fn-nntp-string-octets "20000101")
                   (fn-nntp-string-octets "000000")))
       (before (sb-ext:get-bytes-consed))
       (result (fnn-core 'fn-nntp-newnews-response-stream nil archive nil args nil nil))
       (factory-consed (- (sb-ext:get-bytes-consed) before))
       (plan (fnn-core 'fn-splan-of-effects (cdr result))))
 (unless (and (null (car result)) (fn-nnw-meta-effectp (car (cdr result))))
  (error "actual NEWNEWS factory did not return the configured cursor"))
 (format t "~%native_newnews_allocation: factory ~d bytes~%" factory-consed)
 (let ((answer (fnn-call 'fn-splan-cursor-step plan 1 nil nil)))
  (unless (eq (first answer) :ok) (error "actual sparse metadata plan could not step"))
  (format t "native_newnews_allocation: first actual plan step PASS~%")))


; Matched repeated factory samples resolve SBCL's allocation-region granularity.
; Configured group and article fixture growth occurs before the timed interval.
(dolist (sizes '((11 2) (1024 2) (65536 2) (11 4096)))
 (destructuring-bind (group-count article-count) sizes
  (let* ((groups (append (make-list (- group-count 1) :initial-element "fn.other")
                        (list "fn.test")))
         (article (fn-make-article "<a@x>" '(13 10 13 10 65) '("fn.test")
                                   '(("fn.test" . 1)) 1 5))
         (archive (fn-make-state groups nil (make-list article-count :initial-element article) 0 nil nil))
         (args (list (fn-nntp-string-octets "fn.test")
                     (fn-nntp-string-octets "20000101")
                     (fn-nntp-string-octets "000000")))
         (iterations 1024) (last-result nil))
   (dotimes (i 8) (fnn-core 'fn-nntp-newnews-response-stream nil archive nil args nil nil))
   (sb-ext:gc :full t)
   (let ((before (sb-ext:get-bytes-consed)))
    (dotimes (i iterations)
     (setf last-result (fnn-core 'fn-nntp-newnews-response-stream nil archive nil args nil nil)))
    (unless (fn-nnw-meta-effectp (cadr last-result)) (error "factory benchmark changed effect"))
    (format t "native_newnews_allocation: factory-sample groups=~d articles=~d repeats=~d allocated=~d~%"
            group-count article-count iterations (- (sb-ext:get-bytes-consed) before))))))



; Actual native window allocator and renderer, followed by actual plan steps.
(fnout-load-host-forms "host/native/io.lisp"
 '((deftype fnn-octets) (defun fnn-make-octets)))
(fnout-load-host-forms "host/native/owner.lisp"
 '((defstruct (fnn-output-grant (:constructor %make-fnn-output-grant)))
   (defvar *fnn-output-grant*)
   (defun fnn-make-render-buffer) (defun fnn-response-render-buffer)
   (defun fnn-owner-render-next)))
(defvar *fnout-window* 256)
; Scheduling-policy observation only; the direct renderer and buffer entry
; are the actual source functions. No owner/store operation is replaced here.
(defun fnn-owner-over-window () *fnout-window*)

(dolist (text (list "" "." "abc" ".dot-stuffed" (make-string 4097 :initial-element #\X)))
  (dolist (*fnout-window* '(1 2 7 256))
    (let* ((*fnn-output-grant* (%make-fnn-output-grant))
           (line (fn-sl-start text))
           (expected (fn-sl-remaining line))
           (cur (fn-cur-make nil (fn-nnw-stream-render line nil) nil nil))
           (plan (fn-splan-of-effects (list (fn-nnw-meta-effect cur))))
           (got nil) (steps 0))
      (loop while (fnn-core 'fn-splan-line-ready-p plan) do
        (multiple-value-bind (octets rest donep cursorp) (fnn-owner-render-next plan)
          (assert (and (not donep) (not cursorp) (plusp (length octets))))
          (assert (<= (length octets) *fnout-window*))
          (loop for byte across octets do (push byte got))
          (setf plan rest)
          (incf steps)))
      (assert (equal (nreverse got) expected))
      (assert (<= steps (+ 3 (length text)))))))
(format t "native_newnews_allocation: direct-line-fill PASS empty/dot/text/4097char at1/2/7/256, positive bounded exact output~%")

; Matched allocation observation, not a peak-residency/zero-allocation proof.
; Both routes start from the identical immutable plan and reuse a pre-sized
; private buffer. Fixture text/plan/grant construction is outside the interval.
(let* ((*fnout-window* 4096)
       (*fnn-output-grant* (%make-fnn-output-grant))
       (text (make-string 4097 :initial-element #\X))
       (cur (fn-cur-make nil (fn-nnw-stream-render (fn-sl-start text) nil) nil nil))
       (plan (fn-splan-of-effects (list (fn-nnw-meta-effect cur)))))
  (fnn-response-render-buffer *fnout-window*)
  (dolist (route '(:list-cursor :direct-buffer))
    (flet ((run ()
             (let ((octets
                    (if (eq route :direct-buffer)
                        (fnn-owner-render-next plan)
                      (let ((answer (fnn-call 'fn-splan-cursor-step plan *fnout-window* nil nil)))
                        (assert (eq (first answer) :ok))
                        (fnn-owner-render-next (second answer))))))
               (assert (= (length octets) *fnout-window*)))))
      (dotimes (i 4) (run))
      (sb-ext:gc :full t)
      (let ((before (sb-ext:get-bytes-consed)))
        (dotimes (i 32) (run))
        (format t "native_newnews_allocation: matched-line route=~s quantum=4096 repeats=32 allocated=~d~%"
                route (- (sb-ext:get-bytes-consed) before))))))

; Actual private stobj and semantic window implementation. These grants only
; exercise buffer ownership, not admission or typed ledger settlement.
(defun fnout-render-list (octets)
  (fnn-owner-render-next (cons octets nil)))
(let* ((*fnn-output-grant* (%make-fnn-output-grant))
       (first (fnout-render-list '(1 2 3 4)))
       (buffer (fnn-output-grant-render-buffer *fnn-output-grant*)))
  (assert (equalp first #(1 2 3 4)))
  (dotimes (i 1024)
    ;; The previous bytes have been consumed before the next render.
    (let ((next (fnout-render-list '(5 6 7 8))))
      (assert (eq next first))
      (assert (eq buffer (fnn-output-grant-render-buffer *fnn-output-grant*)))
      (assert (equalp next #(5 6 7 8)))))
  (let ((short (fnout-render-list '(9 10))))
    (assert (equalp short #(9 10)))
    (assert (not (eq short first)))
    (assert (eq buffer (fnn-output-grant-render-buffer *fnn-output-grant*))))
  (assert (equalp (fnout-render-list '(1 2 3 4 5 6 7 8)) #(1 2 3 4 5 6 7 8)))
  (assert (equalp (fnout-render-list '(11)) #(11))))
(let* ((*fnn-output-grant* nil)
       (first (fnout-render-list '(1 2)))
       (second (fnout-render-list '(3 4))))
  (assert (not (eq first second)))
  (assert (equalp first #(1 2)))
  (assert (equalp second #(3 4))))
(format t "native_newnews_allocation: actual-private-buffer-reuse PASS 1024 same-buffer windows, growth, short suffix, fresh callers~%")

(defun fnout-drain-newnews (archive args quantum)
 (let* ((*fnn-output-grant* (%make-fnn-output-grant))
        (*fnout-window* quantum)
        (result (fnn-core 'fn-nntp-newnews-response-stream nil archive nil args nil nil))
        (plan (fnn-core 'fn-splan-of-effects (cdr result)))
        (output (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
        (steps 0) (cursor-steps 0))
  (loop until (fnn-core 'fn-splan-donep plan) do
   (incf steps)
   (when (> steps 10000) (error "test fixture failed to make progress"))
   (multiple-value-bind (octets rest donep cursorp) (fnn-owner-render-next plan)
    (declare (ignore donep))
    (setf plan rest)
    (if cursorp
        (let ((answer (fnn-call 'fn-splan-cursor-step plan quantum nil nil)))
         (unless (eq (first answer) :ok) (error "actual cursor could not step"))
         (incf cursor-steps) (setf plan (second answer)))
      (loop for octet across octets do (vector-push-extend octet output)))))
  (values output steps cursor-steps)))
(let* ((a (fn-make-article "<a@x>" '(13 10 13 10 65) '("fn.test") '(("fn.test" . 1)) 1 5))
       (b (fn-make-article "<b@x>" '(13 10 13 10 66) '("fn.other") '(("fn.other" . 1)) 2 6))
       (archive (fn-make-state '("fn.g0" "fn.g1" "fn.g2" "fn.test") nil (list b a) 0 nil nil))
       (args (list (fn-nntp-string-octets "fn.test") (fn-nntp-string-octets "20000101") (fn-nntp-string-octets "000000"))))
 (multiple-value-bind (tiny tiny-steps tiny-cur) (fnout-drain-newnews archive args 1)
  (multiple-value-bind (large large-steps large-cur) (fnout-drain-newnews archive args 256)
   (unless (equalp tiny large) (error "actual tiny/large window drain changed reply"))
   (let ((reference (fn-served-reply-octets
                      (cdr (fn-nntp-newnews-response-cat nil archive nil args nil nil)))))
    (unless (equalp tiny (coerce reference '(vector (unsigned-byte 8))))
     (error "actual composed window drain differs from original NEWNEWS reply")))
   (format t "native_newnews_allocation: actual-render-drain octets=~d tiny-steps=~d/~d large-steps=~d/~d~%" (length tiny) tiny-steps tiny-cur large-steps large-cur))))
(format t "native_newnews_allocation_raw: PASS normal actual configured factory, plan, native window drain and matched factory samples~%")
