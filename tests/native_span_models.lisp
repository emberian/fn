;;; The span layer's models for the native article tests (tests/native_article_stream_source.lisp,
;;; tests/native_web_article_producer_raw.lisp), loaded after each harness's prelude defines
;;; fn-cbor-octetp.  The step bodies are the real forms of books/nntp-spans.lisp, read here.
(in-package "ACL2")
(defun unsigned-byte-p (n x) (and (integerp x) (<= 0 x) (< x (expt 2 n))))
(with-open-file (stream "books/nntp-spans.lisp")
  (let ((*package* (find-package "ACL2")))
    (loop for f = (read stream nil :eof) until (eq f :eof)
          when (and (consp f) (member (second f) '(*fn-nsp-block-init* fn-nsp-block-next fn-nsp-block-framedp
                                                   fn-nsp-block-head-end fn-nsp-stuff-step fn-nsp-stuff-final)))
            do (case (car f)
                 (defconst (eval `(defparameter ,@(cdr f))))
                 ((defun defun-inline)
                  (destructuring-bind (name args &rest body) (cdr f)
                    (eval `(defun ,name ,args
                             ,@(remove-if (lambda (x) (and (consp x) (eq (car x) 'declare))) body)))))))))
;; The served path's stobjs.  fn-ast-ws and fn-dss-out are def-buffer stobjs
;; (books/def-buffer.lisp), whose logical value is the octet list; the model is a cell
;; holding that list, each export returning the cell as a stobj export does.
(defstruct (obuf (:conc-name obuf-)) (octets nil))
(defun fn-ast-ws-clear (b) (setf (obuf-octets b) nil) b)
(defun fn-ast-ws-len (b) (length (obuf-octets b)))
(defun fn-ast-ws-append-list (xs b)
  (assert (every #'fn-cbor-octetp xs))
  (setf (obuf-octets b) (append (obuf-octets b) xs)) b)
(defun fn-dss-out-clear (b) (setf (obuf-octets b) nil) b)
(defun fn-dss-out-len (b) (length (obuf-octets b)))
(defun fn-dss-out-get (i b) (nth i (obuf-octets b)))
(defun fn-dss-out-list (b) (copy-list (obuf-octets b)))
(defun fn-dss-out-append-octet (o b)
  (assert (fn-cbor-octetp o))
  (setf (obuf-octets b) (append (obuf-octets b) (list o))) b)
(defun fn-dss-out-truncate (n b)
  (setf (obuf-octets b) (subseq (obuf-octets b) 0 n)) b)
;; A-ARENA-SPAN-INTO: the span appended is the span fn-arena-get-span answers.
(defun fn-arena-get-span (h at n arena) (coerce (subseq (nth h arena) at (+ at n)) 'list))
(defun fn-arena-get-span-into (h at n arena b)
  (setf (obuf-octets b) (append (obuf-octets b) (fn-arena-get-span h at n arena))) b)
;; def-span-scan shapes (books/def-span-scan.lisp): the instances' bodies are the real
;; forms of books/nntp-spans.lisp; the loop around them is the shape's list model
;; (fn-dss-fold-list, fn-dss-stream-list), which that book proves equal to the stobj
;; loop (fn-dss-fold-is-list, fn-dss-stream-is-list).
(defun fn-nsp-frame-block (acc i end b)
  (dolist (o (subseq (obuf-octets b) i end) acc) (setq acc (fn-nsp-block-next acc o))))
(defun fn-nsp-stuff (s i end last cap in out)
  (let ((room (max 0 (- cap (fn-dss-out-len out)))) (xs (subseq (obuf-octets in) i end)) (emitted nil))
    (flet ((finish (word s2 n)
             (setf (obuf-octets out) (append (obuf-octets out) (reverse emitted)))
             (values word s2 (+ i n) out)))
      (when (< room 3) (return-from fn-nsp-stuff (values :no-room s i out)))
      (loop for n from 0 for o in xs do
        (when (< room 2) (return-from fn-nsp-stuff (finish :need-output s n)))
        (multiple-value-bind (s2 k w sig) (fn-nsp-stuff-step s o)
          (when (eql sig 2) (return-from fn-nsp-stuff (finish :refused s2 n)))
          (loop repeat k do (push (ldb (byte 8 0) w) emitted) (setq w (ash w -8)))
          (decf room k) (setq s s2)
          (when (eql sig 1) (return-from fn-nsp-stuff (finish :yield s (1+ n))))))
      (cond ((not last) (finish :need-input s (length xs)))
            ((< room 3) (finish :need-output s (length xs)))
            (t (multiple-value-bind (s2 k w sig) (fn-nsp-stuff-final s)
                 (if (eql sig 2) (finish :refused s2 (length xs))
                   (progn (loop repeat k do (push (ldb (byte 8 0) w) emitted) (setq w (ash w -8)))
                          (finish :done s2 (length xs))))))))))
