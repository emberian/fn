;;; Fixed-arity selected compiled boundary. Startup owns installation after
;;; guard/raw-with verification. Each callback is a function object, never an
;;; ACL2_*1* counterpart. Hot calls use a core-carried :ready status, not a
;;; validator. No REST list, APPLY, multiple-value-list, formatting, or lookup.
;;; Caller/representation refinement and condition allocation remain separate
;;; obligations; this file alone does not enable a served family.
(in-package "ACL2")

(defvar *fnn-srt-status* nil)
(defvar *fnn-srt-lpc-begin* nil)
(defvar *fnn-srt-lpc-tick* nil)
(defvar *fnn-srt-spp-begin* nil)
(defvar *fnn-srt-spp-tick* nil)
(defvar *fnn-srt-spp-status* nil)
(defvar *fnn-srt-spp-window-size* nil)
(defvar *fnn-srt-spp-window* nil)
(defvar *fnn-srt-spbc-begin* nil)
(defvar *fnn-srt-spbc-status* nil)
(defvar *fnn-srt-spbc-one* nil)
(defvar *fnn-srt-spbc-finish* nil)
(defvar *fnn-srt-rpin-token* nil)

;;; Installed status kernel is required before any selected operation can be
;;; exposed. Its absence is a startup installation failure, not a hot fallback.
(defmacro fnn-srt-fixed-call (slot carry args)
 `(let ((status (funcall *fnn-srt-status* (not (null ,slot)) ,carry nil)))
    (if (eq status :ready)
        (handler-case (funcall ,slot ,@args)
          (serious-condition () (funcall *fnn-srt-status* t ,carry t)))
        status)))

(defun fnn-selected-lpc-begin (carry handle size pin)
 (fnn-srt-fixed-call *fnn-srt-lpc-begin* carry (handle size pin)))
(defun fnn-selected-lpc-tick (carry cursor fuel arena)
 (fnn-srt-fixed-call *fnn-srt-lpc-tick* carry (cursor fuel arena)))
(defun fnn-selected-spp-begin (carry plan origin resource)
 (fnn-srt-fixed-call *fnn-srt-spp-begin* carry (plan origin resource)))
(defun fnn-selected-spp-tick (carry holder fuel)
 (fnn-srt-fixed-call *fnn-srt-spp-tick* carry (holder fuel)))
(defun fnn-selected-spp-status (carry holder)
 (fnn-srt-fixed-call *fnn-srt-spp-status* carry (holder)))
(defun fnn-selected-spp-window-size (carry holder)
 (fnn-srt-fixed-call *fnn-srt-spp-window-size* carry (holder)))
(defun fnn-selected-spp-window (carry holder window octets)
 (fnn-srt-fixed-call *fnn-srt-spp-window* carry (holder window octets)))
(defun fnn-selected-spbc-begin (carry holder pin fuel)
 (fnn-srt-fixed-call *fnn-srt-spbc-begin* carry (holder pin fuel)))
(defun fnn-selected-spbc-status (carry holder)
 (fnn-srt-fixed-call *fnn-srt-spbc-status* carry (holder)))
(defun fnn-selected-spbc-one (carry holder arena catalog)
 (fnn-srt-fixed-call *fnn-srt-spbc-one* carry (holder arena catalog)))
(defun fnn-selected-spbc-finish (carry holder)
 (fnn-srt-fixed-call *fnn-srt-spbc-finish* carry (holder)))

(defun fnn-selected-rpin-token (carry id owners)
 (fnn-srt-fixed-call *fnn-srt-rpin-token* carry (id owners)))

;;; Startup only. fnn-install-raw-dispatch has already validated raw-with
;;; declarations and carried-entry theorem names in this exact loaded world.
;;; Install function objects from that table; a missing declaration stays NIL.
;;; Primary status is served family; secondary is parser family. A caller
;;; must keep its family unavailable unless its core status is :ready.
(defun fnn-install-selected-runtime ()
 (let* ((world (w *the-live-state*))
        (status-name (find-symbol "FN-SRT-STATUS" "ACL2")))
  (setf *fnn-srt-status*
   (and status-name (fboundp status-name)
        (eq (symbol-class status-name world) :common-lisp-compliant)
        (compiled-function-p (symbol-function status-name))
        (symbol-function status-name)))
  (let ((served-available t) (parser-available t))
   (dolist (binding '((*fnn-srt-lpc-begin* . fn-lpc-begin)
                     (*fnn-srt-lpc-tick* . fn-lpc-tick)
                     (*fnn-srt-spp-begin* . fn-spp-begin)
                     (*fnn-srt-spp-tick* . fn-spp-tick)
                     (*fnn-srt-spp-status* . fn-spp-status)
                     (*fnn-srt-spp-window-size* . fn-spp-window-size)
                     (*fnn-srt-spp-window* . fn-spp-window)
                     (*fnn-srt-spbc-begin* . fn-spbc-begin)
                     (*fnn-srt-spbc-status* . fn-spbc-status)
                     (*fnn-srt-spbc-one* . fn-spbc-one)
                     (*fnn-srt-spbc-finish* . fn-spbc-finish)
                     (*fnn-srt-rpin-token* . fn-rpin-token)))
    (let* ((name (cdr binding)) (raw (gethash name *fnn-raw-dispatch*))
           (callback (and (eq raw name) (fboundp raw)
                          (eq (symbol-class raw world) :common-lisp-compliant)
                          (compiled-function-p (symbol-function raw))
                          (symbol-function raw))))
     (setf (symbol-value (car binding)) callback)
     (unless callback
      (if (member name '(fn-lpc-begin fn-lpc-tick))
          (setf parser-available nil) (setf served-available nil)))))
   (if *fnn-srt-status*
       (values (funcall *fnn-srt-status* served-available :ready nil)
               (funcall *fnn-srt-status* parser-available :ready nil))
       (values nil nil)))))
