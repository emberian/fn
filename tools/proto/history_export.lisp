;;; tools/proto/history_export.lisp -- the store's records, as the native
;;; image's own open decodes them, written for the page store's history
;;; import (lane arena-store-4, 2026-09-28, m4; prototype, never a release).
;;;
;;; Loaded into a native fn image (build/fn-host-developer) before
;;; `(acl2::sbcl-restart)', which it replaces (the pattern of
;;; tools/image_anatomy/entry.lisp): ACL2's restart, the native start-up
;;; checks, then ONE read-only open of FNHX_ROOT (`fnn-open-live-store', the
;;; served open: full replay or checkpoint, ACL2's decode) and, for each
;;; record of the open's extended checkpoint E (`fn-sco-records', the
;;; history every theorem is about), ACL2's `fn-scc-encode' of it, written to
;;; FNHX_OUT as an 8-octet little-endian length and the octets.  The page
;;; store's host (host/native/proto-history-pages.lisp) hands each frame's
;;; octets to ACL2's `fn-scc-decode-tree' (`fn-scc-decode-tree-of-encode'),
;;; so the event the image stores is the event the open decoded.  The frame
;;; length is the one host-computed value here: a transfer between two
;;; prototype images, not a store format.
(in-package "ACL2")

(defun fnhx-export (root out)
  (fnn-open-streams)
  (fnn-crypto-startup) (fnn-tls-reset) (fnn-tls-initialize) (fnn-digest-startup)
  (fnn-hsig-reset) (fnn-hsig-initialize) (fnn-deflate-reset) (fnn-deflate-initialize)
  (let ((t0 (get-internal-real-time)))
    (multiple-value-bind (store count) (fnn-open-live-store root nil)
      (let* ((t-open (/ (- (get-internal-real-time) t0) (float internal-time-units-per-second)))
             (sco (f-get-global 'fn-store-sco-open *the-live-state*))
             (records (fn-sco-records (first sco)))
             (n 0) (octets 0) (bad 0)
             (hdr (make-array 8 :element-type '(unsigned-byte 8))))
        (with-open-file (o out :direction :output :element-type '(unsigned-byte 8)
                               :if-exists :supersede)
          (dolist (ev records)
            (if (not (fn-sccb-treep ev))
                (incf bad)
              (let* ((enc (fn-scc-encode ev))
                     (len (length enc))
                     (v (make-array len :element-type '(unsigned-byte 8) :initial-contents enc)))
                (dotimes (b 8) (setf (aref hdr b) (ldb (byte 8 (* 8 b)) len)))
                (write-sequence hdr o)
                (write-sequence v o)
                (incf n) (incf octets len)))))
        (format t "~&FNHX-JSON {\"event\":\"export\",\"root\":~s,\"open-count\":~d,\"records\":~d,\"exported\":~d,\"not-tree\":~d,\"octets\":~d,\"s-open\":~,1f,\"s-total\":~,1f,\"open-mode\":\"~(~a~)\"}~%"
                root count (length records) n bad octets t-open
                (/ (- (get-internal-real-time) t0) (float internal-time-units-per-second))
                (fnn-store-open-mode store))
        (finish-output)
        (fnn-store-close store)))))

(defun sbcl-restart ()
  (acl2-default-restart)
  (setq *lp-ever-entered-p* t)
  (setq *read-default-float-format* 'double-float)
  (setup-standard-io)
  (push nil *acl2-unwind-protect-stack*)
  (let ((*ld-level* 1) (*readtable* *acl2-readtable*))
    (f-put-global 'ld-level 1 *the-live-state*)
    (f-put-global 'check-invariant-risk t *the-live-state*)
    (handler-case
        (catch 'local-top-level
          (fnhx-export (sb-ext:posix-getenv "FNHX_ROOT") (sb-ext:posix-getenv "FNHX_OUT"))
          (sb-ext:exit :code 0 :abort t))
      (serious-condition (e)
        (format t "~&FNHX-JSON {\"event\":\"error\",\"detail\":~s}~%" (format nil "~a" e))
        (finish-output)
        (sb-ext:exit :code 4 :abort t))))
  (sb-ext:exit :code 1 :abort t))
