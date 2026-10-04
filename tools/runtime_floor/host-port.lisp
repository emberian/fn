;;; tools/runtime_floor/host-port.lisp -- the one piece of host/native the
;;; replayed store open needs, in portable CL (lane runtime-floor): the payload
;;; arena's extent realizer (host/native/extent.lisp, A-DURABLE-EXTENT).  The
;;; same obligation as the SBCL host's: read the entry's protected prefix and
;;; trailer at [EOFF, EOFF+ELEN+32) of the registered file, have ACL2 check it
;;; (fn-arx-entry-ok-buffer over the fn-octets-rd buffer), answer PLEN octets.
;;; pread becomes file-position + read-sequence; the cache keeps ACL2's bound.
(in-package "ACL2")

(defvar *rp-extent-cache* nil)

(defun rp-extent-entry (file eoff elen)
  (let ((hit (find-if (lambda (e) (and (eql (first e) file) (eql (second e) eoff))) *rp-extent-cache*)))
    (if hit
        (cddr hit)
        (let ((path (or (gethash file *rp-extent-paths*)
                        (error 'rf-acl2-error :what (list :arena-extent-read file))))
              (octets (make-array (+ elen 32) :element-type '(unsigned-byte 8))))
          (with-open-file (in path :element-type '(unsigned-byte 8))
            (file-position in eoff)
            (unless (= (read-sequence octets in) (+ elen 32))
              (error 'rf-acl2-error :what (list :arena-extent-read path eoff))))
          (let ((st (cdr (assoc 'fn-octets-rd *rf-user-stobj-alist*))))
            (setf (svref st 0) octets (svref st 1) elen)
            (unwind-protect
                 (unless (eq (acl2_*1*_acl2::fn-arx-entry-ok-buffer (coerce (subseq octets elen) 'list) st) t)
                   (error 'rf-acl2-error :what (list :arena-extent-digest path eoff)))
              (setf (svref st 1) 0 (svref st 0) (make-array 0 :element-type '(unsigned-byte 8)))))
          (let ((limit (acl2_*1*_acl2::fn-arx-read-cache-entries)))
            (when (plusp limit)
              (push (list* file eoff octets) *rp-extent-cache*)
              (when (> (length *rp-extent-cache*) limit)
                (setq *rp-extent-cache* (subseq *rp-extent-cache* 0 limit)))))
          octets))))

(defun fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (declare (ignore plen trailer))
  (aref (rp-extent-entry file eoff elen) (+ (- poff eoff) i)))

(defun fn-durable-realize-octets (file eoff elen poff plen trailer)
  (declare (ignore trailer))
  (let ((entry (rp-extent-entry file eoff elen)) (start (- poff eoff)))
    (coerce (subseq entry start (+ start plen)) 'list)))
