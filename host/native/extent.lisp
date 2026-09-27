;;; fn native host: the payload arena's EXTENT realizer (lane arena-offheap-2,
;;; 2026-09-27; PRF-281; design planning/evidence/arena-offheap-2026-09-27.md
;;; section 3).  Loaded after io.lisp by host/native/build.lisp.
;;;
;;; A-DURABLE-EXTENT (books/assumptions.lisp) constrains the realizer
;;; `fn-durable-realize-octet' to answer the durable octet; this file is its
;;; raw definition, the trust boundary's one read path for an extent handle
;;; (books/payload-arena-extent.lisp fn-arena$x-get / -payload call it).
;;;
;;; What the host does, and nothing else: it holds a read-only descriptor per
;;; durable file an extent names (a log segment, registered by the open, never
;;; closed and never reused within the process: an unlinked segment stays
;;; readable through it), preads an entry's protected prefix into a bounded
;;; cache (ACL2's fn-arx-read-cache-entries entries), and asks ACL2 whether the
;;; octets read match the trailer the open recorded (fn-arx-entry-ok).  A
;;; mismatch or a short read is refused by name -- arena-extent-digest,
;;; arena-extent-read -- as a store fault (a recovery event: the store is
;;; fenced); the octet is never answered.  pread, not mmap: portable (Linux,
;;; OpenBSD), no SIGBUS on a zeroed or truncated tail, one copy.

(in-package "ACL2")

(define-condition fnn-extent-fault (fnn-store-fault) ())

(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "fn extent realizer"))
(defvar *fnn-extent-fds* (make-hash-table))   ; file id -> read-only fd
(defvar *fnn-extent-paths* (make-hash-table)) ; file id -> path (diagnostics)
(defvar *fnn-extent-next-id* 1)
(defvar *fnn-extent-cache* nil)               ; ((file eoff . octets) ...), most recent first
(defvar *fnn-extent-stats* (list 0 0 0))      ; hits, misses (preads), refusals

(defun fnn-extent-register (path)
  "A new file id for PATH: a read-only descriptor held for the process's life."
  (let ((fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (let ((id *fnn-extent-next-id*))
        (incf *fnn-extent-next-id*)
        (setf (gethash id *fnn-extent-fds*) fd
              (gethash id *fnn-extent-paths*) path)
        id))))

(defun fnn-extent-pread (fd octets offset)
  "Fill OCTETS from OFFSET of FD; the count read (short at end of file)."
  (let ((n (length octets)) (done 0))
    (loop while (< done n) do
      (let ((got (sb-sys:with-pinned-objects (octets)
                   (sb-alien:alien-funcall
                    (sb-alien:extern-alien "pread"
                                           (function sb-alien:long sb-alien:int
                                                     sb-alien:system-area-pointer
                                                     sb-alien:unsigned-long sb-alien:long))
                    fd (sb-sys:sap+ (sb-sys:vector-sap octets) done) (- n done) (+ offset done)))))
        (cond ((plusp got) (incf done got))
              ((zerop got) (return))
              (t (return)))))
    done))

(defun fnn-extent-entry (file eoff elen trailer)
  "The verified protected prefix of the entry at [EOFF, EOFF+ELEN) of FILE,
from the cache or read and checked by ACL2 (fn-arx-entry-ok)."
  (let ((hit (find-if (lambda (e) (and (eql (first e) file) (eql (second e) eoff)))
                      *fnn-extent-cache*)))
    (if hit
        (progn (incf (first *fnn-extent-stats*))
               (setq *fnn-extent-cache* (cons hit (remove hit *fnn-extent-cache* :test #'eq)))
               (cddr hit))
      (let ((fd (gethash file *fnn-extent-fds*))
            (octets (make-array elen :element-type '(unsigned-byte 8))))
        (incf (second *fnn-extent-stats*))
        (unless fd
          (incf (third *fnn-extent-stats*))
          (error 'fnn-extent-fault
                 :message (format nil "arena-extent-read: no durable file ~a is registered" file)))
        (unless (= (fnn-extent-pread fd octets eoff) elen)
          (incf (third *fnn-extent-stats*))
          (error 'fnn-extent-fault
                 :message (format nil "arena-extent-read: ~a at ~a holds fewer than ~a octets"
                                  (gethash file *fnn-extent-paths*) eoff elen)))
        (unless (eq (fnn-core 'fn-arx-entry-ok (coerce octets 'list) trailer) t)
          (incf (third *fnn-extent-stats*))
          (error 'fnn-extent-fault
                 :message (format nil "arena-extent-digest: the entry at ~a of ~a does not match the trailer the open recorded"
                                  eoff (gethash file *fnn-extent-paths*))))
        (let ((limit (fnn-core 'fn-arx-read-cache-entries)))
          (push (list* file eoff octets) *fnn-extent-cache*)
          (when (> (length *fnn-extent-cache*) limit)
            (setq *fnn-extent-cache* (subseq *fnn-extent-cache* 0 limit))))
        octets))))

;;; The realizer (A-DURABLE-EXTENT's constrained function), raw and *1*.
(defun fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (declare (ignore plen))
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
    (aref (fnn-extent-entry file eoff elen trailer) (+ (- poff eoff) i))))

(defun acl2_*1*_acl2::fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (fn-durable-realize-octet file eoff elen poff plen trailer i))

(defun fnn-extent-reset ()
  "Forget the cache (a store close or a reopen); descriptors stay open."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (setq *fnn-extent-cache* nil)))

(defun fnn-extent-positions (path text unit count)
  "The open's positions for the COUNT records the scan read from the segment
at PATH (read as TEXT): per record (FILE START N TRAILER), FILE this segment's
new realizer id, the rest ACL2's (fn-arx-positions).  A segment whose
positions ACL2 does not answer contributes nil (its records stay resident)."
  (let ((ps (fnn-core 'fn-arx-positions text 0 unit count nil)))
    (if (and (consp ps) (= (length ps) count))
        (let ((file (fnn-extent-register path)))
          (mapcar (lambda (p) (cons file p)) ps))
        (make-list count :initial-element nil))))
