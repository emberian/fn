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
;;; durable file an extent names (a log segment or an installed checkpoint;
;;; an id is never reused within the process and an unlinked file stays
;;; readable through its descriptor until the file is RETIRED and ACL2's close
;;; decision names it: see the end of this file), preads an entry's protected prefix into a bounded
;;; cache (ACL2's fn-arx-read-cache-entries entries) with the entry's trailer,
;;; and asks ACL2 whether the prefix's frame digest is that trailer, over its
;;; own octet buffer (fn-arx-entry-ok-buffer, books/payload-extent-read.lisp).  A
;;; mismatch or a short read is refused by name -- arena-extent-digest,
;;; arena-extent-read -- as a store fault (a recovery event: the store is
;;; fenced); the octet is never answered.  pread, not mmap: portable (Linux,
;;; OpenBSD), no SIGBUS on a zeroed or truncated tail, one copy.

(in-package "ACL2")

(define-condition fnn-extent-fault (fnn-store-fault) ())

(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "fn extent realizer"))
(defvar *fnn-extent-fds* (make-hash-table))   ; guarded-by: *fnn-extent-lock* (file id -> fd)
(defvar *fnn-extent-paths* (make-hash-table)) ; guarded-by: *fnn-extent-lock* (file id -> path)
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

(defun fnn-extent-cache-limit ()
  "ACL2's bound on the verified entries the realizer keeps
(fn-arx-read-cache-entries); 0 on a developer image started with
FN_NATIVE_EXTENT_CACHE_TEST_OFF=1 (the matched measurement's cache-off arm)."
  (if (equal (fnn-developer-selector "FN_NATIVE_EXTENT_CACHE_TEST_OFF") "1")
      0
    (fnn-core 'fn-arx-read-cache-entries)))

(defvar *fnn-octets-rd* nil)

(defun fnn-live-octets-rd ()
  (or *fnn-octets-rd*
      (setq *fnn-octets-rd*
            (or (cdr (assoc 'fn-octets-rd (user-stobj-alist *the-live-state*)))
                (fnn-fault "the realizer's buffer stobj is not in this image")))))

(defun fnn-extent-entry-ok (octets elen)
  "ACL2's check of the entry read into OCTETS (its protected prefix, ELEN
octets, then its 32-octet trailer): the realizer's own buffer fn-octets-rd
holds the prefix in place (its array is OCTETS, its fill ELEN) and
fn-arx-entry-ok-buffer (books/payload-extent-read.lisp, KEYSTONE
fn-arx-entry-ok-buffer-is-the-frame-check) compares the frame digest of the
buffer, read by index, with the trailer.  Called with the realizer's lock
held; the buffer lets go of OCTETS afterwards."
  (let ((st (fnn-live-octets-rd)))
    (setf (svref st 0) octets
          (svref st 1) elen)
    (unwind-protect
         (first (fnn-call 'fn-arx-entry-ok-buffer (coerce (subseq octets elen) 'list) st))
      (setf (svref st 1) 0
            (svref st 0) (make-array 0 :element-type '(unsigned-byte 8))))))

(defun fnn-extent-entry (file eoff elen trailer)
  (declare (ignore trailer))
  "The verified protected prefix of the entry at [EOFF, EOFF+ELEN) of FILE,
from the cache or read once (one pread of the prefix and its trailer) and
checked by ACL2 (fnn-extent-entry-ok).  Called with the realizer's lock held."
  (let ((hit (find-if (lambda (e) (and (eql (first e) file) (eql (second e) eoff)))
                      *fnn-extent-cache*)))
    (if hit
        (progn (incf (first *fnn-extent-stats*))
               (unless (eq hit (first *fnn-extent-cache*))
                 (setq *fnn-extent-cache* (cons hit (delete hit *fnn-extent-cache* :test #'eq))))
               (cddr hit))
      (let ((fd (gethash file *fnn-extent-fds*))
            (octets (make-array (+ elen 32) :element-type '(unsigned-byte 8))))
        (incf (second *fnn-extent-stats*))
        (unless fd
          (incf (third *fnn-extent-stats*))
          (error 'fnn-extent-fault
                 :message (format nil "arena-extent-read: no durable file ~a is registered" file)))
        (unless (= (fnn-extent-pread fd octets eoff) (+ elen 32))
          (incf (third *fnn-extent-stats*))
          (error 'fnn-extent-fault
                 :message (format nil "arena-extent-read: ~a at ~a holds fewer than ~a octets"
                                  (gethash file *fnn-extent-paths*) eoff (+ elen 32))))
        (unless (eq (fnn-extent-entry-ok octets elen) t)
          (incf (third *fnn-extent-stats*))
          (error 'fnn-extent-fault
                 :message (format nil "arena-extent-digest: the entry at ~a of ~a does not match its trailer"
                                  eoff (gethash file *fnn-extent-paths*))))
        (let ((limit (fnn-extent-cache-limit)))
          (when (plusp limit)
            (push (list* file eoff octets) *fnn-extent-cache*)
            (when (> (length *fnn-extent-cache*) limit)
              (setq *fnn-extent-cache* (subseq *fnn-extent-cache* 0 limit)))))
        octets))))

;;; The realizer (A-DURABLE-EXTENT's constrained function), raw and *1*.
(defun fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (declare (ignore plen))
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
    (aref (fnn-extent-entry file eoff elen trailer) (+ (- poff eoff) i))))

(defun acl2_*1*_acl2::fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (fn-durable-realize-octet file eoff elen poff plen trailer i))

;;; The whole payload in one call (fn-durable-realize-octets): one lock, one
;;; cache lookup or one pread and one trailer check, one list of PLEN octets
;;; built from the verified buffer.
(defun fn-durable-realize-octets (file eoff elen poff plen trailer)
  (let ((entry (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                 (fnn-extent-entry file eoff elen trailer)))
        (start (- poff eoff))
        (acc nil))
    (declare (type (simple-array (unsigned-byte 8) (*)) entry)
             (type fixnum start plen))
    (loop for i of-type fixnum from (+ start plen -1) downto start do
      (push (aref entry i) acc))
    acc))

(defun acl2_*1*_acl2::fn-durable-realize-octets (file eoff elen poff plen trailer)
  (fn-durable-realize-octets file eoff elen poff plen trailer))

;;; A-DURABLE-LZ (books/assumptions.lisp; lane compression-extents, PRF-326):
;;; the realizer of a COMPRESSED extent.  It reads the block C through the
;;; extent realizer above (the entry's trailer checked by ACL2), runs ACL2's
;;; DEFLATE payload decoder over it (host/native/deflate.lisp fnn-pzd-decode:
;;; fn-zpl-decode-bufs over pooled buffers; KEYSTONE
;;; fn-zpl-decode-bufs-is-the-lz-value, books/deflate-pool.lisp: an :ok
;;; answer is the value the constraint names) and answers ACL2's octets.  A decode that fails is
;;; refused by name (arena-extent-lz-decode, a store fault: a recovery
;;; event) and nothing is answered.  One decoded payload is kept (the last
;;; one read) so a reader that reads octet by octet (fn-arena$x-get) decodes
;;; once; the key includes the dictionary's identity (EQ: one shared list
;;; per dictionary).
(defvar *fnn-extent-lz-last* nil)             ; (key dict . octets)

(defun fn-durable-realize-lz (file eoff elen poff plen trailer n dict)
  (let* ((key (list file eoff poff plen n))
         (hit (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                (let ((last *fnn-extent-lz-last*))
                  (and last (equal (first last) key) (eq (second last) dict)
                       (cddr last))))))
    (or hit
        (let* ((c (fn-durable-realize-octets file eoff elen poff plen trailer))
               (r (funcall 'fnn-pzd-decode dict c n)))
          (unless (and (consp r) (eq (first r) :ok) (eql (length (rest r)) n))
            ;; The path is read under the lock that guards the table: another
            ;; thread may be registering a file (fnn-extent-register).
            (let ((path (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                          (incf (third *fnn-extent-stats*))
                          (gethash file *fnn-extent-paths*))))
              (error 'fnn-extent-fault
                     :message (format nil "arena-extent-lz-decode: the block at ~a of ~a does not decode to its ~a octets"
                                      poff path n))))
          (let ((octets (rest r)))
            (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
              (setq *fnn-extent-lz-last* (list* key dict octets)))
            octets)))))

(defun acl2_*1*_acl2::fn-durable-realize-lz (file eoff elen poff plen trailer n dict)
  (fn-durable-realize-lz file eoff elen poff plen trailer n dict))

;;; A-ARENA-STORED (books/assumptions-stored.lisp; lane compress-5, NNT-055):
;;; handle H's payload AS IT IS STORED, for XFN-ZARTICLE
;;; (books/nntp-zarticle.lisp fn-zar-stored).  The live fn-arena is the
;;; concrete arena of books/payload-arena-extent.lisp; EXT[H] names H's
;;; extent.  For a COMPRESSED extent (FILE EOFF ELEN POFF PLEN TRAILER N
;;; DICT) the answer is (DICT C N), C the block's durable octets read through
;;; the extent realizer above (one pread, ACL2's trailer check); nothing is
;;; decoded.  Any other handle (resident, staged, a plain extent, past the
;;; array) answers NIL, and ACL2 then answers as ARTICLE does.
(defun fn-arena-stored (h fn-arena)
  (let ((e (and (integerp h) (<= 0 h)
                (< h (fn-arena$x-ext-length fn-arena))
                (fn-arena$x-exti h fn-arena))))
    (if (fn-arn-lz-extentp e)
        (list (nth 7 e)
              (fn-durable-realize-octets (nth 0 e) (nth 1 e) (nth 2 e)
                                         (nth 3 e) (nth 4 e) (nth 5 e))
              (nth 6 e))
      nil)))

(defun acl2_*1*_acl2::fn-arena-stored (h fn-arena)
  (fn-arena-stored h fn-arena))

;;; A-PGS-HOST-IO's page fill (books/assumptions.lisp `fn-pgs-fill-realize';
;;; lane arena-store-7, 2026-09-28): the 2048 little-endian u64 words page
;;; ADDR of the page file FILE holds, FILE a file id from
;;; `fnn-extent-register'.  One pread of the 16 KiB page; a short read or an
;;; unknown file is refused by name (history-page-read: a store fault, a
;;; recovery event), never answered with made-up words.  Whether the words
;;; are the page the committed table names is ACL2's digest check
;;; (books/history-records-disk.lisp: the lazy decode of the committed
;;; history image `fn-hrs-disk-history', and fn-hrecs's retry loop).
(defun fn-pgs-fill-realize (file addr)
  (let ((fd (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
              (gethash file *fnn-extent-fds*)))
        (octets (make-array 16384 :element-type '(unsigned-byte 8))))
    (unless (and fd (integerp addr) (<= 0 addr))
      (error 'fnn-extent-fault
             :message (format nil "history-page-read: no page file ~a (page ~a)" file addr)))
    (let ((got (fnn-extent-pread fd octets (* addr 16384))))
      (unless (= got 16384)
        (let ((path (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                      (gethash file *fnn-extent-paths*))))
          (error 'fnn-extent-fault
                 :message (format nil "history-page-read: page ~a of ~a: ~a of 16384 octets"
                                  addr path got)))))
    (let ((acc nil))
      (declare (type (simple-array (unsigned-byte 8) (16384)) octets))
      (loop for k of-type fixnum from 2047 downto 0 do
        (let ((w 0) (base (* 8 k)))
          (loop for b of-type fixnum from 7 downto 0 do
            (setq w (logior (ash w 8) (aref octets (+ base b)))))
          (push w acc)))
      acc)))

(defun acl2_*1*_acl2::fn-pgs-fill-realize (file addr)
  (fn-pgs-fill-realize file addr))

;;; Online disk release (lane online-reclaim-2, row Q16, PRF-930;
;;; books/extent-retire.lisp).  A descriptor is no longer held for the
;;; process's life: once a checkpoint publication has reseated the live
;;; payloads at the installed checkpoint's frames, the files it dropped (the
;;; covered log segments, the previous checkpoint) are RETIRED, and a retired
;;; file's descriptor is closed when ACL2's close decision names it
;;; (fn-xrt-close-set: a clean scan of the extent column, no log member in
;;; flight naming it, no off-mutex arena reader).  Closing the last
;;; descriptor of an unlinked file gives its blocks back while the owner
;;; serves.  host/native/owner.lisp fnn-owner-release-extents drives it.

(defvar *fnn-extent-retired* nil)
;; guarded-by: the owner mutex (file ids waiting for their close)
(defvar *fnn-extent-checkpoint-id* nil)
;; guarded-by: the owner mutex (the realizer id of the installed checkpoint
;; the last reseat pointed payloads at)

(defun fnn-extent-ids-of-paths (paths)
  "The registered file ids whose path is one of PATHS."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((ids nil))
      (maphash (lambda (id path) (when (member path paths :test #'equal) (push id ids)))
               *fnn-extent-paths*)
      (sort ids #'<))))

(defun fnn-extent-close (ids)
  "Close the descriptors of IDS (ACL2's close set) and forget every cached
entry of them.  Answers the count closed."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((closed 0))
      (dolist (id ids)
        (let ((fd (gethash id *fnn-extent-fds*)))
          (remhash id *fnn-extent-fds*)
          (remhash id *fnn-extent-paths*)
          (when fd
            (fnn-close fd)
            (incf closed))))
      (setq *fnn-extent-cache*
            (remove-if (lambda (e) (member (first e) ids)) *fnn-extent-cache*))
      (when (and *fnn-extent-lz-last* (member (first (first *fnn-extent-lz-last*)) ids))
        (setq *fnn-extent-lz-last* nil))
      closed)))

(defun fnn-extent-open-count ()
  "The descriptors the realizer holds (the natives' observation)."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (hash-table-count *fnn-extent-fds*)))
