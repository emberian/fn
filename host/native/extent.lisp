;;; fn native host: the payload arena's EXTENT realizer (lane arena-offheap-2,
;;; 2026-09-27; PRF-281; design planning/evidence/arena-offheap-2026-09-27.md
;;; section 3; identity: lane extent-identity, 2026-09-29, PRF-994).  Loaded
;;; after io.lisp by host/native/build.lisp.
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
;;; decision names it: see the end of this file), preads an entry's protected
;;; prefix and its trailer into a bounded cache (ACL2's
;;; fn-arx-read-cache-entries entries), and asks ACL2 for the VERDICT of that
;;; read against the descriptor's commitment (fn-arx-entry-verdict-buffer,
;;; books/payload-extent-read.lisp, over its own octet buffer fn-octets-rd):
;;; the trailer recorded after the prefix must be the descriptor's trailer
;;; (KEYSTONE fn-arx-entry-verdict-buffer-ok-is-the-commitment) and the
;;; prefix's frame digest must be that trailer.  Each verdict but :ok is
;;; refused by name -- arena-extent-trailer (the recorded trailer is not the
;;; descriptor's: another well-formed entry at this offset, a wrong offset,
;;; an entry of another store or generation), arena-extent-digest (the
;;; prefix's digest is not its trailer), arena-extent-read (no file, a short
;;; read) -- as a store fault (a recovery event: the store is fenced); the
;;; octet is never answered.  pread, not mmap: portable (Linux, OpenBSD), no
;;; SIGBUS on a zeroed or truncated tail, one copy.
;;;
;;; IDENTITY.  A cached entry is keyed by the whole descriptor identity --
;;; the file id, the prefix's offset and length and the expected trailer --
;;; and a hit answers only a read that was verified under exactly that
;;; identity.  The file id is this process's name for one durable INCARNATION
;;; of a file: the (device, inode) pair `fnn-extent-register' records from the
;;; descriptor it opened, never reused within the process, dropped (with every
;;; cached entry of it) by `fnn-extent-close'.  It is never persisted: every
;;; descriptor is re-derived at the open from the file the open itself read
;;; and checked, so no process-local id crosses a restart, and the identity
;;; that does cross a restart is the commitment (the entry's trailer, which
;;; the open's chain check established).  A transient OS descriptor number is
;;; not an identity here: it is looked up under the id, never compared.

(in-package "ACL2")

(define-condition fnn-extent-fault (fnn-store-fault) ())

(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "fn extent realizer"))
(defvar *fnn-extent-fds* (make-hash-table))   ; guarded-by: *fnn-extent-lock* (file id -> fd)
(defvar *fnn-extent-paths* (make-hash-table)) ; guarded-by: *fnn-extent-lock* (file id -> path)
(defvar *fnn-extent-incarnations* (make-hash-table))
;; guarded-by: *fnn-extent-lock* (file id -> (device . inode) of the file opened)
(defvar *fnn-extent-bases* (make-hash-table)) ; guarded-by: *fnn-extent-lock* (file id -> page 0's offset)
(defvar *fnn-extent-next-id* nil)
(defvar *fnn-extent-cache* nil)
;; ((file eoff elen trailer . octets) ...), most recent first: the verified
;; entries, each under the descriptor identity it was verified for
(defvar *fnn-extent-stats* (list 0 0 0))      ; hits, misses (preads), refusals
(defvar *fnn-extent-issued-next* 0)
(defvar *fnn-extent-issued* (make-hash-table :test #'equal))
;; guarded-by: *fnn-extent-lock*. Token -> ACL2 ownership row (PRF-1057).
;; Removed only by actual worker completion, never a request's timeout.

(defun fnn-extent-register (path)
  "Reserve ACL2's fresh incarnation name before opening PATH. Failed opens
spend the name; an OS descriptor number can never become its identity."
  (let ((id nil))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (destructuring-bind (word next issued)
          (fnn-call 'fn-pio-file-issue *fnn-extent-next-id*)
        (unless (eq word :issued) (fnn-fault "invalid extent incarnation allocator"))
        (setf *fnn-extent-next-id* next id issued)))
    ;; Resource reservation will precede this open too; it must run while
    ;; the pool's carried state is serialized, without owner/extent inversion.
    (let ((fd nil) (installed nil))
      (unwind-protect
           (progn
             (setq fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+)))
             (let* ((st (fnn-fstat fd))
                    (incarnation (cons (sb-posix:stat-dev st) (sb-posix:stat-ino st))))
               (sb-thread:with-mutex (*fnn-extent-lock*)
                 (setf (gethash id *fnn-extent-fds*) fd
                       (gethash id *fnn-extent-paths*) path
                       (gethash id *fnn-extent-incarnations*) incarnation
                       installed t)))
             id)
        (when (and fd (not installed)) (fnn-close fd))))))

(defun fnn-extent-incarnation (file)
  "The (device . inode) file id FILE opened, or NIL.  Called with the
realizer's lock held."
  (gethash file *fnn-extent-incarnations*))

(defun fnn-extent-where (file eoff)
  "The refusal's naming of the entry at EOFF of FILE: its path and durable
incarnation.  Called with the realizer's lock held."
  (let ((inc (fnn-extent-incarnation file)))
    (format nil "~a (file ~a~@[, dev ~a ino ~a~]) at ~a"
            (gethash file *fnn-extent-paths*) file (car inc) (cdr inc) eoff)))

(defun fnn-extent-register-at (path base)
  "A new file id for PATH whose page A the page fill reads at BASE + 16 KiB * A
(the history image region of the state checkpoint's file: books/history-image-
snapshot.lisp); a read-only descriptor held for the process's life, so the
file stays readable after a later checkpoint replaces its name."
  (let ((id (fnn-extent-register path)))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (setf (gethash id *fnn-extent-bases*) base))
    id))

(defun fnn-extent-pread (fd octets offset)
  "Fill OCTETS from OFFSET of FD; the count read (short at end of file)."
  ;; Developer image only (lane composed-owner-3, row A4): a stalled read
  ;; device.  While the named file exists a pread does not return, as a read
  ;; from a device under maintenance does not (tests/test_native_slow_disk.py).
  (let ((stall (fnn-developer-selector "FN_NATIVE_TEST_READ_STALL_FILE")))
    (when (and stall (plusp (length stall)))
      (loop while (probe-file stall) do (sleep 0.05))))
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

(defmacro fnn-with-octets-rd ((st octets fill) &body body)
  "BODY with the realizer's buffer ST holding OCTETS (its array) at FILL;
the buffer lets go of OCTETS afterwards.  Called with the realizer's lock
held."
  `(let ((,st (fnn-live-octets-rd)))
     (setf (svref ,st 0) ,octets
           (svref ,st 1) ,fill)
     (unwind-protect
          (progn ,@body)
       (setf (svref ,st 1) 0
             (svref ,st 0) (make-array 0 :element-type '(unsigned-byte 8))))))

(defun fnn-extent-entry-verdict (octets elen trailer)
  "ACL2's verdict of the entry read into OCTETS (its protected prefix, ELEN
octets, then its 32-octet trailer) against the descriptor's expected
TRAILER: the realizer's own buffer fn-octets-rd holds the prefix in place
(its array is OCTETS, its fill ELEN) and fn-arx-entry-verdict-buffer
(books/payload-extent-read.lisp, KEYSTONE
fn-arx-entry-verdict-buffer-ok-is-the-commitment) answers :ok, :trailer or
:digest.  Called with the realizer's lock held."
  (fnn-with-octets-rd (st octets elen)
    (first (fnn-call 'fn-arx-entry-verdict-buffer trailer (coerce (subseq octets elen) 'list) st))))

(defun fnn-extent-entry-ok (octets elen)
  "ACL2's self-consistency check of the entry read into OCTETS (its
protected prefix, ELEN octets, then its 32-octet trailer):
fn-arx-entry-ok-buffer (books/payload-extent-read.lisp, KEYSTONE
fn-arx-entry-ok-buffer-is-the-frame-check) compares the frame digest of the
prefix with the trailer read after it.  For a read that has no descriptor
yet (fnn-extent-entry-fresh); a read of an accepted extent is decided
against the descriptor's trailer by fnn-extent-entry-verdict.  Called with
the realizer's lock held."
  (fnn-with-octets-rd (st octets elen)
    (first (fnn-call 'fn-arx-entry-ok-buffer (coerce (subseq octets elen) 'list) st))))

(defun fnn-extent-read-entry (file eoff elen)
  "One pread of the entry at [EOFF, EOFF+ELEN+32) of FILE into a fresh
array; refused by name (arena-extent-read) when no such file is registered
or the file holds fewer octets.  Called with the realizer's lock held."
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
             :message (format nil "arena-extent-read: ~a holds fewer than ~a octets"
                              (fnn-extent-where file eoff) (+ elen 32))))
    octets))

;;; Row A4 (option (c), lane composed-owner-3; books/owner-cold-line.lisp):
;;; the served read span runs with *fnn-extent-no-io* bound true (host/native/
;;; owner.lisp fnn-owner-chunk-span-no-io).  A miss then reads nothing: it
;;; THROWS the entry it needs to the tag fnn-extent-cold (a throw, not a
;;; condition: fnn-call turns every condition into a store fault), the span (pure over its
;;; stobjs) is discarded, and the host reads the entry OUTSIDE the owner mutex
;;; (fnn-extent-prefetch) within ACL2's dependency deadline
;;; (fn-otb-dependency-step).  A hit is a hit either way: the warm path does
;;; no more work than before.  With a cache limit of 0 nothing a prefetch
;;; reads is kept, so the no-I/O mode is never used (fnn-extent-no-io-usable-p).
(defvar *fnn-extent-no-io* nil)

(defun fnn-extent-no-io-usable-p ()
  (plusp (fnn-extent-cache-limit)))

(defun fnn-extent-entry (file eoff elen trailer)
  "The verified entry (its protected prefix at [EOFF, EOFF+ELEN) of FILE
and its trailer) of the descriptor whose expected trailer is TRAILER, from
the cache under that identity or read once and decided by ACL2 against it
(fnn-extent-entry-verdict); every verdict but :ok is refused by name.
Called with the realizer's lock held."
  (let ((hit (find-if (lambda (e) (and (eql (first e) file) (eql (second e) eoff)
                                       (eql (third e) elen) (eql (fourth e) trailer)))
                      *fnn-extent-cache*)))
    (if hit
        (progn (incf (first *fnn-extent-stats*))
               (unless (eq hit (first *fnn-extent-cache*))
                 (setq *fnn-extent-cache* (cons hit (delete hit *fnn-extent-cache* :test #'eq))))
               (cddddr hit))
      (let* ((octets (if *fnn-extent-no-io*
                         (throw 'fnn-extent-cold (list file eoff elen trailer))
                         (fnn-extent-read-entry file eoff elen)))
             (verdict (fnn-extent-entry-verdict octets elen trailer)))
        (unless (eq verdict :ok)
          (incf (third *fnn-extent-stats*))
          (error 'fnn-extent-fault
                 :message
                 (case verdict
                   (:trailer
                    (format nil "arena-extent-trailer: the entry at ~a is not the extent's: its recorded trailer is not the descriptor's"
                            (fnn-extent-where file eoff)))
                   (:digest
                    (format nil "arena-extent-digest: the entry at ~a does not match its trailer"
                            (fnn-extent-where file eoff)))
                   (t
                    (format nil "arena-extent-verdict: ACL2 answered ~s for the entry at ~a"
                            verdict (fnn-extent-where file eoff))))))
        (let ((limit (fnn-extent-cache-limit)))
          (when (plusp limit)
            (push (list* file eoff elen trailer octets) *fnn-extent-cache*)
            (when (> (length *fnn-extent-cache*) limit)
              (setq *fnn-extent-cache* (subseq *fnn-extent-cache* 0 limit)))))
        octets))))

(defun fnn-extent-entry-fresh (file eoff elen)
  "The entry at [EOFF, EOFF+ELEN+32) of FILE read once for a descriptor not
yet made (the publication's reseat, host/native/owner.lisp
fnn-owner-release-extents: ACL2 then compares the frame's payloads with the
arena's and makes the descriptors from the frame's own trailer,
books/extent-retire.lisp fn-xrt-reseat-one), self-consistency checked by
ACL2 (fnn-extent-entry-ok) and refused by name otherwise; never cached (a
cache entry needs the identity a descriptor gives it).  Called with the
realizer's lock held."
  (let ((octets (fnn-extent-read-entry file eoff elen)))
    (unless (eq (fnn-extent-entry-ok octets elen) t)
      (incf (third *fnn-extent-stats*))
      (error 'fnn-extent-fault
             :message (format nil "arena-extent-digest: the entry at ~a does not match its trailer"
                              (fnn-extent-where file eoff))))
    octets))

;;; The entry a cold span needs, read into the cache (a store fault is
;;; signalled as always: the caller re-signals it in the owner's thread).
;;; Called OFF the owner mutex, from a thread of its own.  The pread runs
;;; WITHOUT the realizer's lock, so a stalled disk holds only this thread:
;;; cached reads on every other connection proceed (the lock is taken to find
;;; the descriptor, and again to decide the entry -- ACL2's verdict uses the
;;; realizer's one buffer -- and keep it).  The entry is decided against the
;;; descriptor's TRAILER (fnn-extent-entry-verdict) and cached under that
;;; identity, exactly as fnn-extent-entry decides and caches it.
(defun fnn-extent-issue-read (cid file eoff elen trailer)
  "Acquire the cold worker's ownership BEFORE launching it. NIL means warm."
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
    (when (find-if (lambda (e) (and (eql (first e) file) (eql (second e) eoff)
                                   (eql (third e) elen) (eql (fourth e) trailer)))
                  *fnn-extent-cache*)
      (return-from fnn-extent-issue-read nil))
    (unless (gethash file *fnn-extent-fds*)
      (error 'fnn-extent-fault
             :message (format nil "arena-extent-read: no durable file ~a is registered" file)))
    (destructuring-bind (next row)
        (fnn-call 'fn-pio-issue *fnn-extent-issued-next* cid file eoff elen trailer)
      (let ((token (fnn-core 'fn-pio-token row)))
        (setf *fnn-extent-issued-next* next (gethash token *fnn-extent-issued*) row)
        token))))

(defun fnn-extent-cancel-read (token)
  "Revoke this request's publication right; the worker still owns its fd."
  (when token
    (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
      (let ((row (gethash token *fnn-extent-issued*)))
        (when row
          (setf (gethash token *fnn-extent-issued*) (fnn-core 'fn-pio-cancel row token))
          (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
            (fnn-err "PAGE-IO cancelled token=~s" token)))))))

(defun fnn-extent-complete-read (token verdict)
  "ACL2's completion decision, with the extent lock held. Only actual I/O
settlement calls this. A missing/stale token has no publish or release."
  (destructuring-bind (row answer)
      (fnn-call 'fn-pio-complete (gethash token *fnn-extent-issued*) token verdict)
    (unless (eq answer :stale)
      (setf (gethash token *fnn-extent-issued*) row)
      (remhash token *fnn-extent-issued*))
    answer))

(defun fnn-extent-prefetch (token)
  "Read and verify TOKEN, off owner mutex. Return its private verified result;
only an owner observation of actual worker death may settle/publish/refund."
  (unless token (return-from fnn-extent-prefetch (list :ok nil)))
  (destructuring-bind (id cid file eoff elen trailer) token
    (declare (ignore id cid))
    (let ((fd nil)
          (octets (make-array (+ elen 32) :element-type '(unsigned-byte 8)))
          (hold (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD"))
          (mode (fnn-developer-selector "FN_NATIVE_PAGE_IO_RESULT")))
      (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
        (setq fd (gethash file *fnn-extent-fds*))
        (incf (second *fnn-extent-stats*)))
      (unless fd
        (error 'fnn-extent-fault :message "arena-extent-read: issued file closed"))
      (when (and hold (plusp (length hold)) (not (probe-file hold)))
        (fnn-err "PAGE-IO held token=~s file=~d" token file)
        (loop until (probe-file hold) do (sleep 0.05)))
      (when (equal mode "error")
        (error 'fnn-extent-fault :message "arena-extent-read: injected pread error"))
      (let ((got (if (equal mode "short") 0 (fnn-extent-pread fd octets eoff))))
        (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
          (list (if (= got (+ elen 32))
                    (fnn-extent-entry-verdict octets elen trailer) :read)
                octets))))))

;;; The realizer (A-DURABLE-EXTENT's constrained function), raw and *1*.
;;; The descriptor's guard (books/payload-arena-extent-logic.lisp
;;; fn-arn-extent-guardp: EOFF <= POFF, POFF+PLEN <= EOFF+ELEN) places the
;;; payload slice inside the verified prefix; the arena's invariant
;;; (fn-arena$x-wfp) carries it to every call.
(defun fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (declare (ignore plen))
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
    (aref (fnn-extent-entry file eoff elen trailer) (+ (- poff eoff) i))))

(defun acl2_*1*_acl2::fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (fn-durable-realize-octet file eoff elen poff plen trailer i))

;;; The whole payload in one call (fn-durable-realize-octets): one lock, one
;;; cache lookup or one pread and one verdict, one list of PLEN octets built
;;; from the verified buffer.
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
;;; extent realizer above (the entry decided by ACL2 against the
;;; descriptor's trailer), runs ACL2's DEFLATE payload decoder over it
;;; (host/native/deflate.lisp fnn-pzd-decode: fn-zpl-decode-bufs over pooled
;;; buffers; KEYSTONE fn-zpl-decode-bufs-is-the-lz-value,
;;; books/deflate-pool.lisp: an :ok answer is the value the constraint names)
;;; and answers ACL2's octets.  A decode that fails is refused by name
;;; (arena-extent-lz-decode, a store fault: a recovery event) and nothing is
;;; answered.  One decoded payload is kept (the last one read) so a reader
;;; that reads octet by octet (fn-arena$x-get) decodes once; the key is the
;;; whole descriptor identity (file, entry, expected trailer, block, length)
;;; and the dictionary's identity (EQ: one shared list per dictionary).
(defvar *fnn-extent-lz-last* nil)             ; (key dict . octets)

(defun fn-durable-realize-lz (file eoff elen poff plen trailer n dict)
  (let* ((key (list file eoff elen trailer poff plen n))
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
            (let ((where (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                           (incf (third *fnn-extent-stats*))
                           (fnn-extent-where file poff))))
              (error 'fnn-extent-fault
                     :message (format nil "arena-extent-lz-decode: the block at ~a does not decode to its ~a octets"
                                      where n))))
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
  (multiple-value-bind (fd base)
      (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
        (values (gethash file *fnn-extent-fds*) (gethash file *fnn-extent-bases* 0)))
   (let ((octets (make-array 16384 :element-type '(unsigned-byte 8))))
    (unless (and fd (integerp addr) (<= 0 addr))
      (error 'fnn-extent-fault
             :message (format nil "history-page-read: no page file ~a (page ~a)" file addr)))
    (let ((got (fnn-extent-pread fd octets (+ base (* addr 16384)))))
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
      acc))))

(defun acl2_*1*_acl2::fn-pgs-fill-realize (file addr)
  (fn-pgs-fill-realize file addr))

;;; Online disk release (lane online-reclaim-2, row Q16, PRF-930;
;;; books/extent-retire.lisp).  A descriptor is no longer held for the
;;; process's life: once a checkpoint publication has reseated the live
;;; payloads at the installed checkpoint's frames, the files it dropped (the
;;; covered log segments, the previous checkpoint) are RETIRED, and a retired
;;; file waits until ACL2 finds it quiet (fn-xrt-quiet-files: its count in
;;; the arena's file column is 0 and no log member in flight names it), is
;;; then pending at the arena-reader generation stamped there, and its
;;; descriptor closes once no off-mutex arena reader pinned at or below that
;;; stamp still runs (fnn-arena-clear-p, books/arena-reader-pins.lisp).
;;; Closing the last descriptor of an unlinked file gives its blocks back
;;; while the owner serves.  host/native/owner.lisp fnn-owner-release-extents
;;; drives it.

(defvar *fnn-extent-retired* nil)
;; guarded-by: the owner mutex (file ids not yet found quiet)
(defvar *fnn-extent-pending* nil)
;; guarded-by: the owner mutex ((S . IDS) ...: quiet file ids waiting for
;; the readers pinned at or below the stamp S)
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
entry of them: a closed id is never reused, so no later hit can name it.
Answers the count closed and IDS still owned by issued workers."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((closed 0) (keep nil) (released nil)
          (rows (loop for row being the hash-values of *fnn-extent-issued* collect row)))
      (dolist (id ids)
        (if (fnn-core 'fn-pio-file-clear-p id rows)
            (let ((fd (gethash id *fnn-extent-fds*)))
              (remhash id *fnn-extent-fds*)
              (remhash id *fnn-extent-paths*)
              (remhash id *fnn-extent-incarnations*)
              (remhash id *fnn-extent-bases*)
              (push id released)
              (when fd
                (fnn-close fd) (incf closed)
                (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
                  (fnn-err "PAGE-IO closed file=~d" id))))
          (progn
            (push id keep)
            (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
              (fnn-err "PAGE-IO close-held file=~d" id)))))
      (setq *fnn-extent-cache*
            (remove-if (lambda (e) (member (first e) released)) *fnn-extent-cache*))
      (when (and *fnn-extent-lz-last* (member (first (first *fnn-extent-lz-last*)) released))
        (setq *fnn-extent-lz-last* nil))
      (values closed (nreverse keep)))))

(defun fnn-extent-open-count ()
  "The descriptors the realizer holds (the natives' observation)."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (hash-table-count *fnn-extent-fds*)))

(defun fnn-extent-stats-line ()
  "The realizer's counters (the natives' observation): hits, preads,
refusals."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (format nil "extent-cache hits=~d misses=~d refusals=~d"
            (first *fnn-extent-stats*) (second *fnn-extent-stats*) (third *fnn-extent-stats*))))
