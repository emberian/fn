;;; host/native/proto-pagestore.lisp -- the page-store prototype's host
;;; (lane proto-pagestore, 2026-09-27).  Raw Lisp, loaded after
;;; books/proto/pagestore.lisp in an ACL2 session (tools/proto/pagestore_bench.py
;;; builds one saved image per tree).
;;;
;;; THE TRUST BOUNDARY.  Exactly two functions here touch file bytes:
;;;
;;;   (fnps-fill-from-file FD BYTE-OFFSET VEC START COUNT)
;;;   (fnps-write-to-file  FD BYTE-OFFSET VEC START COUNT)
;;;
;;; VEC is a (simple-array (unsigned-byte 8) (*)) or a
;;; (simple-array (unsigned-byte 64) (*)) -- in practice the arrays of the
;;; stobj `pgs-mem' -- and START/COUNT count its elements.  Each is pread(2) /
;;; pwrite(2) on the pinned vector's storage, looping on short counts and
;;; retrying EINTR; any other failure, and end of file during a fill, is the
;;; named condition `fnps-io-error' (never a silent zero fill).
;;;
;;; Named assumptions (prose, the prototype's boundary; the book states the
;;; ACL2 side as A-PGS-OBSERVE):
;;;   A-PGS-HOST-IO  a completed pread returns the file's bytes at that range
;;;                  and a completed pwrite leaves them there (durable only
;;;                  after the fdatasync the program names; a process death
;;;                  keeps completed writes, a power loss keeps what the
;;;                  device flushed).
;;;   A-PGS-LE       the host stores a u64 array element little-endian, so the
;;;                  file's octets ARE the words' little-endian octets.  The
;;;                  load refuses a host where this fails.
;;;
;;; Everything else that is not open/close/fdatasync/fsync is an ACL2 call
;;; into books/proto/pagestore.lisp: which records are valid and in what
;;; order they are tried (pgs-x-read-rec, pgs-rec-ok, pgs-open-order,
;;; pgs-slot-refusals), the table's verdict (pgs-x-words-digest,
;;; pgs-x-decode-ptab, pgs-ptab-verdict), the pages' verdict (pgs-x-verify,
;;; pgs-x-touch), the commit (pgs-x-dirty-list, pgs-x-keeps, pgs-next-txid-of,
;;; pgs-x-plan, pgs-x-encode-ptab, pgs-x-write-rec) and the two lookups.  The
;;; host decides only how to batch its I/O (a run of consecutive pages is one
;;; call) and where the process may die (`fnps-at').

(in-package "ACL2")

;; The two primitives, the little-endian check and the barrier wrappers
;; live in proto-pagestore-io.lisp (plain SBCL, testable alone).
(load (merge-pathnames "proto-pagestore-io.lisp" (or *load-truename* *default-pathname-defaults*)))

;; ---------------------------------------------------------------------------
;; The live stobjs and their arrays.

(defun fnps-live (name)
  ;; ACL2 keeps the live user stobjs in *user-stobj-alist*.
  (or (cdr (assoc name *user-stobj-alist*))
      (error "no live stobj ~a" name)))
(defmacro fnps-mem () '(fnps-live 'pgs-mem))
(defmacro fnps-shs () '(fnps-live 'fn-shs))
(defun fnps-arr (k) (svref (fnps-mem) k))     ; 0 w, 1 m, 2 d, 3 v
(defun fnps-w () (fnps-arr 0))
(defun fnps-m () (fnps-arr 1))

(defconstant +fnps-page-words+ 2048)
(defconstant +fnps-page-bytes+ 16384)
(defconstant +fnps-tbase+ 1024)

(defun fnps-ensure-m (n)
  (when (< (pgs-m-length (fnps-mem)) n)
    (resize-pgs-m n (fnps-mem))))

(defun fnps-set-pages (npages)
  ;; The resident image: NPAGES pages, dirty and verified flags cleared.
  (resize-pgs-w (* npages +fnps-page-words+) (fnps-mem))
  (resize-pgs-d npages (fnps-mem))
  (resize-pgs-v npages (fnps-mem))
  (fill (fnps-arr 2) 0)
  (fill (fnps-arr 3) 0))

(defun fnps-grow-pages (npages)
  ;; Keep the image, add pages (append growth).
  (resize-pgs-w (* npages +fnps-page-words+) (fnps-mem))
  (resize-pgs-d npages (fnps-mem))
  (resize-pgs-v npages (fnps-mem)))

(defun fnps-npages () (pgs-d-length (fnps-mem)))

;; ---------------------------------------------------------------------------
;; Cuts: every name in the book's *pgs-snapshot-cuts*.

(defvar *fnps-cut* nil)          ; (name . k) from FNPS_CUT
(defvar *fnps-cut-counts* nil)

(defun fnps-cut-names () (w-state-constant '*pgs-snapshot-cuts*))

(defun w-state-constant (sym)
  (let ((w (w *the-live-state*)))
    (cadr (getpropc sym 'const nil w))))

(defun fnps-parse-cut ()
  (let ((s (sb-ext:posix-getenv "FNPS_CUT")))
    (setf *fnps-cut*
          (when (and s (plusp (length s)))
            (let* ((p (position #\: s))
                   (name (intern (string-upcase (subseq s 0 p)) "KEYWORD"))
                   (k (if p (parse-integer s :start (1+ p)) 1)))
              (unless (member name (fnps-cut-names))
                (error "FNPS_CUT ~a is not a cut of *pgs-snapshot-cuts* ~a" name (fnps-cut-names)))
              (cons name k))))
    (setf *fnps-cut-counts* nil)))

(defun fnps-at (name)
  (let ((n (1+ (or (cdr (assoc name *fnps-cut-counts*)) 0))))
    (setf *fnps-cut-counts* (cons (cons name n) (remove name *fnps-cut-counts* :key #'car)))
    (when (and *fnps-cut* (eq (car *fnps-cut*) name) (= (cdr *fnps-cut*) n))
      (format t "~&FNPS-CUT ~a ~a~%" name n)
      (finish-output)
      (sb-ext:exit :code 77 :abort t))))

(defun fnps-torn-here-p ()
  (and *fnps-cut* (eq (car *fnps-cut*) :record-torn)))

;; ---------------------------------------------------------------------------
;; Timing and output.

(defun fnps-now ()
  (multiple-value-bind (sec nsec) (sb-unix:clock-gettime sb-unix:clock-monotonic)
    (+ (* sec 1000.0d0) (/ nsec 1000000.0d0))))
(defmacro fnps-timed (var &body body)
  `(let ((t0 (fnps-now)))
     (multiple-value-prog1 (progn ,@body)
       (setf ,var (- (fnps-now) t0)))))

(defun fnps-rss-kib ()
  (with-open-file (s "/proc/self/status" :if-does-not-exist nil)
    (when s
      (loop for line = (read-line s nil) while line
            when (and (> (length line) 6) (string= "VmRSS:" line :end2 6))
              return (parse-integer line :start 6 :junk-allowed t)))))

(defun fnps-json-value (v)
  (cond ((null v) "null")
        ((eq v t) "true")
        ((keywordp v) (format nil "\"~(~a~)\"" v))
        ((stringp v) (format nil "~s" v))
        ((integerp v) (format nil "~d" v))
        ((floatp v) (format nil "~,3f" v))
        ((and (consp v) (evenp (length v))
              (loop for (k) on v by #'cddr always (keywordp k)))
         (fnps-json v))
        ((listp v) (format nil "[~{~a~^,~}]" (mapcar #'fnps-json-value v)))
        (t (format nil "\"~a\"" v))))

(defun fnps-json (plist)
  (format nil "{~{~a~^,~}}"
          (loop for (k v) on plist by #'cddr
                collect (format nil "\"~(~a~)\":~a" k (fnps-json-value v)))))

(defun fnps-emit (&rest plist)
  (format t "~&FNPS-JSON ~a~%" (fnps-json plist))
  (finish-output))

(defun fnps-refusal-string (r) (format nil "~(~s~)" r))

;; ---------------------------------------------------------------------------
;; The store handle.

(defstruct fnps
  dir root pages-fd root-fd
  k            ; the slot the current commit is in
  slots        ; vector of 2: (rec . ptab) or nil, valid records only
  ptab)        ; the current table

(defun fnps-pages-path (dir) (concatenate 'string dir "/pages"))
(defun fnps-root-path (dir root) (concatenate 'string dir "/root-" root))

(defun fnps-close (s)
  (when (fnps-pages-fd s) (sb-unix:unix-close (fnps-pages-fd s)))
  (when (and (fnps-root-fd s) (not (eql (fnps-root-fd s) (fnps-pages-fd s))))
    (sb-unix:unix-close (fnps-root-fd s))))

;; The INLINE layout (DIR/inline exists): root "main"'s two slots live in the
;; page file itself, at bytes 0 and 4096 of reserved page 0, so a commit is
;; pages + table + record in ONE file and one fdatasync makes it durable.
;; Page 0 is kept from allocation by a pseudo record whose table run is page
;; 0 (`pgs-rec-keeps' of (:pgs-commit 0 0 0 0 0) is (0)), passed to
;; `pgs-x-plan' with the real pairs.  Forks still get root files.
(defun fnps-inline-p (dir) (probe-file (concatenate 'string dir "/inline")))
(defparameter *fnps-reserved-pair* (cons (list :pgs-commit 0 0 0 0 0) nil))

(defun fnps-open-root (dir root pages-fd)
  (if (and (string= root "main") (fnps-inline-p dir))
      pages-fd
    (fnps-open-file (fnps-root-path dir root))))

(defun fnps-read-slots (root-fd)
  ;; Both slots into pgs-m[0, 1024); returns (r0 v0 r1 v1).
  (fnps-ensure-m (+ +fnps-tbase+ +fnps-page-words+))
  (fnps-fill-from-file root-fd 0 (fnps-m) 0 1024)
  (multiple-value-bind (r0 c0) (pgs-x-read-rec 0 (fnps-mem) (fnps-shs))
    (multiple-value-bind (r1 c1) (pgs-x-read-rec 512 (fnps-mem) (fnps-shs))
      (list r0 (pgs-rec-ok r0 c0) r1 (pgs-rec-ok r1 c1)))))

(defun fnps-read-table (pages-fd rec)
  ;; The table run of REC into pgs-m at the table base; (values ptab verdict).
  (let* ((addr (pgs-rec-ptab-addr rec))
         (len (pgs-rec-ptab-len rec))
         (m (pgs-ptab-run-pages len))
         (words (* m +fnps-page-words+)))
    (fnps-ensure-m (+ +fnps-tbase+ words))
    (handler-case
        (fnps-fill-from-file pages-fd (* addr +fnps-page-bytes+) (fnps-m) +fnps-tbase+ words)
      (fnps-io-error (e)
        (return-from fnps-read-table
          (values nil (list :ptab-unreadable addr (fnps-io-error-detail e))))))
    (let* ((observed (pgs-x-words-digest t +fnps-tbase+ (* m 256) (fnps-mem) (fnps-shs)))
           (ptab (reverse (pgs-x-decode-ptab 0 len +fnps-tbase+ nil (fnps-mem)))))
      (values ptab (pgs-ptab-verdict rec ptab observed)))))

(defun fnps-read-runs (pages-fd ptab)
  ;; Bulk read: logical page I from its phys; consecutive phys for
  ;; consecutive logical pages are one call.  Returns the number of calls.
  (let ((calls 0) (i 0) (w (fnps-w)))
    (loop while ptab do
      (let* ((p0 (first (car ptab))) (n 1))
        (loop for rest on (cdr ptab)
              while (= (first (car rest)) (+ p0 n)) do (incf n))
        (fnps-fill-from-file pages-fd (* p0 +fnps-page-bytes+) w
                             (* i +fnps-page-words+) (* n +fnps-page-words+))
        (incf calls)
        (incf i n)
        (setf ptab (nthcdr n ptab))))
    calls))

(defun fnps-open (dir root mode &key (emit t))
  ;; Read the commit, the table, bulk-read the resident image, verify.
  ;; Returns the handle, or nil when no commit opens (refusals emitted).
  (let* ((pages-fd (fnps-open-file (fnps-pages-path dir)))
         (root-fd (fnps-open-root dir root pages-fd))
         (t-commit 0) (t-table 0) (t-bulk 0) (t-verify 0) (t-other 0) (calls 0)
         (lazy (eq mode :lazy))
         slots refusals landed ptab rec)
    (setf slots (fnps-timed t-commit (fnps-read-slots root-fd)))
    (destructuring-bind (r0 v0 r1 v1) slots
      (setf refusals (pgs-slot-refusals r0 v0 r1 v1))
      (dolist (k (pgs-open-order r0 v0 r1 v1))
        (let ((cand (if (= k 0) r0 r1)))
          (multiple-value-bind (pt tv) (fnps-timed t-table (fnps-read-table pages-fd cand))
            (if tv
                (setf refusals (append refusals (list (list* :slot k tv))))
              (progn
                (fnps-set-pages (length pt))
                (setf calls (fnps-timed t-bulk (fnps-read-runs pages-fd pt)))
                (let ((bad (fnps-timed t-verify
                             (pgs-x-verify pt 0 (pgs-rec-txid cand) mode (fnps-mem) (fnps-shs)))))
                  (if bad
                      (setf refusals (append refusals (list (list* :slot k bad))))
                    (progn (setf landed k ptab pt rec cand) (return))))))))))
    (cond
      ((null landed)
       (when emit
         (fnps-emit :event :open :mode mode :landed nil
                    :refusals (mapcar #'fnps-refusal-string refusals)))
       (sb-unix:unix-close pages-fd)
       (unless (eql root-fd pages-fd) (sb-unix:unix-close root-fd))
       nil)
      (t
       (let ((sv (vector nil nil))
             (other (if (= landed 0) 1 0)))
         (setf (svref sv landed) (cons rec ptab))
         ;; The other valid slot's table: its pages are kept too.
         (destructuring-bind (r0 v0 r1 v1) slots
           (let ((orec (if (= other 0) r0 r1)) (ov (if (= other 0) v0 v1)))
             (when ov
               (multiple-value-bind (opt otv) (fnps-timed t-other (fnps-read-table pages-fd orec))
                 (setf (svref sv other) (cons orec (if otv nil opt)))))))
         ;; The table region now holds the other slot's table: put ours back
         ;; (touch reads the landed table's entries there).
         (let ((m (pgs-ptab-run-pages (length ptab))))
           (fnps-ensure-m (+ +fnps-tbase+ (* m +fnps-page-words+)))
           (fnps-read-table pages-fd rec))
         (when emit
           (fnps-emit :event :open :mode mode :landed landed :txid (pgs-rec-txid rec)
                      :pages (length ptab) :read-calls calls
                      :ms-commit t-commit :ms-table t-table :ms-bulk t-bulk
                      :ms-verify t-verify :ms-other-table t-other
                      :ms-total (+ t-commit t-table t-bulk t-verify)
                      :refusals (mapcar #'fnps-refusal-string refusals)
                      :rss-kib (fnps-rss-kib)))
         (make-fnps :dir dir :root root :pages-fd pages-fd :root-fd root-fd
                    :k landed :slots sv :ptab ptab))))))

;; ---------------------------------------------------------------------------
;; The snapshot.

(defun fnps-pairs (s)
  ;; (rec . ptab) of every valid record of every root in the directory.
  (let ((pairs (loop for x across (fnps-slots s) when x collect x)))
    (dolist (p (directory (concatenate 'string (fnps-dir s) "/root-*")))
      (let ((name (subseq (file-namestring p) 5)))
        (unless (string= name (fnps-root s))
          (let ((fd (fnps-open-file (namestring p))))
            (unwind-protect
                 (destructuring-bind (r0 v0 r1 v1) (fnps-read-slots fd)
                   (dolist (rv (list (cons r0 v0) (cons r1 v1)))
                     (when (cdr rv)
                       (multiple-value-bind (pt tv) (fnps-read-table (fnps-pages-fd s) (car rv))
                         (declare (ignore tv))
                         (push (cons (car rv) pt) pairs)))))
              (sb-unix:unix-close fd))))))
    (when (fnps-inline-p (fnps-dir s))
      (push *fnps-reserved-pair* pairs)
      (unless (string= (fnps-root s) "main")
        (destructuring-bind (r0 v0 r1 v1) (fnps-read-slots (fnps-pages-fd s))
          (dolist (rv (list (cons r0 v0) (cons r1 v1)))
            (when (cdr rv)
              (push (cons (car rv) (fnps-read-table (fnps-pages-fd s) (car rv))) pairs))))))
    ;; fnps-read-slots/read-table clobbered pgs-m: restore our slots' words
    ;; is not needed (commit rewrites its target slot) but the table region
    ;; is reloaded by the caller when needed.
    pairs))

(defun fnps-commit (s fsyncs)
  ;; Dirty pages to fresh space, the table run, [barrier], the record into
  ;; the other slot, barrier(s).  Returns a plist of timings.
  (fnps-parse-cut)
  (setf *fnps-syncs* 0)
  (fnps-at :begin)
  (let* ((t-plan 0) (t-pages 0) (t-table 0) (t-sync1 0) (t-rec 0) (t-sync2 0)
         (dirty (pgs-x-dirty-list (fnps-npages) nil (fnps-mem)))
         (ptab (fnps-ptab s))
         (sv (fnps-slots s))
         (pairs (fnps-pairs s))
         (s0 (car (svref sv 0))) (s1 (car (svref sv 1)))
         (txid (pgs-next-txid-of s0 (and s0 t) s1 (and s1 t)))
         (plan (fnps-timed t-plan
                 (pgs-x-plan ptab dirty pairs txid (fnps-mem) (fnps-shs)))))
    (when (eq plan :alloc-short) (error "pgs-x-plan refused: :alloc-short"))
    (destructuring-bind (run-start singles ptab2) plan
      (let ((runs 0) (bytes 0) (pfd (fnps-pages-fd s)))
        ;; Pages, coalesced.
        (fnps-timed t-pages
          (loop with ls = dirty and fs = singles
                while ls do
                  (let ((n 1))
                    (loop for (a . ra) on ls
                          for (b . rb) on fs
                          while (and ra (= (car ra) (+ a 1)) (= (car rb) (+ b 1)))
                          do (incf n))
                    (fnps-write-to-file pfd (* (car fs) +fnps-page-bytes+) (fnps-w)
                                        (* (car ls) +fnps-page-words+) (* n +fnps-page-words+))
                    (incf runs) (incf bytes (* n +fnps-page-bytes+))
                    (fnps-at :page-written)
                    (setf ls (nthcdr n ls) fs (nthcdr n fs)))))
        ;; The table run.
        (let* ((m (pgs-ptab-run-pages (length ptab2)))
               (words (* m +fnps-page-words+)))
          (fnps-timed t-table
            (fnps-ensure-m (+ +fnps-tbase+ words))
            (fill (fnps-m) 0 :start +fnps-tbase+ :end (+ +fnps-tbase+ words))
            (pgs-x-encode-ptab ptab2 0 +fnps-tbase+ (fnps-mem))
            (fnps-write-to-file pfd (* run-start +fnps-page-bytes+) (fnps-m) +fnps-tbase+ words)
            (incf bytes (* words 8)))
          (fnps-at :table-written)
          (when (= fsyncs 2)
            (fnps-timed t-sync1 (fnps-datasync pfd))
            (fnps-at :pages-synced))
          ;; The record.
          (let* ((k2 (if (and (fnps-k s) (= (fnps-k s) 0)) 1 0))
                 (base (* k2 512))
                 (pdig (pgs-x-words-digest t +fnps-tbase+ (* m 256) (fnps-mem) (fnps-shs)))
                 (rec (pgs-x-write-rec base txid run-start (length ptab2) pdig (fnps-mem) (fnps-shs))))
            (fnps-timed t-rec
              (if (fnps-torn-here-p)
                  (progn (fnps-write-to-file (fnps-root-fd s) (* k2 4096) (fnps-m) base 10)
                         (fnps-at :record-torn))
                (fnps-write-to-file (fnps-root-fd s) (* k2 4096) (fnps-m) base 20)))
            (fnps-at :record-written)
            (fnps-timed t-sync2
              (when (and (= fsyncs 1) (not (eql pfd (fnps-root-fd s))))
                (fnps-datasync pfd))
              (fnps-datasync (fnps-root-fd s)))
            (fnps-at :record-synced)
            (pgs-x-clear-dirty dirty (fnps-mem))
            (setf (svref sv k2) (cons rec ptab2)
                  (fnps-k s) k2
                  (fnps-ptab s) ptab2)
            (list :txid txid :dirty (length dirty) :runs runs :bytes bytes
                  :table-pages m :syncs *fnps-syncs* :fsyncs-mode fsyncs
                  :ms-plan t-plan :ms-pages t-pages :ms-table t-table
                  :ms-sync1 t-sync1 :ms-record t-rec :ms-sync2 t-sync2
                  :ms-total (+ t-plan t-pages t-table t-sync1 t-rec t-sync2))))))))

;; ---------------------------------------------------------------------------
;; Synthesis: fn-hist-shaped columns at ~100 B/record.

(defvar *fnps-rng* (sb-ext:seed-random-state 42))

(defun fnps-rand (n) (random n *fnps-rng*))

(defun fnps-put-word (i v)
  (pgs-x-put (floor i +fnps-page-words+) (mod i +fnps-page-words+) v (fnps-mem)))

(defun fnps-msgid (i) (format nil "<~d.~8,'0x@fn.example>" i (fnps-rand #xffffffff)))

(defun fnps-pages-for (words) (ceiling words +fnps-page-words+))

(defun fnps-synthesize (n salt)
  ;; Returns the number of pages; the image is dirty throughout.
  (let* ((hbits (max 4 (integer-length (* 2 n))))
         (h (expt 2 hbits))
         (msgids (make-array n))
         (rows (make-array n))
         (pool-bytes 0))
    (dotimes (i n)
      (let ((m (fnps-msgid i)) (r (+ 30 (fnps-rand 21))))
        (setf (svref msgids i) m (svref rows i) r)
        (incf pool-bytes (* 8 (ceiling (+ 8 (length m) r) 8)))))
    (let* ((off 2048)
           (tab (* 2048 (+ 1 (fnps-pages-for n))))
           (pool (+ tab (* 2048 (fnps-pages-for h))))
           (pool-words (/ pool-bytes 8))
           (npages (+ (floor pool 2048) (fnps-pages-for pool-words)))
           (table (make-array h :element-type '(unsigned-byte 64) :initial-element 0)))
      (fnps-set-pages npages)
      ;; Every word, so every page is dirty.
      (let ((w (fnps-w)))
        (declare (ignorable w))
        (dotimes (lp npages) (pgs-x-put lp 0 0 (fnps-mem))))
      (loop for (k v) on (list 0 *pgs-cols-magic* 1 n 2 hbits 3 off 4 tab 5 pool
                               6 pool-words 7 salt) by #'cddr
            do (fnps-put-word k v))
      (let ((o 0))
        (dotimes (i n)
          (let* ((m (svref msgids i)) (r (svref rows i))
                 (len (+ 8 (length m) r))
                 (bytes (make-array (* 8 (ceiling len 8)) :element-type '(unsigned-byte 8)
                                                            :initial-element 0)))
            (fnps-put-word (+ off i) o)
            (setf (aref bytes 0) (ldb (byte 8 0) (length m)) (aref bytes 1) (ldb (byte 8 8) (length m))
                  (aref bytes 2) (ldb (byte 8 0) r) (aref bytes 3) (ldb (byte 8 8) r))
            (dotimes (j (length m)) (setf (aref bytes (+ 8 j)) (char-code (char m j))))
            (dotimes (j r) (setf (aref bytes (+ 8 (length m) j)) (fnps-rand 256)))
            (dotimes (q (/ (length bytes) 8))
              (let ((v 0))
                (dotimes (b 8) (setf v (logior v (ash (aref bytes (+ (* 8 q) b)) (* 8 b)))))
                (fnps-put-word (+ pool (/ o 8) q) v)))
            (let ((slot (pgs-msgid-start m salt h)))
              (loop until (zerop (aref table slot)) do (setf slot (mod (1+ slot) h)))
              (setf (aref table slot) (1+ i)))
            (incf o (length bytes)))))
      (dotimes (s h) (unless (zerop (aref table s)) (fnps-put-word (+ tab s) (aref table s))))
      (values npages msgids))))

(defun fnps-write-zero-root (path)
  (let ((fd (fnps-open-file path :create t))
        (z (make-array 8192 :element-type '(unsigned-byte 8) :initial-element 0)))
    (fnps-write-to-file fd 0 z 0 8192)
    (fnps-fullsync fd)
    fd))

(defun fnps-init (dir n &optional inline)
  (ensure-directories-exist (concatenate 'string dir "/"))
  (when inline
    (with-open-file (o (concatenate 'string dir "/inline") :direction :output
                       :if-exists :supersede)
      (write-line "root main: slots in page 0 of the page file" o))
    ;; The marker decides the layout at open: it is durable before any page.
    (let ((fd (fnps-open-file (concatenate 'string dir "/inline"))))
      (fnps-fullsync fd)
      (sb-unix:unix-close fd)))
  (let* ((t-syn 0)
         (pfd (fnps-open-file (fnps-pages-path dir) :create t))
         (rfd (if inline
                  (let ((z (make-array +fnps-page-bytes+ :element-type '(unsigned-byte 8)
                                                         :initial-element 0)))
                    (fnps-write-to-file pfd 0 z 0 +fnps-page-bytes+)
                    (fnps-datasync pfd)
                    pfd)
                (fnps-write-zero-root (fnps-root-path dir "main"))))
         (npages (fnps-timed t-syn (fnps-synthesize n (fnps-rand #xffffffff))))
         (s (make-fnps :dir dir :root "main" :pages-fd pfd :root-fd rfd :k nil
                       :slots (vector nil nil)
                       :ptab (make-list npages :initial-element (list 0 0 0)))))
    (fnps-sync-dir dir)
    (let ((c (fnps-commit s 2)))
      (fnps-emit :event :init :records n :pages npages :ms-synthesize t-syn :commit (list* :event :commit c)))
    s))

;; ---------------------------------------------------------------------------
;; Mutations (the writers keep the dirty bitmap through pgs-x-put).

(defun fnps-mutate-random (count)
  ;; COUNT distinct pages (never the header), one word each, a new value.
  (let* ((np (fnps-npages))
         (count (min count (1- np)))
         (chosen (make-hash-table)))
    (loop while (< (hash-table-count chosen) count)
          do (setf (gethash (1+ (fnps-rand (1- np))) chosen) t))
    (loop for lp being the hash-keys of chosen
          do (let ((off (fnps-rand +fnps-page-words+)))
               (pgs-x-put lp off (logxor (aref (fnps-w) (+ (* lp +fnps-page-words+) off))
                                         (1+ (fnps-rand #xffffffffffff)))
                          (fnps-mem))))
    count))

(defun fnps-mutate-append (s count)
  ;; COUNT new pages at the end of the image (history growth): the table
  ;; grows by placeholder entries the commit replaces.
  (let* ((np (fnps-npages)) (np2 (+ np count)))
    (fnps-grow-pages np2)
    (loop for lp from np below np2
          do (dotimes (off +fnps-page-words+)
               (pgs-x-put lp off (fnps-rand #xffffffffffffff) (fnps-mem))))
    (setf (fnps-ptab s) (append (fnps-ptab s) (make-list count :initial-element (list 0 0 0))))
    count))

(defun fnps-image-digest ()
  (pgs-x-words-digest nil 0 (* (fnps-npages) 256) (fnps-mem) (fnps-shs)))

;; ---------------------------------------------------------------------------
;; Commands.

(defun fnps-first-requests (s lazy seed-msgids)
  (declare (ignore s))
  (let* ((n (let ((v (nth-value 1 (pgs-x-rd 1 lazy +fnps-tbase+ (fnps-mem) (fnps-shs))))) v))
         (seq (fnps-rand (max 1 n)))
         (t-seq 0) (t-mid 0))
    (multiple-value-bind (v bytes) (fnps-timed t-seq (pgs-x-lookup-seq seq lazy +fnps-tbase+ (fnps-mem) (fnps-shs)))
      (let* ((mid (or (and seed-msgids (svref seed-msgids seq))
                      (map 'string #'code-char bytes))))
        (multiple-value-bind (v2 got) (fnps-timed t-mid (pgs-x-lookup-msgid mid lazy +fnps-tbase+ (fnps-mem) (fnps-shs)))
          (list :seq seq :seq-verdict (fnps-refusal-string v) :msgid mid
                :msgid-verdict (fnps-refusal-string v2) :msgid-seq got
                :msgid-found (equal got seq)
                :ms-lookup-seq t-seq :ms-lookup-msgid t-mid))))))

(defun fnps-background-pass (tbase)
  (let ((bad nil))
    (dotimes (i (fnps-npages))
      (let ((v (pgs-x-touch i tbase (fnps-mem) (fnps-shs))))
        (unless (eq v :ok) (push i bad))))
    (reverse bad)))

(defun fnps-cmd-open (dir root mode &key touch)
  (let ((s (fnps-open dir root mode)))
    (when s
      (let* ((lazy (eq mode :lazy))
             (fr (fnps-first-requests s lazy nil))
             (t-bg 0) (bad nil)
             (tv (when touch
                   (fnps-refusal-string
                    (pgs-x-touch touch +fnps-tbase+ (fnps-mem) (fnps-shs))))))
        (when (and lazy (not touch))
          (setf bad (fnps-timed t-bg (fnps-background-pass +fnps-tbase+))))
        (fnps-emit :event :first-request :mode mode :requests fr
                   :touch touch :touch-verdict tv
                   :ms-background-pass t-bg :background-damaged bad
                   :rss-kib (fnps-rss-kib)))
      (fnps-close s))
    s))

(defun fnps-cmd-mutate (dir root kind count fsyncs &key (mode :lazy) digest)
  (let ((s (fnps-open dir root mode :emit nil)))
    (unless s (fnps-emit :event :mutate :refused t) (return-from fnps-cmd-mutate nil))
    (let ((pre-txid (pgs-rec-txid (car (svref (fnps-slots s) (fnps-k s))))))
      (ecase kind
        (:random (fnps-mutate-random count))
        (:append (fnps-mutate-append s count)))
      (when digest
        (fnps-emit :event :pre :from-txid pre-txid
                   :next-digest (format nil "~64,'0x" (fnps-image-digest))))
      (let ((c (fnps-commit s fsyncs)))
        (fnps-emit :event :commit :kind kind :count count :commit c)))
    (fnps-close s)))

(defun fnps-cmd-digest (dir root mode)
  (let ((s (fnps-open dir root mode)))
    (when s
      (fnps-emit :event :digest :txid (pgs-rec-txid (car (svref (fnps-slots s) (fnps-k s))))
                 :digest (format nil "~64,'0x" (fnps-image-digest)))
      (fnps-close s))))

(defun fnps-cmd-fork (dir src dst)
  (let ((s (fnps-open dir src :lazy :emit nil)) (t-fork 0))
    (fnps-timed t-fork
      (let* ((base (* 512 (fnps-k s)))
             (rec (car (svref (fnps-slots s) (fnps-k s))))
             (fd (fnps-write-zero-root (fnps-root-path dir dst))))
        (declare (ignore rec))
        ;; pgs-m[base, base+20) still holds the landed record's words? The
        ;; table reads overwrote only the region from the table base, so the
        ;; slot words are the ones read at open.
        (fnps-write-to-file fd 0 (fnps-m) base 20)
        (fnps-fullsync fd)
        (sb-unix:unix-close fd)
        (fnps-sync-dir dir)))
    (fnps-emit :event :fork :src src :dst dst :ms-fork t-fork
               :txid (pgs-rec-txid (car (svref (fnps-slots s) (fnps-k s)))))
    (fnps-close s)))

(defun fnps-cmd-damage (dir root lpage)
  ;; Flip one octet of LPAGE's page under ROOT's newest valid record
  ;; (run twice to restore); prints the page's phys and writer txid.
  (let* ((pfd (fnps-open-file (fnps-pages-path dir)))
         (rfd (fnps-open-root dir root pfd)))
    (destructuring-bind (r0 v0 r1 v1) (fnps-read-slots rfd)
      (let* ((k (car (pgs-open-order r0 v0 r1 v1)))
             (rec (if (= k 0) r0 r1))
             (ptab (fnps-read-table pfd rec))
             (e (nth lpage ptab))
             (b (make-array 1 :element-type '(unsigned-byte 8))))
        (fnps-fill-from-file pfd (+ 8 (* (first e) +fnps-page-bytes+)) b 0 1)
        (setf (aref b 0) (logxor (aref b 0) #x5a))
        (fnps-write-to-file pfd (+ 8 (* (first e) +fnps-page-bytes+)) b 0 1)
        (fnps-datasync pfd)
        (fnps-emit :event :damage :lpage lpage :phys (first e) :entry-txid (second e)
                   :record-txid (pgs-rec-txid rec))))
    (sb-unix:unix-close pfd)
    (unless (eql rfd pfd) (sb-unix:unix-close rfd))))

(defun fnps-cmd-cut-names ()
  (fnps-emit :event :cut-names :cuts (fnps-cut-names)))

(defun fnps-main (args)
  ;; ARGS: a list of strings.  Seeds from FNPS_SEED.
  (sb-ext:disable-debugger)
  (let ((seed (sb-ext:posix-getenv "FNPS_SEED")))
    (when seed (setf *fnps-rng* (sb-ext:seed-random-state (parse-integer seed)))))
  (let ((cmd (first args)) (a (rest args)))
    (handler-case
        (cond
          ((string= cmd "init") (fnps-close (fnps-init (first a) (parse-integer (second a))
                                                       (equal (third a) "inline"))))
          ((string= cmd "open")
           (fnps-cmd-open (first a) (second a) (intern (string-upcase (third a)) "KEYWORD")
                          :touch (and (fourth a) (parse-integer (fourth a)))))
          ((string= cmd "mutate")
           (fnps-cmd-mutate (first a) (second a) (intern (string-upcase (third a)) "KEYWORD")
                            (parse-integer (fourth a)) (parse-integer (fifth a))
                            :mode (if (sixth a) (intern (string-upcase (sixth a)) "KEYWORD") :lazy)
                            :digest (sb-ext:posix-getenv "FNPS_DIGEST")))
          ((string= cmd "digest") (fnps-cmd-digest (first a) (second a)
                                                   (intern (string-upcase (or (third a) "eager")) "KEYWORD")))
          ((string= cmd "fork") (fnps-cmd-fork (first a) (second a) (third a)))
          ((string= cmd "damage") (fnps-cmd-damage (first a) (second a) (parse-integer (third a))))
          ((string= cmd "cut-names") (fnps-cmd-cut-names))
          (t (error "unknown command ~a" cmd)))
      (fnps-io-error (e)
        (fnps-emit :event :io-error :call (fnps-io-error-call e) :errno (fnps-io-error-errno e)
                   :detail (fnps-io-error-detail e))
        (sb-ext:exit :code 3 :abort t))
      (error (e)
        (fnps-emit :event :error :detail (format nil "~a" e))
        (sb-ext:exit :code 4 :abort t)))
    (finish-output)
    (sb-ext:exit :code 0 :abort t)))
