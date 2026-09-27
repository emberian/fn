;;; host/native/proto-pagestore.lisp -- the page store's host (lane
;;; proto-pagestore, 2026-09-27; rewritten for the two-level table by lane
;;; arena-store, 2026-09-27).  Raw Lisp, loaded after
;;; books/proto/pagestore-exec.lisp in an ACL2 session
;;; (tools/proto/pagestore_bench.py builds one saved image per tree).
;;;
;;; THE TRUST BOUNDARY.  Exactly two functions here touch file bytes:
;;;
;;;   (fnps-fill-from-file FD BYTE-OFFSET VEC START COUNT)
;;;   (fnps-write-to-file  FD BYTE-OFFSET VEC START COUNT)
;;;
;;; (proto-pagestore-io.lisp).  VEC is an array of the stobj `pgs-mem' (or a
;;; small octet buffer for the damage tool) and START/COUNT count its
;;; elements.  Each is pread(2) / pwrite(2) on the pinned vector, looping on
;;; short counts and retrying EINTR; any other failure, and end of file
;;; during a fill, is the named condition `fnps-io-error'.
;;;
;;; Named assumptions (the prototype's boundary; the book states the ACL2
;;; side as A-PGS-OBSERVE):
;;;   A-PGS-HOST-IO  a completed pread returns the file's bytes at that range
;;;                  and a completed pwrite leaves them there (durable only
;;;                  after the fdatasync the program names; a process death
;;;                  keeps completed writes, a power loss keeps what the
;;;                  device flushed).
;;;   A-PGS-LE       the host stores a u64 array element little-endian (the
;;;                  load refuses a host where this fails).
;;;
;;; Absent bytes.  A fill that meets end of file (a page a record names that
;;; the file does not hold: possible after a power loss that kept the record
;;; but not the file's extension) leaves that page's words ZERO in the stobj
;;; and the ACL2 verdict decides (the page's digest is checked against its
;;; entry; a directory run that cannot be filled leaves pgs-m short and
;;; `pgs-x-open-dir' answers :dir-unloaded).  The host never decides that a
;;; page is good or bad.
;;;
;;; Everything that is not open/close/fstat/fdatasync/fsync is an ACL2 call
;;; into books/proto/pagestore-exec.lisp (section numbers there):
;;;   open    pgs-x-read-rec, pgs-rec-ok, pgs-slot-refusals, pgs-open-order
;;;           (which record, in what order); pgs-dir-run-pages (how much
;;;           directory to read); pgs-x-open-dir; pgs-x-reset-table;
;;;           pgs-x-open-tables (which table pages now); pgs-x-open-table-page;
;;;           pgs-x-table-page-range + pgs-x-open-pages (which data pages
;;;           now); pgs-x-open-page (10)
;;;   reads   pgs-x-read / pgs-x-rd / pgs-x-lookup-seq / pgs-x-lookup-msgid:
;;;           a (:need-table T PHYS) or (:need-page I PHYS) verdict is served
;;;           by one fill and pgs-x-open-table-page / pgs-x-open-page
;;;           (:eager), then the call is retried (10, 12)
;;;   writes  pgs-x-write, pgs-x-grow-image (11)
;;;   commit  pgs-next-txid-of, pgs-x-dirty-list, pgs-x-commit (the plan and
;;;           every word it writes), pgs-x-commit-durable (11)
;;; The allocator state (FREE HWM) is an ACL2 value the host carries: at
;;; open FREE = nil and HWM = the pages the file holds (no reclamation yet),
;;; after a commit the ALLOC2 the plan answered.  The host decides only how
;;; to batch reads (consecutive pages are one call) and where the process
;;; may die (`fnps-at', every name in *pgs-snapshot-cuts*; each is the model
;;; crash point `pgs-cut-crash-point' names: data pages are written one per
;;; call so :page-written K keeps exactly the first K).
;;;
;;; Layout: the inline one-barrier layout.  16 KiB pages in DIR/pages; page 0
;;; is reserved for root main's two record slots (bytes 0 and 4096 = pgs-m
;;; words 0 and 512); a commit writes its data pages, touched table pages,
;;; directory run and record into that one file and makes it durable with
;;; ONE fdatasync.  A branch (`branch') keeps its two slots in DIR/root-NAME
;;; (a commit on a branch syncs the page file before writing its record).

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
(defun fnps-arr (k) (svref (fnps-mem) k))     ; 0 w, 1 m, 2 t, 3 d, 4 v, 5 tv
(defun fnps-w () (fnps-arr 0))
(defun fnps-m () (fnps-arr 1))
(defun fnps-t () (fnps-arr 2))

(defconstant +fnps-pw+ 2048)       ; words per page
(defconstant +fnps-pb+ 16384)      ; bytes per page

(defun fnps-npages () (pgs-d-length (fnps-mem)))

;; ---------------------------------------------------------------------------
;; Cuts: every name in the book's *pgs-snapshot-cuts*.

(defvar *fnps-cut* nil)          ; (name . k) from FNPS_CUT
(defvar *fnps-cut-counts* nil)

(defun w-state-constant (sym)
  (let ((w (w *the-live-state*)))
    (cadr (getpropc sym 'const nil w))))

(defun fnps-cut-names () (w-state-constant '*pgs-snapshot-cuts*))

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
  ;; Adds the elapsed ms to VAR.
  `(let ((t0 (fnps-now)))
     (multiple-value-prog1 (progn ,@body)
       (incf ,var (- (fnps-now) t0)))))

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
;; Reads into the stobj.

(defun fnps-eof-p (e)
  (and (equal (fnps-io-error-call e) "pread") (eql (fnps-io-error-errno e) 0)
       (search "end of file" (fnps-io-error-detail e))))

(defvar *fnps-read-calls* 0)
(defvar *fnps-absent* nil)       ; pages a fill found past end of file

(defun fnps-fill-page-or-absent (fd phys arr dpage)
  (handler-case
      (progn (incf *fnps-read-calls*)
             (fnps-fill-from-file fd (* phys +fnps-pb+) arr (* dpage +fnps-pw+) +fnps-pw+)
             t)
    (fnps-io-error (e)
      (unless (fnps-eof-p e) (error e))
      (fill arr 0 :start (* dpage +fnps-pw+) :end (* (1+ dpage) +fnps-pw+))
      (push (list dpage phys) *fnps-absent*)
      nil)))

(defun fnps-load-pages (fd arr pairs)
  ;; PAIRS: ((DPAGE PHYS) ...): page DPAGE of ARR (2048-word pages) := the
  ;; file's page PHYS.  A run consecutive in both is one call.
  (loop while pairs do
    (let* ((d0 (first (car pairs))) (p0 (second (car pairs))) (n 1))
      (loop for rest on (cdr pairs)
            while (and (= (first (car rest)) (+ d0 n)) (= (second (car rest)) (+ p0 n)))
            do (incf n))
      (if (= n 1)
          (fnps-fill-page-or-absent fd p0 arr d0)
        (handler-case
            (progn (incf *fnps-read-calls*)
                   (fnps-fill-from-file fd (* p0 +fnps-pb+) arr (* d0 +fnps-pw+) (* n +fnps-pw+)))
          (fnps-io-error (e)
            (unless (fnps-eof-p e) (error e))
            (dotimes (j n) (fnps-fill-page-or-absent fd (+ p0 j) arr (+ d0 j))))))
      (setf pairs (nthcdr n pairs)))))

(defun fnps-file-pages (fd)
  ;; The pages the file holds (a partial last page counts).
  (multiple-value-bind (ok dev ino mode nlink uid gid rdev size) (sb-unix:unix-fstat fd)
    (declare (ignore dev ino mode nlink uid gid rdev))
    (unless ok (error 'fnps-io-error :call "fstat" :errno 0 :detail ""))
    (ceiling size +fnps-pb+)))

;; ---------------------------------------------------------------------------
;; The store handle.

(defstruct fnps
  dir root pages-fd root-fd
  mode
  s0 v0 s1 v1  ; the two slots as read (pgs-x-read-rec) and their validity
  k            ; the slot the open landed on (0 or 1), nil for a fresh store
  rec          ; that record
  n            ; the committed table's length (the record's npages)
  alloc)       ; (FREE HWM), an ACL2 value

(defun fnps-pages-path (dir) (concatenate 'string dir "/pages"))
(defun fnps-root-path (dir root) (concatenate 'string dir "/root-" root))

(defun fnps-close (s)
  (when (fnps-pages-fd s) (sb-unix:unix-close (fnps-pages-fd s)))
  (when (and (fnps-root-fd s) (not (eql (fnps-root-fd s) (fnps-pages-fd s))))
    (sb-unix:unix-close (fnps-root-fd s))))

(defun fnps-open-root (dir root pages-fd)
  (if (string= root "main")
      pages-fd
    (fnps-open-file (fnps-root-path dir root))))

(defun fnps-read-slots (root-fd)
  ;; Both slots into pgs-m[0, 1024) (absent bytes zero: empty slots);
  ;; returns (s0 v0 s1 v1) by pgs-x-read-rec and pgs-rec-ok.
  (resize-pgs-m 0 (fnps-mem))
  (resize-pgs-m *pgs-x-dir-base* (fnps-mem))
  (handler-case (progn (incf *fnps-read-calls*)
                       (fnps-fill-from-file root-fd 0 (fnps-m) 0 1024))
    (fnps-io-error (e)
      (unless (fnps-eof-p e) (error e))
      (fill (fnps-m) 0)))
  (multiple-value-bind (r0 c0) (pgs-x-read-rec 0 (fnps-mem) (fnps-shs))
    (multiple-value-bind (r1 c1) (pgs-x-read-rec 512 (fnps-mem) (fnps-shs))
      (list r0 (pgs-rec-ok r0 c0) r1 (pgs-rec-ok r1 c1)))))

(defun fnps-load-dir (fd rec)
  ;; pgs-m := the slots (kept) and REC's directory run from *pgs-x-dir-base*
  ;; (exactly the run); then pgs-x-open-dir's verdict.
  (let* ((m (pgs-dir-run-pages (pgs-rec-npages rec)))
         (words (* m +fnps-pw+)))
    (resize-pgs-m *pgs-x-dir-base* (fnps-mem))
    (resize-pgs-m (+ *pgs-x-dir-base* words) (fnps-mem))
    (handler-case
        (progn (incf *fnps-read-calls*)
               (fnps-fill-from-file fd (* (pgs-rec-dir-addr rec) +fnps-pb+) (fnps-m)
                                    *pgs-x-dir-base* words))
      (fnps-io-error (e)
        (unless (fnps-eof-p e) (error e))
        (push (list :dir (pgs-rec-dir-addr rec)) *fnps-absent*)
        (resize-pgs-m *pgs-x-dir-base* (fnps-mem))))
    (values (pgs-x-open-dir rec (fnps-mem) (fnps-shs)))))

(defun fnps-size-image (npages)
  ;; A fresh image of NPAGES pages: zero words, not resident, clean.
  (let ((mem (fnps-mem)))
    (resize-pgs-w 0 mem) (resize-pgs-d 0 mem) (resize-pgs-v 0 mem)
    (resize-pgs-w (* npages +fnps-pw+) mem)
    (resize-pgs-d npages mem)
    (resize-pgs-v npages mem)))

(defvar *fnps-t* nil)            ; open timings plist, filled by fnps-try

(defun fnps-try (fd rec mode)
  ;; Open REC: the directory, the table pages and data pages MODE loads
  ;; now.  nil (landed) or the refusal.
  (let ((t-dir 0) (t-tables 0) (t-read 0) (t-verify 0) (ntab 0) (npg 0))
    (unwind-protect
         (block try
           (let ((v (fnps-timed t-dir (fnps-load-dir fd rec))))
             (when v (return-from try v)))
           (let* ((npages (pgs-rec-npages rec))
                  (txid (pgs-rec-txid rec))
                  (nt (pgs-x-ntables npages)))
             (fnps-timed t-tables
               (pgs-x-reset-table npages (fnps-mem))
               (fnps-size-image npages))
             (let ((tabs (pgs-x-open-tables 0 nt txid mode nil (fnps-mem))))
               (setf ntab (length tabs))
               (fnps-timed t-tables (fnps-load-pages fd (fnps-t) tabs))
               (dolist (tp tabs)
                 (let ((v (fnps-timed t-tables
                            (values (pgs-x-open-table-page (first tp) rec mode (fnps-mem) (fnps-shs))))))
                   (when v (return-from try v))))
               (let ((pairs (loop for tp in tabs
                                  append (destructuring-bind (lo hi) (pgs-x-table-page-range (first tp) npages)
                                           (pgs-x-open-pages lo hi txid mode nil (fnps-mem))))))
                 (setf npg (length pairs))
                 (fnps-timed t-read (fnps-load-pages fd (fnps-w) pairs))
                 (dolist (p pairs)
                   (let ((v (fnps-timed t-verify
                              (values (pgs-x-open-page (first p) txid mode (fnps-mem) (fnps-shs))))))
                     (when v (return-from try v))))
                 nil))))
      (setf *fnps-t* (list :ms-dir t-dir :ms-tables t-tables :ms-pages-read t-read
                           :ms-pages-verify t-verify :tables-loaded ntab :pages-loaded npg)))))

(defun fnps-open (dir root mode &key (emit t))
  ;; Returns the handle, or nil when no commit opens (refusals emitted).
  (setf *fnps-read-calls* 0 *fnps-absent* nil)
  (let* ((t0 (fnps-now))
         (pages-fd (fnps-open-file (fnps-pages-path dir)))
         (root-fd (fnps-open-root dir root pages-fd))
         (t-slots 0)
         (slots (fnps-timed t-slots (fnps-read-slots root-fd)))
         (refusals nil) landed rec timings)
    (destructuring-bind (s0 v0 s1 v1) slots
      (setf refusals (pgs-slot-refusals s0 v0 s1 v1))
      (dolist (k (pgs-open-order s0 v0 s1 v1))
        (let* ((cand (if (= k 0) s0 s1))
               (v (fnps-try pages-fd cand mode)))
          (setf timings *fnps-t*)
          (if v
              (setf refusals (append refusals (list (list* :slot k v))))
            (progn (setf landed k rec cand) (return)))))
      (let ((ms-total (- (fnps-now) t0)))
        (cond
          ((null landed)
           (when emit
             (fnps-emit :event :open :mode mode :landed nil
                        :refusals (mapcar #'fnps-refusal-string refusals)
                        :absent (mapcar #'fnps-refusal-string *fnps-absent*)))
           (sb-unix:unix-close pages-fd)
           (unless (eql root-fd pages-fd) (sb-unix:unix-close root-fd))
           nil)
          (t
           (let ((s (make-fnps :dir dir :root root :pages-fd pages-fd :root-fd root-fd :mode mode
                               :s0 s0 :v0 v0 :s1 s1 :v1 v1 :k landed :rec rec
                               :n (pgs-rec-npages rec)
                               :alloc (list nil (fnps-file-pages pages-fd)))))
             (when emit
               (apply #'fnps-emit
                      (append (list :event :open :mode mode :landed landed :txid (pgs-rec-txid rec)
                                    :pages (pgs-rec-npages rec)
                                    :tables (pgs-x-ntables (pgs-rec-npages rec))
                                    :dir-pages (pgs-dir-run-pages (pgs-rec-npages rec))
                                    :read-calls *fnps-read-calls*
                                    :ms-slots t-slots)
                              timings
                              (list :ms-total ms-total
                                    :refusals (mapcar #'fnps-refusal-string refusals)
                                    :absent (mapcar #'fnps-refusal-string *fnps-absent*)
                                    :rss-kib (fnps-rss-kib)))))
             s)))))))

;; ---------------------------------------------------------------------------
;; On demand: the :need-* protocol.

(defvar *fnps-served* 0)

(defun fnps-serve-need (s v)
  ;; V is (:need-table T PHYS) or (:need-page I PHYS): one fill, then the
  ;; book's verdict at first touch (:eager).  nil or the refusal.
  (incf *fnps-served*)
  (ecase (first v)
    (:need-table
     (fnps-load-pages (fnps-pages-fd s) (fnps-t) (list (list (second v) (third v))))
     (values (pgs-x-open-table-page (second v) (fnps-rec s) :eager (fnps-mem) (fnps-shs))))
    (:need-page
     (fnps-load-pages (fnps-pages-fd s) (fnps-w) (list (list (second v) (third v))))
     (values (pgs-x-open-page (second v) (pgs-rec-txid (fnps-rec s)) :eager (fnps-mem) (fnps-shs))))))

(defun fnps-need-p (v)
  (and (consp v) (member (first v) '(:need-table :need-page)) (= (length v) 3)))

(defun fnps-with-needs (s thunk)
  ;; THUNK returns the multiple values of an ACL2 read whose first is the
  ;; verdict; serve each :need-* and retry.  Returns the values of the last
  ;; call, or the refusal a load answered in place of the verdict.
  (loop
    (let ((vals (multiple-value-list (funcall thunk))))
      (if (fnps-need-p (first vals))
          (let ((r (fnps-serve-need s (first vals))))
            (when r (return (values-list (cons r (rest vals))))))
        (return (values-list vals))))))

(defun fnps-read-word (s i off)
  (fnps-with-needs s (lambda () (pgs-x-read i off (fnps-mem) (fnps-shs)))))

(defun fnps-load-all (s)
  ;; Every committed logical page (below the record's table length) resident
  ;; and verified (the lazy background pass): the list of refusals met.
  ;; Pages appended since the open are resident already (pgs-x-grow-image);
  ;; they are not read through pgs-x-read, which answers :out-of-range for
  ;; one in a table page the committed table does not have yet (pgs-tv is
  ;; not grown by pgs-x-grow-image).
  (let ((bad nil))
    (dotimes (i (min (fnps-npages) (fnps-n s)))
      (let ((v (fnps-read-word s i 0)))
        (unless (eq v :ok) (push (list i v) bad))))
    (reverse bad)))

;; ---------------------------------------------------------------------------
;; The snapshot.

(defun fnps-commit (s)
  ;; The dirty pages, the touched table pages, the directory run, the
  ;; record into the slot the open did not land on, ONE barrier.  Returns a
  ;; plist, or (:refused ...) when the book refused.
  (fnps-parse-cut)
  (setf *fnps-syncs* 0 *fnps-read-calls* 0 *fnps-served* 0)
  (fnps-at :begin)
  (let* ((t-dirty 0) (t-plan 0) (t-need 0) (t-pages 0) (t-tables 0) (t-dir 0) (t-rec 0) (t-sync 0)
         (lpages (fnps-timed t-dirty (pgs-x-dirty-list (fnps-npages) nil (fnps-mem))))
         (txid (pgs-next-txid-of (fnps-s0 s) (fnps-v0 s) (fnps-s1 s) (fnps-v1 s)))
         (slot (if (eql (fnps-k s) 0) 512 0))
         (pfd (fnps-pages-fd s)) (rfd (fnps-root-fd s))
         (writes 0) (bytes 0)
         result)
    (loop
      (let ((r (fnps-timed t-plan
                 (values (pgs-x-commit lpages (fnps-n s) txid (fnps-alloc s) slot (fnps-mem) (fnps-shs))))))
        (cond ((and (consp r) (eq (first r) :need-table))
               (let ((v (fnps-timed t-need (fnps-serve-need s r))))
                 (when v (return-from fnps-commit (list :refused v)))))
              (t (setf result r) (return)))))
    (unless (and (consp result) (eq (first result) :plan))
      (return-from fnps-commit (list :refused result)))
    (destructuring-bind (rec fresh tl tfresh run-start m alloc2 digests tdigests) (rest result)
      (declare (ignore digests tdigests))
      ;; Data pages, one call each (the model's per-write crash points).
      (fnps-timed t-pages
        (loop for l in lpages for f in fresh
              do (fnps-write-to-file pfd (* f +fnps-pb+) (fnps-w) (* l +fnps-pw+) +fnps-pw+)
                 (incf writes) (incf bytes +fnps-pb+)
                 (fnps-at :page-written)))
      ;; The touched table pages.
      (fnps-timed t-tables
        (loop for tp in tl for f in tfresh
              do (fnps-write-to-file pfd (* f +fnps-pb+) (fnps-t) (* tp +fnps-pw+) +fnps-pw+)
                 (incf writes) (incf bytes +fnps-pb+)
                 (fnps-at :table-written)))
      ;; The directory run.
      (fnps-timed t-dir
        (fnps-write-to-file pfd (* run-start +fnps-pb+) (fnps-m) *pgs-x-dir-base* (* m +fnps-pw+))
        (incf writes) (incf bytes (* m +fnps-pb+)))
      (fnps-at :dir-written)
      ;; A branch's record is in another file: its pages first.
      (unless (eql pfd rfd) (fnps-timed t-sync (fnps-datasync pfd)))
      ;; The record.
      (fnps-timed t-rec
        (if (fnps-torn-here-p)
            (progn (fnps-write-to-file rfd (* slot 8) (fnps-m) slot 10)
                   (fnps-at :record-torn))
          (fnps-write-to-file rfd (* slot 8) (fnps-m) slot 20))
        (incf writes) (incf bytes 160))
      (fnps-at :record-written)
      (fnps-timed t-sync (fnps-datasync rfd))
      (fnps-at :record-synced)
      (pgs-x-commit-durable lpages (fnps-mem))
      (let ((k2 (if (= slot 0) 0 1)))
        (if (= k2 0)
            (setf (fnps-s0 s) rec (fnps-v0 s) t)
          (setf (fnps-s1 s) rec (fnps-v1 s) t))
        (setf (fnps-k s) k2 (fnps-rec s) rec (fnps-n s) (pgs-rec-npages rec)
              (fnps-alloc s) alloc2))
      (list :txid txid :dirty (length lpages) :tables-written (length tl) :dir-pages m
            :lpages (if (<= (length lpages) 64) lpages nil) :touched-tables tl
            :pages (pgs-rec-npages rec) :writes writes :bytes bytes
            :need-served *fnps-served* :syncs *fnps-syncs*
            :hwm (second alloc2)
            :ms-dirty-scan t-dirty :ms-plan t-plan :ms-need t-need :ms-pages t-pages
            :ms-tables t-tables :ms-dir t-dir :ms-record t-rec :ms-sync t-sync
            :ms-total (+ t-dirty t-plan t-need t-pages t-tables t-dir t-rec t-sync)))))

;; ---------------------------------------------------------------------------
;; Synthesis: fn-hist-shaped columns at ~100 B/record, written through
;; pgs-x-write (which keeps the dirty flags).

(defvar *fnps-rng* (sb-ext:seed-random-state 42))

(defun fnps-rand (n) (random n *fnps-rng*))

(defun fnps-put-word (i v)
  (let ((r (pgs-x-write (floor i +fnps-pw+) (mod i +fnps-pw+) v (fnps-mem))))
    (unless (eq r :ok) (error "pgs-x-write ~a at word ~a" r i))))

(defun fnps-msgid (i) (format nil "<~d.~8,'0x@fn.example>" i (fnps-rand #xffffffff)))

(defun fnps-pages-for (words) (ceiling words +fnps-pw+))

(defun fnps-synthesize (n salt)
  ;; Grows the (empty) image to the columns' pages; every page is dirty.
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
      (pgs-x-grow-image npages (fnps-mem))
      (dotimes (lp npages) (fnps-put-word (* lp +fnps-pw+) 0))
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
      npages)))

(defun fnps-write-zero-root (path)
  (let ((fd (fnps-open-file path :create t))
        (z (make-array 8192 :element-type '(unsigned-byte 8) :initial-element 0)))
    (fnps-write-to-file fd 0 z 0 8192)
    (fnps-fullsync fd)
    fd))

(defun fnps-init (dir n)
  ;; A fresh store: page 0 (root main's slots) zero and durable, then the
  ;; first commit (txid 1) of the synthesized columns over the empty table.
  (ensure-directories-exist (concatenate 'string dir "/"))
  (with-open-file (o (concatenate 'string dir "/inline") :direction :output :if-exists :supersede)
    (write-line "root main: slots in page 0 of the page file" o))
  (let ((fd (fnps-open-file (concatenate 'string dir "/inline"))))
    (fnps-fullsync fd)
    (sb-unix:unix-close fd))
  (let* ((t-syn 0)
         (pfd (fnps-open-file (fnps-pages-path dir) :create t))
         (z (make-array +fnps-pb+ :element-type '(unsigned-byte 8) :initial-element 0)))
    (fnps-write-to-file pfd 0 z 0 +fnps-pb+)
    (fnps-datasync pfd)
    (fnps-sync-dir dir)
    ;; The empty state: no records, a table of 0 entries, the slot words and
    ;; a one-page directory run of zeros.
    (resize-pgs-m 0 (fnps-mem))
    (resize-pgs-m (+ *pgs-x-dir-base* +fnps-pw+) (fnps-mem))
    (pgs-x-reset-table 0 (fnps-mem))
    (fnps-size-image 0)
    (let* ((npages (fnps-timed t-syn (fnps-synthesize n (fnps-rand #xffffffff))))
           (s (make-fnps :dir dir :root "main" :pages-fd pfd :root-fd pfd :mode :eager
                         :k nil :n 0 :alloc (list nil (fnps-file-pages pfd))))
           (c (fnps-commit s)))
      (fnps-emit :event :init :records n :pages npages :ms-synthesize t-syn
                 :commit (list* :event :commit c))
      (when (eq (first c) :refused) (error "init commit refused ~s" c))
      s)))

;; ---------------------------------------------------------------------------
;; Mutations.

(defun fnps-mutate-random (s count)
  ;; COUNT distinct pages (never the header), one word each, a new value:
  ;; read through the store (a lazy page loads and verifies), then write.
  (let* ((np (fnps-npages))
         (count (min count (1- np)))
         (chosen (make-hash-table)))
    (loop while (< (hash-table-count chosen) count)
          do (setf (gethash (1+ (fnps-rand (1- np))) chosen) t))
    (loop for lp being the hash-keys of chosen
          do (let ((off (fnps-rand +fnps-pw+)))
               (multiple-value-bind (v old) (fnps-read-word s lp off)
                 (unless (eq v :ok) (error "read of page ~a answered ~s" lp v))
                 (fnps-put-word (+ (* lp +fnps-pw+) off)
                                (logxor old (1+ (fnps-rand #xffffffffffff)))))))
    count))

(defun fnps-mutate-append (count)
  ;; COUNT new pages at the end of the image (history growth).
  (let* ((np (fnps-npages)) (np2 (+ np count)))
    (pgs-x-grow-image np2 (fnps-mem))
    (loop for lp from np below np2
          do (dotimes (off +fnps-pw+)
               (fnps-put-word (+ (* lp +fnps-pw+) off) (fnps-rand #xffffffffffffff))))
    count))

(defun fnps-image-digest (s)
  ;; The whole image, every page loaded and verified first: (values digest
  ;; refusals); the digest is nil when a page is refused.
  (let ((bad (fnps-load-all s)))
    (if bad
        (values nil bad)
      (values (pgs-x-words-digest 0 0 (* (fnps-npages) 256) (fnps-mem) (fnps-shs)) nil))))

(defun fnps-hex (d) (format nil "~64,'0x" d))

;; ---------------------------------------------------------------------------
;; Commands.

(defun fnps-first-requests (s)
  ;; The two first requests through the store (lazy: they load and verify
  ;; what they touch).
  (setf *fnps-served* 0 *fnps-read-calls* 0)
  (let* ((t-seq 0) (t-mid 0)
         (n (multiple-value-bind (v w) (fnps-timed t-seq
                                         (fnps-with-needs s (lambda () (pgs-x-rd 1 (fnps-mem) (fnps-shs)))))
              (if (eq v :ok) w 1)))
         (seq (fnps-rand (max 1 n))))
    (multiple-value-bind (v bytes)
        (fnps-timed t-seq (fnps-with-needs s (lambda () (pgs-x-lookup-seq seq (fnps-mem) (fnps-shs)))))
      (let ((served-seq *fnps-served*)
            (mid (map 'string #'code-char bytes)))
        (multiple-value-bind (v2 got)
            (fnps-timed t-mid (fnps-with-needs s (lambda () (pgs-x-lookup-msgid mid (fnps-mem) (fnps-shs)))))
          (list :seq seq :seq-verdict (fnps-refusal-string v) :msgid mid
                :msgid-verdict (fnps-refusal-string v2) :msgid-seq got
                :msgid-found (equal got seq)
                :loads-seq served-seq :loads-msgid (- *fnps-served* served-seq)
                :ms-lookup-seq t-seq :ms-lookup-msgid t-mid))))))

(defun fnps-cmd-open (dir root mode &key touch)
  (let* ((t0 (fnps-now))
         (s (fnps-open dir root mode)))
    (when s
      (let* ((fr (fnps-first-requests s))
             (ttfr (- (fnps-now) t0))
             (t-bg 0) (bad nil)
             (tv (when touch (fnps-refusal-string (fnps-read-word s touch 0)))))
        (when (and (eq mode :lazy) (not touch))
          (setf bad (fnps-timed t-bg (fnps-load-all s))))
        (fnps-emit :event :first-request :mode mode :requests fr
                   :ms-to-first-request ttfr
                   :touch touch :touch-verdict tv
                   :ms-background-pass t-bg
                   :background-refused (mapcar #'fnps-refusal-string bad)
                   :rss-kib (fnps-rss-kib)))
      (fnps-close s))
    s))

(defun fnps-cmd-mutate (dir root kind count fsyncs &key (mode :lazy) digest)
  (let ((s (fnps-open dir root mode :emit nil)))
    (unless s (fnps-emit :event :mutate :refused t) (return-from fnps-cmd-mutate nil))
    (let ((pre-txid (pgs-rec-txid (fnps-rec s))))
      (ecase kind
        (:random (fnps-mutate-random s count))
        (:append (fnps-mutate-append count)))
      (when digest
        (multiple-value-bind (d bad) (fnps-image-digest s)
          (fnps-emit :event :pre :from-txid pre-txid :next-digest (and d (fnps-hex d))
                     :refused (mapcar #'fnps-refusal-string bad))))
      (let ((c (fnps-commit s)))
        (fnps-emit :event :commit :kind kind :count count :fsyncs-arg fsyncs :mode mode :commit c)
        (when (eq (first c) :refused)
          (fnps-close s)
          (sb-ext:exit :code 5 :abort t))))
    (fnps-close s)))

(defun fnps-cmd-digest (dir root mode)
  (let ((s (fnps-open dir root mode)))
    (when s
      (multiple-value-bind (d bad) (fnps-image-digest s)
        (fnps-emit :event :digest :txid (pgs-rec-txid (fnps-rec s)) :mode mode
                   :digest (and d (fnps-hex d))
                   :refused (mapcar #'fnps-refusal-string bad)))
      (fnps-close s))))

(defun fnps-cmd-branch (dir src dst)
  (let ((s (fnps-open dir src :lazy :emit nil)) (t-branch 0))
    (fnps-timed t-branch
      ;; pgs-m[0, 1024) still holds the slot words read at open.
      (let* ((base (* 512 (fnps-k s)))
             (fd (fnps-write-zero-root (fnps-root-path dir dst))))
        (fnps-write-to-file fd 0 (fnps-m) base 20)
        (fnps-fullsync fd)
        (sb-unix:unix-close fd)
        (fnps-sync-dir dir)))
    (fnps-emit :event :branch :src src :dst dst :ms-branch t-branch
               :txid (pgs-rec-txid (fnps-rec s)))
    (fnps-close s)))

(defun fnps-cmd-damage (dir root what probe)
  ;; Flip one octet (byte 8) of a page under ROOT's newest valid record
  ;; (run twice to restore): WHAT is a logical page number, "table:T" or
  ;; "dir".  PROBE: report the page's address and writer txid, flip nothing.
  (setf *fnps-read-calls* 0 *fnps-absent* nil)
  (let* ((pfd (fnps-open-file (fnps-pages-path dir)))
         (rfd (fnps-open-root dir root pfd)))
    (destructuring-bind (s0 v0 s1 v1) (fnps-read-slots rfd)
      (let* ((k (car (pgs-open-order s0 v0 s1 v1)))
             (rec (if (eql k 0) s0 s1)))
        (unless k (error "no valid record to damage under"))
        (fnps-load-dir pfd rec)
        (let* ((npages (pgs-rec-npages rec))
               (phys nil) (etxid nil) (kind nil) (lpage nil))
          (cond
            ((string= what "dir")
             (setf kind :dir phys (pgs-rec-dir-addr rec) etxid (pgs-rec-txid rec)))
            ((and (> (length what) 6) (string= "table:" what :end2 6))
             (let* ((tp (parse-integer what :start 6))
                    (d (pgs-x-get-entry 1 *pgs-x-dir-base* tp (fnps-mem))))
               (setf kind :table lpage tp phys (first d) etxid (second d))))
            (t
             (let* ((lp (parse-integer what))
                    (tp (floor lp 341))
                    (d (pgs-x-get-entry 1 *pgs-x-dir-base* tp (fnps-mem))))
               (pgs-x-reset-table npages (fnps-mem))
               (fnps-load-pages pfd (fnps-t) (list (list tp (first d))))
               (let ((e (pgs-x-get-entry 2 0 lp (fnps-mem))))
                 (setf kind :page lpage lp phys (first e) etxid (second e))))))
          (unless probe
            (let ((b (make-array 1 :element-type '(unsigned-byte 8))))
              (fnps-fill-from-file pfd (+ 8 (* phys +fnps-pb+)) b 0 1)
              (setf (aref b 0) (logxor (aref b 0) #x5a))
              (fnps-write-to-file pfd (+ 8 (* phys +fnps-pb+)) b 0 1)
              (fnps-datasync pfd)))
          (fnps-emit :event :damage :kind kind :lpage lpage :phys phys :entry-txid etxid
                     :record-txid (pgs-rec-txid rec) :flipped (not probe) :pages npages))))
    (sb-unix:unix-close pfd)
    (unless (eql rfd pfd) (sb-unix:unix-close rfd))))

(defun fnps-cmd-cut-names ()
  (fnps-emit :event :cut-names :cuts (fnps-cut-names)))

(defun fnps-kw (s) (intern (string-upcase s) "KEYWORD"))

(defun fnps-main (args)
  ;; ARGS: a list of strings.  Seeds from FNPS_SEED.
  (sb-ext:disable-debugger)
  (let ((seed (sb-ext:posix-getenv "FNPS_SEED")))
    (when seed (setf *fnps-rng* (sb-ext:seed-random-state (parse-integer seed)))))
  (let ((cmd (first args)) (a (rest args)))
    (handler-case
        (cond
          ;; init DIR N [inline]: the inline layout is the only one.
          ((string= cmd "init") (fnps-close (fnps-init (first a) (parse-integer (second a)))))
          ((string= cmd "open")
           (fnps-cmd-open (first a) (second a) (fnps-kw (third a))
                          :touch (and (fourth a) (parse-integer (fourth a)))))
          ((string= cmd "mutate")
           (fnps-cmd-mutate (first a) (second a) (fnps-kw (third a))
                            (parse-integer (fourth a)) (parse-integer (fifth a))
                            :mode (if (sixth a) (fnps-kw (sixth a)) :lazy)
                            :digest (sb-ext:posix-getenv "FNPS_DIGEST")))
          ((string= cmd "digest") (fnps-cmd-digest (first a) (second a) (fnps-kw (or (third a) "eager"))))
          ((string= cmd "branch") (fnps-cmd-branch (first a) (second a) (third a)))
          ((string= cmd "damage") (fnps-cmd-damage (first a) (second a) (third a)
                                                   (equal (fourth a) "probe")))
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
