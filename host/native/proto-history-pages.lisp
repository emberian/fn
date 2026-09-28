;;; host/native/proto-history-pages.lisp -- the history image's host over the
;;; page store (lane arena-store-4, 2026-09-28, m4).  Raw Lisp, loaded after
;;; host/native/proto-pagestore.lisp in the page-store image that also
;;; includes books/history-pages-import and books/history-pages-view
;;; (tools/proto/pagestore_bench.py `build').  A PROTOTYPE host: the served
;;; owner does not call it (the owner wiring is P1's host side, not this).
;;;
;;; What the host decides: which file to read, how many events per batch,
;;; when to commit, where the process may die (the page store's cuts,
;;; `fnps-at', inside `fnps-commit').  Every value is ACL2's:
;;;   create   fn-hp-x-init                  the empty image and its header
;;;            answer (N LENS STARTS NP)
;;;   import   fn-scc-decode-tree            each event from its octets
;;;            fn-hp-x-append-all            a batch of events appended; its
;;;            header answer is carried whatever the verdict, and a
;;;            need-verdict ((:need-table T P) / (:need-page P PHYS)) is
;;;            served by one fill (`fnps-serve-need') and the rest of the
;;;            batch asked again
;;;   commit   pgs-x-commit (through `fnps-commit', the page store's host)
;;;   open     pgs-x-* (through `fnps-open'), then fn-hp-x-header over the
;;;            record's page count
;;;   read     fn-hp-records-at              record I (no in-memory suffix
;;;            here: the suffix is the served owner's), needs served
;;; Keystones: fn-hp-x-init-refines, fn-hp-x-append-all-refines
;;; (books/history-pages-import.lisp), fn-hp-x-append-step-refines
;;; (books/history-pages-step.lisp), fn-hp-x-header-of-image
;;; (books/history-pages-row.lisp), fn-hp-records-at-is-nth
;;; (books/history-pages-view.lisp), pgs-x-commit-refines
;;; (books/pagestore-exec.lisp).
;;;
;;; The events file (tools/proto/history_export.lisp writes it from a native
;;; image's open of a store): per event an 8-octet little-endian length and
;;; that many octets of `fn-scc-encode'.  The frame length is the one value
;;; this file computes; the octets are ACL2's to decode, and an event that
;;; does not decode is refused by name (never skipped).
;;;
;;; SALT is the history's MKEY salt, an argument (the image's header does not
;;; carry it; the served owner's salt is the owner wiring's).

(in-package "ACL2")

;; ---------------------------------------------------------------------------
;; The events file.

(defun fnhp-read-frame (in)
  ;; The next frame's octets as a list, or nil at end of file.  A short
  ;; frame is an error by name.
  (let ((hdr (make-array 8 :element-type '(unsigned-byte 8))))
    (let ((got (read-sequence hdr in)))
      (cond ((zerop got) nil)
            ((< got 8) (error "events file: a torn frame header"))
            (t (let* ((len (loop for b from 0 below 8 sum (ash (aref hdr b) (* 8 b))))
                      (v (make-array len :element-type '(unsigned-byte 8))))
                 (unless (= (read-sequence v in) len) (error "events file: a torn frame"))
                 (coerce v 'list)))))))

(defun fnhp-skip-frames (in k)
  (let ((hdr (make-array 8 :element-type '(unsigned-byte 8))))
    (dotimes (i k)
      (unless (= (read-sequence hdr in) 8) (error "events file: fewer than ~d frames" k))
      (file-position in (+ (file-position in)
                           (loop for b from 0 below 8 sum (ash (aref hdr b) (* 8 b))))))))

(defun fnhp-decode (octets index)
  (let ((r (fn-scc-decode-tree octets)))
    (unless (eq (first r) :ok)
      (error "events file: event ~d refused by fn-scc-decode-tree: ~s" index r))
    (second r)))

(defun fnhp-read-events (in k index)
  ;; Up to K events, decoded by ACL2.  (values events octets)
  (let ((evs nil) (octets 0))
    (loop repeat k
          for o = (fnhp-read-frame in)
          while o
          do (push (fnhp-decode o (+ index (length evs))) evs)
             (incf octets (length o)))
    (values (nreverse evs) octets)))

;; ---------------------------------------------------------------------------
;; The handle: the page store's, the salt, and the header answer ACL2 gave.

(defstruct fnhp s salt n lens starts np)

(defun fnhp-header-plist (h)
  (list :n (fnhp-n h) :lens (fnhp-lens h) :starts (fnhp-starts h) :np (fnhp-np h)))

(defvar *fnhp-t-append* 0)

(defun fnhp-append-evs (h evs)
  ;; EVS appended through fn-hp-x-append-all.  Returns (values verdict
  ;; appended): :ok, or the first verdict the host cannot serve.  The header
  ;; answer is carried after every call, whatever its verdict.
  (let ((done 0))
    (loop
      (multiple-value-bind (v k n2 lens2 starts2 np2)
          (fnps-timed *fnhp-t-append*
            (fn-hp-x-append-all evs 0 (fnhp-salt h) (fnhp-n h) (fnhp-lens h) (fnhp-starts h)
                                (fnhp-np h) (fnps-mem)))
        (setf (fnhp-n h) n2 (fnhp-lens h) lens2 (fnhp-starts h) starts2 (fnhp-np h) np2)
        (incf done k)
        (setf evs (nthcdr k evs))
        (cond ((eq v :ok) (return (values :ok done)))
              ((and (fnps-need-p v) (fnhp-s h) (fnps-rec (fnhp-s h)))
               (let ((r (fnps-serve-need (fnhp-s h) v)))
                 (when r (return (values r done)))))
              (t (return (values v done))))))))

(defun fnhp-header (h)
  ;; fn-hp-x-header over the committed record's page count, needs served.
  ;; Sets the header answer from (:ok N LENS STARTS); returns the result.
  (let ((s (fnhp-s h)))
    (multiple-value-bind (v result)
        (fnps-with-needs s (lambda () (fn-hp-x-header (fnps-n s) (fnps-mem))))
      (cond ((not (eq v :ok)) (list :unserved v))
            ((eq (first result) :ok)
             (setf (fnhp-n h) (second result) (fnhp-lens h) (third result)
                   (fnhp-starts h) (fourth result) (fnhp-np h) (fnps-n s))
             result)
            (t result)))))

(defun fnhp-hex (octets) (format nil "~{~2,'0x~}" octets))

(defun fnhp-record (h i &key hex)
  ;; Record I through fn-hp-records-at: a plist.
  (setf *fnps-served* 0 *fnps-read-calls* 0)
  (let ((t0 (fnps-now)))
    (multiple-value-bind (v result)
        (fnps-with-needs (fnhp-s h)
                         (lambda () (fn-hp-records-at i (fnhp-n h) nil (fnhp-salt h) (fnhp-lens h)
                                                      (fnhp-starts h) (fnps-mem))))
      (let* ((ms (- (fnps-now) t0))
             (ok (and (eq v :ok) (consp result) (eq (first result) :ok)))
             (enc (and ok (fn-scc-encode (second result)))))
        (list :i i :verdict (fnps-refusal-string v)
              :result (if ok :ok (fnps-refusal-string result))
              :enc-len (and ok (length enc)) :enc-hex (and ok hex (fnhp-hex enc))
              :loads *fnps-served* :read-calls *fnps-read-calls* :ms ms)))))

;; ---------------------------------------------------------------------------
;; Import: a fresh page store holding the image of the file's first LIMIT
;; events, in one commit.

(defun fnhp-create-store (dir)
  ;; As fnps-init: page 0 (root main's slots) zero and durable, the empty
  ;; state in the stobj.  Returns the page-file descriptor.
  (ensure-directories-exist (concatenate 'string dir "/"))
  (with-open-file (o (concatenate 'string dir "/inline") :direction :output :if-exists :supersede)
    (write-line "root main: slots in page 0 of the page file" o))
  (let ((fd (fnps-open-file (concatenate 'string dir "/inline"))))
    (fnps-fullsync fd)
    (sb-unix:unix-close fd))
  (let ((pfd (fnps-open-file (fnps-pages-path dir) :create t))
        (z (make-array +fnps-pb+ :element-type '(unsigned-byte 8) :initial-element 0)))
    (fnps-write-to-file pfd 0 z 0 +fnps-pb+)
    (fnps-datasync pfd)
    (fnps-sync-dir dir)
    (resize-pgs-m 0 (fnps-mem))
    (resize-pgs-m (+ *pgs-x-dir-base* +fnps-pw+) (fnps-mem))
    (pgs-x-reset-table 0 (fnps-mem))
    (fnps-size-image 0)
    pfd))

(defun fnhp-import (dir evfile salt batch limit &key digest)
  (let* ((pfd (fnhp-create-store dir))
         (s (make-fnps :dir dir :root "main" :pages-fd pfd :root-fd pfd :mode :eager
                       :k nil :n 0 :alloc (list nil (fnps-file-pages pfd))))
         (t0 (fnps-now)) (t-read 0) (octets 0) (count 0) (batches 0))
    (setf *fnhp-t-append* 0)
    (multiple-value-bind (v n lens starts np) (fn-hp-x-init (fnps-mem))
      (unless (eq v :ok) (error "fn-hp-x-init answered ~s" v))
      (let ((h (make-fnhp :s nil :salt salt :n n :lens lens :starts starts :np np)))
        (with-open-file (in evfile :element-type '(unsigned-byte 8))
          (loop
            (let ((want (if limit (min batch (- limit count)) batch)))
              (when (<= want 0) (return))
              (multiple-value-bind (evs o) (fnps-timed t-read (fnhp-read-events in want count))
                (when (null evs) (return))
                (incf octets o) (incf batches)
                (multiple-value-bind (verdict k) (fnhp-append-evs h evs)
                  (incf count k)
                  (unless (eq verdict :ok)
                    (fnps-emit :event :hp-import-refused :at count
                               :verdict (fnps-refusal-string verdict))
                    (sb-ext:exit :code 6 :abort t)))))))
        (let ((t-import (- (fnps-now) t0)))
          (when digest
            (multiple-value-bind (d shs) (pgs-x-words-digest 0 0 (* (fnps-npages) 256) (fnps-mem) (fnps-oct))
              (declare (ignore shs))
              (apply #'fnps-emit :event :hp-pre :from-txid 0 :next-digest (fnps-hex d)
                     (fnhp-header-plist h))))
          (fnps-emit :event :hp-imported :records count :octets octets :batches batches
                     :pages (fnps-npages) :ms-read-decode t-read :ms-append *fnhp-t-append*
                     :ms-import t-import :rss-kib (fnps-rss-kib))
          (let ((c (fnps-commit s)))
            (apply #'fnps-emit :event :hp-import :records count :commit (list* :event :commit c)
                   :file-pages (fnps-file-pages pfd) :rss-kib (fnps-rss-kib)
                   (fnhp-header-plist h))
            (when (eq (first c) :refused) (sb-ext:exit :code 5 :abort t))
            (fnps-close s)))))))

;; ---------------------------------------------------------------------------
;; Open, read, append.

(defun fnhp-open (dir salt mode)
  ;; (values handle header-result ms-header loads) or nil when no commit opens.
  (let ((s (fnps-open dir "main" mode)))
    (when s
      (let ((h (make-fnhp :s s :salt salt)) (t0 (fnps-now)))
        (setf *fnps-served* 0)
        (let ((r (fnhp-header h)))
          (values h r (- (fnps-now) t0) *fnps-served*))))))

(defun fnhp-cmd-open (dir salt mode reads hex digest)
  ;; The open, the header, then READS: record indices (a negative index
  ;; counts from the end: -1 is the last record).
  (let ((t0 (fnps-now)))
    (multiple-value-bind (h r ms-header loads) (fnhp-open dir salt mode)
      (if (null h)
          (fnps-emit :event :hp-open :landed nil)
        (let ((ms-open-header (- (fnps-now) t0)))
          (apply #'fnps-emit :event :hp-open :landed t :txid (pgs-rec-txid (fnps-rec (fnhp-s h)))
                 :header (if (eq (first r) :ok) :ok (fnps-refusal-string r))
                 :ms-header ms-header :header-loads loads :ms-open-header ms-open-header
                 :rss-kib (fnps-rss-kib)
                 (fnhp-header-plist h))
          (when (eq (first r) :ok)
            (dolist (i reads)
              (let ((j (if (< i 0) (+ (fnhp-n h) i) i)))
                (when (<= 0 j)
                  (apply #'fnps-emit :event :hp-record :ms-since-start (- (fnps-now) t0)
                         (fnhp-record h j :hex hex))))))
          (when digest
            (multiple-value-bind (d bad) (fnps-image-digest (fnhp-s h))
              (fnps-emit :event :digest :txid (pgs-rec-txid (fnps-rec (fnhp-s h))) :mode mode
                         :digest (and d (fnps-hex d))
                         :refused (mapcar #'fnps-refusal-string bad))))
          (fnps-emit :event :hp-rss :rss-kib (fnps-rss-kib))
          (fnps-close (fnhp-s h)))))))

(defun fnhp-cmd-append (dir evfile from k salt mode digest)
  ;; Open, the header, K events from index FROM of EVFILE appended, one
  ;; commit.  FNPS_DIGEST: the image digest before the commit (:hp-pre).
  (multiple-value-bind (h r) (fnhp-open dir salt mode)
    (unless (and h (eq (first r) :ok))
      (fnps-emit :event :hp-append :refused (if h (fnps-refusal-string r) "no commit opens"))
      (sb-ext:exit :code 5 :abort t))
    (let ((s (fnhp-s h)) (t-read 0) (from-n (fnhp-n h)))
      (setf *fnhp-t-append* 0 *fnps-served* 0)
      (let ((evs (with-open-file (in evfile :element-type '(unsigned-byte 8))
                   (fnps-timed t-read
                     (fnhp-skip-frames in from)
                     (fnhp-read-events in k from)))))
        (multiple-value-bind (verdict done) (fnhp-append-evs h evs)
          (unless (eq verdict :ok)
            (fnps-emit :event :hp-append :refused (fnps-refusal-string verdict) :appended done)
            (sb-ext:exit :code 6 :abort t))
          (let ((served *fnps-served*))
            (when digest
              (multiple-value-bind (d bad) (fnps-image-digest s)
                (apply #'fnps-emit :event :hp-pre :from-txid (pgs-rec-txid (fnps-rec s))
                       :next-digest (and d (fnps-hex d)) :refused (mapcar #'fnps-refusal-string bad)
                       (fnhp-header-plist h))))
            (let ((c (fnps-commit s)))
              (apply #'fnps-emit :event :hp-append :from-n from-n :appended done
                     :ms-read-decode t-read :ms-append *fnhp-t-append* :append-loads served
                     :commit (list* :event :commit c) :rss-kib (fnps-rss-kib)
                     (fnhp-header-plist h))
              (fnps-close s)
              (when (eq (first c) :refused) (sb-ext:exit :code 5 :abort t)))))))))

(defun fnhp-main (args)
  ;; ARGS: a list of strings.
  ;;   import DIR EVFILE SALT BATCH [LIMIT]
  ;;   open DIR SALT MODE [I ...]        (FNHP_HEX=1: record octets in hex)
  ;;   append DIR EVFILE FROM K SALT MODE
  ;; FNPS_DIGEST=1: image digests (import/append before the commit, open after).
  (sb-ext:disable-debugger)
  (let ((cmd (first args)) (a (rest args))
        (digest (equal (sb-ext:posix-getenv "FNPS_DIGEST") "1")))
    (handler-case
        (cond
          ((string= cmd "import")
           (fnhp-import (first a) (second a) (parse-integer (third a)) (parse-integer (fourth a))
                        (and (fifth a) (parse-integer (fifth a))) :digest digest))
          ((string= cmd "open")
           (fnhp-cmd-open (first a) (parse-integer (second a)) (fnps-kw (third a))
                          (mapcar #'parse-integer (nthcdr 3 a))
                          (equal (sb-ext:posix-getenv "FNHP_HEX") "1") digest))
          ((string= cmd "append")
           (fnhp-cmd-append (first a) (second a) (parse-integer (third a)) (parse-integer (fourth a))
                            (parse-integer (fifth a)) (fnps-kw (sixth a)) digest))
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
