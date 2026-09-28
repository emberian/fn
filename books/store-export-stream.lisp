; fn: `store export' a chunk at a time (lane scale-reads-export, 2026-09-28).
; Prefix `fn-sxp-'.
;
; The export wrote its archive from one call over the whole history
; (fn-sxp-entries, fn-sxp-manifest over every record as an octet list): at
; 1,000,000 records of 2 KiB that exhausted a 32 GB heap.  The host now reads
; the history as the open read it a chunk of records at a time
; (host/native/io.lisp fnn-log-history-each) and asks ACL2 for each step's
; entries and MANIFEST lines:
;   fn-sxp-export-head   the profile, frontier and configuration entries and
;                        their lines, once, first;
;   fn-sxp-export-chunk  one chunk of (SEQUENCE . OCTETS) records' entries and
;                        their lines.
; It writes each step's entries as it gets them and appends each step's lines
; to the MANIFEST it publishes last.  The work and allocation per step are one
; chunk's (the host's quantum, never a bound on the store: every record is
; in exactly one chunk).
;
; KEYSTONE fn-sxp-stream-is-the-export: for EVERY chunking of the records,
; the entries the host writes, in order, are fn-sxp-entries of the whole
; history and the MANIFEST octets it writes are fn-sxp-manifest of them --
; the archive the whole-list export wrote, byte for byte.  No hypotheses.

(in-package "ACL2")
(include-book "store-export")

; -----------------------------------------------------------------------------
; The steps the host calls.

(defun fn-sxp-head-entries (profile frontier configs)
  (declare (xargs :guard t))
  (list* (cons *fn-sxp-profile-name* profile)
         (cons *fn-sxp-frontier-name* frontier)
         (fn-sxp-config-entries configs)))

(defun fn-sxp-export-head (profile frontier configs)
  (declare (xargs :guard t))
  (let ((entries (fn-sxp-head-entries profile frontier configs)))
    (cons entries (fn-sxp-manifest entries))))

(defun fn-sxp-export-chunk (records)
  (declare (xargs :guard t))
  (let ((entries (fn-sxp-record-entries records)))
    (cons entries (fn-sxp-manifest entries))))

; -----------------------------------------------------------------------------
; What the host writes over a chunking CHUNKS of the history (a specification
; of the host's loop; the host never calls these).

(defun fn-sxp-chunks-records (chunks)
  (declare (xargs :guard (true-list-listp chunks)))
  (if (consp chunks)
      (append (car chunks) (fn-sxp-chunks-records (cdr chunks)))
    nil))

(defun fn-sxp-stream-chunk-entries (chunks)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp chunks)
      (append (car (fn-sxp-export-chunk (car chunks)))
              (fn-sxp-stream-chunk-entries (cdr chunks)))
    nil))

(defun fn-sxp-stream-chunk-manifest (chunks)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp chunks)
      (append (cdr (fn-sxp-export-chunk (car chunks)))
              (fn-sxp-stream-chunk-manifest (cdr chunks)))
    nil))

(defun fn-sxp-stream-entries (profile frontier configs chunks)
  (declare (xargs :guard t :verify-guards nil))
  (append (car (fn-sxp-export-head profile frontier configs))
          (fn-sxp-stream-chunk-entries chunks)))

(defun fn-sxp-stream-manifest (profile frontier configs chunks)
  (declare (xargs :guard t :verify-guards nil))
  (append (cdr (fn-sxp-export-head profile frontier configs))
          (fn-sxp-stream-chunk-manifest chunks)))

; -----------------------------------------------------------------------------
; The lemmas: entries and MANIFEST lines distribute over append.

(defthm fn-sxp-entries-unfolds
  (equal (fn-sxp-entries profile frontier configs records)
         (append (fn-sxp-head-entries profile frontier configs)
                 (fn-sxp-record-entries records))))

(defthm fn-sxp-record-entries-of-append
  (equal (fn-sxp-record-entries (append a b))
         (append (fn-sxp-record-entries a) (fn-sxp-record-entries b)))
  :hints (("Goal" :in-theory (disable fn-sxp-record-name))))

(defthm fn-sxp-manifest-under-of-append
  (equal (fn-sxp-manifest-under f9p (append a b))
         (append (fn-sxp-manifest-under f9p a) (fn-sxp-manifest-under f9p b)))
  :hints (("Goal" :in-theory (disable fn-sxp-manifest-line-under))))

(local
 (defthm fn-sxp-stream-chunk-entries-is-record-entries
   (equal (fn-sxp-stream-chunk-entries chunks)
          (fn-sxp-record-entries (fn-sxp-chunks-records chunks)))
   :hints (("Goal" :in-theory (disable fn-sxp-record-entries)))))

(local
 (defthm fn-sxp-stream-chunk-manifest-is-manifest
   (equal (fn-sxp-stream-chunk-manifest chunks)
          (fn-sxp-manifest-under nil (fn-sxp-record-entries (fn-sxp-chunks-records chunks))))
   :hints (("Goal" :in-theory (disable fn-sxp-record-entries fn-sxp-manifest-under)))))

; KEYSTONE (the subject: the steps host/native/io.lisp
; fnn-command-store-export calls, fn-sxp-export-head then fn-sxp-export-chunk
; per chunk, composed in the host's order).
(defthm fn-sxp-stream-is-the-export
  (and (equal (fn-sxp-stream-entries profile frontier configs chunks)
              (fn-sxp-entries profile frontier configs
                              (fn-sxp-chunks-records chunks)))
       (equal (fn-sxp-stream-manifest profile frontier configs chunks)
              (fn-sxp-manifest
               (fn-sxp-entries profile frontier configs
                               (fn-sxp-chunks-records chunks)))))
  :hints (("Goal" :in-theory (disable fn-sxp-record-entries fn-sxp-manifest-under
                                      fn-sxp-head-entries))))
