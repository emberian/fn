; books/owner-export-request.lisp -- `store export DIR' on the RUNNING owner
; (row S3, lane operability-4): the request's words and the client's lines.
;
; The offline export (host/native/io.lisp fnn-command-store-export) takes the
; store under its writer lock, so on a running node the operator's verb goes
; to the owner over PKT-868's administrative route as the request
; `export request DIR' (host/native/admin.lisp fnn-owner-export-request).
; Under the owner mutex ACL2 answers the request's WORD from two
; observations: whether an export is already in flight (the service's
; exporter slot) and whether DIR exists (lstat, read off the mutex before
; the quantum that decides with it).  A request answered :requested
; captures the history O(1) under the mutex (the record list by pointer,
; the configuration history, the frontier: what the publication captures,
; host/owner-host.lisp fn-owner-sco-capture), and the archive is written on
; its own thread off the mutex in bounded chunks by the offline writer's own
; steps (fn-sxp-export-head, fn-sxp-export-chunk, fnn-export-step: the
; records' octets are fn-store-sco-encode-records over the captured rows
; with the live arena, the encoding the offline export reads a checkpoint's
; prefix by).  books/store-export-stream.lisp fn-sxp-stream-is-the-export and
; books/store-export-durability.lisp fn-sxd-crash-is-incomplete-or-complete
; stand unchanged: the same host functions run over the captured octets.
; The client polls `export status' and prints the outcome.
;
; Words.  A request: :requested (accepted); :export-in-flight and
; :archive-exists (refused by name, each with what it would take).  A
; status: :in-flight, :done, :failed, :idle.  The reasoned reply carries one
; word (books/native-control-reason.lisp fn-nctrl-reason-word); the client
; reads it back (fn-oex-word-of-octets: the reply's octets to the word, or
; nil for any other octets, which the client reports as uncertain).

(in-package "ACL2")
(include-book "native-control-reason")

; -----------------------------------------------------------------------------
; The request

(defun fn-oex-request-word (inflightp existsp)
  (declare (xargs :guard t))
  (cond (inflightp :export-in-flight)
        (existsp :archive-exists)
        (t :requested)))

(defun fn-oex-request-status (word)
  (declare (xargs :guard t))
  (if (equal word :requested) :accepted :refused))

; KEYSTONE fn-oex-one-export-in-flight: an export in flight refuses every
; request by that name, and a request is :requested exactly when none is in
; flight and DIR is absent -- the owner never writes two archives at once and
; never writes into an existing DIR.
(defthm fn-oex-one-export-in-flight
  (and (implies inflightp
                (equal (fn-oex-request-word inflightp existsp) :export-in-flight))
       (iff (equal (fn-oex-request-word inflightp existsp) :requested)
            (and (not inflightp) (not existsp)))))

(defthm fn-oex-request-accepted-exactly-when-requested
  (iff (equal (fn-oex-request-status (fn-oex-request-word inflightp existsp)) :accepted)
       (and (not inflightp) (not existsp))))

; -----------------------------------------------------------------------------
; The status: the exporter slot is in flight, or holds the last outcome
; ((:done . N) or (:failed . REASON)), or nothing since the start.

(defun fn-oex-status-word (inflightp outcome)
  (declare (xargs :guard t))
  (cond (inflightp :in-flight)
        ((and (consp outcome) (equal (car outcome) :done)) :done)
        ((and (consp outcome) (equal (car outcome) :failed)) :failed)
        (t :idle)))

(defun fn-oex-status-status (word)
  (declare (xargs :guard t))
  (if (equal word :failed) :refused :accepted))

(defthm fn-oex-in-flight-is-the-status-while-writing
  (iff (equal (fn-oex-status-word inflightp outcome) :in-flight)
       (and inflightp t)))

; -----------------------------------------------------------------------------
; The client's reading of a reply's word

(defconst *fn-oex-words*
  '(:requested :export-in-flight :archive-exists :in-flight :done :failed :idle))

(defun fn-oex-word-of-octets-loop (octets words)
  (declare (xargs :guard t))
  (cond ((atom words) nil)
        ((equal octets (fn-nctrl-reason-word (car words))) (car words))
        (t (fn-oex-word-of-octets-loop octets (cdr words)))))

(defun fn-oex-word-of-octets (octets)
  (declare (xargs :guard t))
  (fn-oex-word-of-octets-loop octets *fn-oex-words*))

; Every word the owner answers reads back as itself from its reply octets.
(defthm fn-oex-word-reads-back
  (implies (member-equal word *fn-oex-words*)
           (equal (fn-oex-word-of-octets (fn-nctrl-reason-word word)) word)))

; -----------------------------------------------------------------------------
; The client's lines (the verb's stdout; the exit code is the status's)

(defun fn-oex-request-line (word dir)
  (declare (xargs :guard (stringp dir)))
  (cond ((equal word :requested)
         (concatenate 'string "export requested archive=" dir
                      ": the owner is writing it while serving; this verb waits for the outcome"))
        ((equal word :export-in-flight)
         "export refused reason=export-in-flight: the owner is writing an archive already; what it would take: wait for its `EXPORT done' log line (or `store export --status'), then request again")
        ((equal word :archive-exists)
         (concatenate 'string "export refused reason=archive-exists: " dir
                      " exists; what it would take: another DIR, or remove it"))
        (t "export uncertain reason=unrecognized-word: the owner answered a word this release does not know")))

(defun fn-oex-outcome-line (word dir)
  (declare (xargs :guard (stringp dir)))
  (cond ((equal word :done)
         (concatenate 'string "exported archive=" dir
                      ": complete (its MANIFEST is written; `store import' reads it)"))
        ((equal word :failed)
         (concatenate 'string "export failed archive=" dir
                      ": no MANIFEST was written (the owner's log names the reason: `EXPORT failed reason=...'); what it would take: remove "
                      dir " and request again"))
        ((equal word :in-flight)
         "export in-flight: the owner is still writing the archive")
        ((equal word :idle)
         "export idle: no export is in flight and none has finished since the owner started")
        (t "export uncertain reason=unrecognized-word: the owner answered a word this release does not know")))

; `store export --status' with no owner (fn-omr-route :offline): nothing is
; in flight and nothing finished, because no owner is serving; by name.
(defun fn-oex-status-no-owner-line ()
  (declare (xargs :guard t))
  "export status refused reason=no-owner: no owner is serving this store, so no export is in flight; what it would take: `store export DIR' with the node stopped runs to completion in this verb")
