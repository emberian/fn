; books/owner-snapshot-request.lisp -- `store snapshot DIR' on the RUNNING
; owner and `store bless-snapshot DIR' (row S7, lane operability-12,
; PRF-1050): the request's words, the blessing's verdict and the client's
; lines.
;
; A snapshot is a copy of the store's files as the open reads them: the
; checkpoint file (if one is published), every segment of journal/ with the
; genesis, the active segment cut at the log kernel's committed FRONTIER
; (host/native/io.lisp fn-lgc-frontier: an appended but unfenced batch lies
; past it and is never history) and preallocated to the extent the owner
; had given it, config.json, config/, keys/, auth.toml and
; filesystem-identity.fnmi when present.  Nothing is decoded, digested or
; re-rendered: the copy is a store directory, and a restore is `cp -a DIR
; STORE` and a start.  On a running node the operator's verb goes to the
; owner over PKT-868's administrative route as `snapshot request DIR'
; (host/native/admin.lisp fnn-owner-snapshot-request).  Under the owner
; mutex ACL2 answers the request's WORD from two observations: whether a
; snapshot is already in flight (the service's snapshotter slot) and whether
; DIR exists (lstat, read off the mutex before the quantum that decides
; with it).  A request answered :requested captures the store's file set
; under the mutex -- one open descriptor per file the copy will read, the
; journal and config/ listings, the kernel's frontier -- so that a
; publication that replaces the checkpoint (a rename) or a compaction that
; drops a covered segment (an unlink) after the capture changes nothing the
; copy reads: an unlinked file stays readable through its descriptor.  The
; copy never reads the arena, so it takes no arena pin
; (books/arena-reader-pins.lisp governs the in-memory staged pages a
; COMPLETE retires, not files).  The copy runs on its own thread off the
; mutex in bounded chunks with the publication's yield, and the marker file
; SNAPSHOT is written LAST by the export's durability program's shape
; (books/store-export-durability.lisp fn-sxd-program with the marker as the
; MANIFEST: data written, one sync, the marker staged, fenced and renamed
; into place, DIR fenced): a snapshot that ended anywhere earlier has no
; marker, and `bless-snapshot' refuses it by that name, never opens it.
;
; Words.  A request: :requested (accepted); :snapshot-in-flight and
; :target-exists (refused by name, each with what it would take).  A
; status: :in-flight, :done, :failed, :idle.  The reasoned reply carries one
; word (books/native-control-reason.lisp fn-nctrl-reason-word); the client
; reads it back (fn-osn-word-of-octets: the reply's octets to the word, or
; nil for any other octets, which the client reports as uncertain).
;
; The blessing (`store bless-snapshot DIR', offline, on the copy): ACL2's
; verdict over three observations the host reads in this order -- the
; marker is present (fnn-check-regular of DIR/SNAPSHOT), the copy OPENS as
; a store (host/native/io.lisp fnn-open-live-store of DIR, read-only: the
; checkpoint's log position against segment K's rotation head,
; books/store-log-lineage.lisp fn-lgl-open, refuses a checkpoint from
; another lineage `foreign-lineage' by name, and every other open refusal
; keeps its name) and keys/ holds the node secret (`run' refuses a store
; without one; the blessing names it here, at the copy, not at the next
; start).  KEYSTONE fn-osn-bless-word-blessed-exactly-when (PRF-1050): the
; verdict is :blessed exactly when all three hold; otherwise it is the
; first failing observation's name: :snapshot-incomplete, the open's
; refusal (:open-refused, its sentence carried), :no-node-secret.  An
; absent marker is never opened: the verdict is decided before the open
; observation is taken (fn-osn-bless-open-needed).

(in-package "ACL2")
(include-book "native-control-reason")

; -----------------------------------------------------------------------------
; The request

(defun fn-osn-request-word (inflightp existsp)
  (declare (xargs :guard t))
  (cond (inflightp :snapshot-in-flight)
        (existsp :target-exists)
        (t :requested)))

(defun fn-osn-request-status (word)
  (declare (xargs :guard t))
  (if (equal word :requested) :accepted :refused))

; KEYSTONE fn-osn-one-snapshot-in-flight: a snapshot in flight refuses every
; request by that name, and a request is :requested exactly when none is in
; flight and DIR is absent -- the owner never copies twice at once and never
; copies into an existing DIR.
(defthm fn-osn-one-snapshot-in-flight
  (and (implies inflightp
                (equal (fn-osn-request-word inflightp existsp) :snapshot-in-flight))
       (iff (equal (fn-osn-request-word inflightp existsp) :requested)
            (and (not inflightp) (not existsp)))))

(defthm fn-osn-request-accepted-exactly-when-requested
  (iff (equal (fn-osn-request-status (fn-osn-request-word inflightp existsp)) :accepted)
       (and (not inflightp) (not existsp))))

; -----------------------------------------------------------------------------
; The status: the snapshotter slot is in flight, or holds the last outcome
; ((:done . FILES) or (:failed . REASON)), or nothing since the start.

(defun fn-osn-status-word (inflightp outcome)
  (declare (xargs :guard t))
  (cond (inflightp :in-flight)
        ((and (consp outcome) (equal (car outcome) :done)) :done)
        ((and (consp outcome) (equal (car outcome) :failed)) :failed)
        (t :idle)))

(defun fn-osn-status-status (word)
  (declare (xargs :guard t))
  (if (equal word :failed) :refused :accepted))

(defthm fn-osn-in-flight-is-the-status-while-copying
  (iff (equal (fn-osn-status-word inflightp outcome) :in-flight)
       (and inflightp t)))

; -----------------------------------------------------------------------------
; The client's reading of a reply's word

(defconst *fn-osn-words*
  '(:requested :snapshot-in-flight :target-exists :in-flight :done :failed :idle))

(defun fn-osn-word-of-octets-loop (octets words)
  (declare (xargs :guard t))
  (cond ((atom words) nil)
        ((equal octets (fn-nctrl-reason-word (car words))) (car words))
        (t (fn-osn-word-of-octets-loop octets (cdr words)))))

(defun fn-osn-word-of-octets (octets)
  (declare (xargs :guard t))
  (fn-osn-word-of-octets-loop octets *fn-osn-words*))

; Every word the owner answers reads back as itself from its reply octets.
(defthm fn-osn-word-reads-back
  (implies (member-equal word *fn-osn-words*)
           (equal (fn-osn-word-of-octets (fn-nctrl-reason-word word)) word)))

; -----------------------------------------------------------------------------
; The blessing's verdict (PRF-1050)

; Whether the open observation is needed at all: only over a present marker.
(defun fn-osn-bless-open-needed (markerp)
  (declare (xargs :guard t))
  (and markerp t))

; OPEN is :ok or the open's refusal sentence (a string); KEYSP whether keys/
; holds the node secret.
(defun fn-osn-bless-word (markerp open keysp)
  (declare (xargs :guard t))
  (cond ((not markerp) :snapshot-incomplete)
        ((not (equal open :ok)) :open-refused)
        ((not keysp) :no-node-secret)
        (t :blessed)))

(defun fn-osn-bless-status (word)
  (declare (xargs :guard t))
  (if (equal word :blessed) :accepted :refused))

; KEYSTONE fn-osn-bless-word-blessed-exactly-when (PRF-1050): blessed exactly
; when the marker is present, the copy opened and the secret is there; and
; each refusal names the first observation that failed.
(defthm fn-osn-bless-word-blessed-exactly-when
  (and (iff (equal (fn-osn-bless-word markerp open keysp) :blessed)
            (and markerp (equal open :ok) keysp))
       (implies (not markerp)
                (equal (fn-osn-bless-word markerp open keysp) :snapshot-incomplete))
       (implies (and markerp (not (equal open :ok)))
                (equal (fn-osn-bless-word markerp open keysp) :open-refused))
       (implies (and markerp (equal open :ok) (not keysp))
                (equal (fn-osn-bless-word markerp open keysp) :no-node-secret))))

(defthm fn-osn-bless-accepted-exactly-when-blessed
  (iff (equal (fn-osn-bless-status (fn-osn-bless-word markerp open keysp)) :accepted)
       (and markerp (equal open :ok) keysp)))

; The open is never taken over an absent marker: the verdict of that case
; does not depend on it.
(defthm fn-osn-absent-marker-never-opens
  (implies (not (fn-osn-bless-open-needed markerp))
           (equal (fn-osn-bless-word markerp open keysp)
                  (fn-osn-bless-word markerp :never-observed keysp))))

; -----------------------------------------------------------------------------
; The decimal renderer: the tree's (explode-nonnegative-integer, as
; books/provenance.lisp fn-prov-nat-string uses it).

(local
 (defthm fn-osn-explode-characters
   (implies (and (natp number) (character-listp accumulator))
            (character-listp (explode-nonnegative-integer number 10 accumulator)))))

(defun fn-osn-nat-string (n)
  (declare (xargs :guard t))
  (coerce (explode-nonnegative-integer (nfix n) 10 nil) 'string))

; -----------------------------------------------------------------------------
; The marker's lines (rendered, never read for a decision: provenance).
; INDEX the active segment's index at the capture, FRONTIER its committed
; octets, FILES the number of files the copy holds.

(defun fn-osn-marker-text (index frontier files)
  (declare (xargs :guard (and (natp index) (natp frontier) (natp files))))
  (concatenate 'string
               "fn snapshot 1" (coerce (list #\Newline) 'string)
               "active-segment=" (fn-osn-nat-string index)
               " frontier=" (fn-osn-nat-string frontier)
               " files=" (fn-osn-nat-string files)
               (coerce (list #\Newline) 'string)))

; -----------------------------------------------------------------------------
; The client's lines (the verb's stdout; the exit code is the status's)

(defun fn-osn-request-line (word dir)
  (declare (xargs :guard (stringp dir)))
  (cond ((equal word :requested)
         (concatenate 'string "snapshot requested target=" dir
                      ": the owner is copying the store while serving; this verb waits for the outcome"))
        ((equal word :snapshot-in-flight)
         "snapshot refused reason=snapshot-in-flight: the owner is copying a snapshot already; what it would take: wait for its `SNAPSHOT done' log line (or `store snapshot --status') and request again")
        ((equal word :target-exists)
         (concatenate 'string "snapshot refused reason=target-exists: " dir
                      " exists; what it would take: another DIR, or remove it"))
        (t "snapshot uncertain reason=unrecognized-word: the owner answered a word this release does not know")))

(defun fn-osn-outcome-line (word dir)
  (declare (xargs :guard (stringp dir)))
  (cond ((equal word :done)
         (concatenate 'string "snapshot taken target=" dir
                      ": complete (its SNAPSHOT marker is written; `store bless-snapshot' checks it, `cp -a' restores it)"))
        ((equal word :failed)
         (concatenate 'string "snapshot failed target=" dir
                      ": no SNAPSHOT marker was written (the owner's log names the reason: `SNAPSHOT failed reason=...'); what it would take: remove "
                      dir " and request again"))
        ((equal word :in-flight)
         "snapshot in-flight: the owner is still copying the store")
        ((equal word :idle)
         "snapshot idle: no snapshot is in flight and none has finished since the owner started")
        (t "snapshot uncertain reason=unrecognized-word: the owner answered a word this release does not know")))

; `store snapshot --status' with no owner (fn-omr-route :offline): nothing is
; in flight and nothing finished, because no owner is serving; by name.
(defun fn-osn-status-no-owner-line ()
  (declare (xargs :guard t))
  "snapshot status refused reason=no-owner: no owner is serving this store, so no snapshot is in flight; what it would take: `store snapshot DIR' with the node stopped copies the store to completion by itself")

; The blessing's line: OPEN's sentence is carried when the open refused.
(defun fn-osn-bless-line (word dir open transactions)
  (declare (xargs :guard (and (stringp dir) (natp transactions))))
  (cond ((equal word :blessed)
         (concatenate 'string "blessed snapshot=" dir " transactions="
                      (fn-osn-nat-string transactions)
                      ": it opens as a store of this lineage and holds the node secret; `cp -a' restores it (docs/operator.md, Back up)"))
        ((equal word :snapshot-incomplete)
         (concatenate 'string "bless-snapshot refused reason=snapshot-incomplete: " dir
                      " has no SNAPSHOT marker (the copy that made it did not finish); what it would take: remove it and take another"))
        ((equal word :open-refused)
         (concatenate 'string "bless-snapshot refused reason=open-refused: "
                      (if (stringp open) open "the copy does not open as a store")
                      "; what it would take: a snapshot of one store, its checkpoint and log from the same capture"))
        ((equal word :no-node-secret)
         (concatenate 'string "bless-snapshot refused reason=no-node-secret: " dir
                      "/keys holds no node-secret.key; what it would take: copy STORE/keys beside it, or `store DIR node-secret create' before the restored node runs"))
        (t "bless-snapshot uncertain reason=unrecognized-word")))
