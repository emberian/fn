; fn: the host's syscall sequences as programs over the byte model (crash
; model v2, §2).
;
; A program is a list of steps; a step is one syscall on a path, one kernel
; observation (an fn-sf event dispatched exactly as fn-sf-dispatch does), or
; a :cut, which is a campaign fault point with no effect.  Paths are a
; directory id and a name, resolved through the view.  fn-bs-run executes a
; program against a byte store and a kernel state to the first error, as the
; host does (every OSError raises), and returns the (bs . ks) pair after each
; step; a crash at cut k is fn-bs-crash of the k-th pair's store.
;
; The five transcriptions are P-FRONTIER (Store.advance_frontier), P-RECORD
; (Store.publish), P-FINISH (Store.finish), P-RECOVER (Store.recover) and
; P-INIT (Store.initialize), tools/run_store.py at 9321344.  Two changes
; from the design's listing, both required by its own rule §2.3 ("every
; durable syscall ... with a :cut after it") and by this lane's brief:
;   * a :cut follows every durable syscall, not only the host's present
;     faults.at sites; the new names (frontier-created, frontier-written,
;     record-created, record-written, record-stage-unlinked and the init-*
;     names) are faults.at sites P2's host half must add;
;   * the directory observations use the kernel's real event names
;     :frontier-dir and :record-dir (store-files-traces.lisp), not the
;     design's :frontier-directory / :record-directory.
;
; Discipline D1-D3 (§2.4) are executable checks over the constant programs,
; asserted here; D4 (no use after a failed fence) is a property of the
; runner by definition, stated as such; D5 (the pending list is disjoint at
; every cut) is asserted on the ground runs of every program.

(in-package "ACL2")
(include-book "byte-store")
(include-book "store-files-traces")

(defconst *fn-bs-config-name* "config.json")
(defconst *fn-bs-frontier-name* "allocation-frontier.json")
(defconst *fn-bs-authority-dirs* '(:root :transactions :records :inbound :checkpoints))

; -----------------------------------------------------------------------------
; Step language.
;   (:create dir name)                    os.open(O_WRONLY|O_CREAT|O_EXCL)
;   (:write-all dir name octets)          write_all: one or more write(2)
;   (:fsync-file dir name)                fsync_file / durable_barrier(fd)
;   (:fsync-dir dir)                      fsync_dir
;   (:link sdir sname ddir dname)         os.link
;   (:link-eexist sdir sname ddir dname)  os.link expected to find final
;   (:rename sdir sname ddir dname)       os.replace
;   (:unlink dir name)                    os.unlink (best-effort cleanup)
;   (:mkdir parent name id)               os.mkdir
;   (:observe event)                      one fn-sf transition (kernel only)
;   (:cut name)                           a campaign fault point; no effect

(defun fn-bs-stepp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp x)
       (case (car x)
         (:create (and (equal (len x) 3) (fn-bs-dir-idp (nth 1 x))
                       (fn-bs-namep (nth 2 x))))
         (:write-all (and (equal (len x) 4) (fn-bs-dir-idp (nth 1 x))
                          (fn-bs-namep (nth 2 x))
                          (fn-cbor-octet-listp (nth 3 x))))
         (:fsync-file (and (equal (len x) 3) (fn-bs-dir-idp (nth 1 x))
                           (fn-bs-namep (nth 2 x))))
         (:fsync-dir (and (equal (len x) 2) (fn-bs-dir-idp (nth 1 x))))
         ((:link :link-eexist :rename)
          (and (equal (len x) 5) (fn-bs-dir-idp (nth 1 x))
               (fn-bs-namep (nth 2 x)) (fn-bs-dir-idp (nth 3 x))
               (fn-bs-namep (nth 4 x))))
         (:unlink (and (equal (len x) 3) (fn-bs-dir-idp (nth 1 x))
                       (fn-bs-namep (nth 2 x))))
         (:mkdir (and (equal (len x) 4) (fn-bs-dir-idp (nth 1 x))
                      (fn-bs-namep (nth 2 x)) (fn-bs-dir-idp (nth 3 x))))
         (:observe (and (equal (len x) 2) (fn-sf-eventp (nth 1 x))))
         (:cut (and (equal (len x) 2) (stringp (nth 1 x))))
         (otherwise nil))))

(defun fn-bs-step-listp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs) (and (fn-bs-stepp (car xs)) (fn-bs-step-listp (cdr xs)))
    (null xs)))

; One step.  OUTCOME is that step's environment choice.  A kernel
; observation dispatches to the fn-sf transition named by the event, exactly
; as fn-sf-dispatch does; the syscall result is what the host would report.
(defun fn-bs-step (bs ks step outcome groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (case (car step)
    (:create (mv-let (r bs1) (fn-bs-create bs (nth 1 step) (nth 2 step) outcome)
               (mv r bs1 ks)))
    (:write-all (let ((ino (fn-bs-lookup bs (nth 1 step) (nth 2 step))))
                  (mv-let (r bs1) (fn-bs-write bs ino 0 (nth 3 step) outcome)
                    (mv r bs1 ks))))
    (:fsync-file (let ((ino (fn-bs-lookup bs (nth 1 step) (nth 2 step))))
                   (mv-let (r bs1) (fn-bs-fsync-file bs ino outcome)
                     (mv r bs1 ks))))
    (:fsync-dir (mv-let (r bs1) (fn-bs-fsync-dir bs (nth 1 step) outcome)
                  (mv r bs1 ks)))
    (:link (mv-let (r bs1) (fn-bs-link bs (nth 1 step) (nth 2 step)
                                       (nth 3 step) (nth 4 step) outcome)
             (mv r bs1 ks)))
    ;; Initialization's immutable-link retry observes EEXIST after the
    ;; actual link(2) call and then cleans up its newly fenced staging file.
    ;; This is deliberately a separate step rather than treating arbitrary
    ;; errors as success: only an already-present destination continues.
    (:link-eexist
     (mv-let (r bs1) (fn-bs-link bs (nth 1 step) (nth 2 step)
                                    (nth 3 step) (nth 4 step) outcome)
       (mv (cond ((equal r :eexist) :ok)
                 ((equal r :ok) :unexpected-link-success)
                 (t r))
           bs1 ks)))
    (:rename (mv-let (r bs1) (fn-bs-rename bs (nth 1 step) (nth 2 step)
                                           (nth 3 step) (nth 4 step) outcome)
               (mv r bs1 ks)))
    (:unlink (mv-let (r bs1) (fn-bs-unlink bs (nth 1 step) (nth 2 step) outcome)
               (mv r bs1 ks)))
    (:mkdir (mv-let (r bs1) (fn-bs-mkdir bs (nth 1 step) (nth 2 step)
                                         (nth 3 step) outcome)
              (mv r bs1 ks)))
    (:observe (mv :ok bs (fn-sf-dispatch ks (nth 1 step) groups capacity)))
    (otherwise (mv :ok bs ks))))

; Run to the first error, as the host does.  Returns the list of (bs . ks)
; pairs after each step, most recent last; the last pair is where the
; process died or returned.  A missing outcome is :ok.
(defun fn-bs-run (bs ks steps outcomes groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (mv-let (r bs1 ks1)
        (fn-bs-step bs ks (car steps) (if (consp outcomes) (car outcomes) :ok)
                    groups capacity)
        (cons (cons bs1 ks1)
              (if (equal r :ok)
                  (fn-bs-run bs1 ks1 (cdr steps) (cdr outcomes) groups capacity)
                nil)))
    nil))

; D4, by definition: after a step whose outcome is an error the run ends, so
; no later step reads or links a path whose fence failed.  The host's
; StoreError / StoreIndeterminate arms are the one-step error observations
; listed with each program below.
(defthm fn-bs-run-stops-at-first-error-by-definition
  (implies (and (consp steps)
                (not (equal (mv-nth 0 (fn-bs-step bs ks (car steps)
                                                  (if (consp outcomes) (car outcomes) :ok)
                                                  groups capacity))
                            :ok)))
           (equal (len (fn-bs-run bs ks steps outcomes groups capacity)) 1))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The transcriptions.  Line numbers refer to tools/run_store.py at 9321344.

; P-FRONTIER (Store.advance_frontier, 840-912).  OCTETS is the new frontier
; file's content; STAGE is .allocation-<pid>-<hex>.
(defun fn-bs-frontier-program (stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :observe '(:start-frontier))                 ; 858
        (list :create :staging stage)                      ; 861  O_EXCL
        (list :cut "frontier-created")
        (list :write-all :staging stage octets)            ; 863
        (list :cut "frontier-written")
        (list :fsync-file :staging stage)                  ; 864  durable_barrier
        ; close(fd) 866: no step
        (list :observe '(:frontier-file :ok))              ; 870
        (list :cut "frontier-staged-durable")              ; 872
        (list :rename :staging stage :root *fn-bs-frontier-name*) ; 878 os.replace
        (list :cut "frontier-replaced")                    ; 882
        (list :observe '(:frontier-replace :ok))           ; 883
        (list :cut "frontier-attempted")                   ; 888
        (list :fsync-dir :root)                            ; 891
        (list :cut "frontier-durable")                     ; 895
        (list :observe '(:frontier-dir :ok))               ; 896
        (list :cut "frontier-reserved")))                  ; 903
; On error before 878: (:observe (:frontier-file :known-fail)) [911].  At or
; after 878 the host raises StoreIndeterminate and observes
; (:frontier-replace :error) [880] or (:frontier-dir :error) [893].  The
; staging directory is never fenced; the rename's source :del-entry on
; :staging stays pending for ever.  Recovery reads nothing in :staging, and
; its sweep removes the stage a death leaves there, renamed or not
; (fn-bs-recover-sweep-program below; K-sweep in byte-store-keystones).
(defconst *fn-bs-frontier-on-known-fail* '((:observe (:frontier-file :known-fail))))
(defconst *fn-bs-frontier-on-replace-error* '((:observe (:frontier-replace :error))))
(defconst *fn-bs-frontier-on-dir-error* '((:observe (:frontier-dir :error))))

; P-RECORD (Store.publish, 914-989).  NAME is {:020d}.txn of the sequence;
; STAGE is .stage-<pid>-<hex>; FRAME is the FNST frame from
; fn-frame-store-encode.
(defun fn-bs-record-program (stage name frame)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)                      ; 924
        (list :cut "record-created")
        (list :write-all :staging stage frame)             ; 926
        (list :cut "record-written")
        (list :fsync-file :staging stage)                  ; 927
        (list :observe '(:record-file :ok))                ; 931
        (list :cut "record-staged-durable")                ; 937
        (list :link :staging stage :transactions name)     ; 941 os.link
        (list :cut "record-linked")                        ; 945
        (list :observe '(:record-link :ok))                ; 946
        (list :cut "record-attempted")                     ; 953
        (list :fsync-dir :transactions)                    ; 955
        (list :cut "record-durable")                       ; 959
        (list :observe '(:record-dir :ok))                 ; 960
        (list :cut "record-completing")                    ; 966
        (list :unlink :staging stage)                      ; 970 best effort
        (list :cut "record-stage-unlinked")
        (list :fsync-dir :staging)                         ; 971 best effort
        (list :cut "record-staging-cleaned")))             ; 974
; On error before 941: StoreError and the composed fn-sn-known-abort
; ((:record-file :known-fail) then (:abort-completion seq txid)).  At or
; after 941: StoreIndeterminate with (:record-link :error) [943] or
; (:record-dir :error) [957].  Errors from 970-971 are swallowed.
(defconst *fn-bs-record-on-link-error* '((:observe (:record-link :error))))
(defconst *fn-bs-record-on-dir-error* '((:observe (:record-dir :error))))

; P-FINISH (Store.finish, 991-1010): no syscall.  The byte state is
; unchanged; its crash images are those of the :ready kernel with the pair
; in the ghost history (the core-durable cut).
(defun fn-bs-finish-program (sequence txid)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :cut "finish-consumed")
        (list :observe (list :core-completion sequence txid))
        (list :observe (list :emit-success sequence txid))
        (list :cut "finish-durable")))

; P-RECOVER (Store.recover, 786-838).  Reads first (_load_frontier 795,
; durable_records 796, staging_orphans 797: reads of the view, no step),
; then five fences on already-durable objects.
(defun fn-bs-recover-program ()
  (declare (xargs :guard t :verify-guards nil))
  (list (list :observe '(:recover))                        ; 798 acl2.recover
        (list :cut "recover-replayed")                     ; 809
        (list :fsync-file :root *fn-bs-config-name*)       ; 815 fsync_regular
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")
        (list :fsync-file :root *fn-bs-frontier-name*)     ; 816
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")
        (list :fsync-dir :transactions)                    ; 817
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")
        (list :fsync-dir :root)                            ; 818
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")
        (list :fsync-dir :parent)                          ; 819
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")))
; On any fence error: (:observe (:recovery-barrier :uncertain)) [826] and
; StoreIndeterminate.  Recovery after an in-process uncertainty (no crash)
; runs with a NON-EMPTY pending list: the link or replacement whose reply
; was lost may still be pending, and 817/818 are what drain it.
(defconst *fn-bs-recover-on-barrier-error* '((:observe (:recovery-barrier :uncertain))))

; Recovery removes bounded staging orphans AFTER fn-bs-recover-program has
; run to its end: the host sweeps only once the fifth recovery barrier
; observation has reached :ready (host/native/io.lisp `fnn-recover', whose
; sweep is the model's, enabled only in that phase), and runs this program
; once per removed orphan.  The native `recovery-stage-unlinked` death point
; is after this unlink and before any subsequent process can rely on
; cleanup; its coordinate is the whole of fn-bs-recover-program followed by
; this program up to the cut (tests/campaign/native_cuts.py).  Staging is not
; an authority directory, but the physical cut still needs a byte-program
; transition.
(defun fn-bs-recover-stage-cleanup-program (stage)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :unlink :staging stage)
        (list :cut "recovery-stage-unlinked")))

; The whole sweep: one cleanup per name the ACL2 sweep returned, in the order
; the host unlinks them (host/native/io.lisp, fnn-sweep-staging, one dolist
; per round of fn-sn-sweep-round).  Rounds are concatenated: between two
; rounds the host only enumerates, which is a read of the view and no step.
; Every cut of this program is a recovery-stage-unlinked death point.
(defun fn-bs-recover-sweep-program (names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (append (fn-bs-recover-stage-cleanup-program (car names))
              (fn-bs-recover-sweep-program (cdr names)))
    nil))

; P-INIT (Store.initialize and _publish_initial_file, 612-667): mkdir root,
; transactions, staging; each of config and frontier is staged, fenced,
; linked (EEXIST reported, never replaced), the root fenced, the stage
; unlinked; then the five recovery fences.  Same shape as P-RECORD with
; :root as the authority directory.  The host has no cuts here today; these
; are the sites P2 adds.
(defun fn-bs-init-file-steps (stage name octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)
        (list :cut "init-created")
        (list :write-all :staging stage octets)
        (list :cut "init-written")
        (list :fsync-file :staging stage)
        (list :cut "init-staged-durable")
        (list :link :staging stage :root name)
        (list :cut "init-linked")
        (list :fsync-dir :root)
        (list :cut "init-durable")
        (list :unlink :staging stage)
        (list :cut "init-stage-unlinked")))

(defun fn-bs-init-program (config-octets frontier-octets)
  (declare (xargs :guard t :verify-guards nil))
  (append (list (list :mkdir :parent "store" :root)
                (list :cut "init-root-created")
                (list :mkdir :root "transactions" :transactions)
                (list :cut "init-transactions-created")
                (list :mkdir :root "staging" :staging)
                (list :cut "init-staging-created"))
          (fn-bs-init-file-steps ".init-config" *fn-bs-config-name* config-octets)
          (fn-bs-init-file-steps ".init-frontier" *fn-bs-frontier-name* frontier-octets)
          (list (list :fsync-file :root *fn-bs-config-name*)
                (list :cut "init-barrier")
                (list :fsync-file :root *fn-bs-frontier-name*)
                (list :cut "init-barrier")
                (list :fsync-dir :transactions)
                (list :cut "init-barrier")
                (list :fsync-dir :root)
                (list :cut "init-barrier")
                (list :fsync-dir :parent)
                (list :cut "init-barrier"))))

; -----------------------------------------------------------------------------
; Program discipline (§2.4) as executable checks over the constants.

; D1: every :link and :rename names a source whose last :write-all was
; followed by a :fsync-file before the link ("safe link").
(defun fn-bs-links-only-fenced-aux (steps fenced)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom steps) t
    (let ((step (car steps)))
      (case (car step)
        (:write-all
         (fn-bs-links-only-fenced-aux
          (cdr steps) (remove-equal (cons (nth 1 step) (nth 2 step)) fenced)))
        (:fsync-file
         (fn-bs-links-only-fenced-aux
          (cdr steps) (cons (cons (nth 1 step) (nth 2 step)) fenced)))
        ((:link :link-eexist :rename)
         (and (member-equal (cons (nth 1 step) (nth 2 step)) fenced)
              (fn-bs-links-only-fenced-aux (cdr steps) fenced)))
        (otherwise (fn-bs-links-only-fenced-aux (cdr steps) fenced))))))
(defun fn-bs-links-only-fencedp (steps)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-links-only-fenced-aux steps nil))

; D2: no :write-all names a path under an authority directory: no in-place
; overwrite, ever.
(defun fn-bs-never-overwrites-authorityp (steps)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom steps) t
    (and (or (not (equal (car (car steps)) :write-all))
             (not (member-equal (nth 1 (car steps)) *fn-bs-authority-dirs*)))
         (fn-bs-never-overwrites-authorityp (cdr steps)))))

; D3: every :link/:rename into an authority directory is followed by
; :fsync-dir of that directory before any further :link/:rename and before
; the observation that reports the directory durable (:frontier-dir :ok,
; :record-dir :ok) or a success (:emit-success).
(defun fn-bs-durable-observationp (event)
  (declare (xargs :guard t :verify-guards nil))
  (or (equal event '(:frontier-dir :ok))
      (equal event '(:record-dir :ok))
      (equal (car event) :emit-success)))
(defun fn-bs-fences-authority-dirs-aux (steps unfenced)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom steps) (null unfenced)
    (let ((step (car steps)))
      (case (car step)
        ((:link :rename)
         (and (null unfenced)
              (fn-bs-fences-authority-dirs-aux
               (cdr steps)
               (if (member-equal (nth 3 step) *fn-bs-authority-dirs*) (nth 3 step) nil))))
        (:fsync-dir
         (fn-bs-fences-authority-dirs-aux
          (cdr steps) (if (equal (nth 1 step) unfenced) nil unfenced)))
        (:observe
         (and (or (null unfenced) (not (fn-bs-durable-observationp (nth 1 step))))
              (fn-bs-fences-authority-dirs-aux (cdr steps) unfenced)))
        (otherwise (fn-bs-fences-authority-dirs-aux (cdr steps) unfenced))))))
(defun fn-bs-fences-authority-dirsp (steps)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-fences-authority-dirs-aux steps nil))

; D5: the pending list is disjoint: no two pending writes to one inode
; overlap, and no name carries more than two pending entry operations.
(defun fn-bs-write-overlapsp (op other)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (car other) :write) (equal (nth 1 other) (nth 1 op))
       (< (nfix (nth 2 op)) (+ (nfix (nth 2 other)) (len (nth 3 other))))
       (< (nfix (nth 2 other)) (+ (nfix (nth 2 op)) (len (nth 3 op))))))
(defun fn-bs-write-overlaps-anyp (op ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops) nil
    (or (fn-bs-write-overlapsp op (car ops))
        (fn-bs-write-overlaps-anyp op (cdr ops)))))
(defun fn-bs-name-op-count (ops dir name)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops) 0
    (+ (if (and (member-equal (car (car ops)) '(:set-entry :del-entry))
                (equal (nth 1 (car ops)) dir) (equal (nth 2 (car ops)) name))
           1 0)
       (fn-bs-name-op-count (cdr ops) dir name))))
(defun fn-bs-pending-disjoint-aux (ops all)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops) t
    (let ((op (car ops)))
      (and (case (car op)
             (:write (not (fn-bs-write-overlaps-anyp op (cdr ops))))
             ((:set-entry :del-entry)
              (<= (fn-bs-name-op-count all (nth 1 op) (nth 2 op)) 2))
             (otherwise t))
           (fn-bs-pending-disjoint-aux (cdr ops) all)))))
(defun fn-bs-pending-disjointp (ops)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-pending-disjoint-aux ops ops))

(defun fn-bs-run-pending-disjointp (pairs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom pairs) t
    (and (fn-bs-pending-disjointp (fn-bs-pending (car (car pairs))))
         (fn-bs-run-pending-disjointp (cdr pairs)))))
(defun fn-bs-run-statep (pairs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom pairs) t
    (and (fn-bs-statep (car (car pairs)))
         (fn-bs-run-statep (cdr pairs)))))

; -----------------------------------------------------------------------------
; -----------------------------------------------------------------------------
; The journals, the inbox and the checkpoint machine (design §2.2, packets
; P5 and P8).  These three have no fn-sf kernel: their logical image is a
; record list (§3.4), so every step is a syscall and no step is an
; :observe.  Transcribed so that every cut the campaign kills at
; (tests/campaign/cuts.py) is a :cut of a program here; tools/transcribe_check.py
; is the check in both directions and names the remainder as fidelity
; defects rather than leaving the correspondence to prose.

; P-JOURNAL, workflow half (WorkflowJournal.publish, tools/workflow_journal.py
; 197-266).  NAME is {seq:016x}.wf; STAGE is {seq:016x}.<pid>.tmp; FRAME is
; the FNWF frame.  The host's own cut names are the ones below.
(defun fn-bs-workflow-program (stage name frame)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)                      ; 220
        (list :write-all :staging stage frame)             ; 223
        (list :cut "write")
        (list :fsync-file :staging stage)                  ; 225
        (list :cut "file-fsync")
        (list :cut "prepublish")
        (list :link :staging stage :records name)          ; 235 os.link
        (list :cut "postlink")
        (list :fsync-dir :records)                         ; 237
        (list :cut "directory-fsync")
        (list :unlink :staging stage)                      ; finally, best effort
        (list :cut "image-applied")))
; On error before the link the stage is unlinked and the error raised; no
; journal record exists.  At or after the link: JournalUncertain and
; self.fenced = True, which is the journal form of "fence after uncertainty".

; P-JOURNAL, receipt half (ReceiptJournal.publish).  Same shape, the host's
; own cut names.
(defun fn-bs-receipt-program (stage name frame)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)
        (list :write-all :staging stage frame)
        (list :fsync-file :staging stage)
        (list :cut "receipt-staged-durable")
        (list :link :staging stage :records name)
        (list :cut "postlink")
        (list :fsync-dir :records)
        (list :cut "receipt-durable")
        (list :unlink :staging stage)
        (list :cut "receipt-applied")))

; P-INBOX (WorkflowJournal.stage_inbound, 326-388).  NAME is
; sha256(bid).hexdigest() + ".bp"; STAGE is NAME + ".<pid>.tmp".
(defun fn-bs-inbox-program (stage name frame)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)                      ; 362
        (list :write-all :staging stage frame)             ; 365
        (list :fsync-file :staging stage)                  ; 365
        (list :cut "inbound-staged-durable")               ; 366
        (list :link :staging stage :inbound name)          ; 372
        (list :cut "inbound-linked")                       ; 373
        (list :fsync-dir :inbound)                         ; 374
        (list :cut "inbound-durable")                      ; 375
        (list :unlink :staging stage)                      ; finally
        ; delete(bid) is a BPA transport side effect, outside this model
        (list :cut "inbound-deleted")))                    ; 386

; The reconciliation branch (final exists: 349-360) issues only the
; directory fence.
(defun fn-bs-inbox-reconcile-program ()
  (declare (xargs :guard t :verify-guards nil))
  (list (list :fsync-dir :inbound)
        (list :cut "inbound-reconciled")))

; P-CHECKPOINT (tools/checkpoint.py).  publish: a new generation file, the
; shape of P-RECORD into :checkpoints.
(defun fn-bs-checkpoint-publish-program (stage generation frame)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)                      ; _stage_and_link 97
        (list :write-all :staging stage frame)
        (list :fsync-file :staging stage)                  ; 100
        (list :cut "checkpoint:candidate-durable")         ; 103
        (list :link :staging stage :checkpoints generation) ; 105
        (list :cut "checkpoint:candidate-linked")          ; 106
        (list :fsync-dir :checkpoints)                     ; 107
        (list :cut "checkpoint:candidate-published")       ; 108
        (list :unlink :staging stage)                      ; 111
        (list :cut "checkpoint:candidate-stage-unlinked")))

; select: the authority marker, the shape of P-FRONTIER into :checkpoints.
(defun fn-bs-checkpoint-select-program (stage frame)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)                      ; 157
        (list :write-all :staging stage frame)
        (list :fsync-file :staging stage)                  ; 160
        (list :cut "checkpoint:selection-durable")         ; 163
        (list :rename :staging stage :checkpoints "selection") ; 165 os.replace
        (list :cut "checkpoint:selection-replaced")        ; 172
        (list :fsync-dir :checkpoints)                     ; 173
        (list :cut "checkpoint:selection-published")))     ; 174
; tools/checkpoint.py also calls os.unlink(stage) at 163, but that is the
; except arm of the replace: on the success path os.replace has already
; removed the staging name, and a model program that unlinked it would stop
; at :enoent.  tools/transcribe_check.py reports it as syscall drift and
; this comment is the answer; the assert-event on the ground run is what
; refused the step.

; -----------------------------------------------------------------------------
; The checks, on the constants.  The byte side of every program runs here
; against an initialized store with the initial kernel state (the kernel's
; transitions are guarded by fn-sf-statep; an observation the phase does not
; expect is a no-op); the composed runs that drive the kernel through its
; phases are in tests/acl2/byte-store-tests.lisp.

(defconst *fn-bs-sample-config* '(1 2 3))
(defconst *fn-bs-sample-frontier* '(0))
(defconst *fn-bs-sample-frame* '(10 11 12 13 14 15 16 17 18 19))
(defconst *fn-bs-empty-store* (fn-bs-make 4 nil (list (cons :parent nil)) nil 0))
(defconst *fn-bs-initialized-store*
  (fn-bs-make 4
              (list (cons 0 *fn-bs-sample-config*) (cons 1 *fn-bs-sample-frontier*))
              (list (cons :parent (list (cons "store" :root)))
                    (cons :root (list (cons *fn-bs-config-name* 0)
                                      (cons *fn-bs-frontier-name* 1)))
                    (cons :transactions nil)
                    (cons :staging nil))
              nil 2))

(defconst *fn-bs-p-frontier* (fn-bs-frontier-program ".allocation-1" '(1)))
(defconst *fn-bs-p-record*
  (fn-bs-record-program ".stage-1" "00000000000000000000.txn" *fn-bs-sample-frame*))
(defconst *fn-bs-p-finish* (fn-bs-finish-program 0 0))
(defconst *fn-bs-p-recover* (fn-bs-recover-program))
(defconst *fn-bs-p-init*
  (fn-bs-init-program *fn-bs-sample-config* *fn-bs-sample-frontier*))

(assert-event (and (fn-bs-step-listp *fn-bs-p-frontier*)
                   (fn-bs-step-listp *fn-bs-p-record*)
                   (fn-bs-step-listp *fn-bs-p-finish*)
                   (fn-bs-step-listp *fn-bs-p-recover*)
                   (fn-bs-step-listp *fn-bs-p-init*)))

; D1-D3 on every program.
(assert-event (and (fn-bs-links-only-fencedp *fn-bs-p-frontier*)
                   (fn-bs-links-only-fencedp *fn-bs-p-record*)
                   (fn-bs-links-only-fencedp *fn-bs-p-finish*)
                   (fn-bs-links-only-fencedp *fn-bs-p-recover*)
                   (fn-bs-links-only-fencedp *fn-bs-p-init*)))
(assert-event (and (fn-bs-never-overwrites-authorityp *fn-bs-p-frontier*)
                   (fn-bs-never-overwrites-authorityp *fn-bs-p-record*)
                   (fn-bs-never-overwrites-authorityp *fn-bs-p-finish*)
                   (fn-bs-never-overwrites-authorityp *fn-bs-p-recover*)
                   (fn-bs-never-overwrites-authorityp *fn-bs-p-init*)))
(assert-event (and (fn-bs-fences-authority-dirsp *fn-bs-p-frontier*)
                   (fn-bs-fences-authority-dirsp *fn-bs-p-record*)
                   (fn-bs-fences-authority-dirsp *fn-bs-p-finish*)
                   (fn-bs-fences-authority-dirsp *fn-bs-p-recover*)
                   (fn-bs-fences-authority-dirsp *fn-bs-p-init*)))

; Teeth for the checkers: the unsafe host of design §5.5 (link before
; fsync) fails D1; an in-place frontier write fails D2; a link with no
; directory fence before the durable observation fails D3.
(assert-event
 (not (fn-bs-links-only-fencedp
       (list '(:create :staging "s") '(:write-all :staging "s" (1))
             '(:link :staging "s" :transactions "t") '(:fsync-file :staging "s")))))
(assert-event
 ;; An expected EEXIST still performs link(2); it needs the same staged-file
 ;; fence as a successful immutable link.
 (not (fn-bs-links-only-fencedp
       (list '(:create :staging "s") '(:write-all :staging "s" (1))
             '(:link-eexist :staging "s" :transactions "t")
             '(:fsync-file :staging "s")))))
(assert-event
 (not (fn-bs-never-overwrites-authorityp
       (list (list :write-all :root *fn-bs-frontier-name* '(1))))))
(assert-event
 (not (fn-bs-fences-authority-dirsp
       (list '(:fsync-file :staging "s") '(:link :staging "s" :transactions "t")
             '(:observe (:record-dir :ok)) '(:fsync-dir :transactions)))))

; D5 and K0 on the ground runs (all outcomes :ok, initial kernel).
(assert-event (fn-bs-statep *fn-bs-empty-store*))
(assert-event (fn-bs-statep *fn-bs-initialized-store*))
(defconst *fn-bs-run-frontier*
  (fn-bs-run *fn-bs-initialized-store* (fn-sf-initial-state) *fn-bs-p-frontier* nil nil nil))
(defconst *fn-bs-run-record*
  (fn-bs-run *fn-bs-initialized-store* (fn-sf-initial-state) *fn-bs-p-record* nil nil nil))
(defconst *fn-bs-run-init*
  (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state) *fn-bs-p-init* nil nil nil))
(defconst *fn-bs-run-recover*
  (fn-bs-run *fn-bs-initialized-store* (fn-sf-initial-state) *fn-bs-p-recover* nil nil nil))

; Every run completes (no syscall errors under :ok outcomes).
(assert-event (equal (len *fn-bs-run-frontier*) (len *fn-bs-p-frontier*)))
(assert-event (equal (len *fn-bs-run-record*) (len *fn-bs-p-record*)))
(assert-event (equal (len *fn-bs-run-init*) (len *fn-bs-p-init*)))
(assert-event (equal (len *fn-bs-run-recover*) (len *fn-bs-p-recover*)))
(assert-event (and (fn-bs-run-pending-disjointp *fn-bs-run-frontier*)
                   (fn-bs-run-pending-disjointp *fn-bs-run-record*)
                   (fn-bs-run-pending-disjointp *fn-bs-run-init*)
                   (fn-bs-run-pending-disjointp *fn-bs-run-recover*)))
(assert-event (and (fn-bs-run-statep *fn-bs-run-frontier*)
                   (fn-bs-run-statep *fn-bs-run-record*)
                   (fn-bs-run-statep *fn-bs-run-init*)
                   (fn-bs-run-statep *fn-bs-run-recover*)))

; Where the programs leave the store.
(assert-event
 (let ((bs (car (car (last *fn-bs-run-frontier*)))))
   (and (equal (fn-bs-durable-entry bs :root *fn-bs-frontier-name*) 2)
        (equal (fn-bs-durable-content bs 2) '(1))
        (fn-bs-fencedp bs 2)
        (fn-bs-dir-quietp bs :root)
        ; the staging source removal is never fenced
        (not (fn-bs-dir-quietp bs :staging)))))
(assert-event
 (let ((bs (car (car (last *fn-bs-run-record*)))))
   (and (equal (fn-bs-durable-entry bs :transactions "00000000000000000000.txn") 2)
        (equal (fn-bs-durable-content bs 2) *fn-bs-sample-frame*)
        (fn-bs-fencedp bs 2)
        (fn-bs-dir-quietp bs :transactions)
        (fn-bs-dir-quietp bs :staging)
        (null (fn-bs-pending bs)))))
(assert-event
 (let ((bs (car (car (last *fn-bs-run-init*)))))
   (and (equal (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-config-name*))
               *fn-bs-sample-config*)
        (equal (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-frontier-name*))
               *fn-bs-sample-frontier*)
        (equal (fn-bs-durable-entry bs :parent "store") :root)
        (fn-bs-dir-quietp bs :root)
        (fn-bs-dir-quietp bs :parent)
        ; initialize never fences :staging either
        (not (fn-bs-dir-quietp bs :staging)))))

; The journal, inbox and checkpoint programs run over their own stores:
; :records, :inbound and :checkpoints beside :staging, no kernel.
(defconst *fn-bs-journal-store*
  (fn-bs-make 4 nil
              (list (cons :root (list (cons "records" :records)
                                      (cons "inbound" :inbound)
                                      (cons "checkpoints" :checkpoints)
                                      (cons "staging" :staging)))
                    (cons :records nil) (cons :inbound nil)
                    (cons :checkpoints nil) (cons :staging nil))
              nil 0))
(defconst *fn-bs-p-workflow*
  (fn-bs-workflow-program "0000000000000000.1.tmp" "0000000000000000.wf"
                          *fn-bs-sample-frame*))
(defconst *fn-bs-p-receipt*
  (fn-bs-receipt-program "0000000000000000.1.tmp" "0000000000000000.rj"
                         *fn-bs-sample-frame*))
(defconst *fn-bs-p-inbox*
  (fn-bs-inbox-program "ab.bp.1.tmp" "ab.bp" *fn-bs-sample-frame*))
(defconst *fn-bs-p-inbox-reconcile* (fn-bs-inbox-reconcile-program))
(defconst *fn-bs-p-checkpoint-publish*
  (fn-bs-checkpoint-publish-program ".cp-1" "generation-1.fncp" *fn-bs-sample-frame*))
(defconst *fn-bs-p-checkpoint-select*
  (fn-bs-checkpoint-select-program ".sel-1" *fn-bs-sample-frame*))

(assert-event (and (fn-bs-step-listp *fn-bs-p-workflow*)
                   (fn-bs-step-listp *fn-bs-p-receipt*)
                   (fn-bs-step-listp *fn-bs-p-inbox*)
                   (fn-bs-step-listp *fn-bs-p-inbox-reconcile*)
                   (fn-bs-step-listp *fn-bs-p-checkpoint-publish*)
                   (fn-bs-step-listp *fn-bs-p-checkpoint-select*)))
(assert-event (and (fn-bs-links-only-fencedp *fn-bs-p-workflow*)
                   (fn-bs-links-only-fencedp *fn-bs-p-receipt*)
                   (fn-bs-links-only-fencedp *fn-bs-p-inbox*)
                   (fn-bs-links-only-fencedp *fn-bs-p-checkpoint-publish*)
                   (fn-bs-links-only-fencedp *fn-bs-p-checkpoint-select*)))
(assert-event (and (fn-bs-never-overwrites-authorityp *fn-bs-p-workflow*)
                   (fn-bs-never-overwrites-authorityp *fn-bs-p-receipt*)
                   (fn-bs-never-overwrites-authorityp *fn-bs-p-inbox*)
                   (fn-bs-never-overwrites-authorityp *fn-bs-p-checkpoint-publish*)
                   (fn-bs-never-overwrites-authorityp *fn-bs-p-checkpoint-select*)))
(assert-event (and (fn-bs-fences-authority-dirsp *fn-bs-p-workflow*)
                   (fn-bs-fences-authority-dirsp *fn-bs-p-receipt*)
                   (fn-bs-fences-authority-dirsp *fn-bs-p-inbox*)
                   (fn-bs-fences-authority-dirsp *fn-bs-p-checkpoint-publish*)
                   (fn-bs-fences-authority-dirsp *fn-bs-p-checkpoint-select*)))

(assert-event (fn-bs-statep *fn-bs-journal-store*))
(defconst *fn-bs-run-workflow*
  (fn-bs-run *fn-bs-journal-store* nil *fn-bs-p-workflow* nil nil nil))
(defconst *fn-bs-run-inbox*
  (fn-bs-run *fn-bs-journal-store* nil *fn-bs-p-inbox* nil nil nil))
(defconst *fn-bs-run-checkpoint-publish*
  (fn-bs-run *fn-bs-journal-store* nil *fn-bs-p-checkpoint-publish* nil nil nil))
(defconst *fn-bs-run-checkpoint-select*
  (fn-bs-run *fn-bs-journal-store* nil *fn-bs-p-checkpoint-select* nil nil nil))
(assert-event (equal (len *fn-bs-run-workflow*) (len *fn-bs-p-workflow*)))
(assert-event (equal (len *fn-bs-run-inbox*) (len *fn-bs-p-inbox*)))
(assert-event (equal (len *fn-bs-run-checkpoint-publish*)
                     (len *fn-bs-p-checkpoint-publish*)))
(assert-event (equal (len *fn-bs-run-checkpoint-select*)
                     (len *fn-bs-p-checkpoint-select*)))
(assert-event (and (fn-bs-run-pending-disjointp *fn-bs-run-workflow*)
                   (fn-bs-run-pending-disjointp *fn-bs-run-inbox*)
                   (fn-bs-run-pending-disjointp *fn-bs-run-checkpoint-publish*)
                   (fn-bs-run-pending-disjointp *fn-bs-run-checkpoint-select*)))
(assert-event (and (fn-bs-run-statep *fn-bs-run-workflow*)
                   (fn-bs-run-statep *fn-bs-run-inbox*)
                   (fn-bs-run-statep *fn-bs-run-checkpoint-publish*)
                   (fn-bs-run-statep *fn-bs-run-checkpoint-select*)))

; Where they leave the store: the final name carries the exact frame and is
; fenced, and the authority directory is quiet.
(assert-event
 (let ((bs (car (car (last *fn-bs-run-workflow*)))))
   (and (equal (fn-bs-durable-content
                bs (fn-bs-durable-entry bs :records "0000000000000000.wf"))
               *fn-bs-sample-frame*)
        (fn-bs-dir-quietp bs :records))))
(assert-event
 (let ((bs (car (car (last *fn-bs-run-inbox*)))))
   (and (equal (fn-bs-durable-content
                bs (fn-bs-durable-entry bs :inbound "ab.bp"))
               *fn-bs-sample-frame*)
        (fn-bs-dir-quietp bs :inbound))))
(assert-event
 (let ((bs (car (car (last *fn-bs-run-checkpoint-select*)))))
   (and (equal (fn-bs-durable-content
                bs (fn-bs-durable-entry bs :checkpoints "selection"))
               *fn-bs-sample-frame*)
        (fn-bs-dir-quietp bs :checkpoints))))

; -----------------------------------------------------------------------------
; Export theory.  Enabled on include: the program constructors, the
; discipline checkers (list-recursive vocabulary) and the constants.
; Withdrawn: the step recognizer, the step and the runner.

(in-theory (disable fn-bs-stepp fn-bs-step fn-bs-run))
