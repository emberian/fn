; Teeth for books/store-export-durability (PRF-370): the export's data files
; share one sync, the MANIFEST is renamed into place last, and a crash
; anywhere leaves no MANIFEST (refused archive-incomplete) or the complete
; archive.
(in-package "ACL2")
(include-book "../../books/store-export-durability")

; A byte state holding the empty archive directory, a unit of 4 octets.
(defconst *sxdt-bs* (fn-bs-make 4 nil (list (cons :arch nil)) nil 0))
; Three entries: the profile in DIR, one configuration record, two records.
(defconst *sxdt-entries*
  '((:arch "profile" 1 2 3 4 5)
    (:cfg "groups" 6 7)
    (:rec "00000000000000000000.txn" 8 9 10)
    (:rec "00000000000000000001.txn" 11)))
(defconst *sxdt-manifest* '(97 98 99 10 100 101 102 10))
(defconst *sxdt-program* (fn-sxd-program *sxdt-entries* *sxdt-manifest*))
(defconst *sxdt-ok* (make-list (len *sxdt-program*) :initial-element :ok))

(defun sxdt-img-all (s)
  ; Everything pending lands.
  (fn-bs-crash s (fn-bs-view-choices (fn-bs-pending s) (fn-bs-unit s))))
(defun sxdt-img-none (s)
  ; Nothing pending lands.
  (fn-bs-crash s nil))
(defun sxdt-conclusion (img)
  (or (null (fn-bs-durable-entry img :arch *fn-sxd-manifest*))
      (fn-sxd-completep img *sxdt-entries* (fn-bs-next-ino *sxdt-bs*) *sxdt-manifest*)))
(defun sxdt-all-hold (states)
  (if (consp states)
      (and (sxdt-conclusion (sxdt-img-all (car states)))
           (sxdt-conclusion (sxdt-img-none (car states)))
           (sxdt-all-hold (cdr states)))
    t))

; -----------------------------------------------------------------------------
; Reachable positive witness of fn-sxd-crash-is-incomplete-or-complete: the
; complete antecedent at a run of every step with every syscall answering
; :ok, then the conclusion at every state of it.
(assert-event (fn-bs-statep *sxdt-bs*))
(assert-event (fn-sxd-quietp *sxdt-bs*))
(assert-event (fn-sxd-keysp *sxdt-entries*))
(assert-event (fn-cbor-octet-listp *sxdt-manifest*))
(assert-event (fn-sxd-outcomesp *sxdt-ok*))
(defconst *sxdt-run* (fn-sxd-run *sxdt-bs* *sxdt-program* *sxdt-ok*))
; Every step ran (no error): the run has a state per step.
(assert-event (equal (len *sxdt-run*) (len *sxdt-program*)))
(assert-event (sxdt-all-hold *sxdt-run*))
; The conclusion's second arm is reached: at the end the MANIFEST is durable
; with nothing lost, and the archive is complete.
(defconst *sxdt-last* (car (last *sxdt-run*)))
(assert-event (null (fn-bs-pending *sxdt-last*)))
(assert-event (equal (fn-bs-durable-entry (sxdt-img-none *sxdt-last*) :arch "MANIFEST") 0))
(assert-event (fn-sxd-completep (sxdt-img-none *sxdt-last*) *sxdt-entries* 0 *sxdt-manifest*))
(assert-event (equal (fn-sxd-archive-verdict
                      (fn-bs-durable-entry (sxdt-img-none *sxdt-last*) :arch "MANIFEST"))
                     :read))
; And the first arm: every state before the rename has no MANIFEST in either
; image (the refusal by name, archive-incomplete) -- even the one where
; every data write and entry landed.
(defconst *sxdt-before-rename*
  (take (- (len *sxdt-program*) 4) *sxdt-run*))
(defun sxdt-no-manifest (states)
  (if (consp states)
      (and (null (fn-bs-durable-entry (sxdt-img-all (car states)) :arch "MANIFEST"))
           (null (fn-bs-durable-entry (sxdt-img-none (car states)) :arch "MANIFEST"))
           (sxdt-no-manifest (cdr states)))
    t))
(assert-event (sxdt-no-manifest *sxdt-before-rename*))
(assert-event (equal (fn-sxd-archive-verdict nil) :archive-incomplete))
; The data is written but not durable before the sync: a crash that lands
; nothing just before it loses the records' octets.
(defconst *sxdt-before-sync*
  (nth (- (len (fn-sxd-write-program *sxdt-entries* *sxdt-manifest*)) 1) *sxdt-run*))
(assert-event (consp (fn-bs-pending *sxdt-before-sync*)))
(assert-event (not (fn-sxd-durable-landed (sxdt-img-none *sxdt-before-sync*)
                                          *sxdt-entries* 0)))
; The sync fails (EIO after landing nothing): the run stops there, and no
; image of it has a MANIFEST.
(defconst *sxdt-sync-eio*
  (fn-sxd-run *sxdt-bs* *sxdt-program*
              (append (make-list (len (fn-sxd-write-program *sxdt-entries* *sxdt-manifest*))
                                 :initial-element :ok)
                      (list (cons :eio nil)))))
(assert-event (equal (len *sxdt-sync-eio*)
                     (1+ (len (fn-sxd-write-program *sxdt-entries* *sxdt-manifest*)))))
(assert-event (sxdt-no-manifest *sxdt-sync-eio*))

; -----------------------------------------------------------------------------
; Mutation witness: the MANIFEST renamed BEFORE the sync (the order the
; decision forbids).  A crash that lands the rename and none of the data
; leaves a MANIFEST over an archive whose entries are empty: the conclusion
; fails, so it is not vacuous.
(defconst *sxdt-bad-program*
  (append (fn-sxd-write-program *sxdt-entries* *sxdt-manifest*)
          (list (list :rename :arch *fn-sxd-partial* :arch *fn-sxd-manifest*)
                (list :sync-all))))
(defconst *sxdt-bad-run*
  (fn-sxd-run *sxdt-bs* *sxdt-bad-program*
              (make-list (len *sxdt-bad-program*) :initial-element :ok)))
(defconst *sxdt-bad-state* (nth (- (len *sxdt-bad-program*) 2) *sxdt-bad-run*))
; Choices: drop every pending write, apply every entry operation.
(defun sxdt-entries-only (ops)
  (if (consp ops)
      (cons (if (equal (car (car ops)) :write) nil :apply)
            (sxdt-entries-only (cdr ops)))
    nil))
(defconst *sxdt-bad-img*
  (fn-bs-crash *sxdt-bad-state* (sxdt-entries-only (fn-bs-pending *sxdt-bad-state*))))
(assert-event (fn-bs-durable-entry *sxdt-bad-img* :arch "MANIFEST"))
(assert-event (not (sxdt-conclusion *sxdt-bad-img*)))
; The same choices on the decided program's last states keep it.
(assert-event (sxdt-conclusion
               (fn-bs-crash *sxdt-last* (sxdt-entries-only (fn-bs-pending *sxdt-last*)))))

; -----------------------------------------------------------------------------
; Hypothesis-removal witnesses.

; (1) fn-sxd-quietp removed: a directory that already holds a durable
; MANIFEST.  Every other hypothesis holds; the omitted one fails; the
; conclusion fails at the first state (a MANIFEST over no entry).
(defconst *sxdt-stale-bs*
  (fn-bs-make 4 (list (cons 0 '(1))) (list (cons :arch (list (cons "MANIFEST" 0)))) nil 1))
(assert-event (fn-bs-statep *sxdt-stale-bs*))
(assert-event (fn-sxd-keysp *sxdt-entries*))
(assert-event (fn-cbor-octet-listp *sxdt-manifest*))
(assert-event (fn-sxd-outcomesp *sxdt-ok*))
(assert-event (not (fn-sxd-quietp *sxdt-stale-bs*)))
(defconst *sxdt-stale-first*
  (car (fn-sxd-run *sxdt-stale-bs* *sxdt-program* *sxdt-ok*)))
(assert-event
 (let ((img (sxdt-img-none *sxdt-stale-first*)))
   (not (or (null (fn-bs-durable-entry img :arch *fn-sxd-manifest*))
            (fn-sxd-completep img *sxdt-entries* (fn-bs-next-ino *sxdt-stale-bs*)
                              *sxdt-manifest*)))))

; (2) fn-sxd-outcomesp removed: a write that reports :ok having accepted no
; octet ((:ok . 0), which write_all never answers).  The run completes, the
; MANIFEST is durable, and the first record's file is empty.
(defconst *sxdt-short-outs*
  (update-nth 4 (cons :ok 0) *sxdt-ok*))
(assert-event (equal (nth 3 *sxdt-program*) '(:create :arch "profile")))
(assert-event (equal (car (nth 4 *sxdt-program*)) :write-all))
(assert-event (fn-bs-statep *sxdt-bs*))
(assert-event (fn-sxd-quietp *sxdt-bs*))
(assert-event (not (fn-sxd-outcomesp *sxdt-short-outs*)))
(defconst *sxdt-short-last*
  (car (last (fn-sxd-run *sxdt-bs* *sxdt-program* *sxdt-short-outs*))))
(assert-event (equal (len (fn-sxd-run *sxdt-bs* *sxdt-program* *sxdt-short-outs*))
                     (len *sxdt-program*)))
(assert-event (not (sxdt-conclusion (sxdt-img-none *sxdt-short-last*))))

; (3) fn-sxd-keysp removed: an entry named MANIFEST in DIR is created (and
; made durable by the sync) before the export's own MANIFEST exists.
(defconst *sxdt-bad-entries* (cons '(:arch "MANIFEST" 42) *sxdt-entries*))
(assert-event (not (fn-sxd-keysp *sxdt-bad-entries*)))
(defconst *sxdt-bad-keys-run*
  (fn-sxd-run *sxdt-bs* (fn-sxd-program *sxdt-bad-entries* *sxdt-manifest*)
              (make-list (len (fn-sxd-program *sxdt-bad-entries* *sxdt-manifest*))
                         :initial-element :ok)))
(defconst *sxdt-bad-keys-sync*
  (nth (len (fn-sxd-write-program *sxdt-bad-entries* *sxdt-manifest*)) *sxdt-bad-keys-run*))
(assert-event
 (let ((img (sxdt-img-none *sxdt-bad-keys-sync*)))
   (and (fn-bs-durable-entry img :arch "MANIFEST")
        (not (equal (fn-bs-durable-entry img :arch "MANIFEST") (fn-bs-next-ino *sxdt-bs*))))))
