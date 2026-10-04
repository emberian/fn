; Sequential statement-context replay. A row freezes the key table/generation
; immediately BEFORE its event; kind3 publication updates only the next row.
; Recovery shares this worker across resident, extent and compressed records.
(in-package "ACL2")
(include-book "store-recover-stream")
(include-book "payload-lz-replay")
(include-book "statement-snapshot-keyring")

(defun fn-ssr-state (rows keyring generation identity)
 (declare (xargs :guard t))
 (list rows keyring generation identity))
(defun fn-ssr-at (n x)
 (declare (xargs :guard (natp n)))
 (if (zp n) (fn-ag-car x) (fn-ssr-at (1- n) (fn-ag-cdr x))))
(defun fn-ssr-statep (x)
 (declare (xargs :guard t))
 (and (true-listp x) (equal (len x) 4)
      (fn-prin-keyringp (fn-ssr-at 1 x)) (natp (fn-ssr-at 2 x))))
(defun fn-ssr-seed (identity)
 (declare (xargs :guard t))
 (fn-ssr-state nil
  (fn-ssk-keyring-of-snapshots (fn-stxk-context-snapshots identity))
  (fn-ssk-generation (fn-stxk-context-snapshots identity)) identity))
(defthm fn-ssr-seed-establishes-statep
 (fn-ssr-statep (fn-ssr-seed identity))
 :hints (("Goal" :in-theory (enable fn-ssr-statep fn-ssr-seed fn-ssr-state fn-ssr-at fn-ssk-generation))))

(defun fn-ssr-publish (acc row wire identity)
 (declare (xargs :guard (fn-ssr-statep acc)
                 :guard-hints (("Goal" :in-theory (enable fn-ssr-statep)))))
 (let* ((old (fn-ssr-at 3 acc))
        (newp (and (fn-stxk-p wire)
                   (equal (fn-stxk-context-kind identity) :ok)
                   (not (equal (fn-stxk-context-current-generation old)
                               (fn-stxk-context-current-generation identity))))))
  (fn-ssr-state (cons row (fn-ssr-at 0 acc))
    (if newp (fn-ssk-apply-snapshot wire (fn-ssr-at 1 acc)) (fn-ssr-at 1 acc))
    (if newp (nfix (fn-stxk-keyring-generation wire)) (fn-ssr-at 2 acc)) identity)))
(defthm fn-ssr-publish-preserves-statep
 (implies (fn-ssr-statep acc) (fn-ssr-statep (fn-ssr-publish acc row wire identity)))
 :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-statep fn-ssr-state fn-ssr-at))))

(defun fn-ssr-intern-step (acc ws rs ps mode dicts fn-arena)
 (declare (xargs :stobjs fn-arena :measure (len ws)
                 :hints (("Goal" :in-theory (disable fn-intern-event fn-arx-intern-event
                   fn-lzr-intern-event fn-replay-identity-step fn-ssr-publish fn-ssr-at)))
                 :guard (and (or (eq acc :bad) (fn-ssr-statep acc))
                             (fn-lzr-dictsp dicts))
                 :guard-hints (("Goal" :in-theory (e/d (fn-ssr-statep)
                   (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                    fn-replay-identity-step fn-ssr-publish fn-ssr-at))))))
 (cond ((or (eq acc :bad) (eq ws :bad)) (mv :bad fn-arena))
       ((atom ws) (mv (if (null ws) acc :bad) fn-arena))
       (t
        (let* ((wire (car ws))
               (r (fn-ag-car rs)) (p (fn-ag-car ps))
               (file (nfix (fn-ag-car p))) (position (fn-ag-cdr p)))
         (mv-let (row fn-arena)
          (cond ((eq mode :lz)
                 (fn-lzr-intern-event wire r position file dicts
                  (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) fn-arena))
                ((eq mode :extent)
                 (fn-arx-intern-event wire r position file
                  (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) fn-arena))
                (t (fn-intern-event wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) fn-arena)))
          ; Identity selectors consume retained rows, not raw ARTICLE wires.
          ; Intern first under the old epoch; then validate and publish it.
          (let ((identity (fn-replay-identity-step (fn-ssr-at 3 acc) row)))
           (if (or (eq row :bad) (not (equal (fn-stxk-context-kind identity) :ok)))
               (mv :bad fn-arena)
             (fn-ssr-intern-step (fn-ssr-publish acc row wire identity)
              (cdr ws) (fn-ag-cdr rs) (fn-ag-cdr ps) mode dicts fn-arena))))))))


(defthm fn-ssr-intern-step-preserves-statep
 (implies (fn-ssr-statep acc)
  (or (eq (mv-nth 0 (fn-ssr-intern-step acc ws rs ps mode dicts fn-arena)) :bad)
      (fn-ssr-statep (mv-nth 0 (fn-ssr-intern-step acc ws rs ps mode dicts fn-arena)))))
 :hints (("Goal" :induct (fn-ssr-intern-step acc ws rs ps mode dicts fn-arena)
   :in-theory (disable fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                       fn-ssr-publish fn-replay-identity-step fn-ssr-statep fn-ssr-at))))
 ; Chunk boundaries do not change rows, active keys, historical generation,
; identity evidence or arena effects. The host calls this same subject.
(defthm fn-ssr-resident-step-of-append
 (implies (true-listp a)
  (equal (fn-ssr-intern-step acc (append a b) nil nil :resident dicts fn-arena)
   (mv-let (middle fn-arena)
    (fn-ssr-intern-step acc a nil nil :resident dicts fn-arena)
    (fn-ssr-intern-step middle b nil nil :resident dicts fn-arena))))
 :hints (("Goal" :induct (fn-ssr-intern-step acc a nil nil :resident dicts fn-arena)
  :do-not '(generalize fertilize eliminate-destructors)
  :in-theory (e/d (fn-ssr-intern-step)
                     (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                      fn-ssr-publish fn-replay-identity-step fn-ssr-at fn-stxk-context-kind)))))

(local (defthm fn-ssr-resident-ignores-places
 (equal (fn-ssr-intern-step acc ws rs ps :resident dicts fn-arena)
        (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))
 :hints (("Goal" :induct (fn-ssr-intern-step acc ws rs ps :resident dicts fn-arena)
  :in-theory (e/d (fn-ssr-intern-step)
                 (fn-intern-event fn-arx-intern-event fn-lzr-intern-event fn-ssr-at
                  fn-replay-identity-step fn-ssr-publish fn-stxk-context-kind))))))
(local (defthm fn-ssr-arena-p-of-intern-event
 (implies (fn-arena-p fn-arena)
  (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
 :hints (("Goal" :in-theory (e/d (fn-intern-event-arena fn-arena-p-is-payload-listp
                                    fn-record-p fn-record-payloadp)
                                   (fn-intern-event fn-stxa-p fn-replay-composite-record))))))

; Physical replay modes refine the very same sequential statement-context
; worker: keys, generations, verdict contexts, rows and arena effects agree.
(defthm fn-ssr-extent-step-refines-resident
 (implies (and (fn-arena-p fn-arena) (fn-arx-faithful-p rs ps))
  (equal (fn-ssr-intern-step acc ws rs ps :extent dicts fn-arena)
         (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)))
 :hints (("Goal" :induct (fn-ssr-intern-step acc ws rs ps :extent dicts fn-arena)
  :do-not '(preprocess generalize fertilize eliminate-destructors)
  :in-theory (e/d (fn-ssr-intern-step fn-arx-faithful-p)
                 (fn-intern-event fn-arx-intern-event fn-lzr-intern-event fn-ssr-at
                  fn-replay-identity-step fn-ssr-publish fn-intern-event-arena fn-stxk-context-kind
                  fn-ssr-resident-ignores-places)))))
(defthm fn-ssr-lz-step-refines-resident
 (implies (and (fn-arena-p fn-arena) (fn-arx-faithful-p rs ps))
  (equal (fn-ssr-intern-step acc ws rs ps :lz dicts fn-arena)
         (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)))
 :hints (("Goal" :induct (fn-ssr-intern-step acc ws rs ps :lz dicts fn-arena)
  :do-not '(preprocess generalize fertilize eliminate-destructors)
  :in-theory (e/d (fn-ssr-intern-step fn-arx-faithful-p)
                 (fn-intern-event fn-arx-intern-event fn-lzr-intern-event fn-ssr-at
                  fn-replay-identity-step fn-ssr-publish fn-intern-event-arena fn-stxk-context-kind
                  fn-ssr-resident-ignores-places)))))

(defun fn-ssr-rows (acc)
 (declare (xargs :guard t))
 (if (eq acc :bad) :bad (fn-ag-rev-onto (fn-ssr-at 0 acc) nil)))
(in-theory (disable fn-ssr-state fn-ssr-statep fn-ssr-seed fn-ssr-publish fn-ssr-intern-step fn-ssr-rows))

; -----------------------------------------------------------------------------
; The relation to the chunked raw replay (books/store-recover-stream.lisp
; fn-srs-intern-step and fn-srs-rows, what host/store-open-host.lisp and
; host/store-write-host.lisp open over; lane proofs 2026-10-04, the KW-i row
; of the 10-01 re-tag): this worker is that one with the keyring and
; generation each row freezes.  Over a history with no keyring snapshot
; (fn-ssr-no-snapshot-p: no wire is an fn-stxk-p event, so no row publishes a
; new generation), from an accumulator whose keys are the open's (no keyring,
; generation 0), the rows this worker answers are exactly the raw worker's
; rows and its arena is the raw worker's arena.  What this worker adds over
; the raw one -- the identity cursor (a history whose sequences do not run
; from the seed's cursor is :bad here and not there) and the frozen keys of
; a rotated keyring -- is exactly what the hypotheses name.  The host's full
; recovery (host/native/io.lisp fnn-bridge-recover-begin) starts from
; fn-ssr-seed of fn-stxk-initial-context, whose keys are the open's:
; fn-ssr-recovery-rows-are-the-raw-rows-without-snapshots is that instance.

(defun fn-ssr-no-snapshot-p (ws)
  (declare (xargs :guard t))
  (if (atom ws)
      t
    (and (not (fn-stxk-p (car ws)))
         (fn-ssr-no-snapshot-p (cdr ws)))))

(local
 (defthm fn-ssr-raw-fold-without-snapshots
   (implies (and (fn-ssr-no-snapshot-p ws)
                 (not (eq acc :bad))
                 (null (fn-ssr-at 1 acc)) (equal (fn-ssr-at 2 acc) 0)
                 (not (eq (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))
                          :bad)))
            (and (not (eq (mv-nth 0 (fn-intern-events ws nil 0 fn-arena)) :bad))
                 (equal (fn-ssr-at 0 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts
                                                                   fn-arena)))
                        (revappend (mv-nth 0 (fn-intern-events ws nil 0 fn-arena))
                                   (fn-ssr-at 0 acc)))
                 (equal (mv-nth 1 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))
                        (mv-nth 1 (fn-intern-events ws nil 0 fn-arena)))))
   :hints (("Goal" :induct (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)
            :do-not '(generalize fertilize eliminate-destructors)
            :in-theory (e/d (fn-ssr-intern-step fn-ssr-publish fn-ssr-state fn-ssr-at
                             fn-intern-events)
                            (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                             fn-replay-identity-step fn-stxk-context-kind
                             fn-stxk-context-current-generation fn-stxk-p
                             fn-ssk-apply-snapshot fn-stxk-keyring-generation
                             fn-ssr-resident-ignores-places))))))

(defthm fn-ssr-rows-are-the-raw-rows-without-snapshots
  (implies (and (fn-ssr-no-snapshot-p ws)
                (not (eq acc :bad))
                (null (fn-ssr-at 1 acc)) (equal (fn-ssr-at 2 acc) 0)
                (true-listp (fn-ssr-at 0 acc))
                (not (eq (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))
                         :bad)))
           (and (equal (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts
                                                                  fn-arena)))
                       (fn-srs-rows (mv-nth 0 (fn-srs-intern-step (fn-ssr-at 0 acc) ws fn-arena))))
                (equal (mv-nth 1 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))
                       (mv-nth 1 (fn-srs-intern-step (fn-ssr-at 0 acc) ws fn-arena)))))
  :hints (("Goal" :do-not-induct t
           :use fn-ssr-raw-fold-without-snapshots
           :in-theory (e/d (fn-ssr-rows fn-srs-intern-step fn-srs-rows)
                           (fn-ssr-intern-step fn-intern-events fn-ssr-at
                            fn-ssr-raw-fold-without-snapshots)))))

; The host's full recovery: from the seed of the initial identity context.
(defthm fn-ssr-recovery-rows-are-the-raw-rows-without-snapshots
  (let ((seed (fn-ssr-seed (fn-stxk-initial-context 0))))
    (implies (and (fn-ssr-no-snapshot-p ws)
                  (not (eq (mv-nth 0 (fn-ssr-intern-step seed ws nil nil :resident dicts fn-arena))
                           :bad)))
             (and (equal (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step seed ws nil nil :resident dicts
                                                                    fn-arena)))
                         (fn-srs-rows (mv-nth 0 (fn-srs-intern-step nil ws fn-arena))))
                  (equal (mv-nth 1 (fn-ssr-intern-step seed ws nil nil :resident dicts fn-arena))
                         (mv-nth 1 (fn-srs-intern-step nil ws fn-arena))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ssr-rows-are-the-raw-rows-without-snapshots
                            (acc (fn-ssr-seed (fn-stxk-initial-context 0)))))
           :in-theory (e/d (fn-ssr-seed fn-ssr-state fn-ssr-at fn-stxk-initial-context
                            fn-stxk-context fn-stxk-context-snapshots
                            fn-ssk-keyring-of-snapshots fn-ssk-generation)
                           (fn-ssr-intern-step fn-srs-intern-step fn-ssr-rows fn-srs-rows
                            fn-ssr-rows-are-the-raw-rows-without-snapshots)))))
