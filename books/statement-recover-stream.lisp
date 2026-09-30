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

; The physical seals and resident seals agree without an arena premise.
; The row equality therefore does not need to revalidate the arena.
(local (defthm fn-ssr-record-payload-octets
 (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
 :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
(local (defthm fn-ssr-resident-record
 (implies (fn-record-p w)
  (equal (fn-intern-event w keyring generation fn-arena)
         (fn-cat-intern-list w keyring generation fn-arena)))
 :hints (("Goal" :in-theory (e/d (fn-intern-event)
   (fn-cat-intern-list fn-record-p fn-stxa-p fn-replay-composite-record
    fn-cat-intern-list-is-row-at-count))))))
(local (defthm fn-ssr-extent-seal-is-list
 (equal (fn-arena-seal-extent file eoff elen poff plen trailer fn-arena)
        (fn-arena-seal-list (fn-durable-octets file poff plen) fn-arena))
 :hints (("Goal" :in-theory (enable fn-arena-seal-extent fn-arena-seal-list
                          fn-arena$a-seal-extent fn-arena$a-seal-list)))))

(local (defthm fn-ssr-lz-seal-is-list
 (equal (fn-arena-seal-lz-extent file eoff elen poff plen trailer n dict fn-arena)
        (fn-arena-seal-list (fn-lzr-lz-value dict (fn-durable-octets file poff plen) n) fn-arena))
 :hints (("Goal" :in-theory (enable fn-arena-seal-lz-extent fn-arena-seal-list
                          fn-arena$a-seal-lz-extent fn-arena$a-seal-list)))))

(local (defthm fn-ssr-extent-row-refines
 (implies (equal (fn-durable-octets (nth 0 x) (nth 3 x) (nth 4 x)) (fn-record-payload w))
  (equal (fn-arx-cat-intern-extent w x keyring generation fn-arena)
         (fn-cat-intern-list w keyring generation fn-arena)))
 :hints (("Goal" :in-theory (e/d (fn-arx-cat-intern-extent fn-cat-intern-list)
                   (fn-record-p fn-held-facts-of fn-held-context-of))))))

(local (defthm fn-ssr-extent-event-refines
 (implies (equal (fn-durable-octets (nfix file) (nfix (nth 2 position)) (len r)) r)
  (equal (fn-arx-intern-event w r position file keyring generation fn-arena)
         (fn-intern-event w keyring generation fn-arena)))
 :hints (("Goal" :in-theory (e/d (fn-arx-intern-event fn-intern-event)
              (fn-arx-cat-intern-extent fn-cat-intern-list fn-arx-extent-of
               fn-stxa-p fn-replay-composite-record fn-cat-intern-list-is-row-at-count))
           :do-not-induct t
           :use ((:instance fn-arx-extent-of-denotes-payload)
                 (:instance fn-ssr-extent-row-refines (x (fn-arx-extent-of file position r w))))))))

(local (defthm fn-ssr-lz-row-refines
 (implies (equal (fn-lzr-lz-value dict (fn-durable-octets (nth 0 x) (nth 3 x) (nth 4 x))
                                (nth 6 x)) (fn-record-payload w))
  (equal (fn-lzr-cat-intern-lz w x dict keyring generation fn-arena)
         (fn-cat-intern-list w keyring generation fn-arena)))
 :hints (("Goal" :in-theory (e/d (fn-lzr-cat-intern-lz fn-cat-intern-list)
                   (fn-record-p fn-held-facts-of fn-held-context-of))))))

(local (defthm fn-ssr-lz-event-refines
 (implies (equal (fn-durable-octets (nfix file) (nfix (nth 2 position)) (len z)) z)
  (equal (fn-lzr-intern-event w z position file dicts keyring generation fn-arena)
         (fn-intern-event w keyring generation fn-arena)))
 :hints (("Goal"
      :in-theory '(fn-lzr-intern-event fn-ssr-resident-record fn-cbor-octet-listp-implies-true-listp)
      :do-not-induct t
      :use ((:instance fn-lzr-extent-of-lz-value (payload (fn-record-payload w)))
            (:instance fn-ssr-extent-event-refines (r z))
            (:instance fn-ssr-lz-row-refines
              (x (fn-lzr-extent-of file position z (fn-record-payload w) dicts))
              (dict (cdr (assoc-equal (nth 7 (fn-lzr-extent-of file position z
                         (fn-record-payload w) dicts)) dicts)))))))))

; Physical replay modes refine the very same sequential statement-context
; worker: keys, generations, verdict contexts, rows and arena effects agree.
(defthm fn-ssr-extent-step-refines-resident
 (implies (fn-arx-faithful-p rs ps)
  (equal (fn-ssr-intern-step acc ws rs ps :extent dicts fn-arena)
         (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)))
 :hints (("Goal" :induct (fn-ssr-intern-step acc ws rs ps :extent dicts fn-arena)
  :do-not '(preprocess generalize fertilize eliminate-destructors)
  :in-theory (e/d (fn-ssr-intern-step fn-arx-faithful-p)
                 (fn-intern-event fn-arx-intern-event fn-lzr-intern-event fn-ssr-at
                  fn-replay-identity-step fn-ssr-publish fn-intern-event-arena fn-stxk-context-kind
                  fn-ssr-resident-ignores-places fn-ssr-resident-record)))))
(defthm fn-ssr-lz-step-refines-resident
 (implies (fn-arx-faithful-p rs ps)
  (equal (fn-ssr-intern-step acc ws rs ps :lz dicts fn-arena)
         (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)))
 :hints (("Goal" :induct (fn-ssr-intern-step acc ws rs ps :lz dicts fn-arena)
  :do-not '(preprocess generalize fertilize eliminate-destructors)
  :in-theory (e/d (fn-ssr-intern-step fn-arx-faithful-p)
                 (fn-intern-event fn-arx-intern-event fn-lzr-intern-event fn-ssr-at
                  fn-replay-identity-step fn-ssr-publish fn-intern-event-arena fn-stxk-context-kind
                  fn-ssr-resident-ignores-places fn-ssr-resident-record)))))

(defun fn-ssr-rows (acc)
 (declare (xargs :guard t))
 (if (eq acc :bad) :bad (fn-ag-rev-onto (fn-ssr-at 0 acc) nil)))
(in-theory (disable fn-ssr-state fn-ssr-statep fn-ssr-seed fn-ssr-publish fn-ssr-intern-step fn-ssr-rows))
