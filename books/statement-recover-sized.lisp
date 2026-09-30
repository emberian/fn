; Parallel ORIGINAL context metadata for the actual sequential recovery worker.
; The public SSR accumulator remains its four-cell representation. Metadata
; availability never changes its row decision or arena effects.
; Source producer b41036086; installed provenance remains a separate obligation.
(in-package "ACL2")
(include-book "statement-recover-stream")
(include-book "replay-produced-size")
(local (in-theory (disable (tau-system))))

(defun fn-ssrs-identity (acc)
 (declare (xargs :guard t))
 (if (eq acc :bad) :bad (fn-ssr-at 3 acc)))

; Fields are the same-source summary annotations, not newly summarized data.
(defun fn-ssrs-seed (identity fields)
 (declare (xargs :guard t))
 (mv (fn-ssr-seed identity)
     (if (fn-ics-carriesp fields) fields nil)
     (if (fn-ics-carriesp fields) :carried :unavailable)))

(defun fn-ssrs-intern-step (acc fields ws rs ps mode dicts snapshot-carries fn-arena)
 (declare (xargs :stobjs fn-arena :measure (len ws) :verify-guards nil
                 :hints (("Goal" :in-theory (disable fn-intern-event fn-arx-intern-event
                   fn-lzr-intern-event fn-ris-produced-step fn-replay-identity-step
                   fn-ssr-publish fn-ssr-at)))
                 :guard (and (or (eq acc :bad) (fn-ssr-statep acc))
                             (fn-lzr-dictsp dicts))))
 (cond ((or (eq acc :bad) (eq ws :bad))
        (mv :bad nil :unavailable fn-arena))
       ((atom ws)
        (mv (if (null ws) acc :bad)
            (if (and (null ws) (fn-ics-carriesp fields)) fields nil)
            (if (and (null ws) (fn-ics-carriesp fields)) :carried :unavailable)
            fn-arena))
       (t
        (let* ((wire (car ws)) (r (fn-ag-car rs)) (p (fn-ag-car ps))
               (file (nfix (fn-ag-car p))) (position (fn-ag-cdr p)))
         (mv-let (row fn-arena)
          (cond ((eq mode :lz)
                 (fn-lzr-intern-event wire r position file dicts
                  (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) fn-arena))
                ((eq mode :extent)
                 (fn-arx-intern-event wire r position file
                  (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) fn-arena))
                (t (fn-intern-event wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) fn-arena)))
          ; Exactly one actual produced decision after actual row intern.
          (mv-let (identity next-fields metadata)
                  (fn-ris-produced-step (fn-ssr-at 3 acc)
                    (if (fn-ics-carriesp fields) fields nil) row
                    (if (fn-scs-carryp (fn-ag-car snapshot-carries))
                        (fn-ag-car snapshot-carries) nil))
           (declare (ignore metadata))
           (if (or (eq row :bad) (not (equal (fn-stxk-context-kind identity) :ok)))
            (mv :bad nil :unavailable fn-arena)
            (fn-ssrs-intern-step (fn-ssr-publish acc row wire identity)
             next-fields (cdr ws) (fn-ag-cdr rs) (fn-ag-cdr ps) mode dicts
             (fn-ag-cdr snapshot-carries) fn-arena))))))))

; The complete existing accumulator and arena effect are preserved even
; when side metadata is unavailable. No provenance/readiness follows.
(local
 (defthm fn-ssrs-produced-context-is-public
  (equal (mv-nth 0 (fn-ris-produced-step ctx fields event snapshot-carry))
         (fn-replay-identity-step ctx event))
  :hints (("Goal" :use ((:instance fn-ris-produced-step-is-public-replay))
           :in-theory (disable fn-ris-produced-step fn-replay-identity-step)))))
(defthm fn-ssrs-intern-step-preserves-complete-public-result
 (equal
  (list (mv-nth 0 (fn-ssrs-intern-step acc fields ws rs ps mode dicts snapshot-carries fn-arena))
        (mv-nth 3 (fn-ssrs-intern-step acc fields ws rs ps mode dicts snapshot-carries fn-arena)))
  (list (mv-nth 0 (fn-ssr-intern-step acc ws rs ps mode dicts fn-arena))
        (mv-nth 1 (fn-ssr-intern-step acc ws rs ps mode dicts fn-arena))))
 :rule-classes nil
 :hints (("Goal"
          :induct (fn-ssrs-intern-step acc fields ws rs ps mode dicts snapshot-carries fn-arena)
          :do-not '(generalize fertilize eliminate-destructors)
          :in-theory (e/d (fn-ssrs-intern-step fn-ssr-intern-step)
                          (fn-ris-produced-step fn-intern-event fn-arx-intern-event
                           fn-lzr-intern-event fn-ssr-at fn-ssr-publish
                           fn-replay-identity-step fn-stxk-context-kind)))))

(defthm fn-ssrs-intern-step-preserves-statep
 (implies (fn-ssr-statep acc)
  (or (eq (mv-nth 0 (fn-ssrs-intern-step acc fields ws rs ps mode dicts snapshot-carries fn-arena)) :bad)
      (fn-ssr-statep
       (mv-nth 0 (fn-ssrs-intern-step acc fields ws rs ps mode dicts snapshot-carries fn-arena)))))
 :hints (("Goal"
          :use ((:instance fn-ssrs-intern-step-preserves-complete-public-result)
                (:instance fn-ssr-intern-step-preserves-statep))
          :in-theory (disable fn-ssrs-intern-step fn-ssr-intern-step
                              fn-ssr-statep fn-ssr-intern-step-preserves-statep))))

(verify-guards fn-ssrs-intern-step
 :hints (("Goal" :in-theory (e/d (fn-ssr-statep)
              (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
               fn-ris-produced-step fn-replay-identity-step fn-ssr-publish fn-ssr-at)))))
