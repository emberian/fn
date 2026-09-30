; One actual recovery row and its retained produced decision. Source assembly
; only: guard verification and complete public-result refinement remain open.
(in-package "ACL2")
(include-book "statement-recover-sized")

(defun fn-ssrp-intern-row (acc fields wire raw position mode dicts snapshot-carry fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil
                 :guard (and (fn-ssr-statep acc) (fn-lzr-dictsp dicts))))
 (let ((file (nfix (fn-ag-car position))) (offset (fn-ag-cdr position)))
  (mv-let (row fn-arena)
   (cond ((eq mode :lz)
          (fn-lzr-intern-event wire raw offset file dicts
           (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) fn-arena))
         ((eq mode :extent)
          (fn-arx-intern-event wire raw offset file
           (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) fn-arena))
         (t (fn-intern-event wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) fn-arena)))
   ; The caller consumes these lexical results before advancing the prefix.
   ; Missing carries affect metadata alone; they never skip the real decision.
   (mv-let (identity next-fields metadata effect child sizes)
    (fn-ris-produced-step-with-effects (fn-ssr-at 3 acc)
     (if (fn-ics-carriesp fields) fields nil) row
     (if (fn-scs-carryp snapshot-carry) snapshot-carry nil))
    (if (or (eq row :bad) (not (equal (fn-stxk-context-kind identity) :ok)))
     (mv :bad nil :unavailable effect child sizes row fn-arena)
     (mv (fn-ssr-publish acc row wire identity) next-fields metadata
         effect child sizes row fn-arena))))))
