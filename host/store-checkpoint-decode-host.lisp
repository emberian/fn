; Single actual PROGRAM checkpoint decoder/metadata implementation.
; Existing native names and arities are preserved; caller bounds and general
; summary annotation/load provenance remain separate open obligations.
(in-package "ACL2")
(include-book "store-checkpoint-context-host")
(include-book "../books/store-checkpoint-arena-load")
(include-book "../books/store-checkpoint-arena-size-load")
(include-book "../books/store-checkpoint-digest")
(defun fn-store-sco-clear (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (fn-store-sco-source-invalidate state))
         (state (f-put-global 'fn-store-sco-checkpoint nil state))
         (state (f-put-global 'fn-store-sco-context-info nil state))
         (state (f-put-global 'fn-store-sco-summary-region nil state))
         (state (f-put-global 'fn-store-sco-recovery-source nil state))
         (state (f-put-global 'fn-store-sco-original-plan nil state))
         (state (f-put-global 'fn-store-sco-load nil state))
         (state (f-put-global 'fn-store-sco-open nil state)))
    (value :cleared)))

(defun fn-store-sco-decode (plan fn-octets state)
  (declare (xargs :stobjs (fn-octets state) :mode :program))
  (let* ((state (fn-store-sco-source-invalidate state))
         (state (f-put-global 'fn-store-sco-checkpoint nil state))
         (state (f-put-global 'fn-store-sco-context-info nil state))
         (state (f-put-global 'fn-store-sco-summary-region nil state))
         (state (f-put-global 'fn-store-sco-recovery-source nil state))
         (state (f-put-global 'fn-store-sco-original-plan nil state))
         (o (fn-scka-open-run plan fn-octets)))
    (if (and (consp o) (eq (car o) :ok))
        (let* ((state (f-put-global 'fn-store-sco-load (list (nth 4 o) (nth 5 o)) state))
               (state (f-put-global 'fn-store-sco-original-plan plan state)))
          (mv nil (list :arena (nth 1 o) (nth 2 o) (nth 3 o)) state fn-octets))
      (let ((state (f-put-global 'fn-store-sco-load nil state)))
        (mv nil
            (list :refused (if (and (consp o) (consp (cdr o))) (cadr o) :malformed))
            state fn-octets)))))

(defun fn-store-sco-decode-finish (i end fn-octets state)
  (declare (xargs :stobjs (fn-octets state) :mode :program))
  (let* ((original-plan (and (boundp-global 'fn-store-sco-original-plan state)
                              (f-get-global 'fn-store-sco-original-plan state)))
         (load (and (boundp-global 'fn-store-sco-load state)
                    (f-get-global 'fn-store-sco-load state)))
         (state (f-put-global 'fn-store-sco-load nil state))
         (state (f-put-global 'fn-store-sco-context-info nil state))
         (state (f-put-global 'fn-store-sco-summary-region nil state))
         (state (f-put-global 'fn-store-sco-recovery-source nil state))
         (state (f-put-global 'fn-store-sco-original-plan nil state)))
   (mv-let (loaded context-info summary-region)
           (if (and (consp load) (consp (cdr load)))
               (fn-sckas-finish (car load) (cadr load) i end fn-octets)
             (mv (list :refused :arena) nil nil))
    (if (and (consp loaded) (eq (car loaded) :ok) (consp (cdr loaded)))
        ; The tables mean the capture (fn-sct-capture-of-tables-of-capture):
        ; the 7-tuple the open extends, its event index rebuilt from E.
        (let* ((checkpoint (fn-sct-capture-of-tables (cadr loaded)))
               (state (f-put-global 'fn-store-sco-checkpoint checkpoint state))
               ; Same decode and physical load; owner epoch/source association
               ; is established by the recovery controller, not this adapter.
               (state (f-put-global 'fn-store-sco-context-info context-info state))
               (state (f-put-global 'fn-store-sco-summary-region summary-region state))
               (state (f-put-global 'fn-store-sco-recovery-source
                        (and original-plan summary-region
                         (list :verified-checkpoint original-plan checkpoint summary-region
                               (fn-sct-tables-log (cadr loaded))
                               (fn-sco-at 2 (fn-sct-tables-f (cadr loaded)))
                               (fn-sco-at 1 (fn-sct-tables-f (cadr loaded))))) state))
               ; PKT-854: the tables' part of the checkpoint digest, only
               ; when `store ROOT digest' asked (fn-store-sco-want-
               ; checkpoint-digest); the arena's part follows the load
               ; (fn-store-sco-note-checkpoint-digest).
               (state (f-put-global
                       'fn-store-sco-tables-digest
                       (and (boundp-global 'fn-store-sco-want-digest state)
                            (f-get-global 'fn-store-sco-want-digest state)
                            (list (fn-sco-sequence checkpoint)
                                  (fn-sckd-tables-digest (cadr loaded))))
                       state))
               ; The F row's log position and frontier (a store's
               ; open starts its scan there: books/store-log-segments.lisp).
               (state (f-put-global 'fn-store-sco-log-position
                                    (list (fn-sct-tables-log (cadr loaded))
                                          (fn-sco-at 2 (fn-sct-tables-f (cadr loaded))))
                                    state))
               ; The F row's NEXT: the prefix's transaction bound the
               ; publication wrote (books/store-checkpoint-tables.lisp
               ; fn-sct-next-of-tables-is-bound-of-loaded-records, PRF-992);
               ; the open's fn-sfi-extend-open takes it, never a walk.
               (state (f-put-global 'fn-store-sco-next
                                    (fn-sct-tables-next (cadr loaded)) state)))
          (mv nil (list :ok (fn-sco-sequence checkpoint)) state fn-octets))
      (let* ((state (f-put-global 'fn-store-sco-checkpoint nil state))
             (state (f-put-global 'fn-store-sco-log-position nil state))
             (state (f-put-global 'fn-store-sco-next nil state)))
        (mv nil
            (list :refused (if (and (consp loaded) (consp (cdr loaded)))
                               (cadr loaded)
                             :malformed))
            state fn-octets))))))
