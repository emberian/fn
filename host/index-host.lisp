; Trusted experimental adapter for the generation-bound index cache (C1-09).
;
; This file holds no enumeration logic.  Every answer it returns comes from
; FN-NNTP-INDEX-CACHE-QUERY (books/nntp-index.lisp), whose :OK answers are
; proved equal to the books/nntp.lisp folds by
; FN-NNTP-INDEX-CACHE-OPEN-ANSWERS-GROUP, -CURSOR and -RANGE.  The host
; chooses when to build and when to ask; it never computes a count, a
; watermark, a cursor step or a range list itself.
;
; Three globals:
;   FN-INDEX-DIGEST  the configuration digest of the archive the reader last
;                    selected.  Set once per selection/recovery by
;                    FN-INDEX-HOST-OBSERVE, never per command.
;   FN-INDEX-CACHE   the built index, tagged with the generation and the
;                    digest it was built from.
;   FN-INDEX-STATUS / FN-INDEX-VALUE  the last answer, split so the Python
;                    boundary reads a symbol and a value, never a parse.
(in-package "ACL2")
(include-book "../books/nntp-index")

(defun fn-index-host-archive (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-reader-archive state)
      (f-get-global 'fn-reader-archive state)
    nil))

; Called once per selection/recovery, alongside FN-READER-USE-STORE.  This is
; the one place the archive configuration is read; the served path below
; compares the recorded digest and never rescans the archive.
(defun fn-index-host-observe (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((archive (fn-index-host-archive state)))
    (if (fn-statep archive)
        (let ((state (f-put-global 'fn-index-digest
                                   (fn-nntp-index-config-digest archive) state)))
          (value :observed))
      (let ((state (f-put-global 'fn-index-digest :none state)))
        (value :refused)))))

; Build the index over the selected archive's committed articles, tagged with
; GENERATION (the store's durable record count at the recovery that produced
; this archive) and the archive's configuration digest.
(defun fn-index-host-open (generation state)
  (declare (xargs :stobjs state :mode :program))
  (let ((archive (fn-index-host-archive state)))
    (if (and (natp generation) (fn-statep archive))
        (let ((state (f-put-global 'fn-index-cache
                                   (fn-nntp-index-cache-open generation archive)
                                   state)))
          (value :ready))
      (let ((state (f-put-global 'fn-index-cache nil state)))
        (value :refused)))))

(defun fn-index-host-install (answer state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-index-status (car answer) state))
         (state (f-put-global 'fn-index-value (cdr answer) state)))
    (value (car answer))))

; The served path.  KIND is :COUNT, :LOW, :HIGH (GROUP), :RANGE (LISTGROUP) or
; :NEXT / :LAST (the cursor commands).  GENERATION is what the caller observed
; on the store for this command.  The answer is :OK with the value, :STALE
; when the caller's generation or the last observed configuration is not the
; one the cache was built for, or :UNKNOWN for a kind this cache does not
; answer.  There is no fourth outcome, and in particular no stale answer.
(defun fn-index-host-query (generation kind group low high current state)
  (declare (xargs :stobjs state :mode :program))
  (let ((cache (if (boundp-global 'fn-index-cache state)
                   (f-get-global 'fn-index-cache state)
                 nil))
        (digest (if (boundp-global 'fn-index-digest state)
                    (f-get-global 'fn-index-digest state)
                  :none)))
    (fn-index-host-install
     (fn-nntp-index-cache-query cache generation digest
                                kind group low high current)
     state)))

; The fold arm.  This is the oracle and the measurement baseline: the
; books/nntp.lisp enumeration run directly over the selected archive, with no
; index.  It is not a served path; FN-INDEX-HOST-QUERY is.
(defun fn-index-host-fold (kind group low high current state)
  (declare (xargs :stobjs state :mode :program))
  (let ((articles (fn-state-articles (fn-index-host-archive state))))
    (fn-index-host-install
     (cond ((equal kind :count)
            (cons :ok (fn-nntp-group-count group articles)))
           ((equal kind :low)
            (cons :ok (fn-nntp-group-low group articles)))
           ((equal kind :high)
            (cons :ok (fn-nntp-group-high group articles)))
           ((equal kind :next)
            (cons :ok (fn-nntp-group-next-number group current articles)))
           ((equal kind :last)
            (cons :ok (fn-nntp-group-last-number group current articles)))
           ((equal kind :range)
            (cons :ok (fn-nntp-group-range-numbers group low high articles)))
           (t (list :unknown)))
     state)))
