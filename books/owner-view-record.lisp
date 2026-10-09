;; fn: the owner's committed view record, its shape and its fields, in a book of
;; its own so a reader of a view outside the owner (books/consumer-remote-
;; visibility.lisp) reads it through these accessors and never by position:
;; R4 (the Message-ID trie's removal) shifted every field after VERDICTS,
;; and a positional reader kept reading the old places (lane b-teeth,
;; 2026-10-09: consumer-remote visibility read the keyring as the withdrawn
;; list and RAW as the withdrawal records).

(in-package "ACL2")
(include-book "acceptance-alloc") ; fn-ag-car, fn-ag-cdr

; -----------------------------------------------------------------------------
; The committed view record:
;   (version frontier archive verdicts buckets withdrawals raw withdrawn
;    keyring)
; ARCHIVE is the state the view serves: the acceptance state of its prefix
; with the withdrawn targets out of its article list (C3, D29,
; `fn-ctl-visible-state').  WITHDRAWALS are the records decided for the
; cancels among RAW, the acceptance archive's own article list, which the
; next refresh compares with the grown archive to extend the visible list
; incrementally (`fn-ctl-refresh-visible').

; WITHDRAWN is the list of RAW's articles the view does not serve, carried
; by `fn-ctl-refresh-withdrawn' (books/control-served.lisp) so a reader's
; `423 withdrawn', `430 withdrawn' and `HDR :fn-control' read it without
; walking RAW (control-c3e).
(defun fn-own-view-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 9)))
(defun fn-own-view-version (v)
  (declare (xargs :guard t))
  (mbe :logic (car v) :exec (fn-ag-car v)))
(defun fn-own-view-frontier (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr v)) :exec (fn-ag-car (fn-ag-cdr v))))
(defun fn-own-view-archive (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr v))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr v)))))
(defun fn-own-view-verdicts (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr v))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr v))))))
(defun fn-own-view-group-index (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr v))))))
(defun fn-own-view-withdrawals (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr v)))))))
(defun fn-own-view-raw (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                         (fn-ag-cdr v))))))))
(defun fn-own-view-withdrawn (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                         (fn-ag-cdr (fn-ag-cdr v)))))))))
; KEYRING is the Store's keyring snapshots (`fn-sn-keyring-snapshots') at
; the refresh that committed the view: the node's keyring view a reader of
; this view is told the current enrollment against (HDR :fn-enrollment,
; books/nntp-enrollment.lisp).  Pinned with the view, like the verdicts.
(defun fn-own-view-keyring (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
               (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr v))))))))))
(defun fn-own-view-make-visible
    (version frontier archive verdicts buckets withdrawals raw withdrawn
             keyring)
  (declare (xargs :guard t))
  (list version frontier archive verdicts buckets withdrawals raw
        withdrawn keyring))
(defun fn-own-view-make-group-indexed
    (version frontier archive verdicts buckets)
  (declare (xargs :guard t))
  (list version frontier archive verdicts buckets nil nil nil nil))
