; served-catalog-join-host-exec.lisp -- the executable twin of the store side
; of fn-sjh-okp (lane join-f2-2, 2026-09-29; PRF-302).
;
; fn-sjh-files-okp (books/served-catalog-join-host.lisp) is S (every row of
; the store's history a well-formed composite, its handles in the arena, no
; withdrawal) and LINK (the host's pending row is the store's in-flight row's
; catalog row, with that row's token and the catalog's count; none when the
; in-flight row loads none).  It is a defun-nx over the catalog's list; the
; twin below reads the same fields of the live stobjs (fn-cat-count for the
; catalog's length) so tests/acl2 can evaluate it on states the host reaches,
; and fn-sjh-files-okp-exec-is-files-okp says it is the predicate.

(in-package "ACL2")

(include-book "served-catalog-join-host")

(local (in-theory (disable (tau-system))))

(defun fn-sjh-inflight-exec (files)
  (declare (xargs :guard t :verify-guards nil))
  (let ((phase (fn-sf-phase files)))
    (cond ((fn-sf-record-phasep phase) (fn-sf-record-candidate files))
          ((equal phase :completing) (car (last (fn-sf-records files))))
          (t nil))))

(defun fn-sjh-files-linkp-exec (files pending fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (let* ((phase (fn-sf-phase files))
         (r (fn-sjh-inflight-exec files)))
    (and (implies (equal phase :completing)
                  (and (consp (fn-sf-records files))
                       (equal (fn-sf-completion files) (fn-sf-record-pair r))))
         (implies (fn-sf-record-phasep phase)
                  (and (fn-row-composite-okp r fn-arena)
                       (fn-rows-handles-inp (list r) fn-arena)
                       (fn-scj-rows-clearp (list r))))
         (if pending
             (and (or (fn-sf-record-phasep phase) (equal phase :completing))
                  (fn-pc-p pending)
                  (equal (fn-scj-load-h r) (fn-pc-held pending))
                  (equal (fn-pc-token pending)
                         (cons (nfix (cdr (fn-sf-record-pair r))) (fn-pc-expected pending)))
                  (equal (fn-pc-expected pending) (fn-cat-count fn-cat)))
           (not (fn-scj-load-h r))))))

(defun fn-sjh-files-okp-exec (files pending fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (and (fn-rows-composites-okp (fn-sf-records files) fn-arena)
       (fn-rows-handles-inp (fn-sf-records files) fn-arena)
       (fn-scj-rows-clearp (fn-sf-records files))
       (fn-sjh-files-linkp-exec files pending fn-arena fn-cat)))

; The twin is the predicate.
(defthm fn-sjh-files-okp-exec-is-files-okp
  (equal (fn-sjh-files-okp-exec files pending fn-arena fn-cat)
         (fn-sjh-files-okp files pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-files-okp-exec fn-sjh-files-okp
                                               fn-sjh-files-linkp-exec fn-sjh-files-linkp
                                               fn-sjh-inflight-exec fn-sjh-inflight
                                               fn-cat-count-is-len)
                                             (theory 'minimal-theory)))))
