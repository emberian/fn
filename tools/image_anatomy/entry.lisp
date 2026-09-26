; tools/image_anatomy/entry.lisp -- an EXPERIMENTAL raw entry (lane
; image-anatomy): start the node without ACL2's read-eval-print loop.  It
; replaces sbcl-restart (which the image script's --eval calls) with the part
; of LP and ld-fn the node's dynamic extent relies on: ACL2's restart, an
; unwind-protect frame, *ld-level* 1 (so a guard violation throws to
; raw-ev-fncall, which fnn-call catches, as inside ld), ACL2's readtable,
; standard channels, and the local-top-level catch.  No LP, no ld, no
; translate of the :return-from-lp form.  Never a release.
(in-package "ACL2")
(defun sbcl-restart ()
  (acl2-default-restart)
  (setq *lp-ever-entered-p* t)
  (setq *read-default-float-format* 'double-float)
  (setup-standard-io)
  (push nil *acl2-unwind-protect-stack*)
  (let ((*ld-level* 1) (*readtable* *acl2-readtable*))
    (f-put-global 'ld-level 1 *the-live-state*)
    (catch 'local-top-level (fn-native-entry *the-live-state*)))
  (sb-ext:exit :code 1 :abort t))
