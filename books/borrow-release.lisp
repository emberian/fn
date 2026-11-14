; Shared output-loan terminal classification, below core and its proof model.
(in-package "ACL2")
(include-book "vocab")

; All terminal loan reclamation uses the action's declared range direction.
; Send may defer reclamation to its separate BorrowReleased cell. Every
; other output action, including upgrades, releases on its terminal event.
(defun fn2-terminal-releases-borrow-p (kind event aux0 release-posted release-harvested)
 (declare (xargs :guard t))
 (or (equal event *fn2-event-borrow-released*)
     (and (equal release-posted 0) (equal release-harvested 0)
          (fn2-op-output-kindp kind) (equal event (fn2-terminal-event kind))
          (or (not (equal kind *fn2-action-send*)) (equal aux0 0)))))

