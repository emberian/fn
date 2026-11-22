; Policy for one selected pair from a frozen XFNC view. END records every
; selected event. NEXT and its chain stop at the last pair in the page.
(in-package "ACL2")
(include-book "arms")
(fn2-book-layer :e)

(defun fn2-xfnc-page-pair-action (event requested end next stopped items max-items bytes max-bytes pair room)
 (declare (xargs :guard t))
 (cond
  ((not (and (posp event) (unsigned-byte-p 60 event)
             (unsigned-byte-p 60 requested) (unsigned-byte-p 60 end)
             (unsigned-byte-p 60 next) (<= next end) (< end event)
             (unsigned-byte-p 32 items) (unsigned-byte-p 32 max-items)
             (unsigned-byte-p 32 bytes) (unsigned-byte-p 32 max-bytes)
             (posp pair) (unsigned-byte-p 32 pair)
             (member-eq stopped '(:none :item-limit :octet-limit))))
   (mv :state stopped))
  ((<= event requested) (mv :prefix stopped))
  ; Ascending selected positions have passed a cursor the view never issued.
  ((< next requested) (mv :scope stopped))
  ((not (eq stopped :none)) (mv :frontier stopped))
  ((>= items max-items) (mv :frontier :item-limit))
  ((or (> (+ bytes pair) max-bytes) (not room)) (mv :frontier :octet-limit))
  (t (mv :include stopped))))

(defun fn2-xfnc-page-scan-verdict (requested end next)
 (declare (xargs :guard t))
 (cond ((not (and (unsigned-byte-p 60 requested) (unsigned-byte-p 60 end)
                  (unsigned-byte-p 60 next) (<= next end)))
        :state)
       ((< end requested) :beyond-frontier)
       ((< next requested) :scope)
       (t :ok)))
