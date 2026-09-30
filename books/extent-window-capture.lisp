; Concrete overlap copy selected by the protected-extent controller.
(in-package "ACL2")
(include-book "extent-window-plan")
(include-book "extent-window-buffer")

(defun fn-ewb-capture (s fn-octets fn-ew-buffer)
  (declare (xargs :stobjs (fn-octets fn-ew-buffer)
                  :guard (and (true-listp s) (natp (nth 5 s))
                              (<= (nth 5 s) 16384)
                              (<= (fn-ewp-demand s) (fn-octets-len fn-octets)))
                  :guard-hints (("Goal"
                    :use (fn-ewp-window-span-bounds fn-ewp-demand-bounded)
                    :in-theory (disable fn-ewp-window-span fn-ewb-copy)))))
  (let ((span (fn-ewp-window-span s)))
    (fn-ewb-copy (car span) (cadr span) (caddr span) fn-octets fn-ew-buffer)))

; The named representation boundary for the actual requested-window copy.
; All unchanged cells are part of the conclusion. The scan input is the
; bounded private block, not a logical list constructed from the extent.
(defthm fn-ewb-capture-exact-output-and-effects
  (implies (natp j)
           (let ((span (fn-ewp-window-span s)))
             (equal (nth j (nth 0 (fn-ewb-capture s fn-octets fn-ew-buffer)))
                    (if (and (<= (caddr span) j)
                             (< j (+ (caddr span) (cadr span))))
                        (nth (+ (car span) (- j (caddr span))) fn-octets)
                      (nth j (nth 0 fn-ew-buffer))))))
  :hints (("Goal" :use (fn-ewp-window-span-bounds
                 (:instance fn-ewb-copy-exact-output-and-effects
                   (src (car (fn-ewp-window-span s)))
                   (count (cadr (fn-ewp-window-span s)))
                   (dst (caddr (fn-ewp-window-span s)))))
           :in-theory (disable fn-ewp-window-span nth nfix))))

(in-theory (disable fn-ewb-capture))
