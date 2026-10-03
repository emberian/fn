; Bounded logical-codec window extraction from the concrete private frame.
; Whole-frame semantic decoding remains the next continuation boundary.
(in-package "ACL2")
(include-book "octets-stobj")
(set-verify-guards-eagerness 0)
(defun fn-tcim-start (end)
 (declare (xargs :guard (natp end))) (if (< end 4096) 0 (- end 4096)))
(verify-guards fn-tcim-start)
(defun fn-tcim-copy (start end acc fn-octets)
 (declare (xargs :stobjs fn-octets :measure (nfix (- end start))
  :guard (and (natp start) (natp end) (<= start end) (<= end (fn-octets-len fn-octets)))
  :verify-guards nil))
 (if (or (not (natp start)) (not (natp end)) (<= end start)) acc
  (fn-tcim-copy start (1- end) (cons (fn-octets-get (1- end) fn-octets) acc) fn-octets)))
(verify-guards fn-tcim-copy)
(defun fn-tcim-turn (end acc fn-octets)
 (declare (xargs :stobjs fn-octets
  :guard (and (natp end) (<= end (fn-octets-len fn-octets))) :verify-guards nil))
 (let ((start (fn-tcim-start end)))
  (list start (fn-tcim-copy start end acc fn-octets))))
(verify-guards fn-tcim-turn)
(defthm fn-tcim-quantum
 (implies (natp end)
  (and (natp (fn-tcim-start end)) (<= (fn-tcim-start end) end)
       (<= (- end (fn-tcim-start end)) 4096))))

; Connect the actual descending concrete window to the logical octet slice.
(defthm fn-tcim-slice-last
 (implies (and (natp start) (natp end) (<= start end))
  (equal (fn-oct-slice-list start (+ 1 end) fn-octets)
   (append (fn-oct-slice-list start end fn-octets)
           (list (fn-octets-get end fn-octets)))))
 :hints (("Goal" :induct (fn-oct-slice-list start end fn-octets)
                  :in-theory (enable fn-oct-slice-list))))
(defthm fn-tcim-copy-is-slice
 (equal (fn-tcim-copy start end acc fn-octets)
         (append (fn-oct-slice-list start end fn-octets) acc))
 :hints (("Goal" :induct (fn-tcim-copy start end acc fn-octets)
                  :in-theory (enable fn-tcim-copy fn-oct-slice-list))
         ("Subgoal *1/2" :use ((:instance fn-tcim-slice-last (end (1- end)))))))
(defthm fn-tcim-turn-boundary
 (equal (fn-tcim-turn end acc fn-octets)
  (list (fn-tcim-start end)
   (append (fn-oct-slice-list (fn-tcim-start end) end fn-octets) acc)))
 :hints (("Goal" :in-theory (enable fn-tcim-turn))))
