; Teeth for books/idle-collection (MEM-003, lane mem3-idle): the keystone
; fn-idle-gc-verdict-collects-only-when-owed at the profile's limits (3 quiet
; ticks, 512 KiB of activity, an 8 MiB floor, generation 6), the verdict
; withheld at each premise's boundary (a publication in flight, one tick short,
; one octet short), and one must-fail per premise of the keystone's conclusion.
(in-package "ACL2")
(include-book "../../books/idle-collection")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

; The limits the host asks with: the rows of books/profile-limits.lisp.
(assert! (equal *fn-idle-gc-quiet-ticks* 3))
(assert! (equal *fn-idle-gc-activity-octets* (* 512 1024)))
(assert! (equal *fn-idle-gc-floor-octets* (* 8192 1024)))
(assert! (equal *fn-idle-gc-generation* 6))

; Reachable :collect (the premise is inhabited): idle three ticks, nothing
; publishing, the floor allocated.
(assert! (equal (fn-idle-gc-decide 3 nil 8388608) '(:collect 6)))
(assert! (equal (fn-idle-gc-decide 10 nil 100000000) '(:collect 6)))

; A publication in flight yields :wait whatever the rest says.
(assert! (equal (fn-idle-gc-decide 3 t 8388608) :wait))
(assert! (equal (fn-idle-gc-decide 1000 t 1000000000) :wait))
; One tick short; one octet short; a count or a figure that is not a natural.
(assert! (equal (fn-idle-gc-decide 2 nil 8388608) :wait))
(assert! (equal (fn-idle-gc-decide 3 nil 8388607) :wait))
(assert! (equal (fn-idle-gc-decide nil nil 8388608) :wait))
(assert! (equal (fn-idle-gc-decide 3 nil -1) :wait))

; The conclusion of the keystone, checked at each of those inputs.
(defun idlec-conclusion (quiet publishingp consed)
  (declare (xargs :mode :program))
  (let ((v (fn-idle-gc-decide quiet publishingp consed)))
    (or (equal v :wait)
        (and (not publishingp)
             (natp quiet) (<= *fn-idle-gc-quiet-ticks* quiet)
             (natp consed) (<= *fn-idle-gc-floor-octets* consed)
             (equal v (list :collect *fn-idle-gc-generation*))))))
(assert! (and (idlec-conclusion 3 nil 8388608) (idlec-conclusion 3 t 8388608)
              (idlec-conclusion 2 nil 8388608) (idlec-conclusion 3 nil 8388607)
              (idlec-conclusion nil nil 8388608) (idlec-conclusion 3 nil -1)))

; The count: an active tick or a publication restarts it; a quiet one grows it.
(assert! (equal (fn-idle-gc-quiet 2 nil 0) 3))
(assert! (equal (fn-idle-gc-quiet 2 nil 524287) 3))
(assert! (equal (fn-idle-gc-quiet 2 nil 524288) 0))
(assert! (equal (fn-idle-gc-quiet 2 t 0) 0))
(assert! (equal (fn-idle-gc-quiet 2 nil nil) 0))
; A burst, then idle: the verdict follows the count from :wait to :collect on
; the third quiet tick, and a publication on the way restarts it.
(assert! (let* ((q (fn-idle-gc-quiet 0 nil 9000000))     ; the burst's last tick
                (q (fn-idle-gc-quiet q nil 1000))
                (q (fn-idle-gc-quiet q nil 1000)))
           (and (equal q 2) (equal (fn-idle-gc-decide q nil 40000000) :wait)
                (equal (fn-idle-gc-decide (fn-idle-gc-quiet q nil 1000) nil 40000000)
                       '(:collect 6)))))
(assert! (let* ((q (fn-idle-gc-quiet 2 t 1000)))
           (and (equal q 0) (equal (fn-idle-gc-decide (fn-idle-gc-quiet q nil 1000) nil 40000000)
                                   :wait))))

; The pages-releasing generation: above SBCL's small_generation_limit (1),
; within the pseudo-static bound.
(assert! (and (< 1 *fn-idle-gc-generation*) (<= *fn-idle-gc-generation* 6)))

; Premise removal.  Each premise of the conclusion, dropped, is a theorem ACL2
; refuses: the publication, the quiet count, the floor.
(must-fail-checked
 (defthm idlec-collects-without-the-publication-premise
   (implies (and (natp quiet) (natp quiet-limit) (<= quiet-limit quiet)
                 (natp consed-octets) (natp floor-octets) (<= floor-octets consed-octets))
            (equal (fn-idle-gc-verdict quiet-limit floor-octets generation
                                       quiet publishingp consed-octets)
                   (list :collect generation)))
   :hints (("Goal" :in-theory (enable fn-idle-gc-verdict)))))

(must-fail-checked
 (defthm idlec-collects-without-the-quiet-premise
   (implies (and (not publishingp)
                 (natp consed-octets) (natp floor-octets) (<= floor-octets consed-octets))
            (equal (fn-idle-gc-verdict quiet-limit floor-octets generation
                                       quiet publishingp consed-octets)
                   (list :collect generation)))
   :hints (("Goal" :in-theory (enable fn-idle-gc-verdict)))))

(must-fail-checked
 (defthm idlec-collects-without-the-floor-premise
   (implies (and (not publishingp)
                 (natp quiet) (natp quiet-limit) (<= quiet-limit quiet))
            (equal (fn-idle-gc-verdict quiet-limit floor-octets generation
                                       quiet publishingp consed-octets)
                   (list :collect generation)))
   :hints (("Goal" :in-theory (enable fn-idle-gc-verdict)))))
