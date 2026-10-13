; The one image-constructed target for the bounded first profile read.
; Count, pending I/O ticket, EOF and custody belong to the recovery controller.
; This object alone grants neither a read nor interpretation of its contents.
(in-package "ACL2")
(include-book "recovery-profile-envelope")

(defconst *fn-rpf-file-limit* (nth 5 (fn-recovery-profile-envelope)))

; Expand the actual grammar dimension into DEFSTOBJ's literal array type.
; The image builder retains this registered object, never a second vector
; that merely has the same length. There is no resize entry point.
(defmacro fn-rpf-define-buffer ()
  `(defstobj fn-recovery-profile-buffer
     (fn-rpf-bytes :type (array (unsigned-byte 8)
                               (,(nth 7 (fn-recovery-profile-envelope))))
                   :initially 0)
     :inline t))
(fn-rpf-define-buffer)

; Bounded bridge to the existing profile decoder. The caller invokes this
; only after its actual completed-read/EOF receipt, with N <= maxFile.
; The extra overflow probe is never part of the decoded prefix. All prefix
; allocation belongs in that caller's genuine operation source and demand.
(defun fn-rpf-prefix-from (i n fn-recovery-profile-buffer)
  (declare (xargs :stobjs fn-recovery-profile-buffer
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n *fn-rpf-file-limit*)
                              (<= n (fn-rpf-bytes-length
                                     fn-recovery-profile-buffer)))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      nil
    (cons (fn-rpf-bytesi i fn-recovery-profile-buffer)
          (fn-rpf-prefix-from (+ 1 i) n fn-recovery-profile-buffer))))

(defun fn-rpf-prefix (n fn-recovery-profile-buffer)
  (declare (xargs :stobjs fn-recovery-profile-buffer
                  :guard (and (natp n) (<= n *fn-rpf-file-limit*)
                              (<= n (fn-rpf-bytes-length
                                     fn-recovery-profile-buffer)))))
  (fn-rpf-prefix-from 0 n fn-recovery-profile-buffer))

; One representation boundary: the host-called prefix is exactly the logical
; array prefix, and the read-only signature returns no replacement buffer.
(encapsulate ()
 (local
  (defthm fn-rpf-car-of-nthcdr
    (equal (car (nthcdr i xs)) (nth i xs))
    :hints (("Goal" :induct (nthcdr i xs)
             :in-theory (enable nthcdr nth)))))
 (local
 (defthm fn-rpf-nthcdr-step
   (implies (natp i)
            (equal (nthcdr (+ 1 i) xs) (cdr (nthcdr i xs))))))
(local
 (defthm fn-rpf-prefix-from-is-slice
   (implies (and (natp i) (natp n) (<= i n))
            (equal (fn-rpf-prefix-from i n fn-recovery-profile-buffer)
                   (take (- n i)
                         (nthcdr i (nth 0 fn-recovery-profile-buffer)))))
   :hints (("Goal" :induct (fn-rpf-prefix-from i n fn-recovery-profile-buffer)
            :in-theory (e/d (fn-rpf-prefix-from fn-rpf-bytesi take)
                            (nth))))))
(defthm fn-rpf-prefix-is-logical-prefix
  (equal (fn-rpf-prefix n fn-recovery-profile-buffer)
         (take n (nth 0 fn-recovery-profile-buffer)))
  :hints (("Goal" :cases ((natp n))
           :use ((:instance fn-rpf-prefix-from-is-slice (i 0)))
           :in-theory (enable fn-rpf-prefix fn-rpf-prefix-from)))
  :rule-classes nil))
