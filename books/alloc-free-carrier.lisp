; Carrier contracts for the canonical allocator mutation. No release decision,
; row mutation, accounting formula, or guard is defined again here.
(in-package "ACL2")
(include-book "alloc")
(fn2-book-layer :b)

; ACCOUNT changes only scalar accounting fields, after its own checked ranges.
; Its actual operation domain includes a valid extent, as its guard states.
(fn2-extents-preserves fn2-alloc-account (i old-state old-reason fn2-extents)
 :position nil :disable t :wfp-type t :raw-rows t
 :hyps ((fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
        (fn2-alloc-slotp i fn2-extents))
 :hints (("Goal" :in-theory (disable fn2-extentsp fn2-extents-wfp))))

; Original UNLINK already exports TYPE/WFP/ROWS. The raw observation bridges
; callers whose concrete ROWS getter was expanded before this opaque call.
(defthm fn2-alloc-unlink-raw-rows
 (equal (nth *fn2-extents-rows* (fn2-alloc-unlink i fn2-extents))
        (nth *fn2-extents-rows* fn2-extents))
 :hints (("Goal" :use ((:instance fn2-alloc-unlink-rows (p fn2-extents))))))
(defthm fn2-alloc-unlink-raw-free-head
 (equal (nth *fn2-alloc-free-head* (fn2-alloc-unlink i fn2-extents))
        (nth *fn2-alloc-free-head* fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-unlink))))
; Carry the original guarded output facts at the actual intermediate call,
; before composing typed row setters and ACCOUNT's input-domain consumer.
(defthm fn2-alloc-unlink-output-carrier
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
               (fn2-alloc-slotp i fn2-extents))
  (and (fn2-extentsp (fn2-alloc-unlink i fn2-extents))
       (fn2-extents-wfp (fn2-alloc-unlink i fn2-extents))
       (fn2-alloc-slotp i (fn2-alloc-unlink i fn2-extents))))
 :hints (("Goal" :in-theory (disable fn2-alloc-unlink fn2-extentsp fn2-extents-wfp)
          :use ((:instance fn2-alloc-unlink-type (p fn2-extents))
                (:instance fn2-alloc-unlink-wfp (p fn2-extents))
                (:instance fn2-alloc-unlink-rows (p fn2-extents)))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn2-alloc-unlink i fn2-extents)))))
(in-theory (disable fn2-alloc-unlink))

; These predicates concern only the concrete carrier, not persisted release
; authority or the allocator's semantic invariant. The actual guarded FREE
; function remains the single mutation used by ordinary and indexed callers.
(fn2-extents-preserves fn2-alloc-free (i fn2-extents)
 :position nil :disable t :wfp-type t :raw-rows t
 :hyps ((fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
        (fn2-alloc-slotp i fn2-extents))
 :hints (("Goal" :in-theory (disable fn2-extentsp fn2-extents-wfp))))
