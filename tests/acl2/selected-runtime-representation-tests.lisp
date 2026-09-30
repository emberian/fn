(in-package "ACL2")
(include-book "../../books/selected-runtime-representation")

(defthm fn-srrt-backed-positive
 (and (equal (fn-srr-observed-limits-status
              4611686018427387903 17592186044416 17592186044416) :compatible)
      (fn-srr-backing-span-domain-p
       32 64 96 128 4096 17592186044416 17592186044416)
      (fn-srr-span-scalars-fit-p 32 64 96 128 4096 4611686018427387903))
 :rule-classes nil)

(defthm fn-srrt-largest-dimension-backing
 (and (equal (fn-srr-observed-limits-status
              4611686018427387903 17592186044416 17592186044416) :compatible)
      (fn-srr-backing-span-domain-p
       0 17592186044415 17592186044415 17592186044415 17592186044415
       17592186044416 17592186044416)
      (fn-srr-span-scalars-fit-p
       0 17592186044415 17592186044415 17592186044415 17592186044415
       4611686018427387903))
 :rule-classes nil)

; Metadata mutation, not an assertion that the physical runtime changed.
(defthm fn-srrt-remove-compatible-metadata
 (and (fn-srr-backing-span-domain-p 0 1 1 1 1 2 2)
      (not (equal (fn-srr-observed-limits-status 0 2 2) :compatible))
      (not (fn-srr-span-scalars-fit-p 0 1 1 1 1 0)))
 :rule-classes nil)

; Corrupted endpoint relation, with retained exact metadata.
(defthm fn-srrt-remove-span-domain
 (and (equal (fn-srr-observed-limits-status
              4611686018427387903 17592186044416 17592186044416) :compatible)
      (not (fn-srr-backing-span-domain-p
            0 2 1 1 1 17592186044416 17592186044416))
      (not (fn-srr-span-scalars-fit-p 0 2 1 1 1 4611686018427387903)))
 :rule-classes nil)

(defthm fn-srrt-dimension-limit-is-strict
 (not (fn-srr-backing-span-domain-p
       0 0 0 0 17592186044416 17592186044416 17592186044416))
 :rule-classes nil)
