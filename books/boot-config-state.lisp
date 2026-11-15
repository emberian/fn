; Actual ROOT boot configuration, with the physical reader geometry fields.
(in-package "ACL2")
(include-book "columns")
(include-book "profile")
(fn2-book-layer :b)
(defconst *fn2-boot-group-entry-bytes* (+ 250 8))
(defcolumns fn2-boot-config nil :init-name fn2-boot-config-empty
 :extra-fields
 ((fn2-boot-config-checkpoint-layout-ready :type (unsigned-byte 1) :initially 0 :why "Set only after checked bootstrap/empty anchor scan and the final startup fence.")
  (fn2-boot-config-geometry :type (array (unsigned-byte 8) (32)) :initially 0 :why "Owned bootstrap geometry hash; not checker scratch.")
  (fn2-boot-config-groups :type t :initially nil :why "Unconsumed trusted startup group configuration; one group per boot visit."
   :resident (* *fn2-boot-group-entry-bytes* (fn2-boot-config-count fn2-boot-config)))
  (fn2-boot-config-path :type t :initially nil :why "Trusted startup path identity, checked against the immutable image record."
   :resident *fn2-profile-path-identity-max*)
  (fn2-boot-config-count :type (unsigned-byte 32) :initially 0 :why "Number of immutable genesis group records.")
  (fn2-boot-config-extents :type (unsigned-byte 32) :initially 0 :why "The image's arena geometry, checked before recovery.")
  (fn2-boot-config-owner :type (unsigned-byte 32) :initially 0 :why "Persisted initial owner account binding.")
  (fn2-boot-config-recovery-assumptions :type (unsigned-byte 8) :initially 2 :why "Declared startup storage fault contract; never inferred from image bytes.")
  (fn2-boot-config-authority :type (unsigned-byte 1) :initially 0 :why "Whether genesis includes the principal directory.")))
