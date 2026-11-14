; Canonical bootstrap encoding, independent of the boot machine.
(in-package "ACL2")
(include-book "layout")
(fn2-book-layer :b)

(deflayout fn2-boot-record
 '((magic :u32) (version :u8) (kind :u8) (index :varint)
   (image-size :varint) (extents :varint) (groups :varint)
   (lineage (:id lineage)) (domain (:id domain)) (incarnation (:id incarnation))
   (history (:id history)) (history-incarnation (:id incarnation))
   (owner :u32) (authority :u8) (identity (:octets 250))
   (value :varint) (epoch :varint) (previous :varint)))
(defconst *fn2-boot-magic* #x54423246)
(defconst *fn2-boot-unit* 4096)
(defconst *fn2-boot-hash-offset* 4064)

