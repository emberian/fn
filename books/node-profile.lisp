; The small native image profile, shared with restart and boot fixtures.
(in-package "ACL2")
(include-book "host-boundary")
(defconst *fn2-node-profile*
 (append '((:listener-targets . fn2-conn) (:groups . (("local.test" . 1)))
           (:posting-interim . t) (:reading . t) (:x . 2)
           (:identity-overlays . 64) (:identity-arena-bytes . 4096)
           (:large-upload-windows . 2) (:extent-slots . 128)
           (:o . 32) (:qa . 16) (:trace . nil)
           (:pool-classes . ((8 . 1024) (128 . 16384) (64 . 65536))))
         *fn2-profile-tiny*))
(assert-event (fn2-core-profilep *fn2-node-profile*))
(assert-event (fn2-core-profilep (fn2-image-profile *fn2-node-profile*)))
