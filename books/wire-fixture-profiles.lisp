; Serving fixture geometry shared independently of keystone campaigns.
; These are the unchanged connection, posting and reading profiles.
(in-package "ACL2")
(include-book "profile")

(defconst *fn2-conn-wire-profile*
  (put-assoc-equal :listener-targets 'fn2-conn
    (put-assoc-equal :pool-classes '((8 . 1024) (4 . 256)) *fn2-profile-tiny*)))

(defconst *fn2-txn-posting-profile*
 (put-assoc-equal :groups '(("local.test" . 1))
  (put-assoc-equal :identity-overlays 64
   (put-assoc-equal :identity-arena-bytes 4096
     (put-assoc-equal :posting-interim t
       (put-assoc-equal :large-upload-windows 2
         (put-assoc-equal :pool-classes '((8 . 1024) (128 . 4096) (64 . 65536)) *fn2-conn-wire-profile*)))))))

(defconst *fn2-cursor-profile*
 (put-assoc-equal :groups '(("local.test" . 1) ("local.empty" . 2))
  (put-assoc-equal :identity-overlays 64
   (put-assoc-equal :large-upload-windows 1
    (put-assoc-equal :reading t
     (put-assoc-equal :x 2
      (put-assoc-equal :pool-classes '((8 . 1024) (128 . 4096) (64 . 65536)) *fn2-txn-posting-profile*)))))))
