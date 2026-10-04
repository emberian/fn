;;; tools/runtime_floor/plain-node.lisp -- a native node WITHOUT ACL2 (lane
;;; runtime-floor, a prototype): bare SBCL + the export (the raw definitions
;;; ACL2 compiled, extract.lisp) + host/native/*.lisp unchanged, saved as one
;;; core.  Run from the source tree's root (host/native/build.lisp's working
;;; directory) with RF_FASL (the export's SBCL fasls), RF_OUT (the export),
;;; RF_HERE (this directory), RF_CORE (the core to write), FN_MLDSA_LIBRARY as
;;; build_native_host.sh sets it.  Never a release.
(setq *compile-verbose* nil *compile-print* nil)
(defvar *fasl* (sb-ext:posix-getenv "RF_FASL"))
(defvar *here* (sb-ext:posix-getenv "RF_HERE"))
(defvar *out* (sb-ext:posix-getenv "RF_OUT"))
(load (concatenate 'string *out* "00-packages.lisp"))
(dolist (f '("shim" "01-globals" "01-stobjs-in" "01-ftypes" "01-inline")) (load (concatenate 'string *fasl* f ".fasl")))
(dolist (p (sort (mapcar #'namestring (directory (concatenate 'string *fasl* "02-defs-*.fasl"))) #'string<)) (load p))
(dolist (f '("03-stobjs" "shim-post")) (load (concatenate 'string *fasl* f ".fasl")))
(load (concatenate 'string *here* "host-shim.lisp"))
;; ACL2's global compilation policy (acl2.lisp *acl2-optimize-form*): the
;; ACL2 image compiles host/native under it, so the plain node does too
(proclaim '(optimize (compilation-speed 0) (speed 3) (space 1) (safety 0)))
(defvar *host-files*
  '("crypto" "io" "extent" "tls" "signatures" "config" "feed-filename" "auth" "auth-admin"
    "immutable-publish" "admin" "owner" "mux" "feed-service" "pull-service" "control"
    "topic-local" "consumer-local" "hybrid-control" "operator" "heap" "signature-command"
    "peer-invite" "keys" "login-bindings" "tls-reload" "checkpoint" "workflow" "tcpcl" "bp"
    "bp-app" "bp-service" "bp-contact" "bp-obligation" "bp-node" "anchor"))
(with-compilation-unit ()
  (dolist (f *host-files*)
    (let ((src (format nil "host/native/~a.lisp" f)))
      ;; as host/native/build.lisp does: LOAD of the source (each form
      ;; compiled by SBCL's native compiler as it is evaluated)
      (load src))
    (cond ((string= f "crypto") (acl2::fnn-crypto-initialize))
          ((string= f "io") nil)
          ((string= f "tls") (acl2::fnn-tls-initialize))
          ((string= f "signatures") (acl2::fnn-hsig-initialize)))))
(acl2::fnn-select-image-profile)
(acl2::fnn-select-release-version)
(defun rf-node-main ()
  (load (concatenate 'string *fasl* "03-stobjs.fasl"))
  (acl2::fnn-native-startup (lambda ()
                              (acl2::fnn-crypto-startup)
                              (acl2::fnn-tls-reset)
                              (acl2::fnn-tls-initialize)
                              (acl2::fnn-hsig-reset)
                              (acl2::fnn-hsig-initialize)))
  (acl2::fnn-main))
(sb-ext:gc :full t)
(format t "~&PN built; dynamic usage ~,1f MiB~%" (/ (sb-kernel:dynamic-usage) 1048576.0))
(sb-ext:save-lisp-and-die (sb-ext:posix-getenv "RF_CORE") :toplevel #'rf-node-main :executable nil)
