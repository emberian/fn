; M2's node: the served core of tests/native-serve.lsp over the same seeded
; store, with the consumer port's local carrier L served beside NNTP. Started
; as `tools/acl2 < tests/native-consumer.lsp` with FN2_LISTENER_PORT,
; FN2_LISTENER_PATH (the owner-only Unix socket) and FN2_OWNER_UID (the uid
; whose connections on it are the owner's) in the environment; prints
; `LISTENING <port>` and `LISTENING-LOCAL <path>` as native-serve does. The
; profile is the surface sessions' (tests/seeded-store.lsp) with posting on
; (an NNTP POST is the port's append on carrier N), control connections and
; consumer request rows, and the listener's :local peers admitted into fn2-ctl
; (:listener-local-target) while TCP peers stay fn2-conn's. The scenario that
; drives it is tests/surface/fn2_consumer_socket.py.
(in-package "ACL2")
(ld "tests/seeded-store.lsp")
(defconst *fn2-nc-profile*
  (put-assoc-equal :listener-local-target 'fn2-ctl
   (put-assoc-equal :control-connections 2
    (put-assoc-equal :cns 4
     (put-assoc-equal :posting-interim t *fn2-ss-profile*)))))
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
:q
(load "host/ffi.lisp")
(load "host/adapter.lisp")
(load "host/native-serve-raw.lisp")
(setf *fn2-nserve-base* *fn2-nc-profile*)
(sb-ext:exit :code (fn2-nserve-main))
