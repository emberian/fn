; Served authority's port (layer E; docs/design/AUTHORITY-20261105.md section
; 3): four verbs on the owner's control socket. principal-create and
; principal-bind name durable principals (fn2-principals); grant-set and
; grant-get write and read the owner-issued grants (fn2-grants and its
; current/head folds). One carrier, L: FNCT request kind 29 (the opcode is the
; request code), replies in kind 30 (authority-codec.lisp). There is no R or N
; carrier: a remote login binds to the same principal ids through E2's
; credential verification, never through these verbs.
(in-package "ACL2")
(include-book "port")
(fn2-book-layer :e)

(defconst *fn2-authority-request-kind* 29)
(defconst *fn2-authority-reply-kind* 30)

(defport fn2-authority
  :fields ((name (:octets 64)) (grantee (:id principal)) (right (:enum fn2-authority-right (:consume :read :append)))
           (scope (:enum fn2-authority-scope (:own-consumers :stream))) (target (:id stream)) (enabled :bool)
           (expected-head (:id grant)) (op (:octets 64))
           (principal (:id principal)) (authority-head (:id grant)) (grant (:id grant)) (receipt :receipt)
           (found :bool) (grantor (:id principal)) (previous (:id grant)))
  :reasons (frame unknown-principal unknown-stream scope stale-revision operation-reused operation-expired)
  :verbs
  ;; Owner only; a repeated name answers its recorded identity (no deletion or reuse in this slice).
  ((principal-create :request (name) :result (principal)
                     :effect :durable :retry :idempotent :grant (:administer name) :meter (:requests :durable-octets)
                     :reasons (frame)
                     :spec "AUTHORITY-20261105.md 1, 3")
   ;; An unbound owner connection, once, before consumer work; connection state, not a mutation.
   (principal-bind :request (name) :result (principal authority-head)
                   :effect :read :retry :repeat :grant (:administer name) :meter (:requests)
                   :reasons (frame unknown-principal)
                   :spec "AUTHORITY-20261105.md 1, 3")
   ;; Owner only; the grantor is the connection's, never the payload's; OP is mandatory.
   (grant-set :request (grantee right scope target enabled expected-head op) :result (grant authority-head receipt)
              :effect :durable :retry :op :grant (:administer grantee) :meter (:requests :durable-octets)
              :reasons (frame unknown-principal unknown-stream scope stale-revision operation-reused operation-expired)
              :spec "AUTHORITY-20261105.md 2, 3")
   ;; The administrator, or the named grantee itself; found = 0 is a successful absent lookup.
   (grant-get :request (grantee right scope target) :result (found authority-head grant grantor enabled previous)
              :effect :read :retry :repeat :grant (:administer grantee) :meter (:requests)
              :reasons (frame unknown-principal unknown-stream scope)
              :spec "AUTHORITY-20261105.md 3")))

(defcarrier fn2-authority-local :port fn2-authority :frame :fnct
  :binds ((principal-create 29 0) (principal-bind 29 1) (grant-set 29 2) (grant-get 29 3)))
