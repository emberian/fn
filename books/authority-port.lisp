; Served authority's port (layer E; docs/design/AUTHORITY-20261105.md section
; 3): verbs on the owner's control socket. principal-create and
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
  :fields ((stream-name (:octets 250)) (name (:octets 64)) (grantee (:id principal)) (right (:enum fn2-authority-right (:consume :read :append :peer :peer-feed :peer-accept)))
           (scope (:enum fn2-authority-scope (:own-consumers :stream :principal))) (target (:id stream)) (enabled :bool)
           (expected-head (:id grant)) (op (:octets 64))
           (history (:id history)) (incarnation (:id incarnation)) (view (:id grant))
           (remote-stream (:octets 64)) (address :u32be) (port :u16be) (timeout-ms :u32be) (user (:octets 64))
           (consumer (:id consumer)) (attempt (:id attempt)) (generation (:id generation))
           (target-stream (:id stream)) (source-domain (:id domain)) (source-incarnation (:id incarnation))
           (source-revision (:id version)) (source-view (:id stream)) (source-view-version (:id version))
           (interpretation :u16be) (position :u64be) (chain :digest)
           (principal (:id principal)) (authority-head (:id grant)) (grant (:id grant)) (receipt :receipt)
           (salt (:octets 16)) (secret (:octets 512))
           (found :bool) (grantor (:id principal)) (previous (:id grant)))
  :reasons (frame unknown-principal unknown-stream scope stale-revision operation-reused operation-expired)
  :verbs
  ;; Owner only; a repeated name answers its recorded identity (no deletion or reuse in this slice).
  ((stream-resolve :request (stream-name) :result (target)
                   :effect :read :retry :repeat :grant (:administer stream-name) :meter (:requests)
                   :reasons (frame unknown-stream) :spec "AUTHORITY-20261105.md 3")
   (principal-create :request (name) :result (principal)
                     :effect :durable :retry :idempotent :grant (:administer name) :meter (:requests :durable-octets)
                     :reasons (frame)
                     :spec "AUTHORITY-20261105.md 1, 3")
   ;; An unbound owner connection, once, before consumer work; connection state, not a mutation.
   (principal-bind :request (name) :result (principal authority-head)
                   :effect :read :retry :repeat :grant (:administer name) :meter (:requests)
                   :reasons (frame unknown-principal)
                   :spec "AUTHORITY-20261105.md 1, 3")
   (principal-set-password :request (name salt secret) :result (principal)
                           :effect :durable :retry :idempotent :grant (:administer name)
                           :meter (:requests :durable-octets) :reasons (frame unknown-principal)
                           :spec "AUTHORITY-20261105.md 3; RELEASE-PLAN E2")
   (peer-pull :request (principal target consumer history incarnation view remote-stream address port timeout-ms user secret)
              :result (attempt generation)
              :effect :park :retry :repeat :grant (:administer principal) :meter (:requests)
              :reasons (frame unknown-principal unknown-stream scope)
              :spec "e-surface.md 13.4: start one receiver-owned pull; the receipt names its live attempt")
   (peer-position :request (principal consumer)
                  :result (found target-stream source-domain source-incarnation source-revision source-view source-view-version interpretation position chain)
                  :effect :read :retry :repeat :grant (:administer principal) :meter (:requests)
                  :reasons (frame scope) :spec "e-surface.md 13.4: read published receiver progress")
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
  :binds ((principal-create 29 0) (principal-bind 29 1) (grant-set 29 2) (grant-get 29 3) (stream-resolve 29 4) (principal-set-password 29 5) (peer-pull 29 6) (peer-position 29 7)))
