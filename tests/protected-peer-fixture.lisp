; The public peer tests begin with stored grants, then STARTTLS and AUTHINFO.
; Only the TLS transport is simulated. The owner runs the existing served
; authority protocol and each response is checked before the client connects.
(in-package "ACL2")
(include-book "authority-served")
(include-book "../books/owed-cursor")
(include-book "../books/node-profile")

(defun fn2-ppf-profile (profile)
  (declare (xargs :verify-guards nil))
  (fn2-node-profile-overlay
   '((:peering-interim . t) (:authority . 1) (:owner-account . 2)
     (:control-connections . 6) (:t . 6) (:p . 8) (:o . 64)
     (:identity-overlays . 64) (:identity-arena-bytes . 4096)
     (:tls-certificate . "fixture.pem") (:tls-key . "fixture.key") (:tls-handshakes . 1)
     (:pool-classes . ((8 . 1024) (128 . 4096) (64 . 65536))))
   (if (assoc-equal :groups profile) profile
     (put-assoc-equal :groups '(("local.test" . 1)) profile))))

(defconst *fn2-ppf-credential* "wire-fixture")

(defun fn2-ppf-owner-round (frame clients store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((cap (len clients))
       ((mv admitted fn2-core) (fn2-as-admit (list cap) fn2-core))
       ((unless (eq admitted :ok)) (mv admitted nil clients store fn2-core))
       (clients (append clients (list (fn2-as-client (list frame)))))
       ((mv status clients store fn2-core)
        (fn2-cw-loop 4000 0 (len clients) clients store fn2-core)))
    (mv status (car (nth cap (fn2-cw-results clients))) clients store fn2-core)))

(defun fn2-ppf-grants (rights group principal head op clients store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom rights) (mv :ok clients store fn2-core)
    (b* ((right (car rights))
         (role (equal right *fn2-authority-right-peer*))
         ((mv status wire clients store fn2-core)
          (fn2-ppf-owner-round
           (fn2-as-set principal right
                       (if role *fn2-authority-scope-principal* *fn2-authority-scope-stream*)
                       (if role 0 group) 1 head op)
           clients store fn2-core))
         ((mv grant next rest) (fnca-set-reply wire))
         ((unless (and (eq status :quiet) (posp grant) (equal grant next) (endp rest)))
          (mv (list :grant right status wire) clients store fn2-core)))
      (fn2-ppf-grants (cdr rights) group principal next (+ 1 (nfix op)) clients store fn2-core))))

(defun fn2-ppf-provision (role store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((principal *fn2-as-mini-id*)
       (name (fn2-as-o "mini"))
       ((mv group fn2-core) (fn2-as-group "local.test" fn2-core))
       ((unless (posp group)) (mv :group nil store fn2-core))
       ((mv made wire clients store fn2-core)
        (fn2-ppf-owner-round (fn2-as-frame 'principal-create (list name)) nil store fn2-core))
       ((unless (and (eq made :quiet)
                     (equal wire (fn2-as-accepted 'principal-create (list principal)))))
        (mv (list :create made wire) clients store fn2-core))
       ((mv password wire clients store fn2-core)
        (fn2-ppf-owner-round
         (fn2-as-frame 'principal-set-password
                       (list name (make-list 16 :initial-element 37) (fn2-as-o *fn2-ppf-credential*)))
         clients store fn2-core))
       ((unless (and (eq password :quiet)
                     (equal wire (fn2-as-accepted 'principal-set-password (list principal)))))
        (mv (list :password password wire) clients store fn2-core))
       (rights (list *fn2-authority-right-peer-accept* *fn2-authority-right-append* *fn2-authority-right-read*))
       (rights (if role (cons *fn2-authority-right-peer* rights) rights)))
    (fn2-ppf-grants rights group principal 0 1 clients store fn2-core)))

;; The owner prelude leaves the listener's real Accept posted with no TCP
;; client. Use that submitted descriptor once the test's client arrives.
(defun fn2-ppf-find-accept (n fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
  (if (zp n) (mv nil 0 0)
    (let ((op (- (nfix n) 1)))
      (if (and (equal (fn2-ops-phase op fn2-ops) *fn2-op-phase-submitted*)
               (equal (fn2-ops-kind op fn2-ops) *fn2-action-accept*))
          (mv t op (fn2-ops-gen op fn2-ops))
        (fn2-ppf-find-accept op fn2-ops)))))

(defun fn2-ppf-wire (profile seeds lines sizes role)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor (fn2-ppf-profile profile) :echo nil fn2-core))
           ((mv epoch fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents)
              (mv code fn2-core)))
           ((unless (eq epoch :ok)) (mv (list :epoch epoch) fn2-core))
           ((mv seeded store fn2-core) (fn2-cs-seed-rev seeds 1 nil fn2-core))
           ((unless (eq seeded :ok)) (mv (list :seed seeded) fn2-core))
           ((mv provisioned clients store fn2-core) (fn2-ppf-provision role store fn2-core))
           ((unless (eq provisioned :ok)) (mv (list :provision provisioned) fn2-core))
           ((mv found op gen)
            (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (found op gen)
              (fn2-ppf-find-accept (fn2-ops-rows fn2-ops) fn2-ops)
              (mv found op gen)))
           ((unless found) (mv '(:accept) fn2-core))
           (cap (len clients))
           (login (list "STARTTLS" "AUTHINFO USER mini"
                        (fn2-csp-cat (list "AUTHINFO PASS " *fn2-ppf-credential*))))
           (input (fn2-cw-crlf-octets (append login lines)))
           ;; Bound the first two receives to the TLS line and the login
           ;; commands, then apply each old operation fixture's chunk schedule.
           (chunks (append (list 10 :tls (- (len (fn2-cw-crlf-octets login)) 10)) sizes))
           (clients (append clients (list (list input chunks nil nil t))))
           (fn2-core (fn2-cw-post-accept op gen cap 77 t fn2-core))
           ((mv status clients & fn2-core)
            (fn2-cw-loop (+ 4800 (* 8 (len chunks))) 0 (len clients) clients store fn2-core)))
        (mv (list status (fn2-core-stop-reason fn2-core)
                  (nth cap (fn2-cw-results clients))) fn2-core))
      result)))

(defconst *fn2-ppf-login-lines*
  '("382 continue with TLS negotiation" "381 password required" "281 authentication accepted"))
