; Whole-domain controls for the actual authorization operation. Requests and
; connections are genuinely admitted; stale references are explicit mutations,
; not a claim that this fixture executes a complete wire close/reopen trace.
(in-package "ACL2")
(include-book "../books/authority-incarnation")
(include-book "core-snapshot-support")

(defconst *fn2-auth-incarnation-profile*
  (put-assoc-equal :cns 2
   (put-assoc-equal :authority 1
    (put-assoc-equal :t 4
     (put-assoc-equal :owner-account 2
      (put-assoc-equal :pool-classes '((16 . 64) (4 . 256) (4 . 4096))
                      *fn2-profile-tiny*))))))

(defun fn2-auth-incarnation-run (mutation fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((profile (if (eq mutation :off-ctl)
                    (put-assoc-equal :authority 0 *fn2-auth-incarnation-profile*)
                  *fn2-auth-incarnation-profile*))
       (fn2-core (fn2-core-init profile fn2-core))
       ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl 0 77 3 0 fn2-core))
       ((unless (eq acode :ok)) (mv (list :admit acode) fn2-core))
       (ctl (fn2-machine-kind-base *fn2-ctl-kind* fn2-core))
       (cg (fn2-machine-generation ctl fn2-core))
       (fn2-core (fn2-ctl-put-core ctl (principal 17) (admin 1)))
       ((mv tcode cns gen fn2-core)
        (fn2-machine-take-fn2-cns *fn2-none* ctl cg 1 0 1 15
                                 (fn2-ctl-row-rx-slot ctl fn2-core)
                                 (fn2-ctl-row-rx-gen ctl fn2-core) fn2-core))
       ((unless (eq tcode :ok)) (mv (list :take tcode) fn2-core))
       ; Both references are well-typed but name a different incarnation.
       (fn2-core (if (member-eq mutation '(:ctl :off-ctl))
                     (fn2-cns-put-core cns (ctl-gen (+ 1 cg))) fn2-core))
       (asked-gen (if (eq mutation :request) (+ 1 gen) gen))
       (whole (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                   (fn2-auth-served fn2-core)
                   (eq (fn2-cns-snapshot-read-code cns fn2-core) :ok)
                   (eq (fn2-ctl-snapshot-read-code ctl fn2-core) :ok)
                   (fn2-cns-admin-p cns fn2-core)))
       (current (fn2-cns-binding-currentp cns asked-gen fn2-core))
       ((mv pcode pid) (fn2-cns-principal cns asked-gen fn2-core))
       (principal (list pcode pid))
       (before (fn2-test-core-snapshot fn2-core))
       ((mv code step head grant fn2-core)
        (fn2-cns-authority-allows cns asked-gen 0 0 0 4 37 41 8 fn2-core)))
    (mv (list whole current principal code step head grant
              (equal (fn2-test-core-snapshot fn2-core) before)) fn2-core)))

(defun fn2-auth-incarnation-test (mutation)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core) (fn2-auth-incarnation-run mutation fn2-core) answer)))

; Full-premise witnesses at both independently stale incarnation references.
(defun fn2-cns-authority-stale-binding-positive ()
  (declare (xargs :verify-guards nil))
  (and (equal (fn2-auth-incarnation-test :ctl) '(t nil (:state 0) :state 0 0 0 t))
       (equal (fn2-auth-incarnation-test :request) '(t nil (:state 0) :state 0 0 0 t))))
; Dropping stale binding admits the current administrator. Dropping served
; authority admits even the stale reference through the explicit profile bypass.
(defun fn2-cns-authority-stale-binding-removed ()
  (declare (xargs :verify-guards nil))
  (and (equal (fn2-auth-incarnation-test nil) '(t t (:ok 17) :ok 0 0 0 t))
       (equal (fn2-auth-incarnation-test :off-ctl) '(nil nil (:state 0) :ok 0 0 0 t))))
(assert-event (fn2-cns-authority-stale-binding-positive))
(assert-event (fn2-cns-authority-stale-binding-removed))
