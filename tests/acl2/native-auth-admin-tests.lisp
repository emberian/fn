; Executable cases and theorem teeth for native AUTHINFO administration.
(in-package "ACL2")
(include-book "../../books/native-auth-admin")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (equal (symbol-class 'fn-native-auth-admin-set-password (w state))
        :common-lisp-compliant))
(assert-event
 (equal (guard 'fn-native-auth-admin-set-password nil (w state)) *t*))
(assert-event
 (equal (symbol-class 'fn-native-auth-admin-list (w state))
        :common-lisp-compliant))

(defconst *fn-naa-test-name* (fn-record-string-octets "native-reader"))
(defconst *fn-naa-test-secret* (fn-record-string-octets "correct-horse"))
(defconst *fn-naa-test-other-secret* (fn-record-string-octets "wrong-horse"))
(defconst *fn-naa-test-salt*
  '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15))
(defconst *fn-naa-test-other-salt*
  '(16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31))

(defun fn-naa-test-argv (strings)
  (if (consp strings)
      (cons (fn-record-string-octets (car strings))
            (fn-naa-test-argv (cdr strings)))
    nil))

; The ACL2 argv subject emits the only raw-executable action shape.  Its
; set-password plan contains the public identity/options and no secret slot.
(defconst *fn-naa-test-set-plan*
  (fn-native-auth-admin-parse-argv
   (fn-naa-test-argv
    '("set-password" "native-reader" "--no-posting" "--principal"
      "0707070707070707070707070707070707070707070707070707070707070707"))))
(assert-event
 (equal (fn-native-auth-admin-plan-status *fn-naa-test-set-plan*) :accepted))
(assert-event
 (equal (fn-native-auth-admin-action-kind *fn-naa-test-set-plan*)
        :set-password))
(assert-event
 (equal (fn-native-auth-admin-plan-action *fn-naa-test-set-plan*)
        (list :set-password *fn-naa-test-name*
              (fn-record-string-octets
               "0707070707070707070707070707070707070707070707070707070707070707")
              t nil)))
(assert-event
 (equal (fn-native-auth-admin-plan-action
         (fn-native-auth-admin-parse-argv
          (fn-naa-test-argv '("list"))))
        '(:list)))
(assert-event
 (equal (fn-native-auth-admin-plan-reason
         (fn-native-auth-admin-parse-argv
          (fn-naa-test-argv '("set-password" "bad\"name"))))
        :name))
(assert-event
 (equal (fn-native-auth-admin-plan-reason
         (fn-native-auth-admin-parse-argv
          (fn-naa-test-argv '("set-password" "native-reader"
                              "--posting" "--no-posting"))))
        :options))

(defun fn-naa-test-prefix-atp (needle haystack)
  (if (consp needle)
      (and (consp haystack) (equal (car needle) (car haystack))
           (fn-naa-test-prefix-atp (cdr needle) (cdr haystack)))
    t))

(defun fn-naa-test-containsp (needle haystack)
  (if (consp haystack)
      (or (fn-naa-test-prefix-atp needle haystack)
          (fn-naa-test-containsp needle (cdr haystack)))
    (null needle)))

(defmacro fn-naa-test-set ()
  '(fn-native-auth-admin-set-password
    nil nil *fn-naa-test-name* *fn-naa-test-secret* *fn-naa-test-secret*
    *fn-naa-test-salt*
    nil nil t 128))

(assert-event (equal (fn-native-auth-admin-result-status (fn-naa-test-set))
                     :accepted))
(assert-event
 (not (fn-naa-test-containsp
       *fn-naa-test-secret*
       (fn-native-auth-admin-result-octets (fn-naa-test-set)))))

; The emitted bytes reopen through the exact startup parser.  Its one row has
; the existing auth-secret verifier, accepts the enrolled secret on concrete
; attached SHA-256 octets, and rejects a concrete different secret.
(defmacro fn-naa-test-reopened ()
  '(fn-native-auth-load
    (fn-native-auth-admin-result-octets (fn-naa-test-set)) t nil nil nil 128))
(defmacro fn-naa-test-credential ()
  '(car (fn-auth-config-creds
         (fn-native-auth-result-config (fn-naa-test-reopened)))))
(assert-event
 (equal (fn-native-auth-result-status (fn-naa-test-reopened)) :accepted))
(assert-event (equal (fn-auth-cred-name (fn-naa-test-credential))
                     *fn-naa-test-name*))
(assert-event
 (fn-authsec-checkp (fn-auth-cred-secret (fn-naa-test-credential))
                    *fn-naa-test-secret*))
(assert-event
 (not (fn-authsec-checkp (fn-auth-cred-secret (fn-naa-test-credential))
                         *fn-naa-test-other-secret*)))

; Default principal mapping is the legacy native/Python mapping, now owned by
; ACL2 rather than duplicated by an adapter.
(assert-event
 (equal (fn-auth-cred-principal (fn-naa-test-credential))
        (fn-digest-tagged *fn-native-auth-admin-local-principal-tag*
                          *fn-naa-test-name*)))

; Listing contains only public fields.  A distinct verifier produces the same
; bytes, a reachable witness for the keystone report theorem.
(defconst *fn-naa-test-principal* (make-list 32 :initial-element 7))
(defmacro fn-naa-test-cred-a ()
  '(fn-auth-make-cred *fn-naa-test-name* *fn-naa-test-principal*
                      (fn-authsec-enrol *fn-naa-test-salt*
                                        *fn-naa-test-secret*) t))
(defmacro fn-naa-test-cred-b ()
  '(fn-auth-make-cred *fn-naa-test-name* *fn-naa-test-principal*
                      (fn-authsec-enrol *fn-naa-test-other-salt*
                                        *fn-naa-test-other-secret*) t))
(assert-event
 (not (equal (fn-auth-cred-secret (fn-naa-test-cred-a))
             (fn-auth-cred-secret (fn-naa-test-cred-b)))))
(assert-event
 (equal (fn-native-auth-admin-public-report (list (fn-naa-test-cred-a)) nil)
        (fn-native-auth-admin-public-report (list (fn-naa-test-cred-b)) nil)))
(assert-event
 (equal (fn-native-auth-admin-result-report
         (fn-native-auth-admin-list
          (fn-native-auth-admin-result-octets (fn-naa-test-set)) t 128))
        (fn-native-auth-admin-public-report
         (list (fn-naa-test-credential)) nil)))

; The native writer retains the existing canonical writer's lexical table
; order even when the observed input file used another valid order.
(defconst *fn-naa-test-later-name* (fn-record-string-octets "z-reader"))
(defmacro fn-naa-test-later-cred ()
  '(fn-auth-make-cred *fn-naa-test-later-name* *fn-naa-test-principal*
                      (fn-authsec-enrol *fn-naa-test-salt*
                                        *fn-naa-test-secret*) nil))
(assert-event
 (equal (fn-native-auth-admin-sort-credentials
         (list (fn-naa-test-later-cred) (fn-naa-test-cred-a)))
        (list (fn-naa-test-cred-a) (fn-naa-test-later-cred))))

; Boundary refusals/faults remain distinct.
(assert-event
 (equal
  (fn-native-auth-admin-result-status
   (fn-native-auth-admin-set-password
    nil nil *fn-naa-test-name* *fn-naa-test-secret* *fn-naa-test-secret*
    '(0 1) nil nil t 128))
  :fault))
(assert-event
 (equal
  (fn-native-auth-admin-result-reason
   (fn-native-auth-admin-set-password
    nil nil *fn-naa-test-name* *fn-naa-test-secret* *fn-naa-test-other-secret*
    *fn-naa-test-salt* nil nil t 128))
  :secret-confirmation))
(assert-event
 (equal
  (fn-native-auth-admin-result-reason
   (fn-native-auth-admin-set-password
    nil nil '(34) *fn-naa-test-secret* *fn-naa-test-secret*
    *fn-naa-test-salt* nil nil t 128))
  :name))
(assert-event
 (equal
  (fn-native-auth-admin-result-reason
   (fn-native-auth-admin-set-password
    (append (fn-record-string-octets "[login.\"old\"]") (list 10)
            (fn-record-string-octets "secret = \"do-not-read\"") (list 10))
    t *fn-naa-test-name* *fn-naa-test-secret* *fn-naa-test-secret*
    *fn-naa-test-salt*
    nil nil t 128))
  :cleartext-credential))

; The host-called wrapper over the shared replacement machine reaches durable
; only after the final directory barrier.
(defconst *fn-naa-test-publish-prefix*
  '((:stage-result :ok) :replace-issued (:replace-result :ok)))
(defconst *fn-naa-test-publish-trace*
  (append *fn-naa-test-publish-prefix* '((:directory-result :ok))))
(assert-event
 (equal (fn-native-auth-admin-rp-trace
         (fn-native-auth-admin-rp-start) *fn-naa-test-publish-prefix*)
        :replace-visible))
(assert-event
 (equal (fn-native-auth-admin-rp-trace
         (fn-native-auth-admin-rp-start) *fn-naa-test-publish-trace*)
        :durable))
(assert-event
 (fn-native-auth-admin-rp-has-directory-okp
  *fn-naa-test-publish-trace*))
; Teeth for the theorem's hypothesis: without a durable trace the required
; directory event can be absent, so its conclusion is false.
(assert-event
 (not (fn-native-auth-admin-rp-has-directory-okp nil)))

(defconst *fn-naa-test-recovery-trace*
  '((:recovery-file-result :ok) (:recovery-directory-result :ok)))
(assert-event
 (equal (fn-native-auth-admin-rp-trace
         (fn-native-auth-admin-rp-recover-start t)
         *fn-naa-test-recovery-trace*)
        :recovered))
(assert-event
 (fn-native-auth-admin-rp-has-recovery-directory-okp
  *fn-naa-test-recovery-trace*))
(assert-event
 (not (fn-native-auth-admin-rp-has-recovery-directory-okp nil)))

; A restart never skips over a stage file that may have survived the prior
; process.  The fixed stage is removed and the containing directory is
; barriered before final-name recovery begins.  These events are also direct
; witnesses for the host-called recovery step.
(defconst *fn-naa-test-cleanup-prefix*
  '(:cleanup-issued (:cleanup-result :ok)))
(defconst *fn-naa-test-cleanup-trace*
  (append *fn-naa-test-cleanup-prefix*
          '((:cleanup-directory-result :ok))))
(assert-event
 (equal (fn-native-auth-admin-recovery-action
         (fn-native-auth-admin-recovery-start t t))
        :issue-cleanup))
(assert-event
 (equal (fn-native-auth-admin-recovery-trace
         (fn-native-auth-admin-recovery-start t t)
         *fn-naa-test-cleanup-prefix*)
        '(:cleanup-visible t)))
(assert-event
 (equal (fn-native-auth-admin-recovery-action
         (fn-native-auth-admin-recovery-trace
          (fn-native-auth-admin-recovery-start t t)
          *fn-naa-test-cleanup-prefix*))
        :cleanup-directory-barrier))
(assert-event
 (equal (fn-native-auth-admin-recovery-trace
         (fn-native-auth-admin-recovery-start t t)
         *fn-naa-test-cleanup-trace*)
        '(:replace-recovery :recover-file)))
(assert-event
 (fn-native-auth-admin-recovery-has-cleanup-directory-okp
  *fn-naa-test-cleanup-trace*))
(assert-event
 (equal (fn-native-auth-admin-recovery-trace
         (fn-native-auth-admin-recovery-start t t)
         (append *fn-naa-test-cleanup-trace*
                 '((:recovery-file-result :ok)
                   (:recovery-directory-result :ok))))
        '(:replace-recovery :recovered)))
(assert-event
 (equal (fn-native-auth-admin-recovery-outcome
         (fn-native-auth-admin-recovery-trace
          (fn-native-auth-admin-recovery-start t t)
          (append *fn-naa-test-cleanup-trace*
                  '((:recovery-file-result :ok)
                    (:recovery-directory-result :ok)))))
        :recovered))

; Without the cleanup-directory success, final recovery is unreachable.
(assert-event
 (not
  (equal (car (fn-native-auth-admin-recovery-trace
               (fn-native-auth-admin-recovery-start t t)
               *fn-naa-test-cleanup-prefix*))
         :replace-recovery)))
(assert-event
 (not (fn-native-auth-admin-recovery-has-cleanup-directory-okp
       *fn-naa-test-cleanup-prefix*)))

; When no stage survives, the same invocation begins directly with the
; observed final-name recovery state.  Missing final is still followed by the
; directory barrier before the empty registry can be accepted.
(assert-event
 (equal (fn-native-auth-admin-recovery-start nil nil)
        '(:replace-recovery :recover-directory)))
(assert-event
 (equal (fn-native-auth-admin-recovery-outcome
         (fn-native-auth-admin-recovery-step
          (fn-native-auth-admin-recovery-start nil nil)
          '(:recovery-directory-result :ok)))
        :recovered))

; D27, PRF-102: the writer refuses a new login exactly past the operator's
; max-credentials.  Over the one-credential file the witness above wrote, a
; second login is accepted under 2 and refused by name under 1; re-setting
; the existing login is not a new one and is accepted under 1.
; A macro, not a defconst: ACL2 ignores the SHA-256 attachment in a defconst.
(defmacro fn-naa-test-one () '(fn-native-auth-admin-result-octets (fn-naa-test-set)))
(defconst *fn-naa-test-other-name* (fn-record-string-octets "second-reader"))
(assert-event
 (equal (fn-native-auth-admin-result-status
         (fn-native-auth-admin-set-password
          (fn-naa-test-one) t *fn-naa-test-other-name* *fn-naa-test-secret*
          *fn-naa-test-secret* *fn-naa-test-salt* nil nil t 2))
        :accepted))
(assert-event
 (equal (fn-native-auth-admin-result-reason
         (fn-native-auth-admin-set-password
          (fn-naa-test-one) t *fn-naa-test-other-name* *fn-naa-test-secret*
          *fn-naa-test-secret* *fn-naa-test-salt* nil nil t 1))
        :too-many-credentials))
(assert-event
 (equal (fn-native-auth-admin-result-status
         (fn-native-auth-admin-set-password
          (fn-naa-test-one) t *fn-naa-test-name* *fn-naa-test-secret*
          *fn-naa-test-secret* *fn-naa-test-salt* nil nil t 1))
        :accepted))

; -----------------------------------------------------------------------------
; `principal bind' / `unbind' (books/login-binding.lisp's binding table).

(defconst *fn-naa-test-signing-hex*
  (fn-record-string-octets
   "0707070707070707070707070707070707070707070707070707070707070707"))
(assert-event
 (equal (fn-native-auth-admin-plan-action
         (fn-native-auth-admin-parse-argv
          (fn-naa-test-argv
           '("bind" "native-reader"
             "0707070707070707070707070707070707070707070707070707070707070707"))))
        (list :bind *fn-naa-test-name* *fn-naa-test-signing-hex*)))
(assert-event
 (equal (fn-native-auth-admin-plan-action
         (fn-native-auth-admin-parse-argv
          (fn-naa-test-argv '("unbind" "native-reader"))))
        (list :bind *fn-naa-test-name* nil)))
(assert-event
 (equal (fn-native-auth-admin-plan-reason
         (fn-native-auth-admin-parse-argv
          (fn-naa-test-argv '("bind" "native-reader" "07"))))
        :principal))
(assert-event
 (equal (fn-native-auth-admin-plan-reason
         (fn-native-auth-admin-parse-argv (fn-naa-test-argv '("bind"))))
        :bind-arguments))

(defmacro fn-naa-test-bound ()
  '(fn-native-auth-admin-bind
    (fn-native-auth-admin-result-octets (fn-naa-test-set)) t
    *fn-naa-test-name* *fn-naa-test-signing-hex* 128))
(assert-event (equal (fn-native-auth-admin-result-status (fn-naa-test-bound))
                     :accepted))
; The written file loads, with the same credential and one binding.
(assert-event
 (equal (fn-native-auth-load-bindings
         (fn-native-auth-admin-result-octets (fn-naa-test-bound)) t 128)
        (list (cons *fn-naa-test-name* *fn-naa-test-principal*))))
(assert-event
 (equal (fn-native-auth-result-status
         (fn-native-auth-load
          (fn-native-auth-admin-result-octets (fn-naa-test-bound)) t nil nil nil 128))
        :accepted))
(assert-event
 (null (fn-native-auth-load-bindings
        (fn-native-auth-admin-result-octets (fn-naa-test-set)) t 128)))
; A password change keeps the binding; unbind removes it.
(assert-event
 (equal (fn-native-auth-load-bindings
         (fn-native-auth-admin-result-octets
          (fn-native-auth-admin-set-password
           (fn-native-auth-admin-result-octets (fn-naa-test-bound)) t
           *fn-naa-test-name* *fn-naa-test-other-secret*
           *fn-naa-test-other-secret* *fn-naa-test-other-salt* nil nil t 128))
         t 128)
        (list (cons *fn-naa-test-name* *fn-naa-test-principal*))))
(assert-event
 (null (fn-native-auth-load-bindings
        (fn-native-auth-admin-result-octets
         (fn-native-auth-admin-bind
          (fn-native-auth-admin-result-octets (fn-naa-test-bound)) t
          *fn-naa-test-name* nil 128))
        t 128)))
; The listing names the binding.
(assert-event
 (equal (fn-native-auth-admin-result-report
         (fn-native-auth-admin-list
          (fn-native-auth-admin-result-octets (fn-naa-test-bound)) t 128))
        (fn-native-auth-admin-public-report
         (list (fn-naa-test-credential))
         (list (cons *fn-naa-test-name* *fn-naa-test-principal*)))))
; Refusals: an unenrolled login, a malformed principal.
(assert-event
 (equal (fn-native-auth-admin-result-reason
         (fn-native-auth-admin-bind
          (fn-native-auth-admin-result-octets (fn-naa-test-set)) t
          (fn-record-string-octets "nobody") *fn-naa-test-signing-hex* 128))
        :unknown-login))
(assert-event
 (equal (fn-native-auth-admin-result-reason
         (fn-native-auth-admin-bind
          (fn-native-auth-admin-result-octets (fn-naa-test-set)) t
          *fn-naa-test-name* (fn-record-string-octets "07") 128))
        :principal))
; A malformed signing field refuses the whole profile, never ignored.
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (append (fn-native-auth-admin-result-octets (fn-naa-test-set))
                  (fn-record-string-octets "signing = \"07\""))
          t nil nil nil 128))
        :credential-shape))

; When a durable credential change reaches service (PKT-102, PKT-221):
; fn-native-auth-admin-effect-word, which host/native/auth-admin.lisp
; fnn-native-auth-admin-result-code calls with the writer-lock observation
; and the owner's answer to the binding reload.

(assert-event (equal (fn-native-auth-admin-effect-word :held nil) :restart-required))
(assert-event (equal (fn-native-auth-admin-effect-word :held :refused) :restart-required))
(assert-event (equal (fn-native-auth-admin-effect-word :held :accepted) :applied))
(assert-event (equal (fn-native-auth-admin-effect-word :held :uncertain) :uncertain))
(assert-event (equal (fn-native-auth-admin-effect-word :free nil) :effective-at-next-start))
(assert-event (equal (fn-native-auth-admin-effect-word :absent :accepted) :effective-at-next-start))
(assert-event (equal (fn-native-auth-admin-effect-word :unknown nil) :restart-required))
(assert-event (equal (fn-native-auth-admin-effect-word nil nil) :restart-required))
; Teeth: "never restart-required" and "always restart-required" (the answer
; the spike saw) are both false.
(must-fail
 (defthm naat-effect-word-always-restart
   (equal (fn-native-auth-admin-effect-word observation live) :restart-required)))
(must-fail
 (defthm naat-effect-word-never-restart
   (not (equal (fn-native-auth-admin-effect-word observation live) :restart-required))))
; Teeth for the `applied' keystone: each literal of its right side is needed.
; Without the owner's :accepted, a held lock is not `applied'; with it, a
; lock seen free is still `effective-at-next-start'.
(must-fail
 (defthm naat-effect-word-applied-without-acceptance
   (implies (not (member-equal observation '(:free :absent)))
            (equal (fn-native-auth-admin-effect-word observation live) :applied))))
(must-fail
 (defthm naat-effect-word-applied-whenever-accepted
   (implies (equal live :accepted)
            (equal (fn-native-auth-admin-effect-word observation live) :applied))))
