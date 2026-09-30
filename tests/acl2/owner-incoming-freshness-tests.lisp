(in-package "ACL2")
(include-book "../../books/owner-incoming-freshness")

; Explicit synthetic canonical/owner installation for STATE boundary tests.
; Actual account/config producer interleavings run in the companion test root.
; The holder and its spent shared reservation are created by the real issuer.
(defun fn-iafst-setup (fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :verify-guards nil))
 (let* ((ns (make-list 40 :initial-element 8))
        (intent (make-list 32 :initial-element 19))
        (root '(:adopted-root :immutable-alias))
        (authority (list :authority 4 5 ns nil nil))
        (cp (list :consumer nil nil 5 nil nil authority))
        (files (fn-sf-make :ready 19 nil '(a b c d e) nil nil nil 0))
        (oc (list (list (list nil nil files)) (fn-cfg-make 9 nil)))
        (state (f-put-global 'fn-owner oc state))
        (state (f-put-global 'fn-owner-canonical-epoch 7 state))
        (state (f-put-global 'fn-owner-canonical-state
                            (list :ready 7 5 nil nil cp nil 0 0 nil) state))
        (state (f-put-global 'fn-owner-account-root-state (list :ready 7 ns 4 5 root) state))
        (state (f-put-global 'fn-owner-incoming-freshness nil state)))
  (mv-let (word token ledger row)
   (fn-ioh-admit '((100 100 100 100 100) (0 0 0 0 0) 0 nil (0 0 0 0 0)) nil '(1 0 0 0 1))
   (declare (ignore word))
   (mv-let (sealed row) (fn-ioh-seal row token)
    (declare (ignore sealed))
    (let* ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool))
           (fn-page-read-pool (update-fn-prp-incoming-slot (fn-ibc-carrier '(:input-backing 0 64) row) fn-page-read-pool))
           (context (list :incoming-context token 7 '(:original-submission) '(65) '(:binding)
                          nil '(:original-take-config) '(:parse) (list '(:original-submission) intent)))
           (state (f-put-global 'fn-owner-incoming-context context state)))
     (mv fn-page-read-pool state))))))

(defun fn-iafst-case (kind fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :verify-guards nil))
 (mv-let (fn-page-read-pool state) (fn-iafst-setup fn-page-read-pool state)
  (mv-let (captured fn-page-read-pool state) (fn-owner-incoming-authority-capture fn-page-read-pool state)
   (let* ((saved (fn-owner-incoming-freshness-state state))
          (ledger (fn-owner-page-read-ledger fn-page-read-pool))
          (state
           (cond
            ((eq kind :configuration)
             (f-put-global 'fn-owner (list (fn-owner-core state) (fn-cfg-make 10 nil)) state))
            ((eq kind :account)
             (let* ((c (fn-owner-canonical-state state))
                    (cp (fn-cp-nth 5 c)) (a (fn-cp-nth 6 cp))
                    (cp (update-nth 6 (update-nth 1 5 a) cp))
                    (state (f-put-global 'fn-owner-canonical-state (update-nth 5 cp c) state)))
              (f-put-global 'fn-owner-account-root-state
               (update-nth 3 5 (fn-owner-account-root-state state)) state)))
            ((eq kind :unavailable) (f-put-global 'fn-owner-account-root-state nil state))
            (t state)))
          (fn-page-read-pool
           (if (eq kind :holder)
               (update-fn-prp-incoming-slot
                (fn-ibc-carrier '(:input-backing 0 64) '((:incoming 99) :readonly (1 0 0 0 1))) fn-page-read-pool)
             fn-page-read-pool)))
    (mv-let (word fn-page-read-pool state) (fn-owner-incoming-authority-recheck fn-page-read-pool state)
     (let ((after (fn-owner-incoming-freshness-state state)))
      (mv-let (again fn-page-read-pool state) (fn-owner-incoming-authority-capture fn-page-read-pool state)
       (mv
        (and (eq captured :authority-captured)
             (eq again :freshness-pending)
             (equal (fn-cp-nth 2 ledger) 1)
             (equal ledger (fn-owner-page-read-ledger fn-page-read-pool))
             (equal (cddr after) (cddr saved))
             (equal after (fn-owner-incoming-freshness-state state))
             (case kind
              (:same (and (eq word :authority-current)
                          (equal (fn-cp-nth 5 saved) (fn-cfg-generation (fn-owner-config state)))
                          (equal (fn-cp-nth 7 saved) (fn-cp-nth 1 (fn-cp-nth 6 (fn-cp-nth 5 (fn-owner-canonical-state state)))))))
              (:configuration (and (eq word :recapture-required) (eq (fn-cp-nth 1 after) :stale-recapture)
                                   (not (equal (fn-cp-nth 5 saved) (fn-cfg-generation (fn-owner-config state))))))
              (:account (and (eq word :recapture-required) (eq (fn-cp-nth 1 after) :stale-recapture)
                             (not (equal (fn-cp-nth 7 saved) (fn-cp-nth 1 (fn-cp-nth 6 (fn-cp-nth 5 (fn-owner-canonical-state state))))))))
              (otherwise (and (eq word :authority-unavailable) (equal after saved)))))
        fn-page-read-pool state))))))))

(defun fn-iafst-local (kind state)
 (declare (xargs :stobjs state :verify-guards nil))
 (with-local-stobj fn-page-read-pool
  (mv-let (ok fn-page-read-pool state) (fn-iafst-case kind fn-page-read-pool state)
   (mv ok state))))

;@positive-witness fn-owner-incoming-recheck-current-matches-live-authority
;@positive-witness fn-owner-incoming-recapture-retains-original-roots
(make-event (mv-let (ok state) (fn-iafst-local :same state)
 (if ok (value '(value-triple :passed-current)) (er soft 'freshness "current failed"))))
;@hypothesis-removal fn-owner-incoming-recheck-current-matches-live-authority
(make-event (mv-let (ok state) (fn-iafst-local :configuration state)
 (if ok (value '(value-triple :passed-config-change)) (er soft 'freshness "config failed"))))
;@mutation-witness incoming-owner-account-publication-change
(make-event (mv-let (ok state) (fn-iafst-local :account state)
 (if ok (value '(value-triple :passed-account-change)) (er soft 'freshness "account failed"))))
;@mutation-witness incoming-owner-publication-unavailable
(make-event (mv-let (ok state) (fn-iafst-local :unavailable state)
 (if ok (value '(value-triple :passed-unavailable)) (er soft 'freshness "unavailable failed"))))
;@mutation-witness incoming-owner-holder-mismatch
(make-event (mv-let (ok state) (fn-iafst-local :holder state)
 (if ok (value '(value-triple :passed-holder-mismatch)) (er soft 'freshness "holder failed"))))

(assert-event
 (and (eq (getpropc 'fn-owner-incoming-authority-capture 'symbol-class nil (w state)) :common-lisp-compliant)
      (eq (getpropc 'fn-owner-incoming-authority-recheck 'symbol-class nil (w state)) :common-lisp-compliant)))
