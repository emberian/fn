; Narrow actual Store prefix for PRF-1118. The source trace fixture through
; enrollment and signed acceptance is reproduced verbatim; later unrelated
; legacy replay assertions remain in store-identity-traces-tests.
(in-package "ACL2")

(include-book "../../books/store-observed")

(include-book "../../books/codec-attach")

(include-book "../../books/crypto-attach")

(include-book "../../books/hybrid-store")

(include-book "held-rows-tests")

(defconst *sit-groups* '("example"))

(defconst *sit-principal* (make-list 32 :initial-element 7))

(defconst *sit-ed-key* (make-list 32 :initial-element 11))

(defconst *sit-ml-key* (make-list 1952 :initial-element 13))

(defconst *sit-keys* (list (cons :ed25519 *sit-ed-key*)
                           (cons :ml-dsa-65 *sit-ml-key*)))

(defconst *sit-signatures*
  (list (cons :ed25519 (make-list 64 :initial-element 17))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))

(defconst *sit-source* '(65 13 10))

(make-event `(defconst *sit-snapshot* ',(fn-hsig-keyring-snapshot *sit-principal* *sit-keys*)))

(defun fn-sit-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))

(defun fn-sit-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))

(defun fn-sit-barriers (s n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) s
    (fn-sit-barriers (fn-sn-io s :recovery-barrier :ok) (1- n))))

(defun fn-sit-commit-identity (s event)
  (fn-sn-finish (fn-sit-publish (fn-sn-prepare-identity
                                 (fn-sit-reserve s) event))))

(defun fn-sit-commit-legacy (s record)
  (fn-sn-finish (fn-sit-publish (fn-sn-prepare
                                 (fn-sit-reserve s) record))))

(defun fn-sit-commit-retention (s event)
  (fn-sn-finish (fn-sit-publish (fn-sn-prepare-retention
                                 (fn-sit-reserve s) event))))

(make-event `(defconst *sit-enrollment* ',(fn-hsig-keyring-event 0 0 0 1 *sit-principal* *sit-keys*)))

(make-event `(defconst *sit-after-enrollment* ',(fn-sit-commit-identity (fn-sn-initial *sit-groups* 32)
                          *sit-enrollment*)))

(assert-event (equal (fn-sf-phase (fn-sn-files *sit-after-enrollment*)) :ready))

(assert-event (equal (fn-sn-keyring-snapshots *sit-after-enrollment*)
                     (list *sit-enrollment*)))

(make-event `(defconst *sit-signed-record* ',(fn-record-make 1 1 1 "<signed@example.invalid>" *sit-source* *sit-groups*
                  "signed-obligation" "signed-subject" "signed-release" 3 841000000)))

(make-event `(defconst *sit-composite-wire* ',(fn-hsig-authorized-article-event
   1 1 1 1 *sit-snapshot* "<signed@example.invalid>"
   (fn-record-string-octets "signed-subject")
   (fn-record-encode-impl *sit-signed-record*)
   *sit-principal* *sit-keys* *sit-source* *sit-signatures* *sit-ml-key*
   :verified :verified)))

(make-event `(defconst *sit-composite* ',(fn-hrt-row-after (list *sit-enrollment*) *sit-composite-wire* nil 0)))

(assert-event (fn-hstxa-p *sit-composite*))

(assert-event (equal (fn-hstxa-stxa *sit-composite*) *sit-composite-wire*))

(defconst *sit-wire-prefix* (list *sit-enrollment* *sit-composite-wire*))

(make-event `(defconst *sit-after-composite* ',(fn-sit-commit-identity *sit-after-enrollment* *sit-composite*)))
