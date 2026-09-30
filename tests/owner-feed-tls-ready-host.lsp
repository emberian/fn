; PKT-599(b): execute the actual host entry on a reachable TLS phase.
; Load after host/owner-host.lisp using owner_feed_connection_host_check.py.
(in-package "ACL2")

(defconst *ftr-peer*
  (fn-cfg-peer-make "tls-ready" "tls-ready.example"
    '(:nntp 1 "127.0.0.1" 119 (:tls :starttls "localhost" "/tmp/ca.pem"))
    '("fn.*" 32768 16) '("fn.*" nil 256 1000)
    '(:source-address "127.0.0.1")))
(assert-event (fn-cfg-peerp *ftr-peer*))
(defconst *ftr-feeds* (fn-own-feed-reconfigure nil (list *ftr-peer*)))
(defconst *ftr-owner*
  (fn-own-with-feeds (fn-own-start (fn-sn-initial '("fn.test") 10) 3) *ftr-feeds*))
(defconst *ftr-ocfg*
  (fn-ocfg-make *ftr-owner*
    (fn-config-replay 0 510 (list *fn-cfg-default-record*)) nil nil))
(assert-event (fn-sn-statep (fn-own-store *ftr-owner*)))
(assert-event (fn-own-feed-tablep *ftr-feeds*))
(defconst *ftr-octets* (fn-record-string-octets "tls-ready"))
(defconst *ftr-greet*
  (fn-fc-step (fn-fc-initial-state nil 29 :starttls) '(50 48 48 13 10)))
(defconst *ftr-upgrade*
  (fn-fc-step (fn-fc-next-state *ftr-greet*) '(51 56 50 13 10)))
(assert-event (equal (fn-fc-kind *ftr-greet*) :starttls))
(assert-event (equal (fn-fc-kind *ftr-upgrade*) :tls))
(assert-event (fn-fc-statep (fn-fc-next-state *ftr-upgrade*)))
(assert-event (equal (fn-fc-kind (fn-fc-after-tls (fn-fc-next-state *ftr-upgrade*))) :ready))

(defun ftr-install-input (input state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (fn-owner-install-ocfg *ftr-ocfg* state))
         (state (f-put-global 'fn-owner-feed-inputs
                              (fn-fc-table-put "tls-ready" input nil) state)))
    state))

; This fails before the repair even though the old wrapper returns :ready:
; the installed owner's connection remains NIL rather than descriptor 29.
(defun ftr-starttls-check (fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let ((state (ftr-install-input (fn-fc-next-state *ftr-upgrade*) state)))
    (mv-let (erp publication state)
      (fn-owner-feed-tls-established *ftr-octets* fn-arena state)
      (if (and (not erp) (equal (fn-ores-feedpub-word publication) :ready)
               (equal (fn-feed-conn (fn-own-feed-find "tls-ready"
                                      (fn-own-feeds (fn-owner-core state)))) 29)
               (equal (fn-owner-core state)
                      (fn-own-feed-connect *ftr-owner* "tls-ready" 29
                        (fn-fc-connection-form
                          (fn-fc-next-state (fn-fc-after-tls (fn-fc-next-state *ftr-upgrade*)))))))
          (value :starttls-feed-installed)
        (er soft 'ftr-starttls-check "Ready publication did not install the feed: ~x0" publication)))))
(ftr-starttls-check fn-arena state)

; Implicit TLS still owes the greeting, and neither auth nor MODE may install
; the feed early. Invalid/repeated TLS reports likewise install nothing.
(defun ftr-pending-check (input expected fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let ((state (ftr-install-input input state)))
    (mv-let (erp publication state)
      (fn-owner-feed-tls-established *ftr-octets* fn-arena state)
      (if (and (not erp) (equal (fn-ores-feedpub-word publication) expected)
               (equal (fn-owner-core state) *ftr-owner*))
          (value expected)
        (er soft 'ftr-pending-check "Pending TLS phase changed the feed: ~x0" publication)))))
(ftr-pending-check (fn-fc-initial-state nil 30 :implicit) :need-input fn-arena state)
(ftr-pending-check
 (fn-fc-next-state (fn-fc-step
  (fn-fc-next-state (fn-fc-step (fn-fc-initial-state t 31 :starttls) '(50 48 48 13 10)))
  '(51 56 50 13 10))) :mode fn-arena state)
(ftr-pending-check
 (fn-fc-next-state (fn-fc-step
  (fn-fc-next-state (fn-fc-step
   (fn-fc-initial-auth-state nil 32 :starttls '(117) '(112) nil) '(50 48 48 13 10)))
  '(51 56 50 13 10))) :auth-user fn-arena state)
(ftr-pending-check (fn-fc-initial-state nil 33 :starttls) :invalid fn-arena state)
