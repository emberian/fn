; fn: `peer set' and `peer login' (books/peer-set.lisp, PRF-973), the test
; book: the plan the operator's words make through the administrative plan,
; the delta over a live table, and the teeth of each keystone.

(in-package "ACL2")
(include-book "../../books/native-admin")

(defun pst-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (pst-argv (cdr words)))
    nil))

(defconst *pst-hex*
  "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")

; The record `peer confirm' writes (books/peer-invite.lisp
; fn-pinv-confirmed-peer's shape): one direction, clear, principal-bound;
; plus a `peer pull' row, an extension row.
(defconst *pst-confirmed*
  (fn-cfg-peer-make "friend" "friend.example.net"
                    (list :nntp 1 "198.51.100.9" 119 '(:clear))
                    (list "local.*" *fn-record-max-payload* 16)
                    nil
                    (list :principal *pst-hex*)))
(defconst *pst-pull-row* (list "friend" "pull-interval" "" 20))
(defconst *pst-peers*
  (append (fn-cfg-peer-rows *pst-confirmed*)
          (list *pst-pull-row*
                (list "other" "path-identity" "other.example" 0))))
(defconst *pst-v*
  (fn-cfg-value-make nil 0 nil nil nil *pst-peers* nil nil nil nil))

(assert-event (fn-cfg-peerp *pst-confirmed*))
(assert-event (equal (fn-cfg-peer-find "friend" *pst-peers*) *pst-confirmed*))

;; ---------------------------------------------------------------------------
;; The walk's one `peer set': send, encrypt, pin the anchor.

(defconst *pst-words*
  '("peer" "set" "friend" "--send" "local.*" "--tls" "starttls"
    "--server-name" "friend.example.net" "--anchor" "/var/lib/fn/friend-cert.pem"))
(defconst *pst-plan* (fn-native-admin-plan (pst-argv *pst-words*)))
(assert-event (equal (fn-native-admin-result-status *pst-plan*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *pst-plan*) :extend-peer))
(defconst *pst-opts* (cadr (fn-native-admin-result-value *pst-plan*)))
(defconst *pst-deltas* (fn-native-admin-plan-deltas-over *pst-plan* *pst-peers*))
(assert-event (equal (len *pst-deltas*) 1))
(assert-event (equal (fn-native-admin-plan-refusal-over *pst-plan* *pst-peers*) nil))
(defconst *pst-edited*
  (cadr (fn-pset-edit (fn-cfg-peer-find "friend" *pst-peers*) *pst-opts*)))
(defconst *pst-after* (fn-cfg-apply *pst-v* 1 nil *pst-deltas*))
(assert-event (fn-cfg-valuep *pst-after*))

; KEYSTONE fn-pset-plan-sets-the-record-and-keeps-the-extensions, positive:
; the antecedent (an :ok plan) and the conclusion (the group is the edited
; record's rows then the kept pull row), literally.
(assert-event (equal (car (fn-pset-plan "friend" *pst-opts* *pst-peers*)) :ok))
(assert-event
 (equal (fn-cfg-rows-with-key
         (fn-cfg-peers (fn-cfg-apply-delta
                        *pst-v* 1 nil
                        (car (cadr (fn-pset-plan "friend" *pst-opts* *pst-peers*)))))
         "friend")
        (append (fn-cfg-peer-rows *pst-edited*)
                (fn-pset-extension-rows (fn-cfg-rows-with-key *pst-peers* "friend")))))
(assert-event (member-equal *pst-pull-row*
                            (fn-cfg-rows-with-key (fn-cfg-peers *pst-after*) "friend")))
; The other peer is untouched, and the table decodes the edited record.
(assert-event (equal (fn-cfg-rows-with-key (fn-cfg-peers *pst-after*) "other")
                     (list (list "other" "path-identity" "other.example" 0))))
(assert-event (equal (fn-cfg-peer-find "friend" (fn-cfg-peers *pst-after*))
                     *pst-edited*))
(assert-event
 (equal (fn-cfg-peer-transport *pst-edited*)
        (list :nntp 1 "198.51.100.9" 119
              (list :tls :starttls "friend.example.net"
                    "/var/lib/fn/friend-cert.pem"))))
; Teeth, hypothesis removal: a plan that is not :ok (no such peer) has no
; delta, and the refusal is named.
(defconst *pst-nobody*
  (fn-native-admin-plan (pst-argv '("peer" "set" "nobody" "--send" "local.*"))))
(assert-event (equal (car (fn-pset-plan "nobody" (cadr (fn-native-admin-result-value
                                                        *pst-nobody*))
                                        *pst-peers*))
                     :refused))
(assert-event (equal (fn-native-admin-plan-deltas-over *pst-nobody* *pst-peers*) nil))
(assert-event (equal (fn-native-admin-plan-refusal-over *pst-nobody* *pst-peers*)
                     :no-such-peer))
; Mutation witness: `peer add' with the same fields replaces the group and
; loses the pull row, which is what `peer set' exists to keep.
(assert-event
 (not (member-equal *pst-pull-row*
                    (fn-cfg-rows-with-key
                     (fn-cfg-peers (fn-cfg-apply *pst-v* 1 nil
                                                 (list (fn-cfg-set-peer-delta *pst-edited*))))
                     "friend"))))

;; ---------------------------------------------------------------------------
;; fn-pset-edit-keeps-unnamed-fields

(defconst *pst-send-only* (cadr (fn-pset-options '("--send" "local.*") nil)))
(defconst *pst-send-edit* (fn-pset-edit *pst-confirmed* *pst-send-only*))
; Positive: every hypothesis (a live record, an :ok edit, no transport, take
; or auth flag) and the three conclusions it reaches.
(assert-event (fn-cfg-peerp *pst-confirmed*))
(assert-event (equal (car *pst-send-edit*) :ok))
(assert-event (not (fn-pset-opt "--host" *pst-send-only*)))
(assert-event (equal (fn-cfg-peer-transport (cadr *pst-send-edit*))
                     (fn-cfg-peer-transport *pst-confirmed*)))
(assert-event (equal (fn-cfg-peer-inbound (cadr *pst-send-edit*))
                     (fn-cfg-peer-inbound *pst-confirmed*)))
(assert-event (equal (fn-cfg-peer-auth (cadr *pst-send-edit*))
                     (fn-cfg-peer-auth *pst-confirmed*)))
; Hypothesis removal (a transport flag named): the transport changes.
(defconst *pst-port-edit*
  (fn-pset-edit *pst-confirmed* (cadr (fn-pset-options '("--port" "563") nil))))
(assert-event (equal (car *pst-port-edit*) :ok))
(assert-event (not (equal (fn-cfg-peer-transport (cadr *pst-port-edit*))
                          (fn-cfg-peer-transport *pst-confirmed*))))

;; fn-pset-edit-sets-the-named-send-and-login, positive and removal.
(assert-event (equal (fn-cfg-peer-outbound-groups (cadr *pst-send-edit*)) "local.*"))
(defconst *pst-login-edit*
  (fn-pset-edit (cadr *pst-send-edit*)
                (cadr (fn-pset-options '("--login" "/var/lib/fn/friend.fnauth") nil))))
(assert-event (equal (car *pst-login-edit*) :ok))
(assert-event (equal (cadr (nth 4 (fn-cfg-peer-outbound (cadr *pst-login-edit*))))
                     "/var/lib/fn/friend.fnauth"))
; The login belongs to the sending half: on the confirmed record (nothing
; sent) it is refused by the name of what it would take.
(assert-event
 (equal (fn-pset-edit *pst-confirmed*
                      (cadr (fn-pset-options '("--login" "/var/lib/fn/friend.fnauth") nil)))
        '(:refused :needs-send)))

;; Refusals by name.
(assert-event (equal (fn-pset-options '("--bogus" "1") nil) '(:refused :unknown-flag)))
(assert-event (equal (fn-pset-options '("--send") nil) '(:refused :flag-without-value)))
(assert-event (equal (fn-pset-options '("--send" "a.*" "--send" "b.*") nil)
                     '(:refused :repeated-flag)))
(assert-event
 (equal (fn-pset-edit *pst-confirmed* (cadr (fn-pset-options '("--tls" "starttls") nil)))
        '(:refused :tls-needs-server-name)))
(assert-event
 (equal (fn-pset-edit *pst-confirmed* (cadr (fn-pset-options '("--port" "70000") nil)))
        '(:refused :port)))
(assert-event
 (equal (fn-pset-edit *pst-confirmed*
                      (cadr (fn-pset-options (list "--principal" *pst-hex*
                                                   "--source-address" "10.0.0.1")
                                             nil)))
        '(:refused :auth-twice)))

;; ---------------------------------------------------------------------------
;; The login file

(defconst *pst-pass* (fn-record-string-octets "s3cret-Word"))
(defconst *pst-file* (fn-pset-login-file "me-node" *pst-pass* *pst-pass*))
; KEYSTONE fn-pset-login-file-reads-back (and -octets-round-trip), positive.
(assert-event (equal (car *pst-file*) :ok))
(assert-event (equal (fn-fap-decode (cadr *pst-file*))
                     (list :ok (fn-record-string-octets "me-node") *pst-pass*)))
(assert-event (fn-pset-login-octets "me-node" *pst-pass*))
; Teeth: the entries disagree; a password the reader cannot carry (a space);
; a login that is no token.  Each refused by name, so no file is written.
(assert-event (equal (fn-pset-login-file "me-node" *pst-pass*
                                         (fn-record-string-octets "other"))
                     '(:refused :passwords-differ)))
(assert-event (equal (fn-pset-login-file "me-node"
                                         (fn-record-string-octets "two words")
                                         (fn-record-string-octets "two words"))
                     '(:refused :password)))
(assert-event (equal (fn-pset-login-file "" *pst-pass* *pst-pass*)
                     '(:refused :login)))
; Hypothesis removal for the round trip: a hand-written file with a space in
; the password is one the reader refuses.
(assert-event
 (equal (car (fn-fap-decode (append *fn-fap-magic* (fn-record-string-octets "me-node")
                                    (list 10) (fn-record-string-octets "two words")
                                    (list 10))))
        :bad))
; The words `peer login' then applies are `peer set NAME --login FILE'.
(assert-event
 (equal (fn-native-admin-plan-deltas-over
         (fn-native-admin-plan (fn-pset-login-argv "friend" "/var/lib/fn/friend.fnauth"))
         (fn-cfg-peers *pst-after*))
        (list (fn-cfg-set-peer
               "friend"
               (append (fn-cfg-peer-rows
                        (cadr (fn-pset-edit *pst-edited*
                                            (list (cons "--login"
                                                        "/var/lib/fn/friend.fnauth")))))
                       (list *pst-pull-row*))))))
