; Witnesses and teeth for books/tls-key-exchange.lisp (lane w-serve, PRF-1327).
; For each keystone: a reached witness asserting its antecedent and conclusion,
; and a tooth where the antecedent is dropped and the conclusion fails.
(in-package "ACL2")
(include-book "../../books/tls-key-exchange")
(include-book "must-fail-checked")
(include-book "../../books/defkeystone")

(defun tkxt-octs (s) (declare (xargs :guard (stringp s))) (fn-record-string-octets s))

; --- The [tls] table: the default, both words, and the refusals.
(assert-event (equal (fn-tlsk-config-plan (tkxt-octs "[store]
path = \"/tmp/s\"
"))
                     '(:policy :hybrid-preferred)))
(assert-event (equal (fn-tlsk-config-plan nil) '(:policy :hybrid-preferred)))
(assert-event (equal (fn-tlsk-config-plan (tkxt-octs "[tls]
key_exchange = \"hybrid-preferred\"
"))
                     '(:policy :hybrid-preferred)))
(assert-event (equal (fn-tlsk-config-plan (tkxt-octs "[tls]
key_exchange = \"hybrid-required\"
"))
                     '(:policy :hybrid-required)))
; A word that is neither, or not a string: refused by name, never a default.
(assert-event (equal (fn-tlsk-config-plan (tkxt-octs "[tls]
key_exchange = \"classical\"
"))
                     '(:refused :key-exchange-value)))
(assert-event (equal (fn-tlsk-config-plan (tkxt-octs "[tls]
key_exchange = 1
"))
                     '(:refused :key-exchange-value)))
; An unknown key of the table, or an unknown table: the profile is refused.
(assert-event (equal (fn-tlsk-config-plan (tkxt-octs "[tls]
groups = \"x\"
"))
                     '(:refused :syntax)))
; The whole profile admits the table (the owner's record does not carry it).
(assert-event (equal (car (fn-native-config-load
                           (tkxt-octs "[store]
path = \"/tmp/s\"

[tls]
key_exchange = \"hybrid-required\"
")))
                     :accepted))
(assert-event (equal (fn-native-config-load
                      (tkxt-octs "[store]
path = \"/tmp/s\"

[tls]
key_exchange = \"hybrid-required\"
groups = \"x\"
"))
                     '(:refused :syntax)))

; --- KEYSTONE fn-tlsk-required-serves-only-the-hybrid-list (and its arm
; fn-tlsk-required-without-the-hybrid-refuses-by-definition).  Witness: both
; observations.
(assert-event (equal (fn-tlsk-decide :hybrid-required nil)
                     '(:refuse :hybrid-unavailable)))
(assert-event (equal (fn-tlsk-decide :hybrid-required t)
                     (list :serve "X25519MLKEM768:X25519:secp256r1:secp384r1" :hybrid)))
; Teeth: required with a library that cannot offer the hybrid is not served,
; and a classical list is never required's answer.
(must-fail-checked
 (defthm tkxt-tooth-required-serves-without-the-hybrid
   (fn-tlsk-servep (fn-tlsk-decide :hybrid-required offered))
   :rule-classes nil))
(must-fail-checked
 (defthm tkxt-tooth-required-may-serve-classical
   (equal (fn-tlsk-serve-groups (fn-tlsk-decide :hybrid-required offered))
          *fn-tlsk-classical-list*)
   :rule-classes nil))

; --- KEYSTONE fn-tlsk-preferred-never-refuses and
; fn-tlsk-preferred-serves-the-hybrid-iff-offered.  Witness: both cases.
(assert-event (equal (fn-tlsk-decide :hybrid-preferred nil)
                     (list :serve "X25519:secp256r1:secp384r1" :classical)))
(assert-event (equal (fn-tlsk-decide :hybrid-preferred t)
                     (list :serve "X25519MLKEM768:X25519:secp256r1:secp384r1" :hybrid)))
; Teeth: preferred is not "served as hybrid" whatever the library offers.
(must-fail-checked
 (defthm tkxt-tooth-preferred-always-hybrid
   (equal (fn-tlsk-serve-groups (fn-tlsk-decide :hybrid-preferred offered))
          *fn-tlsk-hybrid-list*)
   :rule-classes nil))

; --- KEYSTONE fn-tlsk-hybrid-is-served-only-when-offered.  Witness: the mode
; of each served answer; tooth: dropping the offer lets the mode be :hybrid.
(assert-event (equal (fn-tlsk-serve-mode (fn-tlsk-decide :hybrid-required t)) :hybrid))
(assert-event (equal (fn-tlsk-serve-mode (fn-tlsk-decide :hybrid-preferred nil)) :classical))
(must-fail-checked
 (defthm tkxt-tooth-hybrid-without-the-offer
   (implies (equal (fn-tlsk-serve-mode (fn-tlsk-decide policy offered)) :hybrid)
            (not offered))
   :rule-classes nil))
; Every classical group the ordinary readers need stays in every served list.
(assert-event (and (equal (subseq *fn-tlsk-hybrid-list* 0 14) *fn-tlsk-hybrid-group*)
                   (equal (subseq *fn-tlsk-hybrid-list* 15 (length *fn-tlsk-hybrid-list*))
                          *fn-tlsk-classical-list*)
                   (not (member-equal #\K (coerce *fn-tlsk-classical-list* 'list)))))
; An unknown policy decides nothing it can serve.
(assert-event (equal (fn-tlsk-decide :classical-only t) '(:refuse :policy)))
(must-fail-checked
 (defthm tkxt-tooth-unknown-policy-serves
   (fn-tlsk-servep (fn-tlsk-decide policy offered))
   :rule-classes nil))

; The start's refusal names the node's words.
(assert-event (equal (fn-record-octets-string
                      (fn-tlsk-refusal-line '(:refuse :hybrid-unavailable)))
                     "tls key-exchange hybrid-required: the TLS library cannot offer X25519MLKEM768 (OpenSSL 3.5 or later; FN_OPENSSL_PREFIX names the prefix)"))

; --- KEYSTONE fn-tlsk-group-token-is-a-safe-token.  Witness: a library name
; passes; a name with a line break, a space or a control byte, an empty, an
; overlong or an absent name is `unknown'.  Tooth: the token is not the name.
(assert-event (equal (fn-tlsk-group-token "X25519MLKEM768") "X25519MLKEM768"))
(assert-event (equal (fn-tlsk-group-token "secp256r1") "secp256r1"))
(assert-event (equal (fn-tlsk-group-token (concatenate 'string "X" (string #\Newline) "tls reload accepted"))
                     "unknown"))
(assert-event (equal (fn-tlsk-group-token "a b") "unknown"))
(assert-event (equal (fn-tlsk-group-token "") "unknown"))
(assert-event (equal (fn-tlsk-group-token nil) "unknown"))
(assert-event (equal (fn-tlsk-group-token 7) "unknown"))
(assert-event (equal (fn-tlsk-group-token (coerce (make-list 33 :initial-element #\a) (quote string))) "unknown"))
(assert-event (equal (fn-tlsk-group-token (coerce (make-list 32 :initial-element #\a) (quote string)))
                     (coerce (make-list 32 :initial-element #\a) (quote string))))
(must-fail-checked
 (defthm tkxt-tooth-token-is-the-name
   (equal (fn-tlsk-group-token name) name)
   :rule-classes nil))
(assert-event (equal (fn-record-octets-string (fn-tlsk-session-line "X25519MLKEM768"))
                     "tls established group=X25519MLKEM768"))
(assert-event (equal (fn-record-octets-string (fn-tlsk-session-line nil))
                     "tls established group=unknown"))

; --- KEYSTONE fn-tlsk-tally-bump-*.  Witness: three sessions, one of each
; kind, are counted once each; tooth: an unknown group is not a hybrid session.
(assert-event (equal (fn-tlsk-tally-bump '(0 0 0) "X25519MLKEM768") '(1 0 0)))
(assert-event (equal (fn-tlsk-tally-bump '(1 0 0) "X25519") '(1 1 0)))
(assert-event (equal (fn-tlsk-tally-bump '(1 1 0) nil) '(1 1 1)))
(assert-event (equal (fn-tlsk-tally-total '(1 1 1)) 3))
; A malformed tally counts from zero rather than failing a session.
(assert-event (equal (fn-tlsk-tally-bump :junk "X25519") '(0 1 0)))
(must-fail-checked
 (defthm tkxt-tooth-unknown-counts-as-hybrid
   (equal (fn-tlsk-tally-count (fn-tlsk-tally-bump tally name) 0)
          (+ 1 (fn-tlsk-tally-count tally 0)))
   :rule-classes nil))

; --- The report lines.
(assert-event (equal (fn-record-octets-string
                      (fn-tlsk-kx-line :hybrid-required :hybrid '(3 2 1)))
                     "tls key-exchange policy=hybrid-required serving=hybrid hybrid=3 classical=2 unknown=1"))
(assert-event (equal (fn-record-octets-string
                      (fn-tlsk-kx-line :hybrid-preferred :classical *fn-tlsk-zero-tally*))
                     "tls key-exchange policy=hybrid-preferred serving=classical hybrid=0 classical=0 unknown=0"))
(defconst *tkxt-served* (tkxt-octs "tls names=a.example not-after=2027-01-01T00:00:00Z"))
(defconst *tkxt-kx* (fn-tlsk-kx-line :hybrid-preferred :hybrid '(1 0 0)))
(assert-event (equal (fn-tlsk-status-lines *tkxt-served* *tkxt-kx*)
                     (append *tkxt-served* (list 10) *tkxt-kx*)))
; Past the reply's bound the served line stands alone.
(assert-event (equal (fn-tlsk-status-lines-within *tkxt-served* *tkxt-kx* (+ (len *tkxt-served*) (len *tkxt-kx*) 1))
                     (append *tkxt-served* (list 10) *tkxt-kx*)))
(assert-event (equal (fn-tlsk-status-lines-within *tkxt-served* *tkxt-kx* (+ (len *tkxt-served*) (len *tkxt-kx*)))
                     *tkxt-served*))
; `health' prints what follows the first line break of an accepted reply.
(assert-event (equal (fn-tlsk-health-client-line (list :accepted nil (fn-tlsk-status-lines *tkxt-served* *tkxt-kx*)))
                     *tkxt-kx*))
(assert-event (null (fn-tlsk-health-client-line (list :accepted nil *tkxt-served*))))
(assert-event (null (fn-tlsk-health-client-line :bad)))
(assert-event (null (fn-tlsk-health-client-line (list :refused nil (fn-tlsk-status-lines *tkxt-served* *tkxt-kx*)))))

; --- KEYSTONES fn-tlsk-library-without-tls-never-refuses and
; fn-tlsk-library-served-tls-never-falls-back (D59's refusal scope).
; Witness: each of the three answers is reached, and both antecedents are
; inhabited (a served node and a hybrid-required one, each with the pair
; missing, are refused, not fallen back).
(assert-event (equal (fn-tlsk-library-decide nil t :hybrid-required) :pinned))
(assert-event (equal (fn-tlsk-library-decide t nil :hybrid-preferred) :fallback))
(assert-event (equal (fn-tlsk-library-decide t t :hybrid-preferred) :refuse))
(assert-event (equal (fn-tlsk-library-decide t nil :hybrid-required) :refuse))
; A bad policy word on a node with no certificate is not hybrid-required: the
; [tls] table is refused only where the key exchange is decided.
(assert-event (equal (fn-tlsk-library-decide t nil :bad) :fallback))
(assert-event (equal (fn-record-octets-string (fn-tlsk-library-line :fallback))
                     "tls library warning: no OpenSSL libcrypto/libssl pair under the pinned prefix; the system's pair is loaded, and this node serves no TLS"))
(assert-event (null (fn-tlsk-library-line :pinned)))
; Teeth: a missing pinned pair does not always refuse (the node without TLS
; runs), and a served TLS node with it missing never falls back.
(must-fail-checked
 (defthm tkxt-tooth-missing-always-refuses
   (implies missing
            (equal (fn-tlsk-library-decide missing served policy) :refuse))
   :rule-classes nil))
(must-fail-checked
 (defthm tkxt-tooth-served-may-fall-back
   (implies (and missing served)
            (equal (fn-tlsk-library-decide missing served policy) :fallback))
   :rule-classes nil))
(must-fail-checked
 (defthm tkxt-tooth-required-without-tls-runs
   (implies missing
            (not (equal (fn-tlsk-library-decide missing nil :hybrid-required) :refuse)))
   :rule-classes nil))
(must-fail-checked
 (defthm tkxt-tooth-any-node-never-falls-back
   (not (equal (fn-tlsk-library-decide missing served policy) :fallback))
   :rule-classes nil))

; TEETH-22 BEGIN
; fn-tlsk-hybrid-is-served-only-when-offered stays owed: its first hypothesis
; (fn-tlsk-servep of the decision) is a conjunct of the second (fn-tlsk-serve-mode
; starts with fn-tlsk-servep), so no assignment keeps the mode hypothesis while
; breaking the serve hypothesis; a removal for it would need the keystone
; restated (no-counterexample, the fn-rcw-rebuild class).
(defteeth fn-tlsk-required-serves-only-the-hybrid-list
  :claim (((served (fn-tlsk-servep (fn-tlsk-decide :hybrid-required offered))))
          (and offered
               (equal (fn-tlsk-serve-groups (fn-tlsk-decide :hybrid-required offered))
                      *fn-tlsk-hybrid-list*)))
  :subject fn-tlsk-decide
  :witness ((offered t))
  :breaks ((served ((offered nil))))
  :mutations ((serves-the-classical-list
               (:conclusion (and offered
                                 (equal (fn-tlsk-serve-groups
                                         (fn-tlsk-decide :hybrid-required offered))
                                        *fn-tlsk-classical-list*)))
               ((offered t))
               :fault "hybrid-required serving the classical list when the library offers the hybrid group")))

(defteeth fn-tlsk-preferred-never-refuses
  :claim (() (fn-tlsk-servep (fn-tlsk-decide :hybrid-preferred offered)))
  :subject fn-tlsk-decide
  :witness ((offered t))
  :mutations ((refuses-the-offered-library
               (:conclusion (equal (fn-tlsk-decide :hybrid-preferred offered)
                                   (list :refuse :policy)))
               ((offered t))
               :fault "hybrid-preferred refusing a library that offers the hybrid group")))

(defteeth fn-tlsk-library-without-tls-never-refuses
  :claim (((serves-no-tls (not served))
           (not-required (not (equal policy :hybrid-required))))
          (not (equal (fn-tlsk-library-decide missing served policy) :refuse)))
  :subject fn-tlsk-library-decide
  :witness ((missing t) (served nil) (policy :hybrid-preferred))
  :breaks ((serves-no-tls ((missing t) (served t) (policy :hybrid-preferred)))
           (not-required ((missing t) (served nil) (policy :hybrid-required))))
  :mutations ((refuses-a-plain-node
               (:conclusion (equal (fn-tlsk-library-decide missing served policy) :refuse))
               ((missing t) (served nil) (policy :hybrid-preferred))
               :fault "a node that serves no TLS refusing its start for lack of the pinned library")))

(defteeth fn-tlsk-library-served-tls-never-falls-back
  :claim (((served-or-required (or served (equal policy :hybrid-required))))
          (not (equal (fn-tlsk-library-decide missing served policy) :fallback)))
  :subject fn-tlsk-library-decide
  :witness ((missing t) (served t) (policy :hybrid-preferred))
  :breaks ((served-or-required ((missing t) (served nil) (policy :hybrid-preferred))))
  :mutations ((falls-back-to-the-system-pair
               (:conclusion (equal (fn-tlsk-library-decide missing served policy) :fallback))
               ((missing t) (served t) (policy :hybrid-preferred))
               :fault "a TLS-serving node running on the system library pair in place of the pinned one")))
; TEETH-22 END
