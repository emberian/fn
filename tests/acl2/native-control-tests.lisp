; Reachable witnesses for the bounded FNCT local-control grammar.
(in-package "ACL2")
(include-book "../../books/native-control")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-nctrl-test-msgid*
  (fn-record-string-octets "<control-1@example.invalid>"))
(defconst *fn-nctrl-test-groups*
  (list (fn-record-string-octets "fn.letters")
        (fn-record-string-octets "fn.local")))
(defconst *fn-nctrl-test-article*
  (fn-record-string-octets
   "From: author@example.invalid\r\nSubject: exact\r\n\r\nbody\r\n"))
; A defconst cannot call an attached function (:DOC ignored-attachment).
; Assertions evaluate the ground encoder with fn-frame-digest's attachment.
(assert-event
 (fn-cbor-octet-listp
  (fn-native-control-request-encode
   *fn-nctrl-test-msgid* *fn-nctrl-test-groups* *fn-nctrl-test-article*)))
(assert-event
 (<= (len (fn-native-control-request-encode
            *fn-nctrl-test-msgid* *fn-nctrl-test-groups*
            *fn-nctrl-test-article*))
     *fn-nctrl-max-frame*))
(assert-event
 (equal (fn-native-control-request-decode
         (fn-native-control-request-encode
          *fn-nctrl-test-msgid* *fn-nctrl-test-groups*
          *fn-nctrl-test-article*))
        (list :request *fn-nctrl-test-msgid* *fn-nctrl-test-groups*
              *fn-nctrl-test-article*)))

; A byte change and a missing required group are both rejected.
(assert-event
 (equal (car (fn-native-control-request-decode
              (cons 0
                    (cdr (fn-native-control-request-encode
                          *fn-nctrl-test-msgid* *fn-nctrl-test-groups*
                          *fn-nctrl-test-article*)))))
        :refused))
(assert-event
 (equal (fn-native-control-request-encode
         *fn-nctrl-test-msgid* nil *fn-nctrl-test-article*)
        :bad))

(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :accepted))
        :accepted))
(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :uncertain))
        :uncertain))
(assert-event (equal (fn-native-control-status-exit-code :accepted) 0))
(assert-event (equal (fn-native-control-status-exit-code :refused) 1))
(assert-event (equal (fn-native-control-status-exit-code :clock-unusable) 1))
(assert-event (equal (fn-native-control-status-exit-code :uncertain) 3))
(assert-event (equal (fn-native-control-status-exit-code :fault) 4))
(assert-event (equal (fn-native-control-max-active-clients) 16))

; The control surface has two words beyond the three outcomes, and this is
; the projection that decides what each one costs the caller.  :duplicate is
; a second submission of octets the node already holds: nothing new was
; created and nothing was refused, so it is an acceptance and exits 0.
; :busy is a refusal to act, so it exits 1.  Both words still reach the
; operator whole -- host/native/operator.lisp's fnn-operator-execute-post
; passes the status itself as the detail of fnn-operator-emit-status -- so
; `accepted operator post DUPLICATE' is not `accepted operator post
; ACCEPTED'.  The 2026-09-22 native matrix saw one submission answer with
; both words in two runs; the octets differed, not this projection
; (planning/evidence/native-duplicate-outcome-2026-09-22.md).
(assert-event (member-equal :duplicate *fn-nctrl-statuses*))
(assert-event (equal (fn-native-control-status-class :duplicate) :accepted))
(assert-event (equal (fn-native-control-status-exit-code :duplicate) 0))
(assert-event (equal (fn-native-control-status-class :busy) :refused))
(assert-event (equal (fn-native-control-status-exit-code :busy) 1))
(assert-event (equal (fn-native-control-status-class :clock-unusable) :refused))

; A refusal that names its reason.  The owner's injection decision `:oversize'
; (an operator article past the profile's A) is carried as its own word, a
; refusal (exit 1) that survives the sealed reply; every other reason stays
; the plain refusal.  Teeth for fn-native-control-refusal-status-is-a-refusal:
; the status is a refusal only because the map sends every reason to one of
; the two refusal words; `:uncertain' and `:fault' are in the vocabulary and
; are not refusals.
(assert-event (equal (fn-native-control-refusal-status :oversize)
                     :article-exceeds-profile-bound))
(assert-event (equal (fn-native-control-refusal-status :unparsable) :refused))
(assert-event (equal (fn-native-control-status-exit-code
                      :article-exceeds-profile-bound)
                     1))
(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :article-exceeds-profile-bound))
        :article-exceeds-profile-bound))
(assert-event (equal (fn-native-control-reply-decode
                      (fn-native-control-reply-encode :refused))
                     :refused))
(assert-event (not (equal (fn-native-control-status-class :uncertain) :refused)))
(assert-event (not (equal (fn-native-control-status-class :fault) :refused)))

; The word has to survive the sealed reply or the operator cannot print it.
(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :duplicate))
        :duplicate))
(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :refused))
        :refused))
(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :clock-unusable))
        :clock-unusable))

; Teeth.  Exit 0 is not this function's default: it needs the status to be
; in the accepted class.  Drop that hypothesis -- ask for any other word in
; the vocabulary, or a word outside it -- and the conclusion fails.  The
; three outcomes keep three codes, and the duplicate takes the accepted
; one rather than a fourth of its own (D13).
(assert-event (equal (fn-native-control-status-exit-code :bogus) 4))
(assert-event (equal (fn-native-control-status-class :bogus) :fault))
(assert-event
 (not (equal (fn-native-control-status-exit-code :duplicate)
             (fn-native-control-status-exit-code :refused))))
(assert-event
 (not (equal (fn-native-control-status-exit-code :duplicate)
             (fn-native-control-status-exit-code :uncertain))))
(assert-event
 (not (equal (fn-native-control-status-exit-code :duplicate)
             (fn-native-control-status-exit-code :bogus))))
(assert-event
 (equal (fn-native-control-status-exit-code :duplicate)
        (fn-native-control-status-exit-code :accepted)))
(assert-event
 (not (equal (fn-native-control-status-exit-code :refused)
             (fn-native-control-status-exit-code :uncertain))))

(assert-event
 (equal (fn-native-control-lease-path
         (fn-record-string-octets "/run/fn/control.sock"))
        (fn-record-string-octets "/run/fn/control.sock.lock")))
(assert-event
 (equal (fn-native-control-lease-path nil) :bad))

; Losing the connection after a complete handoff cannot be called refusal.
(assert-event
 (equal (fn-native-control-transport-outcome :before-submission) :refused))
(assert-event
 (equal (fn-native-control-transport-outcome :after-submission) :uncertain))

(defconst *fn-nctrl-admin-argv*
  (list (fn-record-string-octets "peer")
        (fn-record-string-octets "remove")
        (fn-record-string-octets "far")))
(assert-event
 (equal (fn-native-control-admin-decode
         (fn-native-control-admin-encode *fn-nctrl-admin-argv*))
        (list :admin *fn-nctrl-admin-argv*)))
(assert-event (equal (fn-native-control-admin-encode nil) :bad))

; Admin argv is an ordered vector, so the ordinary symmetric peer plan carries
; its repeated wildmat word and the full 512-octet word budget.
(defconst *fn-nctrl-admin-symmetric-argv*
  (list (fn-record-string-octets "peer")
        (fn-record-string-octets "add")
        (fn-record-string-octets "near")
        (fn-record-string-octets "path-id")
        (fn-record-string-octets "host.example")
        (fn-record-string-octets "119")
        (fn-record-string-octets "*")
        (fn-record-string-octets "*")
        (fn-record-string-octets "198.51.100.5")
        (fn-record-string-octets "true")))
(defconst *fn-nctrl-admin-tls-argv*
  (append *fn-nctrl-admin-symmetric-argv*
          (list (fn-record-string-octets "starttls")
                (fn-record-string-octets "host.example")
                (fn-record-string-octets "anchor.example"))))
(defun fn-nctrl-test-repeat-argv (count)
  (if (zp count)
      nil
    (cons (fn-record-string-octets "extra")
          (fn-nctrl-test-repeat-argv (1- count)))))
(defconst *fn-nctrl-admin-over-budget-argv*
  (fn-nctrl-test-repeat-argv (1+ *fn-native-admin-max-arguments*)))
(defconst *fn-nctrl-admin-512-octets*
  (append (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")))
(assert-event
 (equal (fn-native-control-admin-decode
         (fn-native-control-admin-encode *fn-nctrl-admin-symmetric-argv*))
        (list :admin *fn-nctrl-admin-symmetric-argv*)))
(assert-event
 (or (< *fn-native-admin-max-arguments* (len *fn-nctrl-admin-tls-argv*))
     (equal (fn-native-control-admin-decode
             (fn-native-control-admin-encode *fn-nctrl-admin-tls-argv*))
            (list :admin *fn-nctrl-admin-tls-argv*))))
(assert-event
 (equal (fn-native-control-admin-decode
         (fn-native-control-admin-encode (list *fn-nctrl-admin-512-octets*)))
        (list :admin (list *fn-nctrl-admin-512-octets*))))
(assert-event
 (equal (fn-native-control-admin-encode
         *fn-nctrl-admin-over-budget-argv*)
        :bad))
(assert-event
 (equal (fn-native-control-admin-encode
         (list (append *fn-nctrl-admin-512-octets* '(97))))
        :bad))
(assert-event
 (equal (car (fn-native-control-admin-decode
              (fn-nctrl-seal
               *fn-nctrl-admin-kind*
               (append (fn-cbor-encode
                        (cons :uint (1+ *fn-native-admin-max-arguments*)))
                       (fn-nctrl-admin-words-encode
                        *fn-nctrl-admin-over-budget-argv*)))))
        :refused))
(assert-event
 (equal (fn-nctrl-admin-words-encode '(bad)) nil))
(assert-event
 (equal (fn-nctrl-admin-words-decode 'bad nil)
        (fn-record-parse-error :arguments)))
(assert-event
 (equal (car (fn-native-control-admin-decode
              (fn-nctrl-seal
               *fn-nctrl-admin-kind*
               (append (fn-cbor-encode (cons :uint 1))
                       (fn-cbor-encode (cons :bytes '(128)))))))
        :refused))
(assert-event
 (equal (car (fn-native-control-admin-decode
              (fn-nctrl-seal *fn-nctrl-admin-kind*
                              (append (fn-nctrl-admin-argv-encode
                                       *fn-nctrl-admin-argv*)
                                      '(0)))))
        :refused))
(assert-event
 (equal (car (fn-native-control-admin-decode
              (fn-nctrl-seal *fn-nctrl-admin-kind* '(1 65))))
        :refused))

; -----------------------------------------------------------------------------
; D27 (PRF-091): the FNCT article field is the record codec's payload
; ceiling, and the owner's read bound follows the profile's A and G.

; An article one octet past the old `:blob' width is a request field and
; round-trips through the request grammar; under the pre-D27 spec it is not.
(defconst *nct-big* (make-list 131073 :initial-element 65))
(defconst *nct-groups-octets* (fn-nctrl-groups-encode *fn-nctrl-test-groups*))
(assert-event
 (fn-frame-values-okp *fn-nctrl-request-spec*
                      (list *nct-big* *fn-nctrl-test-msgid* *nct-groups-octets*)))
(assert-event
 (not (fn-frame-values-okp '(:blob :text :blob)
                           (list *nct-big* *fn-nctrl-test-msgid*
                                 *nct-groups-octets*))))
(assert-event
 (equal (fn-frame-fields-parse
         *fn-nctrl-request-spec*
         (fn-frame-fields-octets *fn-nctrl-request-spec*
                                 (list *nct-big* *fn-nctrl-test-msgid*
                                       *nct-groups-octets*)))
        (fn-frame-parse-ok (list *nct-big* *fn-nctrl-test-msgid*
                                 *nct-groups-octets*)
                           nil)))
; The request's octets are unchanged for an article within the old width.
(assert-event
 (equal (fn-frame-fields-octets *fn-nctrl-request-spec*
                                (list *fn-nctrl-test-article*
                                      *fn-nctrl-test-msgid*
                                      *nct-groups-octets*))
        (fn-frame-fields-octets '(:blob :text :blob)
                                (list *fn-nctrl-test-article*
                                      *fn-nctrl-test-msgid*
                                      *nct-groups-octets*))))
(assert-event (<= *fn-nctrl-max-payload* *fn-frame-max-payload*))

; The read bound: the command-frame floor at small A, and the profile's
; request frame above it.
(assert-event (equal (fn-nctrl-read-bound-for 32768 2)
                     *fn-nctrl-max-command-frame*))
(assert-event (< *fn-nctrl-max-command-frame*
                 (fn-nctrl-read-bound-for 300000 2)))
(assert-event (< 300000 (fn-nctrl-read-bound-for 300000 2)))

; Witness for `fn-native-control-request-within-profile-frame': the test
; request at A its exact article length and G two, within the bound, with
; the bound less than 1 100 octets above it.
(defconst *nct-a* (len *fn-nctrl-test-article*))
(assert-event
 (let ((n (len (fn-native-control-request-encode
                *fn-nctrl-test-msgid* *fn-nctrl-test-groups*
                *fn-nctrl-test-article*))))
   (and (< 0 n)
        (<= n (fn-nctrl-max-frame-for *nct-a* 2))
        (< (fn-nctrl-max-frame-for *nct-a* 2) (+ n 1100)))))

; One counterexample per hypothesis: each request below satisfies every
; hypothesis but the named one, and its encoding exceeds the bound.
(defconst *nct-2000* (make-list 2000 :initial-element 65))
(defun nct-forty-groups (i)
  (declare (xargs :mode :program))
  (if (zp i) nil
    (cons (fn-record-string-octets
           (concatenate 'string "fn.teeth.group." (coerce (explode-atom (+ 9 i) 10) 'string)))
          (nct-forty-groups (- i 1)))))
(defconst *nct-40* (nct-forty-groups 40))
(assert-event (equal (len *nct-40*) 40))
(assert-event
 (fn-cbor-octet-listp
  (fn-native-control-request-encode *fn-nctrl-test-msgid* *nct-40*
                                    *fn-nctrl-test-article*)))
(assert-event
 (<= (len (fn-nctrl-groups-encode *nct-40*))
     (+ 5 (* (+ 5 *fn-record-max-group-name*) 40))))
; Without (<= (len article) a): a 2 000-octet article at A = 0.
(assert-event
 (< (fn-nctrl-max-frame-for 0 2)
    (len (fn-native-control-request-encode *fn-nctrl-test-msgid*
                                           *fn-nctrl-test-groups*
                                           *nct-2000*))))
; Without (<= (len groups) g): forty groups at G = 0.
(assert-event
 (< (fn-nctrl-max-frame-for *nct-a* 0)
    (len (fn-native-control-request-encode *fn-nctrl-test-msgid* *nct-40*
                                           *fn-nctrl-test-article*))))
; Without (natp a): A = 4001/2 admits the 2 000-octet article, and reads as 0.
(assert-event
 (and (<= 2000 4001/2)
      (< (fn-nctrl-max-frame-for 4001/2 2)
         (len (fn-native-control-request-encode *fn-nctrl-test-msgid*
                                                *fn-nctrl-test-groups*
                                                *nct-2000*)))))
; Without (natp g): G = 81/2 admits forty groups, and reads as 0.
(assert-event
 (and (<= 40 81/2)
      (< (fn-nctrl-max-frame-for *nct-a* 81/2)
         (len (fn-native-control-request-encode *fn-nctrl-test-msgid* *nct-40*
                                                *fn-nctrl-test-article*)))))

; ---------------------------------------------------------------------------
; fn-native-control-liveness-decides (PKT-344).  Positive witnesses, one per
; arm: a crashed owner's socket (node present, lock free) is :stale and runs
; offline; a live owner (node, lock held) is :live; no node and a free lock
; is :offline; no node and a held lock is :held and never runs offline.
(assert-event (equal (fn-native-control-liveness t :free) :stale))
(assert-event (equal (fn-native-control-liveness t :absent) :stale))
(assert-event (fn-native-control-liveness-offlinep :stale))
(assert-event (equal (fn-native-control-liveness t :held) :live))
(assert-event (equal (fn-native-control-liveness t :unknown) :live))
(assert-event (equal (fn-native-control-liveness nil :free) :offline))
(assert-event (equal (fn-native-control-liveness nil :held) :held))
(assert-event (equal (fn-native-control-liveness nil :unknown) :held))
(assert-event (not (fn-native-control-liveness-offlinep :held)))
(assert-event (not (fn-native-control-liveness-offlinep :live)))
(assert-event (stringp (fn-native-control-liveness-note :stale)))
(assert-event (null (fn-native-control-liveness-note :live)))
; The conclusion fails for the pre-PKT-344 rule (the socket node alone):
; with a stale node that rule answered :live and the connect refused.
(defun nct-livep-by-node-alone (socket-node lock)
  (declare (ignore lock))
  (if socket-node :live :offline))
(assert-event (not (fn-native-control-liveness-offlinep
                    (nct-livep-by-node-alone t :free))))
(assert-event (fn-native-control-liveness-offlinep
                (nct-livep-by-node-alone nil :held)))
; Without the lock: the node alone does not decide stale.
(must-fail
 (defthm nct-stale-without-lock
   (iff (equal (fn-native-control-liveness socket-node lock) :stale)
        socket-node)
   :rule-classes nil))
; Without the node: a free lock alone is not stale.
(must-fail
 (defthm nct-stale-without-node
   (iff (equal (fn-native-control-liveness socket-node lock) :stale)
        (member-equal lock '(:free :absent)))
   :rule-classes nil))
