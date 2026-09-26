; Teeth for PRF-195 (NNT-039): books/config-descriptions.lisp,
; books/owner-descriptions-read.lisp, and the `group describe' / `motd'
; plans of books/native-admin.lisp.
(in-package "ACL2")
(include-book "../../books/owner-descriptions-read")
(include-book "../../books/native-admin")
(include-book "std/testing/must-fail" :dir :system)

(defmacro gdt-o (text) `(fn-nntp-string-octets ,text))

; -----------------------------------------------------------------------------
; A reachable configuration: the default record (fn.letters, fn.test) and a
; record that describes fn.test and sets the node's message, replayed.

(defconst *gdt-desc* (fn-cfg-set-group-description "fn.test" '("Friends " "and letters")))
(defconst *gdt-motd* (fn-cfg-set-group-description "" '("Welcome to fn." "Ask ember.")))
(defconst *gdt-record2*
  (fn-cfg-record-make 1 1 2 (list *gdt-desc* *gdt-motd*) *fn-cfg-default-stamp*))
(defconst *gdt-cfg1*
  (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*)))
(defconst *gdt-cfg*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record* *gdt-record2*)))
(defconst *gdt-v1* (fn-cfg-value *gdt-cfg1*))
(defconst *gdt-v* (fn-cfg-value *gdt-cfg*))

; The record was admitted and replayed: generation 2, the text is there.
(assert-event (fn-cfg-recordp *gdt-record2*))
(assert-event (equal (fn-cfg-generation *gdt-cfg*) 2))
(assert-event (fn-cfg-valuep *gdt-v*))
(assert-event (null (fn-cfg-admissible-reason *gdt-v1* 2 *fn-cfg-default-stamp* 0
                                              512 (list *gdt-desc* *gdt-motd*))))
(assert-event (equal (fn-cfg-description-octets *gdt-v* "fn.test")
                     (gdt-o "Friends and letters")))
(assert-event (equal (fn-cfg-description-octets *gdt-v* "fn.letters") nil))
(assert-event (equal (fn-cfg-motd-lines *gdt-v*)
                     (list (gdt-o "Welcome to fn.") (gdt-o "Ask ember."))))
; The code on the record wire is 20, and it reads back.
(assert-event (equal (fn-cfg-kind-code :set-group-description) 20))
(assert-event (equal (fn-cfg-code-kind 20) :set-group-description))

; fn-cfg-description-after-set-is-its-pieces: the positive witness.
(assert-event
 (equal (fn-cfg-description-octets
         (fn-cfg-apply-delta *gdt-v1* 2 *fn-cfg-default-stamp* *gdt-desc*) "fn.test")
        (fn-cfg-pieces-octets '("Friends " "and letters"))))
; Replacing, not appending: a second description replaces the first.
(assert-event
 (equal (fn-cfg-description-octets
         (fn-cfg-apply-delta *gdt-v* 2 *fn-cfg-default-stamp*
                             (fn-cfg-set-group-description "fn.test" '("Letters")))
         "fn.test")
        (gdt-o "Letters")))
; ... and no pieces clears it.
(assert-event
 (equal (fn-cfg-description-octets
         (fn-cfg-apply-delta *gdt-v* 2 *fn-cfg-default-stamp*
                             (fn-cfg-set-group-description "fn.test" nil))
         "fn.test")
        nil))

; fn-cfg-description-after-set-of-another-name: witness, and without
; (not (equal other name)) the conclusion fails at OTHER = NAME.
(assert-event
 (equal (fn-cfg-description-octets
         (fn-cfg-apply-delta *gdt-v* 2 *fn-cfg-default-stamp*
                             (fn-cfg-set-group-description "fn.letters" '("L")))
         "fn.test")
        (fn-cfg-description-octets *gdt-v* "fn.test")))
(assert-event
 (not (equal (fn-cfg-description-octets
              (fn-cfg-apply-delta *gdt-v1* 2 *fn-cfg-default-stamp* *gdt-desc*)
              "fn.test")
             (fn-cfg-description-octets *gdt-v1* "fn.test"))))
(must-fail
 (defthm gdt-another-name-without-its-hypothesis
   (equal (fn-cfg-description-octets
           (fn-cfg-apply-delta v gen stamp
                               (fn-cfg-set-group-description name pieces))
           other)
          (fn-cfg-description-octets v other))))

; fn-cfg-motd-after-set-is-its-lines: the message delta keys on "".
(assert-event
 (equal (fn-cfg-motd-lines
         (fn-cfg-apply-delta *gdt-v1* 2 *fn-cfg-default-stamp* *gdt-motd*))
        (fn-cfg-pieces-lines '("Welcome to fn." "Ask ember."))))
; A group's description is not the message.
(assert-event
 (equal (fn-cfg-motd-lines
         (fn-cfg-apply-delta *gdt-v1* 2 *fn-cfg-default-stamp* *gdt-desc*))
        nil))

; fn-cfg-descriptions-of-other-kinds: another kind keeps the slot; without
; the kind hypothesis the conclusion fails at the description delta.
(assert-event
 (equal (fn-cfg-descriptions
         (fn-cfg-apply-delta *gdt-v* 2 *fn-cfg-default-stamp*
                             (fn-cfg-create-group "fn.new" *fn-cfg-default-policy-id*)))
        (fn-cfg-descriptions *gdt-v*)))
(assert-event
 (not (equal (fn-cfg-descriptions
              (fn-cfg-apply-delta *gdt-v1* 2 *fn-cfg-default-stamp* *gdt-desc*))
             (fn-cfg-descriptions *gdt-v1*))))

; fn-cfg-set-group-description-refuses-an-unknown-group-by-definition: witness, and each
; hypothesis's failure.
(defmacro gdt-reason (d) `(fn-cfg-delta-reason *gdt-v1* 2 *fn-cfg-default-stamp* 0 512 ,d))
(assert-event (equal (gdt-reason (fn-cfg-set-group-description "fn.nosuch" '("x")))
                     :no-such-group))
;   the group is live: admitted.
(assert-event (null (gdt-reason (fn-cfg-set-group-description "fn.test" '("x")))))
;   the name is "": admitted (the node's message).
(assert-event (null (gdt-reason (fn-cfg-set-group-description "" '("x")))))
;   another kind: not :no-such-group.
(assert-event (not (equal (gdt-reason (fn-cfg-set-capacity 1048576)) :no-such-group)))
;   not a delta: :malformed-delta.
(assert-event (equal (gdt-reason (list :set-group-description "fn.nosuch" "" 0))
                     :malformed-delta))
; A retired group is not live.
(assert-event
 (equal (fn-cfg-delta-reason
         (fn-cfg-apply-delta *gdt-v1* 2 *fn-cfg-default-stamp* (fn-cfg-remove-group "fn.test"))
         3 *fn-cfg-default-stamp* 0 512
         (fn-cfg-set-group-description "fn.test" '("x")))
        :no-such-group))

; fn-cfg-admitted-description-rows-are-printable: the admission refuses a
; control octet, a row keyed on another name, and a group text of spaces.
(assert-event
 (equal (gdt-reason (fn-cfg-set-group-description
                     "fn.test" (list (coerce (list #\a (code-char 9) #\b) 'string))))
        :description-row))
(assert-event
 (equal (gdt-reason (fn-cfg-delta-make :set-group-description "fn.test" "" 0
                                       (fn-cfg-description-rows "fn.letters" '("x"))))
        :description-row))
(assert-event (equal (gdt-reason (fn-cfg-set-group-description "fn.test" '("   ")))
                     :description-blank))
; ... while the node's message may hold a blank line.
(assert-event (null (gdt-reason (fn-cfg-set-group-description "" '("a" "" "b")))))
(assert-event
 (not (fn-cfg-description-rowsp
       (fn-cfg-description-rows "fn.test" (list (coerce (list (code-char 9)) 'string)))
       "fn.test")))

; -----------------------------------------------------------------------------
; The listing the owner installs (fn-oag-post-config, called by
; host/owner-host.lisp fn-owner-post-config).

(defconst *gdt-post* (fn-oag-post-config *gdt-cfg* 32768))
(assert-event (fn-inj-configp *gdt-post*))
(assert-event
 (equal (fn-nntp-description-of
         "fn.test" (fn-nntp-listing-descs (fn-inj-config-listing *gdt-post*)))
        (gdt-o "Friends and letters")))
; A served group without a description has no entry.
(assert-event
 (equal (fn-nntp-description-of
         "fn.letters" (fn-nntp-listing-descs (fn-inj-config-listing *gdt-post*)))
        nil))
(assert-event
 (equal (fn-nntp-listing-motd (fn-inj-config-listing *gdt-post*))
        (list (gdt-o "Welcome to fn.") (gdt-o "Ask ember."))))
; fn-oag-description-of-descs, the membership conjunct: a described name
; the served table does not hold has no entry.
(assert-event
 (equal (fn-nntp-description-of "fn.test" (fn-oag-descs '("fn.letters") *gdt-v*))
        nil))
; The injection decision ignores the listing (a ground instance).
(assert-event
 (equal (fn-inj-config-agent *gdt-post*)
        (fn-inj-config-agent (fn-oag-post-config *gdt-cfg1* 32768))))

; -----------------------------------------------------------------------------
; The dispatcher: LIST NEWSGROUPS and LIST MOTD over a two-group archive.

(defconst *gdt-archive* (fn-initial-state '("fn.letters" "fn.test")))
(defconst *gdt-open* (fn-nntp-open-session *gdt-archive*))
(defconst *gdt-env*
  (fn-nntp-env-listed (fn-clock-observation 0 0 0 nil) nil nil
                      (fn-inj-config-listing *gdt-post*)))
(defmacro gdt-cmd (env keyword &rest args)
  `(fn-nntp-archive-command-pinned *gdt-open* *gdt-archive* nil nil ,env
                                   (gdt-o ,keyword)
                                   (list ,@(pairlis-x1 'fn-nntp-string-octets
                                                      (pairlis$ args nil)))))
(defmacro gdt-lines (&rest lines)
  `(list ,@(pairlis-x1 'fn-nntp-string-octets (pairlis$ lines nil))))
(defconst *gdt-tab* (coerce (list (code-char 9)) 'string))

(assert-event
 (equal (gdt-cmd *gdt-env* "LIST" "NEWSGROUPS")
        (fn-nntp-multi *gdt-open* "215 list of newsgroups follows"
                       (list (append (gdt-o "fn.letters") '(9) (gdt-o "(no description)"))
                             (append (gdt-o "fn.test") '(9)
                                     (gdt-o "Friends and letters"))))))
(assert-event
 (equal (gdt-cmd *gdt-env* "list" "newsgroups" "fn.t*")
        (fn-nntp-multi *gdt-open* "215 list of newsgroups follows"
                       (list (append (gdt-o "fn.test") '(9)
                                     (gdt-o "Friends and letters"))))))
(assert-event
 (equal (gdt-cmd *gdt-env* "LIST" "NEWSGROUPS" "a" "b")
        (fn-nntp-single *gdt-open* "501 syntax error")))
(assert-event
 (equal (gdt-cmd *gdt-env* "LIST" "MOTD")
        (fn-nntp-multi *gdt-open* "215 message of the day follows"
                       (gdt-lines "Welcome to fn." "Ask ember."))))
(assert-event
 (equal (gdt-cmd *gdt-env* "LIST" "MOTD" "x")
        (fn-nntp-single *gdt-open* "501 syntax error")))
; With no listing: the marker listing of before, and an empty message.
(assert-event
 (equal (gdt-cmd (fn-nntp-blind-env) "LIST" "NEWSGROUPS")
        (fn-nntp-list-newsgroups *gdt-open* (fn-state-groups *gdt-archive*))))
(assert-event
 (equal (gdt-cmd (fn-nntp-blind-env) "LIST" "MOTD")
        (fn-nntp-multi *gdt-open* "215 message of the day follows" nil)))
; A description a listing carries but the test refuses is not sent: the
; marker is.
(assert-event
 (equal (fn-nntp-description-field "fn.test" (list (cons "fn.test" '(97 13 10 98))))
        (gdt-o "(no description)")))
(assert-event
 (equal (fn-nntp-motd-lines (list (gdt-o "ok") '(97 13 10)))
        (list (gdt-o "ok"))))
; CAPABILITIES names the variant.
(assert-event
 (member-equal (gdt-o "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT")
               (fn-nntp-capability-lines nil)))

; -----------------------------------------------------------------------------
; The operator plans (`group describe', `motd set|clear').

(defmacro gdt-argv (&rest words)
  `(list ,@(pairlis-x1 'fn-nntp-string-octets (pairlis$ words nil))))
(defconst *gdt-plan* (fn-native-admin-plan (gdt-argv "group" "describe" "fn.test"
                                                     "Friends" "and" "letters")))
(assert-event (equal (fn-native-admin-result-status *gdt-plan*) :accepted))
(assert-event
 (equal (fn-native-admin-plan-deltas *gdt-plan*)
        (list (fn-cfg-set-group-description "fn.test" '("Friends and letters")))))
(assert-event
 (fn-cfg-delta-listp (fn-native-admin-plan-deltas *gdt-plan*)))
; No text clears.
(assert-event
 (equal (fn-native-admin-plan-deltas
         (fn-native-admin-plan (gdt-argv "group" "describe" "fn.test")))
        (list (fn-cfg-set-group-description "fn.test" nil))))
; A long description is cut into pieces of at most 256 octets and joins back.
(defconst *gdt-long-word* (make-list 300 :initial-element 120))
(defconst *gdt-long-plan*
  (fn-native-admin-plan (list (gdt-o "group") (gdt-o "describe") (gdt-o "fn.test")
                              *gdt-long-word* *gdt-long-word*)))
(assert-event (equal (fn-native-admin-result-status *gdt-long-plan*) :accepted))
(assert-event
 (equal (len (fn-cfg-delta-rows (car (fn-native-admin-plan-deltas *gdt-long-plan*))))
        3))
(assert-event
 (equal (fn-cfg-description-octets
         (fn-cfg-apply-delta *gdt-v1* 2 *fn-cfg-default-stamp*
                             (car (fn-native-admin-plan-deltas *gdt-long-plan*)))
         "fn.test")
        (append *gdt-long-word* (list 32) *gdt-long-word*)))
(assert-event
 (fn-cfg-delta-listp (fn-native-admin-plan-deltas *gdt-long-plan*)))
; Refusals: spaces only; a control octet; not a group name.
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan (gdt-argv "group" "describe" "fn.test" "   ")))
        :description-blank))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan (list (gdt-o "group") (gdt-o "describe") (gdt-o "fn.test")
                                     '(97 9 98))))
        :description-text))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan (gdt-argv "group" "describe" "Not A Group" "x")))
        :group-name))
; The message: lines, clear, a line past one row refused.
(assert-event
 (equal (fn-native-admin-plan-deltas
         (fn-native-admin-plan (gdt-argv "motd" "set" "Welcome to fn." "Ask ember.")))
        (list *gdt-motd*)))
(assert-event
 (equal (fn-native-admin-plan-deltas (fn-native-admin-plan (gdt-argv "motd" "clear")))
        (list (fn-cfg-set-group-description "" nil))))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan (list (gdt-o "motd") (gdt-o "set")
                                     (make-list 257 :initial-element 120))))
        :motd-line))
(assert-event
 (equal (fn-native-admin-result-reason (fn-native-admin-plan (gdt-argv "motd")))
        :syntax))
