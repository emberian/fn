; fn: teeth for books/app-pattern.lisp.
;
; fn-pat-cli-run-binds-every-step: the pub and sub command lines are
; accepted (the hypothesis is inhabited) and bind every need; a command line
; one word short, with an empty or NUL word, with an unknown option or an
; extra word on a role that does not loop, or naming an unknown pattern or
; role, is refused by name.  fn-pat-values-check-is-the-kind: a check that
; answers nil on the example values and names the row of each refinement
; (the same values with a bad From, Newsgroups or Message-ID).  def-pattern
; refuses each malformed declaration.

(in-package "ACL2")
(include-book "../../books/app-pattern")
(include-book "must-fail-checked")
(include-book "../../books/defkeystone")

(defconst *apt-pub-argv*
  (list (fn-ak-text "/s/control") (fn-ak-text "1") (fn-ak-text "/k")
        (fn-ak-text "mini.blocks") (fn-ak-text "Mini <mini@example.invalid>")
        (fn-ak-text "<b1.mini@example.invalid>") (fn-ak-text "/p") (fn-ak-text "/spool")))
(defconst *apt-sub-argv*
  (list (fn-ak-text "/s/control") (fn-ak-text "sub-1") (fn-ak-text "mini.blocks")
        (fn-ak-text "/out")))
(defconst *apt-pubsub* (fn-ak-text "pubsub"))
(defconst *apt-pub* (fn-ak-text "pub"))
(defconst *apt-sub* (fn-ak-text "sub"))

(defun apt-cli (role argv) (fn-pat-cli-plan *apt-pubsub* role argv))
(defun apt-covers (cli)
  (and (equal (car cli) :run)
       (fn-pat-bindings-coverp (fn-pat-plan-needs (nth 4 cli)) (nth 5 cli))))

; Satisfiable: both roles run, and the bindings cover the plans.
(assert-event (apt-covers (apt-cli *apt-pub* *apt-pub-argv*)))
(assert-event (apt-covers (apt-cli *apt-sub* *apt-sub-argv*)))
(assert-event
 (equal (nth 4 (apt-cli *apt-pub* *apt-pub-argv*))
        '(((:encode :opaque-1) (:sign) (:author)) nil)))
(assert-event
 (equal (nth 4 (apt-cli *apt-sub* *apt-sub-argv*))
        '(((:register)) ((:wait) (:project) (:decode :opaque-1) (:deliver) (:ack)))))
(assert-event
 (equal (fn-pat-lookup :group (nth 5 (apt-cli *apt-pub* *apt-pub-argv*)))
        (fn-ak-text "mini.blocks")))
; Options of a looping role.
(assert-event
 (equal (nthcdr 6 (apt-cli *apt-sub* (append *apt-sub-argv*
                                             (list (fn-ak-text "--count") (fn-ak-text "3")
                                                   (fn-ak-text "--timeout") (fn-ak-text "5")))))
        '(5 3)))
(assert-event (equal (nthcdr 6 (apt-cli *apt-sub* *apt-sub-argv*)) '(30 0)))

; Teeth: every refusal named.
(assert-event (equal (apt-cli *apt-pub* (butlast *apt-pub-argv* 1)) '(:usage :argc)))
(assert-event (equal (apt-cli *apt-sub* (butlast *apt-sub-argv* 1)) '(:usage :argc)))
(assert-event (equal (apt-cli *apt-pub* (append *apt-pub-argv* (list (fn-ak-text "x"))))
                     '(:usage :argc)))
(assert-event (equal (apt-cli *apt-sub* (cons nil (cdr *apt-sub-argv*))) '(:usage :word)))
(assert-event (equal (apt-cli *apt-sub* (cons '(47 0) (cdr *apt-sub-argv*))) '(:usage :word)))
(assert-event (equal (apt-cli *apt-sub* (append *apt-sub-argv* (list (fn-ak-text "--timeout")
                                                                  (fn-ak-text "0"))))
                     '(:usage :option)))
(assert-event (equal (apt-cli *apt-sub* (append *apt-sub-argv* (list (fn-ak-text "--timeout")
                                                                  (fn-ak-text "3601"))))
                     '(:usage :option)))
(assert-event (equal (apt-cli *apt-sub* (append *apt-sub-argv* (list (fn-ak-text "--count"))))
                     '(:usage :option)))
(assert-event (equal (apt-cli (fn-ak-text "push") *apt-sub-argv*) '(:usage :role)))
(assert-event (equal (fn-pat-cli-plan (fn-ak-text "nosuch") *apt-sub* *apt-sub-argv*)
                     '(:usage :pattern)))

; pair: four roles from the same two verbs, the groups crossed.
(defconst *apt-pair* (fn-ak-text "pair"))
(assert-event
 (equal (nth 4 (fn-pat-cli-plan *apt-pair* (fn-ak-text "left-send") *apt-pub-argv*))
        '(((:encode :opaque-1) (:sign) (:author)) nil)))
(assert-event
 (equal (nth 4 (fn-pat-cli-plan *apt-pair* (fn-ak-text "right-recv") *apt-sub-argv*))
        '(((:register)) ((:wait) (:project) (:decode :opaque-1) (:deliver) (:ack)))))
(assert-event
 (equal (fn-pat-role-usage *apt-pair* (fn-pat-find (fn-ak-text "left-send")
                                                   (fn-pat-row-roles (fn-pat-find *apt-pair* *fn-pat-patterns*))))
        (append (fn-ak-text "  fn pattern pair left-send CONTROL GENERATION KEYS FORWARD FROM MSGID PAYLOAD SPOOL")
                '(10))))
(assert-event (equal (fn-pat-cli-plan *apt-pair* *apt-pub* *apt-pub-argv*) '(:usage :role)))
(assert-event (equal (car (fn-pat-cli-plan (fn-ak-text "help") nil nil)) :help))

; The usage text is the plans'.
(assert-event
 (equal (fn-pat-role-usage *apt-pubsub* (fn-pat-find *apt-pub* (fn-pat-row-roles (car *fn-pat-patterns*))))
        (append (fn-ak-text "  fn pattern pubsub pub CONTROL GENERATION KEYS TOPIC FROM MSGID PAYLOAD SPOOL")
                '(10))))

; The values check: nil on the example, the row's word on each refinement.
(defconst *apt-from* (fn-ak-text "Mini <mini@example.invalid>"))
(defconst *apt-group* (fn-ak-text "mini.blocks"))
(defconst *apt-msgid* (fn-ak-text "<b1.mini@example.invalid>"))
(assert-event (null (fn-pat-values-check *apt-pubsub* *apt-from* 1791115200 *apt-group* *apt-msgid*)))
(assert-event (fn-ak-rows-valuesp *fn-ak-v1-rows*
                                  (fn-pat-values *apt-pubsub* *apt-from* 1791115200
                                                 *apt-group* *apt-msgid*)))
(assert-event (equal (fn-pat-values-check *apt-pubsub* (fn-ak-text "not a mailbox") 0
                                          *apt-group* *apt-msgid*)
                     :from))
(assert-event (equal (fn-pat-values-check *apt-pubsub* *apt-from* 0
                                          (fn-ak-text "two,,commas") *apt-msgid*)
                     :groups))
(assert-event (equal (fn-pat-values-check *apt-pubsub* *apt-from* 0
                                          *apt-group* (fn-ak-text "no-brackets"))
                     :msgid))

; The Date row.
(assert-event (equal (fn-pat-date-text 1791115200) (fn-ak-text "Sun, 04 Oct 2026 12:00:00 +0000")))
(assert-event (equal (fn-pat-date-text 0) (fn-ak-text "Thu, 01 Jan 1970 00:00:00 +0000")))
(assert-event (equal (fn-pat-date-text 951825599) (fn-ak-text "Tue, 29 Feb 2000 11:59:59 +0000")))

; def-pattern refuses each malformed declaration.
(must-fail-checked
 (def-pattern bad-kind :kind :opaque-2 :roles ((p :posts g) (s :reads g)) :guarantee nil)
 :unchecked "def-pattern refuses an unknown kind at admission")
(must-fail-checked
 (def-pattern bad-unread :kind :opaque-1 :roles ((p :posts g) (s :reads h)) :guarantee nil)
 :unchecked "def-pattern refuses a group posted to and never read")
(must-fail-checked
 (def-pattern bad-dup :kind :opaque-1 :roles ((p :posts g) (p :reads g)) :guarantee nil)
 :unchecked "def-pattern refuses a repeated role name")
(must-fail-checked
 (def-pattern bad-verb :kind :opaque-1 :roles ((p :pushes g) (s :reads g)) :guarantee nil)
 :unchecked "def-pattern refuses a verb outside the vocabulary")
(must-fail-checked
 (def-pattern bad-word :kind :opaque-1 :roles ((p :posts g) (s :reads g)) :guarantee (:exactly-once))
 :unchecked "def-pattern refuses a guarantee word outside the vocabulary")
(must-fail-checked
 (def-pattern pubsub :kind :opaque-1 :roles ((p :posts g) (s :reads g)) :guarantee nil)
 :unchecked "def-pattern refuses a second declaration of a name")
; ... and admits a well-formed one (the refusals above are not a refusal of all).
(def-pattern ok-pattern :kind :opaque-1 :roles ((p :posts g) (s :reads g)) :guarantee nil)

; pipeline: the partitioned pull role needs INDEX < WORKERS <= 1024.
(defconst *apt-pipeline* (fn-ak-text "pipeline"))
(defconst *apt-pull-argv*
  (list (fn-ak-text "/s/control") (fn-ak-text "w-1") (fn-ak-text "1") (fn-ak-text "3")
        (fn-ak-text "jobs") (fn-ak-text "/out")))
(assert-event (apt-covers (fn-pat-cli-plan *apt-pipeline* (fn-ak-text "pull") *apt-pull-argv*)))
(assert-event
 (equal (nth 4 (fn-pat-cli-plan *apt-pipeline* (fn-ak-text "pull") *apt-pull-argv*))
        '(((:register)) ((:wait) (:project) (:decode :opaque-1) (:select) (:deliver) (:ack)))))
(assert-event
 (equal (fn-pat-cli-plan *apt-pipeline* (fn-ak-text "pull")
                         (update-nth 2 (fn-ak-text "3") *apt-pull-argv*))
        '(:usage :partition)))
(assert-event
 (equal (fn-pat-cli-plan *apt-pipeline* (fn-ak-text "pull")
                         (update-nth 3 (fn-ak-text "x") *apt-pull-argv*))
        '(:usage :partition)))
(assert-event
 (equal (fn-pat-cli-plan *apt-pipeline* (fn-ak-text "pull")
                         (update-nth 3 (fn-ak-text "1025") *apt-pull-argv*))
        '(:usage :partition)))
(assert-event (apt-covers (fn-pat-cli-plan *apt-pipeline* (fn-ak-text "push") *apt-pub-argv*)))
; A group pushed to and read only by a partitioned role is admitted.
(must-fail-checked
 (def-pattern bad-partition :kind :opaque-1 :roles ((p :posts g) (s :reads-partition h)) :guarantee (:partitioned))
 :unchecked "def-pattern refuses a partitioned reader of a group nobody posts to")

; ---------------------------------------------------------------------------
; fn-pat-cli-run-binds-every-step with its teeth (TEETH CONTRACT v1).  The
; keystone's own `let' carries its one antecedent, (equal (car cli) :run), so
; the claim has no labelled hypothesis: that antecedent has no counterexample
; to remove (fn-pat-cli-plan answers :usage and :help with a nil plan, whose
; needs are bound vacuously), and teeth-gate-owed.md records it as such.
(defteeth fn-pat-cli-run-binds-every-step
  :claim (() (let ((cli (fn-pat-cli-plan name role argv)))
               (implies (equal (car cli) :run)
                        (fn-pat-bindings-coverp (fn-pat-plan-needs (nth 4 cli))
                                                (nth 5 cli)))))
  :subject fn-pat-cli-plan
  :witness ((name *apt-pubsub*) (role *apt-sub*) (argv *apt-sub-argv*))
  :mutations ((covers-every-argument
               (:conclusion (let ((cli (fn-pat-cli-plan name role argv)))
                              (implies (equal (car cli) :run)
                                       (fn-pat-bindings-coverp *fn-pat-arg-order* (nth 5 cli)))))
               ((name *apt-pubsub*) (role *apt-pub*) (argv *apt-pub-argv*))
               :fault "an accepted command line claimed to bind every argument of the pattern language, not the plan's needs (a pub line binds no consumer)")))
