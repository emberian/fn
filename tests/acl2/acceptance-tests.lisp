; Independent executable traces for the abstract acceptance machine.
; These exercise logical transitions, not disk persistence or NNTP bytes.
(in-package "ACL2")
(include-book "../../books/acceptance")

(defconst *test-groups* '("fn.letters" "fn.test"))
(defconst *test-id-a* "<a@example.invalid>")
(defconst *test-id-b* "<b@example.invalid>")
(defconst *test-payload* '(72 105 13 10))
(defconst *test-empty* (fn-initial-state *test-groups*))

(assert-event (fn-statep *test-empty*))
(assert-event (equal (fn-state-articles *test-empty*) nil))
(assert-event (not (fn-statep '(nil nil nil 0))))
(assert-event (not (fn-statep (append *test-empty* '(hidden-field)))))
(assert-event (not (fn-statep '(nil nil nil 0 nil nil . hidden-tail))))

; Input policy rejects the entire local cross-post.
(assert-event
 (equal (fn-accept-prepare *test-empty* 7 *test-id-a* *test-payload*
                           '("fn.letters" "unknown"))
        *test-empty*))
(assert-event
 (equal (fn-accept-prepare *test-empty* 7 *test-id-a* *test-payload*
                           '("fn.letters" "fn.letters"))
        *test-empty*))
(assert-event
 (equal (fn-accept-prepare *test-empty* 7 *test-id-a* '(256) *test-groups*)
        *test-empty*))

(defconst *test-prepared*
  (fn-accept-prepare *test-empty* 7 *test-id-a* *test-payload* *test-groups*))
(assert-event (fn-statep *test-prepared*))
(assert-event (equal (fn-state-articles *test-prepared*) nil))
(assert-event (equal (fn-state-nexts *test-prepared*)
                     (fn-state-nexts *test-empty*)))
(assert-event (equal (fn-state-next-txid *test-prepared*) 1))
(assert-event
 (not (fn-pendingp *test-groups* (fn-state-nexts *test-empty*) 1
                   (append (fn-state-pending *test-prepared*) 'hidden-tail))))
(assert-event
 (equal (fn-pending-memberships (fn-state-pending *test-prepared*))
        '(("fn.letters" . 1) ("fn.test" . 1))))

; Wrong transaction, wrong generation, and arbitrary status do not publish.
(assert-event
 (equal (fn-accept-complete *test-prepared* 19 7 :durable) *test-prepared*))
(assert-event
 (equal (fn-accept-complete *test-prepared* 0 8 :durable) *test-prepared*))
(assert-event
 (equal (fn-accept-complete *test-prepared* 0 7 :nonsense) *test-prepared*))

(defconst *test-committed* (fn-accept-complete *test-prepared* 0 7 :durable))
(assert-event (fn-statep *test-committed*))
(assert-event (equal (len (fn-state-articles *test-committed*)) 1))
(assert-event
 (not (fn-articlep *test-groups*
                   (append (car (fn-state-articles *test-committed*))
                           'hidden-tail))))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *test-id-a* (fn-state-articles *test-committed*)))
        '(("fn.letters" . 1) ("fn.test" . 1))))
(assert-event
 (equal (fn-article-payload
         (fn-find-article *test-id-a* (fn-state-articles *test-committed*)))
        *test-payload*))
(assert-event
 (equal (fn-article-pin
         (fn-find-article *test-id-a* (fn-state-articles *test-committed*)))
        t))
(assert-event (equal (fn-state-nexts *test-committed*)
                     '(("fn.letters" . 2) ("fn.test" . 2))))

; A lost response/retry and a conflicting payload cannot overwrite or allocate.
(assert-event
 (equal (fn-accept-prepare *test-committed* 7 *test-id-a* *test-payload* *test-groups*)
        *test-committed*))
(assert-event
 (equal (fn-accept-prepare *test-committed* 7 *test-id-a* '(69 118 105 108) *test-groups*)
        *test-committed*))
(assert-event
 (equal (fn-accept-prepare *test-committed* 7 *test-id-a* *test-payload* '("fn.test"))
        *test-committed*))

(defconst *test-second-prepared*
  (fn-accept-prepare *test-committed* 7 *test-id-b* *test-payload* '("fn.letters")))
(assert-event (fn-statep *test-second-prepared*))
(assert-event
 (equal (fn-accept-complete *test-second-prepared* 0 7 :durable)
        *test-second-prepared*))
(defconst *test-second-committed*
  (fn-accept-complete *test-second-prepared* 1 7 :durable))
(assert-event (fn-statep *test-second-committed*))
(assert-event
 (equal (fn-find-article *test-id-a* (fn-state-articles *test-second-committed*))
        (fn-find-article *test-id-a* (fn-state-articles *test-committed*))))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *test-id-b* (fn-state-articles *test-second-committed*)))
        '(("fn.letters" . 2))))

; Indeterminate result preserves the proposal and fences all ordinary completion.
(defconst *test-fenced*
  (fn-accept-complete *test-second-prepared* 1 7 :indeterminate))
(assert-event (fn-statep *test-fenced*))
(assert-event (equal (fn-state-fenced *test-fenced*) t))
(assert-event
 (equal (fn-state-pending *test-fenced*) (fn-state-pending *test-second-prepared*)))
(assert-event
 (equal (fn-accept-prepare *test-fenced* 7 "<c@example.invalid>" '(1) '("fn.test"))
        *test-fenced*))
(assert-event (equal (fn-accept-complete *test-fenced* 1 7 :durable) *test-fenced*))
(assert-event (equal (fn-accept-complete *test-fenced* 1 7 :aborted) *test-fenced*))
(assert-event (equal (fn-accept-recover *test-fenced* 0 7 :committed) *test-fenced*))
(assert-event (equal (fn-accept-recover *test-fenced* 1 8 :absent) *test-fenced*))
(assert-event (equal (fn-accept-recover *test-fenced* 1 7 :nonsense) *test-fenced*))

(defconst *test-recovered-committed* (fn-accept-recover *test-fenced* 1 7 :committed))
(assert-event (equal *test-recovered-committed* *test-second-committed*))
(assert-event (fn-statep *test-recovered-committed*))
(assert-event
 (equal (fn-accept-prepare *test-recovered-committed* 7 *test-id-b* *test-payload* '("fn.letters"))
        *test-recovered-committed*))

(defconst *test-recovered-absent* (fn-accept-recover *test-fenced* 1 7 :absent))
(assert-event (fn-statep *test-recovered-absent*))
(assert-event
 (equal (fn-state-articles *test-recovered-absent*) (fn-state-articles *test-committed*)))
(assert-event (equal (fn-state-next-txid *test-recovered-absent*) 2))
(defconst *test-after-absent*
  (fn-accept-prepare *test-recovered-absent* 7 *test-id-b* *test-payload* '("fn.letters")))
(assert-event (fn-statep *test-after-absent*))
(assert-event (equal (fn-pending-txid (fn-state-pending *test-after-absent*)) 2))
(assert-event
 (equal (fn-accept-complete *test-after-absent* 1 7 :durable) *test-after-absent*))

; Successful known abort also leaves the transaction identity consumed.
(defconst *test-aborted* (fn-accept-complete *test-prepared* 0 7 :aborted))
(assert-event (fn-statep *test-aborted*))
(assert-event (equal (fn-state-next-txid *test-aborted*) 1))
(assert-event (equal (fn-state-articles *test-aborted*) nil))
(defconst *test-after-abort*
  (fn-accept-prepare *test-aborted* 7 *test-id-b* *test-payload* '("fn.test")))
(assert-event (fn-statep *test-after-abort*))
(assert-event (equal (fn-pending-txid (fn-state-pending *test-after-abort*)) 1))
(assert-event
 (equal (fn-accept-complete *test-after-abort* 0 7 :durable) *test-after-abort*))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *test-id-b*
                          (fn-state-articles
                           (fn-accept-complete *test-after-abort* 1 7 :durable))))
        '(("fn.test" . 1))))

; Case in a Message-ID is significant, including its domain-looking part.
(defconst *test-case-prepared*
  (fn-accept-prepare *test-committed* 7 "<a@EXAMPLE.invalid>" *test-payload* '("fn.test")))
(assert-event (fn-statep *test-case-prepared*))
(assert-event (consp (fn-state-pending *test-case-prepared*)))
(defconst *test-case-committed* (fn-accept-complete *test-case-prepared* 1 7 :durable))
(assert-event (fn-statep *test-case-committed*))
(assert-event (equal (len (fn-state-articles *test-case-committed*)) 2))
