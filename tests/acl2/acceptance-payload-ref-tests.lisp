; Teeth for books/acceptance-payload-ref.
;
; The witness is a Store opened from a two-article history through the
; host's open (fn-sco-finalize of the extended capture, the pair
; fn-owner-recover installs): at rest, the relation holds, and the record's
; payload found through the event index is the acceptance article's, for a
; present and for an absent Message-ID.  The hypothesis witness is the same
; Store with its event index dropped: the article is still there, the index
; finds nothing, and the reader through the reference and the field differ.
(in-package "ACL2")
(include-book "../../books/acceptance-payload-ref")
; The host's open (fn-sco-finalize), for the witness only.
(include-book "../../books/store-checkpoint-open")

(defconst *apr-t-configs* (list *fn-cfg-default-record*))
(defconst *apr-t-records*
  (list (fn-record-make 0 0 0 "<apr-0@example.invalid>" '(72 105 13 10)
                        '("fn.test") "o0" "s0" "e0" 4 841000000)
        (fn-record-make 1 1 1 "<apr-1@example.invalid>" '(89 111 13 10)
                        '("fn.test") "o1" "s1" "e1" 4 841000001)))
(defconst *apr-t-open*
  (fn-sco-finalize (fn-sco-extend (fn-sco-capture *apr-t-configs* nil)
                                  *apr-t-configs* *apr-t-records*)
                   *apr-t-configs* 2))
(defconst *apr-t-s* (cadr *apr-t-open*))

; The open succeeded and the Store is at rest.
(assert-event (equal (car *apr-t-open*) :ok))
(assert-event (fn-apr-store-at-restp *apr-t-s*))

; The relation, both halves, on the reached Store.
(assert-event (fn-apr-refsp (fn-stx-store (fn-sn-node *apr-t-s*))
                            (fn-sf-records (fn-sn-files *apr-t-s*))))
(assert-event (fn-apr-recordedp (fn-sf-records (fn-sn-files *apr-t-s*))
                                (fn-stx-store (fn-sn-node *apr-t-s*))))

; fn-apr-replay-establishes-refs on the replay of this history: the
; antecedent (the replay succeeded) and both halves of the conclusion.
(defconst *apr-t-replay* (fn-replay '("fn.letters" "fn.test") 1048576 *apr-t-records*))
(assert-event (fn-replay-okp *apr-t-replay*))
(assert-event (equal (len (fn-stx-store (fn-replay-result-node *apr-t-replay*))) 2))
(assert-event (fn-apr-refsp (fn-stx-store (fn-replay-result-node *apr-t-replay*))
                            *apr-t-records*))
(assert-event (fn-apr-recordedp *apr-t-records*
                                (fn-stx-store (fn-replay-result-node *apr-t-replay*))))

; The keystone's antecedent and conclusion, present and absent.
(assert-event (equal (fn-apr-payload-of "<apr-1@example.invalid>" *apr-t-s*)
                     '(89 111 13 10)))
(assert-event (equal (fn-apr-payload-of "<apr-1@example.invalid>" *apr-t-s*)
                     (fn-apr-field-payload "<apr-1@example.invalid>" *apr-t-s*)))
(assert-event (equal (fn-apr-payload-of "<apr-9@example.invalid>" *apr-t-s*) nil))
(assert-event (equal (fn-apr-field-payload "<apr-9@example.invalid>" *apr-t-s*) nil))
(assert-event (equal (fn-apr-foundp "<apr-0@example.invalid>" *apr-t-s*) t))
(assert-event (equal (fn-apr-foundp "<apr-9@example.invalid>" *apr-t-s*) nil))

; Hypothesis removal: fn-apr-store-at-restp.  The same Store with its event
; index emptied keeps the retained hypothesis (a string Message-ID), fails
; the omitted one (the index no longer corresponds), and the conclusion
; fails: the field holds the article's bytes, the index finds nothing.
(defconst *apr-t-unindexed*
  (update-nth 13 nil *apr-t-s*))
(assert-event (equal (fn-stx-store (fn-sn-node *apr-t-unindexed*))
                     (fn-stx-store (fn-sn-node *apr-t-s*))))
(assert-event (stringp "<apr-1@example.invalid>"))
(assert-event (not (fn-apr-store-at-restp *apr-t-unindexed*)))
(assert-event (not (equal (fn-apr-payload-of "<apr-1@example.invalid>" *apr-t-unindexed*)
                          (fn-apr-field-payload "<apr-1@example.invalid>"
                                                *apr-t-unindexed*))))
(assert-event (not (equal (fn-apr-foundp "<apr-1@example.invalid>" *apr-t-unindexed*)
                          (if (fn-find-article "<apr-1@example.invalid>"
                                               (fn-stx-store (fn-sn-node *apr-t-unindexed*)))
                              t nil))))
