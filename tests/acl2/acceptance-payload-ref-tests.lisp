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
(include-book "held-rows-tests")

; lane history-columns-3: the readers take the history stobj fn-hist.
(defun fn-apr-foundp-hx (msgid s hist)
  ; fn-apr-foundp over a history stobj loaded with HIST (R holds when HIST is the history it reads).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist)))
        (mv (fn-apr-foundp msgid s fn-hist) fn-hist))
      ans)))
(defun fn-apr-payload-of-hx (msgid s hist)
  ; fn-apr-payload-of over a history stobj loaded with HIST (R holds when HIST is the history it reads).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist)))
        (mv (fn-apr-payload-of msgid s fn-hist) fn-hist))
      ans)))

; lane history-columns-3: the readers take the history stobj fn-hist.
(defun fn-apr-foundp-h (msgid s)
  ; fn-apr-foundp over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files s))) 0 fn-hist)))
        (mv (fn-apr-foundp msgid s fn-hist) fn-hist))
      ans)))
(defun fn-apr-payload-of-h (msgid s)
  ; fn-apr-payload-of over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files s))) 0 fn-hist)))
        (mv (fn-apr-payload-of msgid s fn-hist) fn-hist))
      ans)))

(defconst *apr-t-configs* (list *fn-cfg-default-record*))
(defconst *apr-t-wire*
  (list (fn-record-make 0 0 0 "<apr-0@example.invalid>" '(72 105 13 10)
                        '("fn.test") "o0" "s0" "e0" 4 841000000)
        (fn-record-make 1 1 1 "<apr-1@example.invalid>" '(89 111 13 10)
                        '("fn.test") "o1" "s1" "e1" 4 841000001)))
; The store retains held rows (records-flip): the open interns the decoded
; history (store-intern fn-intern-events, keyring nil at generation 0), so
; the two articles are rows at handles 0 and 1 of the open's arena.
(defconst *apr-t-records* (fn-hrt-rows *apr-t-wire* nil 0))
(assert-event (and (fn-held-p (car *apr-t-records*)) (fn-held-p (cadr *apr-t-records*))))
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
; by specification: the flip: the payload found through the reference is the
; article's handle (1); the bytes under it are the article's octets.
(assert-event (equal (fn-apr-payload-of-h "<apr-1@example.invalid>" *apr-t-s*) 1))
(assert-event (equal (fn-hrt-bytes *apr-t-wire*
                                   (fn-apr-payload-of-h "<apr-1@example.invalid>" *apr-t-s*))
                     '(89 111 13 10)))
(assert-event (equal (fn-apr-payload-of-h "<apr-1@example.invalid>" *apr-t-s*)
                     (fn-apr-field-payload "<apr-1@example.invalid>" *apr-t-s*)))
(assert-event (equal (fn-apr-payload-of-h "<apr-9@example.invalid>" *apr-t-s*) nil))
(assert-event (equal (fn-apr-field-payload "<apr-9@example.invalid>" *apr-t-s*) nil))
(assert-event (equal (fn-apr-foundp-h "<apr-0@example.invalid>" *apr-t-s*) t))
(assert-event (equal (fn-apr-foundp-h "<apr-9@example.invalid>" *apr-t-s*) nil))

; Hypothesis removal: R (lane history-columns-3; the store node's event
; index is retired).  The same Store at rest, read through a history stobj
; that is NOT its history (empty): the retained hypotheses hold (at rest, a
; string Message-ID), R fails, and the conclusion fails: the field holds the
; article's bytes, the stobj finds nothing.
(assert-event (fn-apr-store-at-restp *apr-t-s*))
(assert-event (stringp "<apr-1@example.invalid>"))
(assert-event (consp (fn-sf-records (fn-sn-files *apr-t-s*))))
(assert-event (not (equal (fn-apr-payload-of-hx "<apr-1@example.invalid>" *apr-t-s* nil)
                          (fn-apr-field-payload "<apr-1@example.invalid>" *apr-t-s*))))
(assert-event (not (equal (fn-apr-foundp-hx "<apr-1@example.invalid>" *apr-t-s* nil)
                          (if (fn-find-article "<apr-1@example.invalid>"
                                               (fn-stx-store (fn-sn-node *apr-t-s*)))
                              t nil))))
