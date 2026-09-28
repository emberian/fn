; fn: one hostile reader archive, shared by test books.
;
; A committed, served reader view holding, together, every article
; condition the reader dispatcher (fn-nntp-command-pinned) answers specially.
; Built the way a node builds one: seven articles through fn-accept-prepare
; / fn-accept-complete (arena handles 0..6, *hra-payloads* their octets),
; then the control fold (fn-ctl-articles-withdrawals over the raw list, the
; verdicts and the Store history's rows) and the visible state and pin the
; served connection carries (fn-ctl-visible-state, fn-ctl-pin).
;
;   handle  article                 numbers              condition
;   0  T <t@example.invalid>  fn.mod.a 1          WITHDRAWN (cancelled by C)
;   1  O <o@example.invalid>  fn.mod.a 2          ordinary
;   2  C <c@example.invalid>  control.cancel 1    CONTROL MESSAGE: P cancels
;                                                 T, verified, executed
;   3  D <d@example.invalid>  control.cancel 2    control message; its target
;                                                 U never arrived (owed)
;   4  R <r@example.invalid>  fn.mod.a 3          RECLAIMED: the arena holds
;                                                 its tombstone
;   5  F <f@example.invalid>  fn.mod.a 4          UNFRAMED: no blank line
;   6  X <x@example.invalid>  fn.mod.a 5, fn.misc 1   CROSS-POSTED
;
; Constants: *hra-archive* (the visible served state), *hra-index* (trie,
; group index, control pin), *hra-verdicts*, *hra-env*, *hra-session*
; (opened on the archive, fn.mod.a selected), *hra-payloads* (the arena).
; Each condition is a named theorem stated with the predicate the arm
; tests; the replies are witnessed through fn-nntp-command-pinned
; (`hra-reply').  The one step no accept path reaches is the tombstone:
; reclamation rewrites a payload in place, so handle 4's octets are the
; tombstone from the start (the arena after reclamation, not before).
(in-package "ACL2")
(include-book "control-served-tests")    ; csv-octets, csv-row, the P/Q verdicts
(include-book "../../books/nntp")
(include-book "arena-lift")

(defun hra-oct (text) (fn-nntp-string-octets text))
(defun hra-lines (lines)
  (if (consp lines)
      (append (hra-oct (car lines)) '(13 10) (hra-lines (cdr lines)))
    nil))
(defun hra-plain (msgid groups)
  (hra-lines (list (concatenate 'string "Message-ID: " msgid)
                   (concatenate 'string "Newsgroups: " groups)
                   "From: p@example.invalid" "Subject: s" "" "body")))
(defun hra-cancel (msgid target)
  (csv-octets (list "From: p@example.invalid" "Newsgroups: control.cancel"
                    (concatenate 'string "Message-ID: " msgid)
                    "Subject: cmsg cancel"
                    (concatenate 'string "Control: cancel " target))))

(defconst *hra-tombstone* (append *fn-rcl-magic* (make-list 81 :initial-element 0)))
(defconst *hra-payloads*
  (list (hra-plain "<t@example.invalid>" "fn.mod.a")
        (hra-plain "<o@example.invalid>" "fn.mod.a")
        (hra-cancel "<c@example.invalid>" "<t@example.invalid>")
        (hra-cancel "<d@example.invalid>" "<u@example.invalid>")
        *hra-tombstone*
        (hra-lines (list "Message-ID: <f@example.invalid>" "Newsgroups: fn.mod.a"
                         "Subject: no body separator"))
        (hra-plain "<x@example.invalid>" "fn.mod.a,fn.misc")))
(defconst *hra-posts*
  '(("<t@example.invalid>" "fn.mod.a") ("<o@example.invalid>" "fn.mod.a")
    ("<c@example.invalid>" "control.cancel") ("<d@example.invalid>" "control.cancel")
    ("<r@example.invalid>" "fn.mod.a") ("<f@example.invalid>" "fn.mod.a")
    ("<x@example.invalid>" "fn.mod.a" "fn.misc")))

; Accept post K at handle K, transaction K+1, one second apart.
(defun hra-accept (posts k st)
  (declare (xargs :measure (len posts)))
  (if (consp posts)
      (hra-accept (cdr posts) (1+ (nfix k))
                  (fn-accept-complete
                   (fn-accept-prepare st (1+ (nfix k)) (car (car posts)) (nfix k)
                                      (cdr (car posts)) (+ 841000000 (* 1000 (nfix k))))
                   (nfix k) (1+ (nfix k)) :durable))
    st))
(defconst *hra-raw-archive*
  (hra-accept *hra-posts* 0 (fn-initial-state '("fn.mod.a" "control.cancel" "fn.misc"))))
(defconst *hra-raw* (fn-state-articles *hra-raw-archive*))

(defun hra-rows (posts payloads k)
  (if (and (consp posts) (consp payloads))
      (cons (csv-row k (car (car posts)) (car payloads) (cdr (car posts)))
            (hra-rows (cdr posts) (cdr payloads) (1+ (nfix k))))
    nil))
(defconst *hra-hist* (hra-rows *hra-posts* *hra-payloads* 0))
(defconst *hra-verdicts*
  (list (cons "<t@example.invalid>" *csv-p-verified*)
        (cons "<c@example.invalid>" *csv-p-verified*)
        (cons "<d@example.invalid>" *csv-q-verified*)))
(defconst *hra-ws* (fn-ctl-articles-withdrawals *hra-raw* *hra-verdicts* *hra-hist* nil))
(defconst *hra-archive* (fn-ctl-visible-state *hra-raw-archive* *hra-ws* *hra-verdicts*))
(defconst *hra-visible* (fn-state-articles *hra-archive*))
(defconst *hra-withdrawn* (fn-ctl-withdrawn-articles *hra-raw* *hra-ws* *hra-verdicts*))
(defconst *hra-index*
  (fn-gidx-pin-with-control (fn-midx-build *hra-visible*) (fn-gidx-build *hra-visible*)
                            (fn-ctl-pin *hra-withdrawn* *hra-ws*)))
(defconst *hra-session*
  (fn-nntp-set-cursor (fn-nntp-open-session *hra-archive*) "fn.mod.a" nil))
(defconst *hra-env* (fn-nntp-env nil nil nil))

(defun hra-article (msgid) (fn-find-article msgid *hra-raw*))

; -----------------------------------------------------------------------------
; The conditions.

; The archives are committed states; the served one is a projection, so
; the session opened on it carries a positive projection verdict.
(defthm hra-archive-is-committed
  (and (fn-statep *hra-raw-archive*)
       (equal (len *hra-raw*) 7)
       (fn-nntp-projectionp *hra-archive*)
       (fn-nntp-session-projected *hra-session*))
  :rule-classes nil)

; WITHDRAWN: the pin's W is exactly T, the served archive does not hold T,
; and the 423/430 withdrawn arms' own tests hold.
(defthm hra-t-is-withdrawn
  (and (equal *hra-withdrawn* (list (hra-article "<t@example.invalid>")))
       (not (member-equal (hra-article "<t@example.invalid>") *hra-visible*))
       (equal (len *hra-visible*) 6)
       (fn-nntp-number-withdrawn-p *hra-session* *hra-archive* *hra-index* (hra-oct "1"))
       (fn-nntp-msgid-withdrawn-p *hra-index* (hra-oct "<t@example.invalid>")))
  :rule-classes nil)

; CANCELLED and CONTROL: T's withdrawal is C's executed cancel on the author
; basis; D (a cancel whose target never arrived) is owed; both are served.
(defthm hra-cancel-and-control
  (and (equal (len *hra-ws*) 2)
       (member-equal (hra-article "<c@example.invalid>") *hra-visible*)
       (member-equal (hra-article "<d@example.invalid>") *hra-visible*)
       (equal (fn-ctl-target-octets (nth 2 *hra-payloads*)) "<t@example.invalid>")
       (equal (fn-ctl-control-status (hra-article "<c@example.invalid>") (nth 2 *hra-payloads*)
                                     *hra-visible* *hra-withdrawn* *hra-ws* *hra-verdicts*)
              (list :executed :author))
       (equal (fn-ctl-control-status (hra-article "<d@example.invalid>") (nth 3 *hra-payloads*)
                                     *hra-visible* *hra-withdrawn* *hra-ws* *hra-verdicts*)
              (list :owed)))
  :rule-classes nil)

; RECLAIMED, UNFRAMED, CROSS-POSTED: over the bytes the arena holds.
(defthm hra-payload-conditions
  (and (equal (fn-article-payload (hra-article "<r@example.invalid>")) 4)
       (fn-rcl-tombstonep (nth 4 *hra-payloads*))
       (equal (fn-article-payload (hra-article "<f@example.invalid>")) 5)
       (not (fn-rcl-tombstonep (nth 5 *hra-payloads*)))
       (not (fn-nntp-framed-of-bytes (nth 5 *hra-payloads*)))
       (fn-nntp-framed-of-bytes (nth 6 *hra-payloads*))
       (equal (fn-article-groups (hra-article "<x@example.invalid>")) '("fn.mod.a" "fn.misc"))
       (equal (fn-nntp-find-group-number "fn.mod.a" 5 *hra-visible*)
              (hra-article "<x@example.invalid>"))
       (equal (fn-nntp-find-group-number "fn.misc" 1 *hra-visible*)
              (hra-article "<x@example.invalid>")))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The replies, through the reader dispatcher itself.

(defun hra-run (session line fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-nntp-command-pinned session *hra-archive* *hra-index* *hra-verdicts* *hra-env*
                          (fn-nntp-tokenize (hra-oct line)) fn-arena))
(bpr-lift hra-run 2)

(defun hra-reply (session line)
  (declare (xargs :verify-guards nil))
  (in-arena-hra-run *hra-payloads* session line))

(defun hra-single (text) (fn-nntp-single *hra-session* text))

(assert-event (equal (hra-reply *hra-session* "ARTICLE 1") (hra-single "423 withdrawn")))
(assert-event (equal (hra-reply *hra-session* "ARTICLE <t@example.invalid>")
                     (hra-single "430 withdrawn")))
(assert-event (equal (hra-reply *hra-session* "ARTICLE 3") (hra-single "423 article reclaimed")))
(assert-event (equal (hra-reply *hra-session* "BODY 3") (hra-single "423 article reclaimed")))
(assert-event (equal (hra-reply *hra-session* "ARTICLE <r@example.invalid>")
                     (hra-single "430 article reclaimed")))
(assert-event (equal (hra-reply *hra-session* "ARTICLE 4")
                     (hra-single "503 stored article framing unavailable")))
(assert-event (equal (hra-reply *hra-session* "HEAD <f@example.invalid>")
                     (hra-single "503 stored article framing unavailable")))
; The framing arm is load-bearing only where the payload is read: STAT 4 is
; not refused.
(assert-event (not (equal (hra-reply *hra-session* "STAT 4")
                          (hra-single "503 stored article framing unavailable"))))
; O, served and framed, is not refused by either arm.
(assert-event (not (equal (hra-reply *hra-session* "ARTICLE 2") (hra-single "423 withdrawn"))))

; HDR :fn-control over the control messages: C's executed withdrawal of T,
; D owed.
(defun hra-hdr-line (text)
  (fn-nntp-multi *hra-session* (fn-nntp-hdr-initial nil)
                 (list (fn-nntp-hdr-line (fn-nntp-decimal-field 0) (hra-oct text)))))
(assert-event (equal (hra-reply *hra-session* "HDR :fn-control <c@example.invalid>")
                     (hra-hdr-line "executed withdrawal <t@example.invalid> author")))
(assert-event (equal (hra-reply *hra-session* "HDR :fn-control <d@example.invalid>")
                     (hra-hdr-line "owed")))
