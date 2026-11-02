; D6 evidence: the teeth of owed-cursor.lisp's keystones (docs/d-machines-
; nntp.md section 15.7). Until the cursor serves (D6 1/n), the teeth check the
; reference against hand-written replies (RFC 3977, H's model), that each
; negative case is caught, and that the seeded store publishes through C-S3:
; the served core answers the interim 503 then, so the rows stay owed.
; Run: sh tools/certify.sh tests/cursor-unit.lisp
(in-package "ACL2")
(include-book "../books/owed-cursor")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-cru-groups* (fn2-profile-get :groups *fn2-cursor-profile*))
(defun fn2-cru-tab () (declare (xargs :verify-guards nil)) (coerce (list (code-char 9)) 'string))
(defun fn2-cru-line (subject mid)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list subject (fn2-cru-tab) "a@example.invalid" (fn2-cru-tab) "Fri, 30 Oct 2026 12:00:00 +0000"
                     (fn2-cru-tab) mid (fn2-cru-tab) "" (fn2-cru-tab) "120" (fn2-cru-tab) "1")))
(defconst *fn2-cru-seeds*
  (list (list 1 "<a@example.invalid>" (fn2-cru-line "one" "<a@example.invalid>"))
        (list 1 "<b@example.invalid>" (fn2-cru-line "two" "<b@example.invalid>"))
        (list 1 "<c@example.invalid>" (fn2-cru-line "three" "<c@example.invalid>"))))
(assert-event (fn2-csp-seedsp *fn2-cru-seeds* *fn2-cru-groups* nil))

; One transcript, every covered command positive and refused.
(defconst *fn2-cru-lines*
  '("LIST" "NEXT" "STAT" "OVER" "LISTGROUP" "GROUP nope.nope" "GROUP local.empty" "NEXT" "GROUP local.test" "STAT"
    "NEXT" "NEXT" "NEXT" "LAST" "LAST" "LAST" "STAT 9" "STAT <b@example.invalid>" "STAT <z@example.invalid>" "LISTGROUP"
    "LISTGROUP local.test 2-" "LIST COUNTS" "LIST newsgroups" "OVER 2-3" "OVER 7-9" "XOVER 7-9" "OVER"
    "OVER <c@example.invalid>" "ARTICLE" "HEAD 2" "BODY <b@example.invalid>" "ARTICLE 9"
    "HEAD <z@example.invalid>" "QUIT"))
(assert-event (fn2-csp-linesp *fn2-cru-lines*))
(defun fn2-cru-ov (n subject mid)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list (fn2-csp-str n) (fn2-cru-tab) (fn2-cru-line subject mid))))
(defun fn2-cru-expected ()
  (declare (xargs :verify-guards nil))
  (list "215 list of active newsgroups follows" "local.empty 0 1 y" "local.test 3 1 y" "."
        "412 no newsgroup selected" "412 no newsgroup selected" "412 no newsgroup selected" "412 no newsgroup selected"
        "411 no such newsgroup" "211 0 1 0 local.empty" "420 no current article"
        "211 3 1 3 local.test" "223 1 <a@example.invalid> retrieved"
        "223 2 <b@example.invalid> retrieved" "223 3 <c@example.invalid> retrieved" "421 no next article"
        "223 2 <b@example.invalid> retrieved" "223 1 <a@example.invalid> retrieved" "422 no previous article"
        "423 no article with that number" "223 0 <b@example.invalid> retrieved" "430 no article with that message-id"
        "211 3 1 3 local.test list follows" "1" "2" "3" "."
        "211 3 1 3 local.test list follows" "2" "3" "."
        "215 list of active newsgroups follows" "local.empty 0 1 0 y" "local.test 3 1 3 y" "."
        "215 list of newsgroups follows" "local.empty (no description)" "local.test (no description)" "."
        "224 overview information follows" (fn2-cru-ov 2 "two" "<b@example.invalid>") (fn2-cru-ov 3 "three" "<c@example.invalid>") "."
        "423 no articles in that range" "420 no article(s) selected"
        "224 overview information follows" (fn2-cru-ov 1 "one" "<a@example.invalid>") "."
        "224 overview information follows" (fn2-cru-ov 3 "three" "<c@example.invalid>") "."
        "220 1 <a@example.invalid> article follows"
        "From: a@example.invalid" "Subject: one" "Date: Fri, 30 Oct 2026 12:00:00 +0000"
        "Message-ID: <a@example.invalid>" "" "xxxxx" "."
        "221 2 <b@example.invalid> headers follow"
        "From: a@example.invalid" "Subject: two" "Date: Fri, 30 Oct 2026 12:00:00 +0000"
        "Message-ID: <b@example.invalid>" "."
        "222 0 <b@example.invalid> body follows" "xxxxx" "."
        "423 no article with that number" "430 no article with that message-id"
        "205 closing connection"))
(defun fn2-cru-expected-wire ()
  (declare (xargs :verify-guards nil))
  (list (fn2-cw-crlf-octets (cons "200 fn-nntp experimental server ready" (fn2-cru-expected))) t))

(defun fn2-cru-subst (new old xs)
  (declare (xargs :verify-guards nil))
  (if (atom xs) nil (cons (if (equal (car xs) old) new (car xs)) (fn2-cru-subst new old (cdr xs)))))
; reply-exact. Positive: the reference gives the hand-written replies.
(defun fn2-cursor-test-spec ()
  (declare (xargs :verify-guards nil))
  (equal (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-lines*) (fn2-cru-expected-wire)))
; Negative: an empty group answered 211 0 0 0 (LOW not high + 1), and a
; reader that saw one entry past its view (a fourth article), both differ.
(defun fn2-cursor-test-spec-negative ()
  (declare (xargs :verify-guards nil))
  (let ((want (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-lines*)))
    (and (not (equal want (list (fn2-cw-crlf-octets (cons "200 fn-nntp experimental server ready"
                                                          (fn2-cru-subst "211 0 0 0 local.empty" "211 0 1 0 local.empty"
                                                                        (fn2-cru-expected))))
                                t)))
         (not (equal want (fn2-cursor-spec-wire *fn2-cru-groups*
                                                (append *fn2-cru-seeds* (list (list 1 "<d@example.invalid>"
                                                                                   (fn2-cru-line "four" "<d@example.invalid>"))))
                                                *fn2-cru-lines*))))))
; The subject runs: the seeds publish through C-S3 (seeded :ok), the core
; does not stop, and the cursor serves GROUP (D6 1/n).
(defun fn2-cursor-test-seeded ()
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-cursor-wire-run *fn2-cursor-profile* *fn2-cru-seeds*
                                (list (list (fn2-cw-crlf-octets '("GROUP local.test" "QUIT")) nil)))))
    (and (or (eq (nth 0 r) :ok) (cw "seeded ~x0~%" (nth 0 r)))
         (equal (nth 3 r) 0)
         (or (equal (car (nth 2 r))
                    (list (fn2-cw-crlf-octets '("200 fn-nntp experimental server ready"
                                                "211 3 1 3 local.test" "205 closing connection"))
                          t))
             (cw "wire ~x0~%" (car (nth 2 r)))))))

; range-cost. Positive: OVER 1-2147483647 (the grammar's article-number cap) over three entries is three rows
; in the reference, and the bound it allows is a constant plus 16 per row.
(defun fn2-cursor-test-range-cost ()
  (declare (xargs :verify-guards nil))
  (let ((lines (fn2-cursor-over-lines 1 2147483647)))
    (and (fn2-csp-linesp lines)
         (equal (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* lines)
                (list (fn2-cw-crlf-octets (list "200 fn-nntp experimental server ready" "211 3 1 3 local.test"
                                                "224 overview information follows"
                                                (fn2-cru-ov 1 "one" "<a@example.invalid>") (fn2-cru-ov 2 "two" "<b@example.invalid>")
                                                (fn2-cru-ov 3 "three" "<c@example.invalid>") "." "205 closing connection"))
                      t))
         (equal (+ *fn2-cursor-visits-base* (* *fn2-cursor-visits-per-entry* 3)) 112))))
; Negative: a cursor that steps every number of the range visits at least
; once per number, which the bound refuses for this range.
(defun fn2-cursor-test-range-cost-negative ()
  (declare (xargs :verify-guards nil))
  (< (+ *fn2-cursor-visits-base* (* *fn2-cursor-visits-per-entry* 3)) (- 2147483647 1)))

; view-pinned. Positive: the reference reads only the state at the pin.
; Negative: a reader without the position limit would see the later
; publication (the reference over the union differs).
(defconst *fn2-cru-later* (list (list 1 "<d@example.invalid>" (fn2-cru-line "four" "<d@example.invalid>"))))
(defconst *fn2-cru-pinned-lines* '("GROUP local.test" "OVER 1-" "NEXT" "NEXT" "NEXT" "LAST" "STAT 3" "QUIT"))
(defun fn2-cursor-test-pinned ()
  (declare (xargs :verify-guards nil))
  (and (fn2-csp-seedsp (append *fn2-cru-seeds* *fn2-cru-later*) *fn2-cru-groups* nil)
       (fn2-csp-linesp *fn2-cru-pinned-lines*) (fn2-csp-no-repin-p (cdr *fn2-cru-pinned-lines*))
       (let ((r (fn2-cursor-serve-run *fn2-cursor-profile* *fn2-cru-seeds* *fn2-cru-later*
                                (list (list (fn2-cw-crlf-octets *fn2-cru-pinned-lines*) nil)))))
         ;; the later seed was published while the client read
         (or (eq (nth 0 r) :ok) (cw "pinned seeded ~x0~%" (nth 0 r))))))
(defun fn2-cursor-test-pinned-negative ()
  (declare (xargs :verify-guards nil))
  (not (equal (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-pinned-lines*)
              (fn2-cursor-spec-wire *fn2-cru-groups* (append *fn2-cru-seeds* *fn2-cru-later*) *fn2-cru-pinned-lines*))))

;; Served = reference (D6 1/n-b) over the transcript less OVER <id> (the
;; article's number in the group comes with the transaction's address
;; entries), whole and in small chunks.
(defconst *fn2-cru-served-lines* *fn2-cru-lines*)
(defun fn2-cursor-test-served (sizes)
  (declare (xargs :verify-guards nil))
  (let ((got (fn2-cursor-wire-solo *fn2-cru-seeds* *fn2-cru-served-lines* sizes))
        (want (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-served-lines*)))
    (or (equal got want) (cw "served ~x0~%want ~x1~%" got want))))
;; LIST over a directory whose rows span pages: five groups of 200-octet
;; names (two rows a page of a 1,024-octet TX after its 256-octet key area),
;; so the scan resumes from the key TX keeps across every page.
(defun fn2-cru-long-name (c)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list "long." (coerce (make-list 190 :initial-element #\x) 'string) "." (coerce (list c) 'string))))
(defconst *fn2-cru-long-groups*
  (list (cons (fn2-cru-long-name #\c) 3) (cons (fn2-cru-long-name #\a) 1) (cons (fn2-cru-long-name #\e) 5)
        (cons (fn2-cru-long-name #\b) 2) (cons (fn2-cru-long-name #\d) 4)))
(defconst *fn2-cru-long-lines* '("LIST" "LIST COUNTS" "LIST NEWSGROUPS" "GROUP local.none" "QUIT"))
(defun fn2-cursor-test-list-pages ()
  (declare (xargs :verify-guards nil))
  (let* ((profile (put-assoc-equal :groups *fn2-cru-long-groups* *fn2-cursor-profile*))
         (r (fn2-cursor-serve-run profile nil nil (list (list (fn2-cw-crlf-octets *fn2-cru-long-lines*) '(5 2)))))
         (want (fn2-cursor-spec-wire *fn2-cru-long-groups* nil *fn2-cru-long-lines*)))
    (and (equal (nth 3 r) 0)
         (or (equal (car (nth 2 r)) want) (cw "list pages ~x0~%want ~x1~%" (car (nth 2 r)) want)))))
; Negative: the listing in the profile's order (the reference sorts by
; name) differs, so the positive checks the order the scan delivers.
(defun fn2-cursor-test-list-pages-negative ()
  (declare (xargs :verify-guards nil))
  (not (equal (fn2-csp-list-rows "ACTIVE" (fn2-csp-sort *fn2-cru-long-groups*) nil)
              (fn2-csp-list-rows "ACTIVE" *fn2-cru-long-groups* nil))))
(defun fn2-cursor-test-pinned-served ()
  (declare (xargs :verify-guards nil))
  (let ((got (fn2-cursor-wire-interleaved *fn2-cru-seeds* *fn2-cru-later* *fn2-cru-pinned-lines* nil))
        (want (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-pinned-lines*)))
    (or (equal got want) (cw "pinned ~x0~%want ~x1~%" got want))))
(assert-event (fn2-cursor-test-spec))
(assert-event (fn2-cursor-test-spec-negative))
(assert-event (fn2-cursor-test-seeded))
(assert-event (fn2-cursor-test-range-cost))
(assert-event (fn2-cursor-test-range-cost-negative))
(assert-event (fn2-cursor-test-pinned))
(assert-event (fn2-cursor-test-pinned-negative))
(assert-event (fn2-cursor-test-served nil))
(assert-event (fn2-cursor-test-served '(7 3 1)))
(assert-event (fn2-cursor-test-pinned-served))
(assert-event (fn2-cursor-test-list-pages))
(assert-event (fn2-cursor-test-list-pages-negative))
