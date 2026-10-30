; D6 evidence: the teeth of owed-cursor.lisp's keystones (fn2/docs/d-machines-
; nntp.md section 15.7). Until the cursor serves (D6 1/n), the teeth check the
; reference against hand-written replies (RFC 3977, H's model), that each
; negative case is caught, and that the seeded store publishes through C-S3:
; the served core answers the interim 503 then, so the rows stay owed.
; Run: sh fn2/tools/certify.sh tests/cursor-unit.lisp
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
  '("NEXT" "STAT" "OVER" "GROUP nope.nope" "GROUP local.empty" "NEXT" "GROUP local.test" "STAT" "NEXT" "NEXT" "NEXT"
    "LAST" "LAST" "LAST" "STAT 9" "STAT <b@example.invalid>" "STAT <z@example.invalid>" "LISTGROUP"
    "LISTGROUP local.test 2-" "OVER 2-3" "OVER 7-9" "XOVER 7-9" "OVER" "OVER <c@example.invalid>" "QUIT"))
(assert-event (fn2-csp-linesp *fn2-cru-lines*))
(defun fn2-cru-ov (n subject mid)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list (fn2-csp-str n) (fn2-cru-tab) (fn2-cru-line subject mid))))
(defun fn2-cru-expected ()
  (declare (xargs :verify-guards nil))
  (list "412 no newsgroup selected" "412 no newsgroup selected" "412 no newsgroup selected"
        "411 no such newsgroup" "211 0 1 0 local.empty" "420 no current article"
        "211 3 1 3 local.test" "223 1 <a@example.invalid> retrieved"
        "223 2 <b@example.invalid> retrieved" "223 3 <c@example.invalid> retrieved" "421 no next article"
        "223 2 <b@example.invalid> retrieved" "223 1 <a@example.invalid> retrieved" "422 no previous article"
        "423 no article with that number" "223 2 <b@example.invalid> retrieved" "430 no article with that message-id"
        "211 3 1 3 local.test list follows" "1" "2" "3" "."
        "211 3 1 3 local.test list follows" "2" "3" "."
        "224 overview information follows" (fn2-cru-ov 2 "two" "<b@example.invalid>") (fn2-cru-ov 3 "three" "<c@example.invalid>") "."
        "423 no articles in that range" "420 no article(s) selected"
        "224 overview information follows" (fn2-cru-ov 1 "one" "<a@example.invalid>") "."
        "224 overview information follows" (fn2-cru-ov 3 "three" "<c@example.invalid>") "."
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
; does not stop, and today's served reply to GROUP is the interim 503, so
; the row is owed (the D6 1/n commit turns this tooth into served = spec).
(defun fn2-cursor-test-seeded ()
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-cursor-wire-run *fn2-cursor-profile* *fn2-cru-seeds*
                                (list (list (fn2-cw-crlf-octets '("GROUP local.test" "QUIT")) nil)))))
    (and (or (eq (nth 0 r) :ok) (cw "seeded ~x0~%" (nth 0 r)))
         (equal (nth 3 r) 0)
         (or (equal (car (nth 2 r))
                    (list (fn2-cw-crlf-octets '("200 fn-nntp experimental server ready"
                                                "503 archive projection unavailable" "205 closing connection"))
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
       (let ((r (fn2-cursor-run *fn2-cursor-profile* *fn2-cru-seeds* *fn2-cru-later*
                                (list (list (fn2-cw-crlf-octets *fn2-cru-pinned-lines*) nil)))))
         ;; the later seed was published while the client read
         (or (eq (nth 0 r) :ok) (cw "pinned seeded ~x0~%" (nth 0 r))))))
(defun fn2-cursor-test-pinned-negative ()
  (declare (xargs :verify-guards nil))
  (not (equal (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-pinned-lines*)
              (fn2-cursor-spec-wire *fn2-cru-groups* (append *fn2-cru-seeds* *fn2-cru-later*) *fn2-cru-pinned-lines*))))

(assert-event (fn2-cursor-test-spec))
(assert-event (fn2-cursor-test-spec-negative))
(assert-event (fn2-cursor-test-seeded))
(assert-event (fn2-cursor-test-range-cost))
(assert-event (fn2-cursor-test-range-cost-negative))
(assert-event (fn2-cursor-test-pinned))
(assert-event (fn2-cursor-test-pinned-negative))
