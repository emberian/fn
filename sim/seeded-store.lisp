; The seeded store every surface session serves (D6, H20 item 2): the
; simulator session (sim/session.lisp, tests/sim-session.lsp) and the native
; ones (tests/native-serve.lsp, tests/native-session.lsp, which ld
; tests/seeded-store.lsp) include this book, so the three nodes start from
; one profile and one store.
;
; The profile is the cursor's (read rows, x 2; the groups local.test 1 and
; local.empty 2) less its posting, so the posting replies stay the
; reader-only node's. Before any client opens, the store holds three
; articles in local.test, each produced by the transaction's own path and
; committed by B on the core's turns (owed-cursor's fn2-cs-seed): numbers
; 1-3 in batches and events 1-3, Message-IDs <a|b|c@example.invalid>, each
; overview line synthesized from its source with its Xref field, each
; source and B's log on the carrier's device; local.empty holds none. So B's
; commit frontier is batch 4 and C's read frontier batch 3, and a POST after
; seeding is batch 4. fn2-ss-replay is ENVELOPE's replay of a boundary trace from
; this store (sim/check-envelope.lisp's fn2-envelope-replay, seeded), and
; fn2-ss-envelope-check its check against the clients' bytes.
(in-package "ACL2")
(include-book "../books/owed-cursor")
(include-book "check-envelope")
(defconst *fn2-ss-profile*
  (put-assoc-equal :trace nil (remove1-assoc-equal :posting-interim *fn2-cursor-profile*)))
(defun fn2-ss-tab () (declare (xargs :verify-guards nil)) (coerce (list (code-char 9)) 'string))
;; Each article's stored source (owed-cursor's seed TEXT): its header, an
;; empty line, and a body with a line that starts with "." (stuffed on the
;; wire), stored at an extent of its own; ARTICLE, HEAD and BODY serve it
;; through B's block read.
(defun fn2-ss-text (subject mid)
  (declare (xargs :verify-guards nil))
  (list "From: a@example.invalid" (fn2-csp-cat (list "Subject: " subject))
        "Date: Fri, 30 Oct 2026 12:00:00 +0000" (fn2-csp-cat (list "Message-ID: " mid))
        "Newsgroups: local.test" "" (fn2-csp-cat (list "body " subject)) ".dotted" "end"))
;; The body's line count: the lines after the header's empty line.
(defun fn2-ss-body-lines (text)
  (declare (xargs :verify-guards nil))
  (cond ((atom text) 0) ((equal (car text) "") (len (cdr text))) (t (fn2-ss-body-lines (cdr text)))))
;; A stored overview line is the full form (RFC 3977 8.3.2, 8.4; specs/nntp.md
;; PRF-206): its ninth field is "Xref: SERVER group:number", SERVER the
;; profile's path identity, as the transaction's late fill of the overview
;; row writes it (fn2-txn-xref, C-S3a); the cursor renders the line as
;; stored. Its :bytes and :lines are the stored source's (CRLF lines,
;; unstuffed). This is the reference's statement of the line; seeding
;; refuses a seed whose synthesized line differs.
(defun fn2-ss-line (subject mid n text)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list subject (fn2-ss-tab) "a@example.invalid" (fn2-ss-tab) "Fri, 30 Oct 2026 12:00:00 +0000"
                     (fn2-ss-tab) mid (fn2-ss-tab) "" (fn2-ss-tab) (fn2-csp-str (len (fn2-cs-source text)))
                     (fn2-ss-tab) (fn2-csp-str (fn2-ss-body-lines text))
                     (fn2-ss-tab) "Xref: " (fn2-profile-path-identity *fn2-ss-profile*) " local.test:" (fn2-csp-str n))))
(defun fn2-ss-seed (subject mid n)
  (declare (xargs :verify-guards nil))
  (let ((text (fn2-ss-text subject mid)))
    (list 1 mid (fn2-ss-line subject mid n text) text)))
(defconst *fn2-ss-seeds*
  (list (fn2-ss-seed "one" "<a@example.invalid>" 1)
        (fn2-ss-seed "two" "<b@example.invalid>" 2)
        (fn2-ss-seed "three" "<c@example.invalid>" 3)))
; (verdict caps); a refused seed is the verdict (:seed batch code).
(defun fn2-ss-replay (trace profile seeds bytes-p)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (verdict caps fn2-core)
      (let ((fn2-core (fn2-init-executor profile :echo nil fn2-core)))
        (mv-let (code store fn2-core) (fn2-cs-seed-all seeds 1 fn2-core)
          (declare (ignore store))
          (if (eq code :ok)
              (fn2-env-steps trace 0 bytes-p nil nil fn2-core)
            (mv (cons :seed code) nil fn2-core))))
      (list verdict caps))))
(defun fn2-ss-envelope-check (trace clients profile seeds)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-ss-replay trace profile seeds t)))
    (if (not (eq (car r) :pass)) (car r) (fn2-env-bytes (cadr r) clients))))
