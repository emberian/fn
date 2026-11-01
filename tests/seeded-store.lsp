; The seeded store every surface session serves (D6, H20 item 2): the
; simulator session (sim-session.lsp) and the native ones (native-serve.lsp,
; native-session.lsp) ld this file, so the three nodes start from one profile
; and one store. Loading it prints nothing.
;
; The profile is the cursor's (read rows, x 2; the groups local.test 1 and
; local.empty 2) less its posting, so the posting replies stay the
; reader-only node's. Before any client opens, the store holds three
; articles in local.test, published through C-S3 as tests/cursor-unit.lisp
; seeds them (numbers 1-3, Message-IDs <a|b|c@example.invalid>, each overview
; line with its Xref field); local.empty holds none. fn2-ss-replay is ENVELOPE's replay of a boundary trace from
; this store (sim/check-envelope.lisp's fn2-envelope-replay, seeded), and
; fn2-ss-envelope-check its check against the clients' bytes.
(in-package "ACL2")
(include-book "../books/owed-cursor")
(include-book "../sim/check-envelope")
(defconst *fn2-ss-profile*
  (put-assoc-equal :trace nil (remove1-assoc-equal :posting-interim *fn2-cursor-profile*)))
(defun fn2-ss-tab () (declare (xargs :verify-guards nil)) (coerce (list (code-char 9)) 'string))
;; A stored overview line is the full form (RFC 3977 8.3.2, 8.4; specs/nntp.md
;; PRF-206): its ninth field is "Xref: SERVER group:number", SERVER the path
;; identity (.invalid while unset), as the transaction's late fill of the
;; overview row writes it (C-S3a); the cursor renders the line as stored.
(defun fn2-ss-line (subject mid n)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list subject (fn2-ss-tab) "a@example.invalid" (fn2-ss-tab) "Fri, 30 Oct 2026 12:00:00 +0000"
                     (fn2-ss-tab) mid (fn2-ss-tab) "" (fn2-ss-tab) "120" (fn2-ss-tab) "1"
                     (fn2-ss-tab) "Xref: .invalid local.test:" (fn2-csp-str n))))
(defconst *fn2-ss-seeds*
  (list (list 1 "<a@example.invalid>" (fn2-ss-line "one" "<a@example.invalid>" 1))
        (list 1 "<b@example.invalid>" (fn2-ss-line "two" "<b@example.invalid>" 2))
        (list 1 "<c@example.invalid>" (fn2-ss-line "three" "<c@example.invalid>" 3))))
; (verdict caps); a refused seed is the verdict (:seed batch code).
(defun fn2-ss-replay (trace profile seeds bytes-p)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (verdict caps fn2-core)
      (let ((fn2-core (fn2-init-executor profile :echo nil fn2-core)))
        (mv-let (code fn2-core) (fn2-cs-seed-all seeds 1 fn2-core)
          (if (eq code :ok)
              (fn2-env-steps trace 0 bytes-p nil nil fn2-core)
            (mv (cons :seed code) nil fn2-core))))
      (list verdict caps))))
(defun fn2-ss-envelope-check (trace clients profile seeds)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-ss-replay trace profile seeds t)))
    (if (not (eq (car r) :pass)) (car r) (fn2-env-bytes (cadr r) clients))))
