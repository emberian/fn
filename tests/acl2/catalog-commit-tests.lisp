; fn: teeth for books/catalog-commit.lisp (wave 5, lane catalog-slice step 4).
;
; What this book is evidence FOR.  `fn-cat-complete-by-token' (PRF-203):
; with the pending's token and EXPECTED the count, the completion commits
; the held row at EXPECTED, clears the pending and emits the delta of that
; row, with no search; a stale token, a mismatched EXPECTED and a prepare
; over a pending commit are refused by name and change nothing; a token from
; an abandoned attempt cannot complete the next attempt because the next
; txid differs (the witness with EQUAL txids shows the hypothesis is what
; keeps it out).  `fn-sn-finish-held-is-finish': on the article arm the held
; finish over the completing record's held view and the context of its bytes
; is `fn-sn-finish', on store-node-tests' store at :completing; a stale
; context is refused by name.  `fn-sn-context-fixed-between-prepare-and-
; finish': the transitions leave the keyring and its generation, and the one
; writer advances the generation (the negative of the design's phase gate,
; labelled unreachable-in-composition: no native host line calls it).
;
; Corrupted-state witnesses are labelled: the expected-mismatch refusal, and
; the store whose pending bytes differ from the completing record's, where
; the held finish (which does not read the bytes) and the reference finish
; disagree -- the case the payload hypothesis excludes and the maintained
; relation (step 6) rules out.

(in-package "ACL2")
(include-book "../../books/catalog-commit")
(include-book "store-node-tests")
(include-book "held-rows-tests")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; The host runs compiled code.

(assert-event
 (and (eq (symbol-class 'fn-cat-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-complete (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-abandon (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sn-finish-held (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-snh-enabledp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-snh-bindsp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pc-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-dart-p (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; Ground fixtures: one article's bytes, three wire records with distinct
; txids (1, 2, 3) over them, and one with txid 1 again.

(defconst *cct-art*
  (append (fn-record-string-octets "Subject: a") '(13 10 13 10)
          (fn-record-string-octets "line1") '(13 10)
          (fn-record-string-octets "line2") '(13 10)))

(defun cct-w (seq txid)
  (fn-record-make seq txid 0 "<a@x>" *cct-art* '("fn.test") "o" "s" "e" 1 5))

(defconst *cct-w1* (cct-w 0 1))
(defconst *cct-w2* (cct-w 1 2))
(defconst *cct-w3* (cct-w 1 3))

(assert-event (and (fn-record-p *cct-w1*) (fn-record-p *cct-w2*) (fn-record-p *cct-w3*)
                   (fn-prin-keyringp nil)))

; -----------------------------------------------------------------------------
; The executable path on live stobjs: the token protocol end to end.

(defun cct-run-in (fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    ; attempt 1: prepare, then complete by its token
    (mv-let (pc1 fn-arena)
      (fn-cat-prepare *cct-w1* :plan :res fn-octets nil 0 nil fn-arena fn-cat)
      (mv-let (refused fn-arena)
        (fn-cat-prepare *cct-w2* :plan :res fn-octets nil 0 pc1 fn-arena fn-cat)
        (mv-let (r1 p1 fn-cat)
          (fn-cat-complete (fn-pc-token pc1) pc1 fn-cat)
          (mv-let (r2 p2 fn-cat)
            (fn-cat-complete (fn-pc-token pc1) p1 fn-cat)
            ; attempt 2 (txid 2): prepared then abandoned; attempt 3 (txid 3):
            ; the abandoned token cannot complete it, its own can
            (mv-let (pc2 fn-arena)
              (fn-cat-prepare *cct-w2* :plan :res fn-octets nil 0 p2 fn-arena fn-cat)
              (mv-let (st3 p3)
                (fn-cat-abandon (fn-pc-token pc2) pc2)
                (mv-let (st4 p4)
                  (fn-cat-abandon (fn-pc-token pc2) p3)
                  (mv-let (pc3 fn-arena)
                    (fn-cat-prepare *cct-w3* :plan :res fn-octets nil 0 p4 fn-arena fn-cat)
                    (mv-let (r5 p5 fn-cat)
                      (fn-cat-complete (fn-pc-token pc2) pc3 fn-cat)
                      (mv-let (r6 p6 fn-cat)
                        (fn-cat-complete (fn-pc-token pc3) p5 fn-cat)
                        ; CORRUPTED STATE: a pending whose EXPECTED is not the
                        ; count is refused by name and commits nothing
                        (let ((bad (fn-pc-make (cons 9 0) 0 (fn-pc-held pc1) :plan :res)))
                          (mv-let (r7 p7 fn-cat)
                            (fn-cat-complete (cons 9 0) bad fn-cat)
                            (mv (list (list (fn-pc-token pc1) (fn-pc-expected pc1)
                                            (fn-record-payload (fn-pc-held pc1))
                                            (fn-held-numbers (fn-pc-held pc1)))
                                      refused
                                      (list (car r1) (fn-dart-seq r1) (fn-dart-msgid r1)
                                            (fn-dart-numbers r1) (fn-dart-handle r1)
                                            (fn-hf-octets (fn-dart-facts r1))
                                            (fn-hc-generation (fn-dart-context r1))
                                            p1 (fn-cat-count fn-cat))
                                      (list r2 p2)
                                      (list (fn-pc-token pc2) st3 p3 st4 p4)
                                      (list (fn-pc-token pc3) r5 (equal p5 pc3))
                                      (list (car r6) (fn-dart-seq r6) (fn-dart-numbers r6)
                                            (fn-dart-handle r6) p6)
                                      (list r7 (equal p7 bad) (fn-cat-count fn-cat)
                                            (fn-arena-count fn-arena)
                                            (equal (fn-held-wire-of (fn-cat-at 0 fn-cat) fn-arena)
                                                   *cct-w1*)
                                            (equal (fn-held-wire-of (fn-cat-at 1 fn-cat) fn-arena)
                                                   *cct-w3*)))
                                fn-arena fn-cat fn-octets)))))))))))))))

(defun cct-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (with-local-stobj fn-octets
    (mv-let (result fn-arena fn-cat fn-octets)
      (let ((fn-octets (fn-octets-from-list *cct-art* fn-octets)))
        (cct-run-in fn-octets fn-arena fn-cat))
      (mv result fn-arena fn-cat))))

(defun cct-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cct-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event
 (equal (cct-exec)
        (list (list '(1 . 0) 0 0 nil)                      ; attempt 1's token, expected, handle, no numbers yet
              '(:pending)                                  ; a prepare over a pending commit
              (list :article 0 "<a@x>" '(("fn.test" . 1)) 0 (len *cct-art*) 0 nil 2)   ; the count read at the run's end
              (list '(:stale-token) nil)                   ; the consumed token
              (list '(2 . 1) :ok nil :stale-token nil)     ; abandon, then a stale abandon
              (list '(3 . 1) '(:stale-token) t)            ; the abandoned token on attempt 3
              (list :article 1 '(("fn.test" . 2)) 2 nil)   ; attempt 3 by its own token (handle 2: the abandoned seal is garbage)
              (list '(:expected-mismatch) t 2 3 t t))))

; The NEGATIVE of the txid hypothesis: two attempts with the SAME txid make
; the same token, and the abandoned token completes the second.  This is
; what `fn-cat-token-of-abandoned-attempt-is-stale' assumes away; the
; host's frontier advance per attempt is what makes the hypothesis true.
(defun cct-same-txid-in (fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (pc1 fn-arena)
      (fn-cat-prepare *cct-w1* :plan :res fn-octets nil 0 nil fn-arena fn-cat)
      (mv-let (st p)
        (fn-cat-abandon (fn-pc-token pc1) pc1)
        (declare (ignore st))
        (mv-let (pc2 fn-arena)
          (fn-cat-prepare *cct-w1* :plan :res fn-octets nil 0 p fn-arena fn-cat)
          (mv-let (r p2 fn-cat)
            (fn-cat-complete (fn-pc-token pc1) pc2 fn-cat)
            (mv (list (equal (fn-pc-token pc1) (fn-pc-token pc2)) (car r) p2
                      (fn-cat-count fn-cat))
                fn-arena fn-cat fn-octets)))))))

(defun cct-same-txid-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (with-local-stobj fn-octets
    (mv-let (result fn-arena fn-cat fn-octets)
      (let ((fn-octets (fn-octets-from-list *cct-art* fn-octets)))
        (cct-same-txid-in fn-octets fn-arena fn-cat))
      (mv result fn-arena fn-cat))))

(defun cct-same-txid ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cct-same-txid-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event (equal (cct-same-txid) (list t :article nil 1)))

; -----------------------------------------------------------------------------
; The keystone on ground values: complete antecedent and conclusion.
; A two-row catalog; a pending whose held record is a third article with
; expected 2 and the token (7 . 2).

(defun cct-held (seq txid msgid)
  (fn-held-make seq txid 0 msgid seq '("fn.test") "o" "s" "e" 1 5
                (fn-hf-make 100 14 2 nil nil)
                ; by specification: the flip types the held context's verdict
                ; (fn-hc-verdictp): the verdict value, token :unverified.
                (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0) nil nil))

(defconst *cct-c*
  (list (fn-cat-assign (cct-held 0 1 "<a@x>") nil)
        (fn-cat-assign (cct-held 1 2 "<b@x>") (list (fn-cat-assign (cct-held 0 1 "<a@x>") nil)))))
(defconst *cct-pc* (fn-pc-make (cons 7 2) 2 (cct-held 2 7 "<c@x>") :plan :res))

(defthm cct-w-complete-by-token
  (and (fn-pc-p *cct-pc*)
       (equal (cons 7 2) (fn-pc-token *cct-pc*))
       (equal (fn-pc-expected *cct-pc*) (fn-cat-count *cct-c*))
       (mv-let (result pending2 c2)
         (fn-cat-complete (cons 7 2) *cct-pc* *cct-c*)
         (and (equal (fn-cat-at 2 c2) (fn-cat-assign (fn-pc-held *cct-pc*) *cct-c*))
              (equal (fn-cat-count c2) 3)
              (equal pending2 nil)
              (equal result (fn-delta-of-row 2 (fn-cat-assign (fn-pc-held *cct-pc*) *cct-c*)))
              (equal (fn-held-numbers (fn-cat-at 2 c2)) '(("fn.test" . 3)))
              (fn-dart-p result))))
  :rule-classes nil)

; Per hypothesis: the retained ones hold, the omitted one fails, the
; conclusion fails.
(defthm cct-w-no-token          ; the wrong token: refused, the row absent
  (and (fn-pc-p *cct-pc*)
       (equal (fn-pc-expected *cct-pc*) (fn-cat-count *cct-c*))
       (not (equal (cons 8 2) (fn-pc-token *cct-pc*)))
       (mv-let (result pending2 c2)
         (fn-cat-complete (cons 8 2) *cct-pc* *cct-c*)
         (and (equal result '(:stale-token))
              (equal pending2 *cct-pc*)
              (equal (fn-cat-count c2) 2))))
  :rule-classes nil)

(defthm cct-w-no-expected       ; CORRUPTED STATE: expected is not the count
  (let ((pc (fn-pc-make (cons 7 1) 1 (cct-held 2 7 "<c@x>") :plan :res)))
    (and (fn-pc-p pc)
         (equal (cons 7 1) (fn-pc-token pc))
         (not (equal (fn-pc-expected pc) (fn-cat-count *cct-c*)))
         (mv-let (result pending2 c2)
           (fn-cat-complete (cons 7 1) pc *cct-c*)
           (and (equal result '(:expected-mismatch))
                (equal pending2 pc)
                (equal (fn-cat-count c2) 2)))))
  :rule-classes nil)

(must-fail-checked
 (defthm cct-w-no-token-conclusion
   (mv-let (result pending2 c2)
     (fn-cat-complete (cons 8 2) *cct-pc* *cct-c*)
     (declare (ignore result pending2))
     (equal (fn-cat-count c2) 3))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; The shared transition on store-node-tests' store at :completing.
;
; by specification: the flip.  The store retains held rows, so the completing
; record IS the held row (store-node-tests' *sn-row*: *sn-record*'s positions
; at handle 0), the pending payload is that handle, and the keystone
; fn-sn-finish-held-is-finish (books/catalog-commit.lisp, restated by the
; flip) takes H = the completion row and CTX = its own context.  The witness
; asserts that statement's complete antecedent and conclusion; each tooth
; drops one hypothesis.  The row's context is the context of its bytes under
; the store's keyring and generation, as the entry decides it
; (fn-held-context-of, store-intern fn-intern-row-at).

(defconst *cct-bytes* (fn-record-payload *sn-record*))
; The row the entry interns from *sn-record* (handle 0, the bytes' facts and
; context under the store's keyring nil at generation 0), prepared and
; published on store-node-tests' reserved store.
(defconst *cct-row* (fn-hrt-row-at *sn-record* 0))
(defconst *cct-s* (fn-sn-test-publish (fn-sn-prepare *sn-reserved* *cct-row*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *cct-s*)) :completing))
(defconst *cct-h* (fn-sn-completion-record *cct-s*))
(defconst *cct-ctx* (fn-held-context *cct-h*))
(assert-event (equal *cct-ctx* (fn-held-context-of *cct-bytes* (fn-sn-keyring *cct-s*)
                                                   (fn-sn-keyring-generation *cct-s*))))

(defthm cct-w-finish-held-is-finish
  (and (fn-sn-statep *cct-s*)
       (equal (fn-sn-completion-record *cct-s*) *cct-h*)
       (equal *cct-h* *cct-row*)
       (fn-held-p *cct-h*)
       (equal (fn-held-wire *cct-h* *cct-bytes*) *sn-record*)
       (equal (fn-record-payload *cct-h*)
              (fn-pending-payload (fn-state-pending (fn-node-acceptance (fn-sn-node *cct-s*)))))
       (equal *cct-ctx* (fn-held-context *cct-h*))
       (equal (fn-sn-finish-held *cct-s* *cct-h* *cct-ctx*) (fn-sn-finish *cct-s*))
       ; not vacuous: the finish commits
       (not (equal (fn-sn-finish *cct-s*) *cct-s*))
       (equal (fn-sf-successes (fn-sn-files (fn-sn-finish-held *cct-s* *cct-h* *cct-ctx*)))
              '((0 . 0)))
       (fn-snh-enabledp *cct-s* *cct-h* *cct-ctx*))
  :rule-classes nil)

; A stale context (a generation the store does not hold) is refused by name.
(defthm cct-w-stale-context-refused
  (let ((stale (fn-hc-make (fn-hc-verdict *cct-ctx*) (fn-hc-delta *cct-ctx*)
                           (1+ (fn-sn-keyring-generation *cct-s*)))))
    (and (not (equal (fn-hc-generation stale) (fn-sn-keyring-generation *cct-s*)))
         (equal (fn-sn-finish-held *cct-s* *cct-h* stale) *cct-s*)
         (not (fn-snh-enabledp *cct-s* *cct-h* stale))))
  :rule-classes nil)

; Without the completion-record hypothesis (a held row that is not the
; completing row, same handle and context): the held finish refuses, the
; finish commits.
(defconst *cct-other*
  (fn-held-make 0 0 0 "<other@example>" 0 *sn-groups* "sn-pin" "sn-content"
                "sn-release" 2 841000000 (fn-held-facts *cct-h*) *cct-ctx* nil nil))
(defthm cct-w-no-alpha
  (and (fn-held-p *cct-other*)
       (not (equal (fn-sn-completion-record *cct-s*) *cct-other*))
       (equal (fn-record-payload *cct-other*)
              (fn-pending-payload (fn-state-pending (fn-node-acceptance (fn-sn-node *cct-s*)))))
       (equal *cct-ctx* (fn-held-context *cct-other*))
       (equal (fn-sn-finish-held *cct-s* *cct-other* *cct-ctx*) *cct-s*)
       (not (equal (fn-sn-finish-held *cct-s* *cct-other* *cct-ctx*) (fn-sn-finish *cct-s*))))
  :rule-classes nil)

; Without the held record at all: refused.
(defthm cct-w-no-held
  (and (not (fn-held-p nil))
       (equal (fn-sn-finish-held *cct-s* nil *cct-ctx*) *cct-s*)
       (not (equal (fn-sn-finish-held *cct-s* nil *cct-ctx*) (fn-sn-finish *cct-s*))))
  :rule-classes nil)

; Without the context hypothesis (a well-formed verdict the bytes do not
; carry, :absent where they decide :unverified, under the store's generation): the held finish commits THAT verdict; the finish
; commits the row's.  The two differ in the recorded verdict.
(defthm cct-w-no-context
  (let ((bogus (fn-hc-make (fn-stx-make-verdict :absent nil (fn-sn-keyring-generation *cct-s*))
                           (fn-hc-delta *cct-ctx*) (fn-sn-keyring-generation *cct-s*))))
    (and (not (equal bogus (fn-held-context *cct-h*)))
         (not (equal (fn-sn-finish-held *cct-s* *cct-h* bogus) *cct-s*))
         (not (equal (fn-sn-finish-held *cct-s* *cct-h* bogus) (fn-sn-finish *cct-s*)))
         (equal (fn-sn-verdict-lookup (fn-sn-finish-held *cct-s* *cct-h* bogus) "<sn@example>")
                (fn-hc-verdict bogus))))
  :rule-classes nil)

; CORRUPTED STATE (the payload hypothesis): a store whose pending payload is
; another handle (1) than the completing row's (0).  The reference finish
; refuses (its binding reads the handle); the held finish, which reads
; metadata, commits.  The maintained relation excludes this state; the
; theorem's payload hypothesis names it.
(defthm cct-w-no-payload-corrupted
  (let ((s (fn-sn-update *cct-s* (fn-sn-files *cct-s*)
                        (fn-node-prepare (fn-sn-node *sn-initial*) 0 "<sn@example>" 1
                                         *sn-groups* "sn-pin" "sn-content" "sn-release"
                                         2 841000000))))
    (and (fn-sn-statep s)
         (equal (fn-sn-completion-record s) *cct-h*)
         (fn-held-p *cct-h*)
         (equal *cct-ctx* (fn-held-context *cct-h*))
         (not (equal (fn-record-payload *cct-h*)
                     (fn-pending-payload (fn-state-pending (fn-node-acceptance (fn-sn-node s))))))
         (equal (fn-sn-finish s) s)
         (not (equal (fn-sn-finish-held s *cct-h* *cct-ctx*) s))
         (not (equal (fn-sn-finish-held s *cct-h* *cct-ctx*) (fn-sn-finish s)))))
  :rule-classes nil)

(must-fail-checked
 (defthm cct-w-no-alpha-conclusion
   (equal (fn-sn-finish-held *cct-s* *cct-other* *cct-ctx*) (fn-sn-finish *cct-s*))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; The context theorem on the ground store: the transitions the host applies
; leave the keyring and its generation; the writer advances the generation
; (unreachable-in-composition: no native host line calls fn-sn-set-keyring).

(defthm cct-w-context-fixed
  (and (equal (fn-sn-keyring-generation *cct-s*) 0)
       (equal (fn-sn-keyring-generation (fn-sn-finish *cct-s*)) 0)
       (equal (fn-sn-keyring (fn-sn-finish *cct-s*)) (fn-sn-keyring *cct-s*))
       (equal (fn-sn-keyring-generation (fn-sn-finish-held *cct-s* *cct-h* *cct-ctx*)) 0)
       (equal (fn-sn-keyring-generation (fn-snrt-step *sn-prepared* '(:known-abort))) 0)
       (not (equal (fn-snrt-step *sn-prepared* '(:known-abort)) *sn-prepared*))
       (equal (fn-sn-keyring-generation (fn-sn-io *sn-prepared* :record-file :ok)) 0)
       (equal (fn-sn-keyring-generation (fn-snrt-step *sn-reserved* (list :prepare *sn-row*))) 0)
       ; the writer: the generation moves.  by specification: the flip: the
       ; writer recontexts the retained rows, so it acts at :ready only (the
       ; store after the finish), and takes the rows' contexts
       ; (store-intern's entry fn-store-set-keyring computes them).
       (fn-prin-keyringp nil)
       (equal (fn-sn-keyring-generation
               (fn-sn-set-keyring (fn-sn-finish *cct-s*) nil
                                  (list (fn-held-context-of *cct-bytes* nil 1))))
              1))
  :rule-classes nil)
