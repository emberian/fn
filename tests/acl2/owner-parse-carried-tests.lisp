; Teeth for books/owner-parse-carried.lisp.
(in-package "ACL2")
(include-book "../../books/owner-parse-carried")
(include-book "must-fail-checked")
(include-book "owner-commit-carried-tests")
(include-book "peer-authored-accept-tests")

; lane history-columns-3: the readers take the history stobj fn-hist.
(defun fn-apc-own-finish-h (o cfg fn-arena carry)
  ; fn-apc-own-finish over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store o)))) 0 fn-hist)))
        (mv (fn-apc-own-finish o cfg fn-arena fn-hist carry) fn-hist))
      ans)))

; The host runs compiled code: every function it calls here is
; guard-verified, as its reference is.  The resolution publication's
; reference (fn-ores-submission-resolution-publication) and its twin were
; :ideal until lane depth-debt-5 verified both (row K2).
(assert-event
 (equal (list (symbol-class 'fn-apc-take (w state))
              (symbol-class 'fn-apc-icar-carry-of (w state))
              (symbol-class 'fn-apc-take-result (w state))
              (symbol-class 'fn-apc-submission-intent (w state))
              (symbol-class 'fn-apc-filing-plan (w state))
              (symbol-class 'fn-apc-carrier-form (w state))
              (symbol-class 'fn-apc-current-plan (w state))
              (symbol-class 'fn-apc-transit-verdict (w state))
              (symbol-class 'fn-apc-transit-refusal-detail (w state))
              (symbol-class 'fn-apc-intern-row-at (w state))
              (symbol-class 'fn-apc-own-finish (w state))
              (symbol-class 'fn-apc-submission-resolution-publication (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; Reachable witness 1: owner-served-invariants-tests' *osi-completing*,
; connection 4's served POST taken by fn-own-take-submission and staged at
; :completing.  No login: the submission's, the injected and the stored
; octets are one list, so the take parses once and the carry has one entry.

(defconst *apc-t-o* *osi-completing*)
(defconst *apc-t-cfg* *osi-cfg*)
(defconst *apc-t-sub* (fn-own-inflight *apc-t-o*))
(defconst *apc-t-secret* (fn-own-node-secret *apc-t-o*))
(defconst *apc-t-tk* (fn-apc-take *apc-t-cfg* *apc-t-sub* *apc-t-secret*))
(defconst *apc-t-stored* (car *apc-t-tk*))
(defconst *apc-t-carry* (cdr *apc-t-tk*))

(assert-event (equal *apc-t-stored*
                     (fn-own-sub-stored-octets *apc-t-cfg* *apc-t-sub* *apc-t-secret*)))
(assert-event (equal *apc-t-stored* (fn-own-sub-octets *apc-t-sub*)))
(assert-event (equal (len *apc-t-stored*) 328))
(assert-event (fn-apc-p *apc-t-carry*))
(assert-event (equal (len *apc-t-carry*) 1))
(assert-event (equal *apc-t-carry*
                     (list (cons *apc-t-stored* (fn-article-parse *apc-t-stored*)))))
(assert-event (equal (fn-apc-parse *apc-t-stored* *apc-t-carry*)
                     (fn-article-parse *apc-t-stored*)))
(assert-event (fn-article-result-okp (fn-apc-parse *apc-t-stored* *apc-t-carry*)))

; The take's three host calls (fn-apc-take-is-take-result): the
; SubmissionTaken of the stored octets, its INTENT field fn-icar-carry-of.
; The digests run through their attachments (books/crypto-attach), which a
; defconst may not call: the intent carries are thunks.
(defun apc-t-icar () (fn-apc-icar-carry-of *apc-t-sub* *apc-t-carry*))
(assert-event (equal (apc-t-icar) (fn-icar-carry-of *apc-t-sub*)))
(assert-event (fn-icar-carryp (apc-t-icar)))
(assert-event (equal (fn-apc-take-result *apc-t-sub* *apc-t-stored* (apc-t-icar))
                     (fn-ores-take-result *apc-t-sub* *apc-t-stored*)))
(assert-event (equal (fn-ores-taken-word
                      (fn-apc-take-result *apc-t-sub* *apc-t-stored* (apc-t-icar)))
                     :taken))

; Each ingress reader over the stored octets is its reference, and the
; values are the unsigned ordinary article's.
(defconst *apc-t-groups* (list (fn-nntp-string-octets "fn.letters")))
(assert-event (equal (fn-apc-carrier-form *apc-t-stored* *apc-t-carry*) :absent))
(assert-event (equal (fn-pa-carrier-form *apc-t-stored*) :absent))
(assert-event (equal (fn-apc-current-plan *apc-t-stored* nil nil t *apc-t-carry*)
                     (fn-pa-current-plan *apc-t-stored* nil nil t)))
(assert-event (equal (fn-apc-current-plan *apc-t-stored* nil nil t *apc-t-carry*) :absent))
(assert-event (equal (fn-apc-transit-verdict *apc-t-stored* nil nil t nil nil *apc-t-carry*)
                     (fn-pcb-transit-verdict *apc-t-stored* nil nil t nil nil)))
(assert-event (equal (fn-apc-transit-verdict *apc-t-stored* nil nil t nil nil *apc-t-carry*)
                     :unsigned))
(assert-event (equal (fn-apc-transit-refusal-detail *apc-t-stored* nil nil nil nil *apc-t-carry*)
                     (fn-pcb-transit-refusal-detail *apc-t-stored* nil nil nil nil)))
(assert-event (null (fn-apc-transit-refusal-detail *apc-t-stored* nil nil nil nil *apc-t-carry*)))
; PKT-541: the twin names a revoked principal's refusal as the reference
; does (fn-apc-admission-verdict-of-plan-is-reference), with an empty and
; with a filled parse carry.
(defconst *apc-t-pat-carry*
  (list (cons *pat-relayed* (fn-article-parse *pat-relayed*))))
(assert-event (fn-apc-p *apc-t-pat-carry*))
(assert-event (equal (fn-apc-transit-refusal-detail *pat-relayed* *pat-after-revocation*
                                                    nil :verified :verified nil)
                     '(:no-local-binding :revoked-principal)))
(assert-event (equal (fn-apc-transit-refusal-detail *pat-relayed* *pat-after-revocation*
                                                    nil :verified :verified
                                                    *apc-t-pat-carry*)
                     '(:no-local-binding :revoked-principal)))
(assert-event (equal (fn-apc-transit-verdict *pat-relayed* *pat-after-revocation* nil nil
                                             :verified :verified *apc-t-pat-carry*)
                     :revoked-principal))
(assert-event (equal (fn-apc-transit-verdict *pat-relayed* *pat-after-revocation* nil t
                                             :verified :verified *apc-t-pat-carry*)
                     :revoked))
(assert-event (equal (fn-apc-transit-refusal-detail *pat-relayed* nil nil nil nil
                                                    *apc-t-pat-carry*)
                     '(:no-local-binding :unenrolled)))
(assert-event (equal (fn-apc-filing-plan *apc-t-stored* *apc-t-groups* nil *apc-t-carry*)
                     (fn-pa-filing-plan *apc-t-stored* *apc-t-groups* nil)))
(assert-event (equal (fn-apc-filing-plan *apc-t-stored* *apc-t-groups* nil *apc-t-carry*)
                     (list :file *apc-t-groups*)))
(assert-event (equal (fn-apc-received-fields *apc-t-stored* *apc-t-carry*)
                     (fn-ctl-received-fields *apc-t-stored*)))
(assert-event (equal (len (fn-apc-received-fields *apc-t-stored* *apc-t-carry*)) 8))

; The prepare's row: the staged wire record carrying the stored octets.
(defconst *apc-t-wire* (osi-record-of-wire 2 2 *apc-t-sub* *apc-t-stored*))
(assert-event (fn-record-p *apc-t-wire*))
(assert-event (equal (fn-apc-held-context-of *apc-t-stored* nil 0 *apc-t-carry*)
                     (fn-held-context-of *apc-t-stored* nil 0)))
(assert-event (equal (fn-apc-intern-row-at *apc-t-wire* nil 0 2 *apc-t-carry*)
                     (fn-intern-row-at *apc-t-wire* nil 0 2)))
(assert-event (fn-held-p (fn-apc-intern-row-at *apc-t-wire* nil 0 2 *apc-t-carry*)))

; The finish, over the arena of the entry that interned the history.
(defun apc-t-eval-in (o cfg prior carry fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (mv (list (fn-apc-own-finish-h o cfg fn-arena carry)
              (fn-ccar-own-finish o cfg fn-arena)
              (fn-apc-completion-names-submission-p o cfg fn-arena carry)
              (fn-ccar-completion-names-submission-p o cfg fn-arena))
        fn-arena)))
(defun apc-t-eval (o cfg prior carry)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (apc-t-eval-in o cfg prior carry fn-arena)
      result)))
(defconst *apc-t-finish*
  (apc-t-eval *apc-t-o* *apc-t-cfg* *osi-completing-prior* *apc-t-carry*))
(assert-event (equal (nth 0 *apc-t-finish*) (nth 1 *apc-t-finish*)))
(assert-event (equal (car (nth 0 *apc-t-finish*)) :durable))
(assert-event (equal (nth 2 *apc-t-finish*) (nth 3 *apc-t-finish*)))
(assert-event (equal (nth 2 *apc-t-finish*) t))

; -----------------------------------------------------------------------------
; Reachable witness 2: owner-tests' *own-cancel-a*, a cancel filed in
; control.cancel whose Newsgroups is fn.letters, taken into an owner whose
; peer "out" asks for fn.*.  The intent reads the control groups and the
; Distribution from the carry.

(defconst *apc-t-c-o* *own-cancel-a*)
(defconst *apc-t-c-sub* (fn-own-inflight *apc-t-c-o*))
(defconst *apc-t-c-tk* (fn-apc-take nil *apc-t-c-sub* nil))
(defconst *apc-t-c-carry* (cdr *apc-t-c-tk*))
(defun apc-t-c-icar () (fn-apc-icar-carry-of *apc-t-c-sub* *apc-t-c-carry*))
(assert-event (fn-apc-p *apc-t-c-carry*))
(assert-event (equal (len *apc-t-c-carry*) 1))
(assert-event (equal (car (fn-apc-classify-octets (car *apc-t-c-tk*) *apc-t-c-carry*))
                     :control))
(assert-event (equal (fn-apc-submission-targets *apc-t-c-o* (apc-t-c-icar) *apc-t-c-carry*)
                     '("out")))
(defun apc-t-c-intent (carry)
  (fn-apc-submission-intent *apc-t-c-o* (apc-t-c-icar) carry
                            *own-control-evidence* 1 3))
(assert-event (equal (apc-t-c-intent *apc-t-c-carry*)
                     (cons (fn-own-submission-intent-result
                            *apc-t-c-o* *own-control-evidence* 1 3)
                           (fn-own-submission-intent-records
                            *apc-t-c-o* *own-control-evidence* 1 3))))
(assert-event (equal (car (apc-t-c-intent *apc-t-c-carry*)) :ready))
(assert-event (equal (len (cdr (apc-t-c-intent *apc-t-c-carry*))) 1))
(assert-event (equal (fn-apc-submission-resolution-records
                      *apc-t-c-o* (apc-t-c-icar) *apc-t-c-carry* :duplicate
                      *own-control-evidence* 1 3)
                     (fn-own-submission-resolution-records *apc-t-c-o* :duplicate
                      *own-control-evidence* 1 3)))
(assert-event (consp (fn-apc-submission-resolution-records
                      *apc-t-c-o* (apc-t-c-icar) *apc-t-c-carry* :duplicate
                      *own-control-evidence* 1 3)))
; Its control filing: exactly control.cancel when the operator created it.
(defconst *apc-t-c-domain* (list "control.cancel" "fn.letters"))
(assert-event (equal (fn-apc-filing-plan (car *apc-t-c-tk*) *apc-t-groups*
                                         *apc-t-c-domain* *apc-t-c-carry*)
                     (fn-pa-filing-plan (car *apc-t-c-tk*) *apc-t-groups*
                                        *apc-t-c-domain*)))
(assert-event (equal (fn-apc-filing-plan (car *apc-t-c-tk*) *apc-t-groups*
                                         *apc-t-c-domain* *apc-t-c-carry*)
                     (list :file (list (fn-nntp-string-octets "control.cancel")))))

; -----------------------------------------------------------------------------
; Reachable witness 3: a transit submission (owner-served-invariants-tests'
; *osi-transit-sub*): the stored octets are the received ones with this
; node's identity on Path, so the carry has two entries, and the finish
; reads the second.

(defconst *apc-t-t-tk* (fn-apc-take *apc-t-cfg* *osi-transit-sub* nil))
(assert-event (equal (car *apc-t-t-tk*) *osi-transit-stored*))
(assert-event (equal (len (cdr *apc-t-t-tk*)) 2))
(assert-event (fn-apc-p (cdr *apc-t-t-tk*)))
(assert-event (equal (strip-cars (cdr *apc-t-t-tk*))
                     (list *osi-transit-stored* *osi-transit-received*)))
(defconst *apc-t-t-finish*
  (apc-t-eval *osi-transit-completing* *apc-t-cfg* *osi-transit-prior*
              (cdr *apc-t-t-tk*)))
(assert-event (equal (nth 0 *apc-t-t-finish*) (nth 1 *apc-t-t-finish*)))
(assert-event (equal (car (nth 0 *apc-t-t-finish*)) :durable))

; -----------------------------------------------------------------------------
; A stale carry (witness 2's, of another article) and the empty carry the
; host starts with: every reader parses and gives the reference.

(assert-event (not (fn-apc-find *apc-t-stored* *apc-t-c-carry*)))
(assert-event (equal (fn-apc-carrier-form *apc-t-stored* *apc-t-c-carry*) :absent))
(assert-event (equal (fn-apc-filing-plan *apc-t-stored* *apc-t-groups* nil *apc-t-c-carry*)
                     (list :file *apc-t-groups*)))
(assert-event (equal (fn-apc-transit-verdict *apc-t-stored* nil nil t nil nil nil)
                     :unsigned))
(assert-event (equal (apc-t-eval *apc-t-o* *apc-t-cfg* *osi-completing-prior* *apc-t-c-carry*)
                     *apc-t-finish*))
(assert-event (equal (apc-t-eval *apc-t-o* *apc-t-cfg* *osi-completing-prior* nil)
                     *apc-t-finish*))
(assert-event (equal (apc-t-c-intent nil) (apc-t-c-intent *apc-t-c-carry*)))
(assert-event (equal (apc-t-c-intent *apc-t-carry*) (apc-t-c-intent *apc-t-c-carry*)))

; -----------------------------------------------------------------------------
; Teeth (CORRUPTED carries, which no take writes).  The one hypothesis of
; every theorem is fn-apc-p.  A carry whose entry for the stored octets
; holds another article's parse violates it, and the readers then differ
; from their references.

; (a) The served article's octets carried with the cancel's parse: the
; filing reads a control article and files it in control.cancel.
(defconst *apc-t-bad-cancel*
  (list (cons *apc-t-stored* (fn-article-parse (car *apc-t-c-tk*)))))
(assert-event (not (fn-apc-p *apc-t-bad-cancel*)))
(assert-event (not (equal (fn-apc-filing-plan *apc-t-stored* *apc-t-groups*
                                              *apc-t-c-domain* *apc-t-bad-cancel*)
                          (fn-pa-filing-plan *apc-t-stored* *apc-t-groups*
                                             *apc-t-c-domain*))))
(assert-event (equal (fn-apc-filing-plan *apc-t-stored* *apc-t-groups*
                                         *apc-t-c-domain* *apc-t-bad-cancel*)
                     (list :file (list (fn-nntp-string-octets "control.cancel")))))

; (b) The served article's octets carried with a parser refusal: the carrier
; form, the transit verdict, the held context and the Cancel-Lock fields
; all read an unparsable article.
(defconst *apc-t-bad-error*
  (list (cons *apc-t-stored* (fn-article-parse '(1 2 3)))))
(assert-event (not (fn-apc-p *apc-t-bad-error*)))
(assert-event (true-listp (fn-article-parse '(1 2 3))))
(assert-event (not (fn-article-result-okp (fn-article-parse '(1 2 3)))))
(assert-event (equal (fn-apc-carrier-form *apc-t-stored* *apc-t-bad-error*)
                     '(:refused :article)))
(assert-event (not (equal (fn-apc-transit-verdict *apc-t-stored* nil nil t nil nil
                                                  *apc-t-bad-error*)
                          (fn-pcb-transit-verdict *apc-t-stored* nil nil t nil nil))))
(assert-event (not (equal (fn-apc-held-context-of *apc-t-stored* nil 0 *apc-t-bad-error*)
                          (fn-held-context-of *apc-t-stored* nil 0))))
(assert-event (not (equal (fn-apc-intern-row-at *apc-t-wire* nil 0 2 *apc-t-bad-error*)
                          (fn-intern-row-at *apc-t-wire* nil 0 2))))
(assert-event (null (fn-apc-received-fields *apc-t-stored* *apc-t-bad-error*)))
(assert-event (not (equal (fn-apc-received-fields *apc-t-stored* *apc-t-bad-error*)
                          (fn-ctl-received-fields *apc-t-stored*))))

; (c) The cancel's octets carried with the served article's parse: the
; intent loses its control groups and offers the cancel to nobody.
(defconst *apc-t-bad-intent*
  (list (cons (car *apc-t-c-tk*) (fn-article-parse *apc-t-stored*))))
(assert-event (not (fn-apc-p *apc-t-bad-intent*)))
(assert-event (null (fn-apc-submission-targets *apc-t-c-o* (apc-t-c-icar)
                                               *apc-t-bad-intent*)))
(assert-event (not (equal (apc-t-c-intent *apc-t-bad-intent*)
                          (apc-t-c-intent *apc-t-c-carry*))))

; The keystone and the host-line equalities without fn-apc-p.
(must-fail-checked
 (defthm apc-t-parse-without-apc-p
   (equal (fn-apc-parse octets carry) (fn-article-parse octets))))
(must-fail-checked
 (defthm apc-t-filing-without-apc-p
   (equal (fn-apc-filing-plan received groups domain carry)
          (fn-pa-filing-plan received groups domain))))
(must-fail-checked
 (defthm apc-t-transit-verdict-without-apc-p
   (equal (fn-apc-transit-verdict received snapshots carried transitp ed ml carry)
          (fn-pcb-transit-verdict received snapshots carried transitp ed ml))))
(must-fail-checked
 (defthm apc-t-row-without-apc-p
   (equal (fn-apc-intern-row-at w keyring generation h carry)
          (fn-intern-row-at w keyring generation h))))
(must-fail-checked
 (defthm apc-t-intent-without-apc-p
   (implies (fn-icar-carryp icar)
            (equal (fn-apc-submission-intent o icar carry evidence generation txid)
                   (cons (fn-own-submission-intent-result o evidence generation txid)
                         (fn-own-submission-intent-records o evidence generation txid))))))

; -----------------------------------------------------------------------------
; keystone-audit 2026-09-27: witnesses the book's keystones lacked.

; fn-apc-held-facts-of-is-reference: reachable positive (witness 1's carry),
; and the CORRUPTED carry (a) (the cancel's parse under the served octets,
; not fn-apc-p) gives other held facts.
(assert-event (fn-apc-p *apc-t-carry*))
(assert-event (equal (fn-apc-held-facts-of *apc-t-stored* *apc-t-carry*)
                     (fn-held-facts-of *apc-t-stored*)))
(assert-event (equal (car (fn-held-facts-of *apc-t-stored*)) 328))
(assert-event (not (fn-apc-p *apc-t-bad-cancel*)))
(assert-event (not (equal (fn-apc-held-facts-of *apc-t-stored* *apc-t-bad-cancel*)
                          (fn-held-facts-of *apc-t-stored*))))

; fn-apc-current-plan-is-reference: the CORRUPTED carry (b) reads a refused
; carrier where the reference reads no carrier.
(assert-event (not (fn-apc-p *apc-t-bad-error*)))
(assert-event (equal (fn-apc-current-plan *apc-t-stored* nil nil t *apc-t-bad-error*)
                     '(:refused :article)))
(assert-event (not (equal (fn-apc-current-plan *apc-t-stored* nil nil t *apc-t-bad-error*)
                          (fn-pa-current-plan *apc-t-stored* nil nil t))))

; fn-apc-own-outcome-is-acar-own-outcome: reachable positive over the owner
; witness 1's finish leaves (connection 4's durable POST, answered 240).
(defun apc-t-outcome-owner ()
  (cdr (nth 0 (apc-t-eval *apc-t-o* *apc-t-cfg* *osi-completing-prior* *apc-t-carry*))))
(assert-event (fn-icar-carryp (apc-t-icar)))
(assert-event (equal (fn-apc-own-outcome (apc-t-outcome-owner) (fn-own-sub-id *apc-t-sub*)
                                         :durable (apc-t-icar) *apc-t-carry*)
                     (fn-acar-own-outcome (apc-t-outcome-owner) (fn-own-sub-id *apc-t-sub*)
                                          :durable)))
(assert-event (equal (car (fn-acar-own-outcome (apc-t-outcome-owner)
                                               (fn-own-sub-id *apc-t-sub*) :durable))
                     (list (list :reply (fn-nntp-string-octets
                                         (concatenate 'string "240 article received OK"
                                                      (coerce (list (code-char 13) (code-char 10))
                                                              'string)))))))

; =============================================================================
; Audit packet G2-P4 (lane audit-fixes, sub-lane g12b): a biting witness for
; fn-apc-own-finish-is-ccar-own-finish's two hypotheses.  The carry reaches
; the finish only through the stored octets of an ACCOUNT's submission (the
; Cancel-Lock the owner writes reads the parse's fields), and no reached
; owner in these books posts under a login.  CONSTRUCTED owner (labelled):
; owner-tests' taken owner (*own-taken*) with its in-flight submission
; replaced by the same injected article under the login "alice" and an
; account (owner-cancel-lock-tests' shape) and a node secret; from it the
; Store runs the host's post events (owner-tests' own-post-events) over the
; record the host stages for that submission -- its stored octets, the
; account's lock in front of the injected octets -- to :completing.
(defconst *apc-g-secret*
  (list (fn-ns-create-entry (fn-record-string-octets "fn.test") (make-list 32 :initial-element 7))))
(defconst *apc-g-account* (make-list 32 :initial-element 1))
(defconst *apc-g-sub*
  (let ((s *osi-sub*))
    (fn-own-sub-make-author (fn-own-sub-id s) (fn-own-sub-version s) (fn-own-sub-mark s)
                            (fn-own-sub-decision s) (fn-record-string-octets "alice") *apc-g-account*)))
(defun apc-g-with-sub (o sub secret)
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
               sub (fn-own-feeds o) secret (fn-own-refused o)))
(defconst *apc-g-taken* (apc-g-with-sub *own-taken* *apc-g-sub* *apc-g-secret*))
(defconst *apc-g-stored* (fn-own-sub-stored-octets *osi-cfg* *apc-g-sub* *apc-g-secret*))
(defconst *apc-g-wire* (osi-record-of-wire 2 2 *apc-g-sub* *apc-g-stored*))
(defconst *apc-g-o*
  (in-arena-fn-own-run *sr-arena* *apc-g-taken*
                       (osi-drop-last (own-post-events (osi-record-of 2 2 *apc-g-sub* *apc-g-stored*)))))
(defconst *apc-g-prior* (osi-prior *apc-g-wire*))
(defconst *apc-g-tk* (fn-apc-take *osi-cfg* *apc-g-sub* *apc-g-secret*))
(defconst *apc-g-carry* (cdr *apc-g-tk*))
(defconst *apc-g-x*
  (fn-ipp-injected-octets (fn-own-sub-decision *apc-g-sub*) *apc-g-secret*
                          (fn-own-sub-login *apc-g-sub*) *osi-cfg*))
; The corrupted carry (no take writes it): the injected octets carried with
; the parse of the same octets under a Cancel-Lock header, so the owner
; thinks the author locked the article and writes no lock of its own.
(defconst *apc-g-bad*
  (list (cons *apc-g-x*
              (fn-article-parse (append (fn-nntp-string-octets "Cancel-Lock: sha256:AAAA") '(13 10)
                                        *apc-g-x*)))))
(defconst *apc-g-finish* (apc-t-eval *apc-g-o* *osi-cfg* *apc-g-prior* *apc-g-carry*))
(defconst *apc-g-bad-finish* (apc-t-eval *apc-g-o* *osi-cfg* *apc-g-prior* *apc-g-bad*))
; Positive: the take's carry, both hypotheses, the equality; the finish is
; :durable and the account's lock is in the stored octets (non-degenerate:
; stored /= injected).

; Removal of (fn-apc-p carry): the index hypothesis holds; the carried
; stored octets lose the lock, so the finish answers :fault where the
; reference answers :durable.

; Removal of (fn-ceis-indexedp (fn-own-store o)) (CORRUPTED Store): the same
; owner with its Store's event index built from no history; fn-apc-p holds,
; the Store is a state and completion-enabled, and the indexed completion's
; owner differs from the reference's (same word).




; Not done here: fn-apc-own-outcome-is-acar-own-outcome's fn-apc-p (the carry
; is read only for peer targets, and no owner here posts with a peer) and
; fn-apc-submission-intent-is-reference's fn-icar-carryp.
