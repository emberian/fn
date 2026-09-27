; Witnesses and teeth for books/checkpoint-pack-chain-once (PRF-240): each
; link decoded once per open, every answer the reference's under a sound memo.
(in-package "ACL2")
(include-book "../../books/checkpoint-pack-chain-once")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

; The fixtures of tests/acl2/checkpoint-pack-chain-tests.lisp: a two-link
; chain over a five-event history.
; The five-event history of the compaction tests: txids 0..4, frontier 6.
(defconst *ct-a0*
  (fn-record-make 0 0 0 "<chain@example.invalid>" '(65 13 10)
                  '("fn.letters") "archive-0" "subject-0" "evidence-0" 3 841000000))
(defconst *ct-e1*
  (fn-store-retention-event-make :undertake 1 1 1 "forward-1" "subject-1" "evidence-1" 2))
(defconst *ct-e2*
  (fn-store-retention-event-make :release 2 2 2 "forward-1" "subject-1" "receipt-1" 0))
(defconst *ct-i3*
  (fn-stxe-make 3 3 3 "<chain@example.invalid>" :unverified
                '(117 110 118 101 114 105 102 105 101 100) 7 '(116 101 115 116)))
(defconst *ct-k4*
  (fn-stxk-make 4 4 4 7 '(116 101 115 116) '(1 2 3 4)))
(make-event `(defconst *ct-h*
               ',(list (fn-store-event-encode *ct-a0*) (fn-store-event-encode *ct-e1*)
                       (fn-store-event-encode *ct-e2*) (fn-store-event-encode *ct-i3*)
                       (fn-store-event-encode *ct-k4*))))
(assert-event (fn-cc-octet-event-listp *ct-h* 0 0 6))

; A two-link chain: link A covers [0,3) (a hand-made first link), link B is
; the capture of the uncovered suffix above it.  Digests are the host's
; trailers; the model compares them, it does not compute them.
(defconst *ct-da* (make-list 32 :initial-element 7))
(defconst *ct-db* (make-list 32 :initial-element 9))
(defconst *ct-link-a* (fn-ccc-make 0 3 0 3 0 nil (take 3 *ct-h*)))
(assert-event (fn-ccc-linkp *ct-link-a*))
(make-event `(defconst *ct-cap-b* ',(fn-ccc-capture-link *ct-h* 3 3 0 *ct-da*)))
(assert-event (equal (car *ct-cap-b*) :ok))
(defconst *ct-link-b* (cadr *ct-cap-b*))
(assert-event (and (equal (fn-ccc-boundary *ct-link-b*) 5)
                   (equal (fn-ccc-frontier *ct-link-b*) 5)
                   (equal (fn-ccc-events *ct-link-b*) (nthcdr 3 *ct-h*))))
(make-event `(defconst *ct-bound* ',(fn-ccc-link-octet-bound *fn-bs-profile-development*)))
(make-event `(defconst *ct-fa* ',(append (fn-ccc-encode-link *ct-link-a*) *ct-da*)))
(make-event `(defconst *ct-fb* ',(append (fn-ccc-encode-link *ct-link-b*) *ct-db*)))
(defconst *ct-chain* (list (list 1 *ct-fb* *ct-db*) (list 0 *ct-fa* *ct-da*)))
; The codec, executed: each link decodes to itself (no round-trip theorem;
; see the evidence record).
(assert-event (equal (fn-ccc-decode-link (fn-ccc-encode-link *ct-link-b*) *ct-bound*)
                     (list :ok *ct-link-b*)))
(make-event `(defconst *ct-entries* ',(fn-ccc-decode-entries *ct-chain* *ct-bound*)))
(assert-event (equal *ct-entries* (list (list 1 *ct-link-b* *ct-db*)
                                        (list 0 *ct-link-a* *ct-da*))))
(defconst *ct-observed* (list (list 0 (nth 0 *ct-h*)) (list 1 (nth 1 *ct-h*))
                              (list 2 (nth 2 *ct-h*)) (list 3 (nth 3 *ct-h*))
                              (list 4 (nth 4 *ct-h*))))

; -----------------------------------------------------------------------------
; The memo the open builds: the walk's steps and the coverage remember each
; link once; the memo is sound, and it holds both links.
(make-event `(defconst *ct-memo* ',(fn-ccco-remember-all *ct-chain* *ct-bound* nil)))
(assert-event (fn-ccco-memo-soundp *ct-memo*))
(assert-event (equal (len *ct-memo*) 2))
(assert-event (and (fn-ccco-lookup *ct-fb* *ct-db* *ct-bound* *ct-memo*)
                   (fn-ccco-lookup *ct-fa* *ct-da* *ct-bound* *ct-memo*)))
; A second remember of the same chain decodes nothing and adds nothing.
(assert-event (equal (fn-ccco-remember-all *ct-chain* *ct-bound* *ct-memo*) *ct-memo*))
(assert-event (equal (fn-ccco-remember *ct-fb* *ct-db* *ct-bound* *ct-memo*) *ct-memo*))

; Positive witnesses, per keystone: the complete antecedent (a sound memo
; that holds the links) and the conclusion, on a chain that covers and
; reconstructs.
(assert-event (equal (fn-ccco-entry-step *ct-fb* *ct-db* *ct-bound* *ct-memo*)
                     (fn-ccc-entry-step *ct-fb* *ct-db* *ct-bound*)))
(assert-event (equal (fn-ccco-entry-step *ct-fb* *ct-db* *ct-bound* *ct-memo*) '(:ok 3 0)))
(assert-event (equal (fn-ccco-coverage-chain *ct-chain* 5 6 *ct-bound* *ct-memo*)
                     (fn-ccc-coverage-chain *ct-chain* 5 6 *ct-bound*)))
(assert-event (equal (fn-ccco-coverage-chain *ct-chain* 5 6 *ct-bound* *ct-memo*) '(:ok 5 5)))
(assert-event (equal (fn-ccco-observe-chain *ct-chain* *ct-observed* 6 *ct-bound* *ct-memo*)
                     (fn-ccc-observe-chain *ct-chain* *ct-observed* 6 *ct-bound*)))
(assert-event (equal (fn-ccco-observe-chain *ct-chain* *ct-observed* 6 *ct-bound* *ct-memo*)
                     (list :ok *ct-h* 6)))
; The corrupt chain (a digest that is not the trailer) is refused as the
; reference refuses it, from the memo too.
(defconst *ct-chain-torn* (list (list 1 *ct-fb* *ct-da*) (list 0 *ct-fa* *ct-da*)))
(make-event `(defconst *ct-memo-torn* ',(fn-ccco-remember-all *ct-chain-torn* *ct-bound* *ct-memo*)))
(assert-event (fn-ccco-memo-soundp *ct-memo-torn*))
(assert-event (equal (fn-ccco-coverage-chain *ct-chain-torn* 5 6 *ct-bound* *ct-memo-torn*)
                     '(:error :integrity)))
(assert-event (equal (fn-ccco-coverage-chain *ct-chain-torn* 5 6 *ct-bound* *ct-memo-torn*)
                     (fn-ccc-coverage-chain *ct-chain-torn* 5 6 *ct-bound*)))

; Hypothesis removal (fn-ccco-memo-soundp): a memo that remembers link A's
; decode under link B's bytes.  The retained hypotheses are none; the
; omitted one fails; each conclusion fails; so each keystone without it
; is false.
(defconst *ct-memo-lie*
  (list (list *ct-fb* *ct-db* *ct-bound* (list :ok *ct-link-a*))))
(assert-event (not (fn-ccco-memo-soundp *ct-memo-lie*)))
(assert-event (not (equal (fn-ccco-entry-step *ct-fb* *ct-db* *ct-bound* *ct-memo-lie*)
                          (fn-ccc-entry-step *ct-fb* *ct-db* *ct-bound*))))
(local (must-fail (defthm ct-step-without-sound-memo
                    (equal (fn-ccco-entry-step framed digest max memo)
                           (fn-ccc-entry-step framed digest max)))))
(assert-event (not (equal (fn-ccco-coverage-chain *ct-chain* 5 6 *ct-bound* *ct-memo-lie*)
                          (fn-ccc-coverage-chain *ct-chain* 5 6 *ct-bound*))))
(local (must-fail (defthm ct-coverage-without-sound-memo
                    (equal (fn-ccco-coverage-chain framed count frontier max memo)
                           (fn-ccc-coverage-chain framed count frontier max)))))
(assert-event (not (equal (fn-ccco-observe-chain *ct-chain* *ct-observed* 6 *ct-bound* *ct-memo-lie*)
                          (fn-ccc-observe-chain *ct-chain* *ct-observed* 6 *ct-bound*))))
(local (must-fail (defthm ct-observe-without-sound-memo
                    (equal (fn-ccco-observe-chain framed observed frontier max memo)
                           (fn-ccc-observe-chain framed observed frontier max)))))

; fn-ccco-links-okp-of-decoded: over decoded entries the chain check is its
; chaining conditions.  Witness: the decoded two-link chain.
(make-event `(defconst *ct-entries* ',(fn-ccc-decode-entries *ct-chain* *ct-bound*)))
(assert-event (and (not (equal *ct-entries* :bad))
                   (fn-ccc-links-okp *ct-entries*)
                   (fn-ccco-links-chainedp *ct-entries*)))
; Without its hypothesis (entries that no decode produced): link A with one
; event dropped is chained but no link, so the two checks differ.
(defconst *ct-short-a* (fn-ccc-make 0 3 0 3 0 nil (take 2 *ct-h*)))
(defconst *ct-entries-short* (list (list 0 *ct-short-a* *ct-da*)))
(assert-event (and (fn-ccco-links-chainedp *ct-entries-short*)
                   (not (fn-ccc-links-okp *ct-entries-short*))))
(local (must-fail (defthm ct-links-okp-without-decoded
                    (equal (fn-ccc-links-okp entries)
                           (fn-ccco-links-chainedp entries)))))

; The single-dispatch decode (no hypotheses): each twin agrees with its
; reference on a link that decodes and on one that does not.
(assert-event (equal (fn-ccco-framed-link-fast *ct-fb* *ct-db* *ct-bound*)
                     (fn-ccc-framed-link *ct-fb* *ct-db* *ct-bound*)))
(assert-event (equal (car (fn-ccco-framed-link-fast *ct-fb* *ct-db* *ct-bound*)) :ok))
(assert-event (equal (fn-ccco-framed-link-fast *ct-fb* *ct-da* *ct-bound*)
                     (fn-ccc-framed-link *ct-fb* *ct-da* *ct-bound*)))
(assert-event (equal (fn-ccco-framed-link-fast *ct-fb* *ct-da* *ct-bound*) '(:error :integrity)))
(assert-event (equal (fn-ccco-octet-event-listp *ct-h* 0 0 6) (fn-cc-octet-event-listp *ct-h* 0 0 6)))
(assert-event (fn-ccco-octet-event-listp *ct-h* 0 0 6))
(assert-event (not (fn-ccco-octet-event-listp *ct-h* 1 0 6)))
(assert-event (equal (fn-ccco-event-fields *ct-a0*) (list t 0 0 0)))
(assert-event (equal (fn-ccco-event-fields *ct-e1*)
                     (list t (fn-store-event-sequence *ct-e1*) (fn-store-event-txid *ct-e1*)
                           (fn-store-event-generation *ct-e1*))))
(assert-event (equal (fn-ccco-event-fields 'not-an-event) (list nil nil nil nil)))

; fn-ccco-coverage-headers-is-coverage-chain (PKT-686): the coverage over
; link headers is the reference's coverage.  Reachable witness: the decoded
; two-link chain, with the open's memo and with none (compaction's case),
; the complete antecedent (a sound memo) and the conclusion (:ok 5 5); the
; headers carry no event.
(assert-event (and (fn-ccco-memo-soundp *ct-memo*) (fn-ccco-memo-soundp nil)))
(assert-event (equal (fn-ccco-coverage-headers *ct-chain* 5 6 *ct-bound* nil)
                     (fn-ccc-coverage-chain *ct-chain* 5 6 *ct-bound*)))
(assert-event (equal (fn-ccco-coverage-headers *ct-chain* 5 6 *ct-bound* *ct-memo*)
                     '(:ok 5 5)))
(assert-event (equal (fn-ccco-decode-headers *ct-chain* *ct-bound* nil)
                     (list (list 1 (fn-ccco-link-header *ct-link-b*) *ct-db*)
                           (list 0 (fn-ccco-link-header *ct-link-a*) *ct-da*))))
(assert-event (null (fn-ccc-events (fn-ccco-link-header *ct-link-b*))))
; Each refusal agrees: a torn link (integrity), an unchained pair (chain), a
; count below the boundary (coverage).
(assert-event (equal (fn-ccco-coverage-headers *ct-chain-torn* 5 6 *ct-bound* nil)
                     '(:error :integrity)))
(assert-event (equal (fn-ccco-coverage-headers (list (list 1 *ct-fb* *ct-db*)) 5 6 *ct-bound* nil)
                     (fn-ccc-coverage-chain (list (list 1 *ct-fb* *ct-db*)) 5 6 *ct-bound*)))
(assert-event (equal (fn-ccco-coverage-headers (list (list 1 *ct-fb* *ct-db*)) 5 6 *ct-bound* nil)
                     '(:error :chain)))
(assert-event (equal (fn-ccco-coverage-headers *ct-chain* 4 6 *ct-bound* nil)
                     (fn-ccc-coverage-chain *ct-chain* 4 6 *ct-bound*)))
(assert-event (equal (fn-ccco-coverage-headers *ct-chain* 4 6 *ct-bound* nil)
                     '(:error :coverage)))
; Hypothesis removal (fn-ccco-memo-soundp): under the lying memo the
; conclusion fails, so the keystone without it is false.
(assert-event (not (fn-ccco-memo-soundp *ct-memo-lie*)))
(assert-event (not (equal (fn-ccco-coverage-headers *ct-chain* 5 6 *ct-bound* *ct-memo-lie*)
                          (fn-ccc-coverage-chain *ct-chain* 5 6 *ct-bound*))))
(local (must-fail (defthm ct-coverage-headers-without-sound-memo
                    (equal (fn-ccco-coverage-headers framed count frontier max memo)
                           (fn-ccc-coverage-chain framed count frontier max)))))
