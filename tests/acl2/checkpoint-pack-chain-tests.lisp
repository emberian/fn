; Witnesses and teeth for books/checkpoint-pack-chain (chained packs, P5).
(in-package "ACL2")
(include-book "../../books/checkpoint-pack-chain")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

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
(assert-event (fn-ccc-links-okp *ct-entries*))
(assert-event (equal (fn-ccc-links-events *ct-entries*) *ct-h*))
(assert-event (equal (fn-ccc-coverage-chain *ct-chain* 5 6 *ct-bound*) '(:ok 5 5)))
; A version-0 pack is a first link.
(make-event `(defconst *ct-v0* ',(fn-cc-encode (fn-cc-make 3 3 (take 3 *ct-h*)))))
(assert-event (equal (fn-ccc-decode-link *ct-v0* *ct-bound*) (list :ok *ct-link-a*)))

; ---------------------------------------------------------------------------
; fn-ccc-capture-extends-the-chain: reachable, and one tooth per hypothesis.
(defconst *ct-one* (list (list 0 *ct-link-a* *ct-da*)))
(assert-event (fn-ccc-links-okp *ct-one*))
(assert-event (fn-ccc-prefixp (fn-ccc-links-events *ct-one*) *ct-h*))
(assert-event (fn-ccc-links-okp (cons (list 1 *ct-link-b* *ct-db*) *ct-one*)))
; Without a valid chain: link A with a wrong lower frontier.  The prefix and
; the capture hold; the extended chain is refused.
(defconst *ct-bad-a* (list (list 0 (fn-ccc-make 0 3 1 3 0 nil (take 3 *ct-h*)) *ct-da*)))
(assert-event (and (consp *ct-bad-a*)
                   (fn-ccc-prefixp (fn-ccc-links-events *ct-bad-a*) *ct-h*)
                   (equal (car (fn-ccc-capture-link *ct-h* 3 3 0 *ct-da*)) :ok)))
(local (must-fail (defthm ct-extends-without-chain
                    (fn-ccc-links-okp (cons (list 1 *ct-link-b* *ct-db*) *ct-bad-a*)))))
; Without the prefix: the chain's records are not the history's; the new
; chain is not a prefix of it.
(defconst *ct-other* (list (nth 1 *ct-h*) (nth 0 *ct-h*) (nth 2 *ct-h*)
                           (nth 3 *ct-h*) (nth 4 *ct-h*)))
(local (must-fail (defthm ct-extends-without-prefix
                    (fn-ccc-prefixp (fn-ccc-links-events
                                     (cons (list 1 *ct-link-b* *ct-db*) *ct-one*))
                                    *ct-other*))))
; Without a successful capture: a history already covered.
(assert-event (not (equal (car (fn-ccc-capture-link (take 3 *ct-h*) 3 3 0 *ct-da*)) :ok)))

; ---------------------------------------------------------------------------
; fn-ccc-chain-reconstructs-the-history and the reclaim keystone.
(defconst *ct-observed* (list (list 0 (nth 0 *ct-h*)) (list 1 (nth 1 *ct-h*))
                              (list 2 (nth 2 *ct-h*)) (list 3 (nth 3 *ct-h*))
                              (list 4 (nth 4 *ct-h*))))
(assert-event (and (fn-ccp-contiguousp *ct-observed* 0)
                   (fn-ccc-pairs-match *ct-observed* *ct-h*)
                   (fn-cc-valid-suffixp (fn-ccc-chain-summary *ct-entries*) nil 6)))
(assert-event (equal (fn-ccc-observe-chain *ct-chain* *ct-observed* 6 *ct-bound*)
                     (list :ok *ct-h* 6)))
; After a reclaim of the covered names only the empty suffix is left.
(assert-event (equal (fn-ccc-observe-chain *ct-chain* nil 6 *ct-bound*)
                     (list :ok *ct-h* 6)))
; Without integrity (the digest is not the trailer): refused.
(defconst *ct-chain-torn* (list (list 1 *ct-fb* *ct-da*) (list 0 *ct-fa* *ct-da*)))
(local (must-fail (defthm ct-reconstructs-without-integrity
                    (equal (fn-ccc-observe-chain *ct-chain-torn* *ct-observed* 6 *ct-bound*)
                           (list :ok *ct-h* 6)))))
; Without a linked chain: B names a foreign predecessor digest.
(defconst *ct-chain-unlinked* (list (list 1 *ct-fb* *ct-db*)
                                    (list 0 *ct-fa* *ct-da*) ))
(make-event `(defconst *ct-fb-foreign* ',(append (fn-ccc-encode-link (cadr (fn-ccc-capture-link *ct-h* 3 3 0 *ct-db*))) *ct-db*)))
(local (must-fail (defthm ct-reconstructs-without-link
                    (equal (fn-ccc-observe-chain
                            (list (list 1 *ct-fb-foreign* *ct-db*) (list 0 *ct-fa* *ct-da*))
                            *ct-observed* 6 *ct-bound*)
                           (list :ok *ct-h* 6)))))
; Without the prefix: the observation holds another history.
(local (must-fail (defthm ct-reconstructs-without-prefix
                    (equal (fn-ccc-observe-chain *ct-chain*
                                                 (list (list 0 (nth 1 *ct-h*)) (list 1 (nth 0 *ct-h*))
                                                       (list 2 (nth 2 *ct-h*)) (list 3 (nth 3 *ct-h*))
                                                       (list 4 (nth 4 *ct-h*)))
                                                 6 *ct-bound*)
                           (list :ok *ct-other* 6)))))
; Without a complete observation: a missing newest record is not H.
(local (must-fail (defthm ct-reconstructs-without-complete-observation
                    (equal (fn-ccc-observe-chain *ct-chain* (butlast *ct-observed* 1)
                                                 6 *ct-bound*)
                           (list :ok (append *ct-h* (list (nth 4 *ct-h*))) 6)))))
; Without a valid suffix under the final frontier: frontier 5 is below txid 4 + 1
; for a record above the chain.
(defconst *ct-short* (list (list 0 *ct-fa* *ct-da*)))
(local (must-fail (defthm ct-reconstructs-without-valid-suffix
                    (equal (fn-ccc-observe-chain *ct-short* *ct-observed* 4 *ct-bound*)
                           (list :ok *ct-h* 4)))))

; ---------------------------------------------------------------------------
; fn-ccc-retire-plan-keeps-the-chain: generation 2 (outside) goes, 0 and 1 stay.
(assert-event (equal (fn-ccc-retire-plan '(0 1 2) *ct-chain* *ct-bound*) '(2)))
(assert-event (equal (fn-ccc-retire-plan '(0 1 2) *ct-chain-torn* *ct-bound*) :invalid))

; ---------------------------------------------------------------------------
; fn-ccc-publication-crash-walks-old-or-new-chain.
(defconst *ct-files* (list (cons 0 (cons *ct-fa* *ct-da*))))
(defconst *ct-image* (list (cons 1 (cons *ct-fb* *ct-db*)) (cons 0 (cons *ct-fa* *ct-da*))))
(assert-event (equal (fn-ccc-walk *ct-files* 0 1 *ct-bound*) (list (list 0 *ct-fa* *ct-da*))))
(assert-event (equal (fn-ccc-entry-step *ct-fb* *ct-db* *ct-bound*) '(:ok 3 0)))
(assert-event (equal (fn-ccc-walk *ct-image* 1 2 *ct-bound*) *ct-chain*))
(assert-event (equal (fn-ccc-walk *ct-image* 0 2 *ct-bound*) (list (list 0 *ct-fa* *ct-da*))))
; Without the old chain's files kept: the image lost generation 0.
(local (must-fail (defthm ct-crash-without-agreement
                    (equal (fn-ccc-walk (list (cons 1 (cons *ct-fb* *ct-db*))) 1 2 *ct-bound*)
                           *ct-chain*))))
; Without the new link's complete bytes: a torn candidate is selected.
(local (must-fail (defthm ct-crash-without-complete-candidate
                    (not (equal (fn-ccc-walk (list (cons 1 (cons (butlast *ct-fb* 1) *ct-db*))
                                                   (cons 0 (cons *ct-fa* *ct-da*)))
                                             1 2 *ct-bound*)
                                :bad)))))
; Without fuel: none walks nothing.
(assert-event (equal (fn-ccc-walk *ct-files* 0 0 *ct-bound*) :bad))
