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

;
; The observation from N: every reclaim cut.  The full antecedent and the
; conclusion at N = 3 (link A's files reclaimed, B's still present) and N = 5
; (every covered file reclaimed; the empty observation).
(defconst *ct-from-3* (list (list 3 (nth 3 *ct-h*)) (list 4 (nth 4 *ct-h*))))
(assert-event (and (not (equal *ct-entries* :bad))
                   (fn-ccc-links-okp *ct-entries*)
                   (fn-ccc-prefixp (fn-ccc-links-events *ct-entries*) *ct-h*)
                   (true-listp *ct-h*)
                   (<= 3 (len (fn-ccc-links-events *ct-entries*)))
                   (fn-ccp-contiguousp *ct-from-3* 3)
                   (fn-ccc-pairs-match *ct-from-3* *ct-h*)
                   (equal (+ 3 (len *ct-from-3*)) (len *ct-h*))
                   (fn-cc-valid-suffixp (fn-ccc-chain-summary *ct-entries*)
                                        (fn-cc-observation-suffix *ct-from-3* 5) 6)
                   (equal (fn-ccc-observe-chain *ct-chain* *ct-from-3* 6 *ct-bound*)
                          (list :ok *ct-h* 6))))
(assert-event (and (<= 5 (len (fn-ccc-links-events *ct-entries*)))
                   (fn-ccp-contiguousp nil 5)
                   (equal (+ 5 (len nil)) (len *ct-h*))
                   (fn-cc-valid-suffixp (fn-ccc-chain-summary *ct-entries*) nil 6)
                   (equal (fn-ccc-observe-chain *ct-chain* nil 6 *ct-bound*)
                          (list :ok *ct-h* 6))))
; Without N at or below the boundary: link A alone (boundary 3) and a history
; with a record X at sequence 3 whose file is gone (N = 4).  Every other
; hypothesis holds; the reconstruction lacks X, so it is not the history.
(defconst *ct-gap-h* (list (nth 0 *ct-h*) (nth 1 *ct-h*) (nth 2 *ct-h*)
                           (nth 1 *ct-h*) (nth 3 *ct-h*) (nth 4 *ct-h*)))
(defconst *ct-from-4* (list (list 4 (nth 3 *ct-h*)) (list 5 (nth 4 *ct-h*))))
(make-event `(defconst *ct-short-entries*
               ',(fn-ccc-decode-entries *ct-short* *ct-bound*)))
(assert-event (and (not (equal *ct-short-entries* :bad))
                   (fn-ccc-links-okp *ct-short-entries*)
                   (fn-ccc-prefixp (fn-ccc-links-events *ct-short-entries*) *ct-gap-h*)
                   (true-listp *ct-gap-h*)
                   (natp 4)
                   (not (<= 4 (len (fn-ccc-links-events *ct-short-entries*))))
                   (fn-ccp-contiguousp *ct-from-4* 4)
                   (fn-ccc-pairs-match *ct-from-4* *ct-gap-h*)
                   (equal (+ 4 (len *ct-from-4*)) (len *ct-gap-h*))
                   (fn-cc-valid-suffixp (fn-ccc-chain-summary *ct-short-entries*)
                                        (fn-cc-observation-suffix *ct-from-4* 3) 6)))
(local (must-fail (defthm ct-reconstructs-without-n-within-boundary
                    (equal (fn-ccc-observe-chain *ct-short* *ct-from-4* 6 *ct-bound*)
                           (list :ok *ct-gap-h* 6)))))

; Without the history a true list: H with a non-nil final tail.  Every other
; hypothesis holds; the reconstruction is a true list, so it is not H.
(defconst *ct-dotted-h* (append *ct-h* 7))
; (pairs-match's guard asks for a true list, so its instance is a theorem.)
(local (defthm ct-dotted-retained-hypotheses
         (and (fn-ccc-prefixp (fn-ccc-links-events *ct-entries*) *ct-dotted-h*)
              (not (true-listp *ct-dotted-h*))
              (fn-ccp-contiguousp *ct-observed* 0)
              (fn-ccc-pairs-match *ct-observed* *ct-dotted-h*)
              (equal (+ 0 (len *ct-observed*)) (len *ct-dotted-h*)))
         :rule-classes nil))
(local (must-fail (defthm ct-reconstructs-without-true-list
                    (equal (fn-ccc-observe-chain *ct-chain* *ct-observed* 6 *ct-bound*)
                           (list :ok *ct-dotted-h* 6)))))
; Without the files matching H: link A alone, the complete observation of the
; five records, and a history whose record 4 differs.  The prefix, the count
; and the valid suffix hold; the reconstruction is the files', not H.
(defconst *ct-other-4* (list (nth 0 *ct-h*) (nth 1 *ct-h*) (nth 2 *ct-h*)
                             (nth 3 *ct-h*) (nth 2 *ct-h*)))
(assert-event (and (fn-ccc-prefixp (fn-ccc-links-events *ct-short-entries*) *ct-other-4*)
                   (<= 0 (len (fn-ccc-links-events *ct-short-entries*)))
                   (fn-ccp-contiguousp *ct-observed* 0)
                   (not (fn-ccc-pairs-match *ct-observed* *ct-other-4*))
                   (equal (len *ct-observed*) (len *ct-other-4*))
                   (fn-cc-valid-suffixp (fn-ccc-chain-summary *ct-short-entries*)
                                        (fn-cc-observation-suffix *ct-observed* 3) 6)))
(local (must-fail (defthm ct-reconstructs-without-pairs-match
                    (equal (fn-ccc-observe-chain *ct-short* *ct-observed* 6 *ct-bound*)
                           (list :ok *ct-other-4* 6)))))
; Not toothed: the contiguity of the observation.  Below the boundary a gap
; is harmless (the chain holds those records) and above it the valid suffix
; refuses one; it is not proved redundant, so it stays.

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

; Nothing uncovered (fn-ccc-nothing-uncovered-leaves-files-and-marker-by-definition): the
; chain A+B covers all five records, so the capture above it is the named
; no-op and the pack changes neither the files nor the marker, selected or not.
(assert-event (equal (fn-ccc-capture-link *ct-h* 5 5 1 *ct-db*)
                     '(:nothing-uncovered 5)))
(assert-event (equal (fn-ccc-pack-effect *ct-image* 1 2
                                         (fn-ccc-capture-link *ct-h* 5 5 1 *ct-db*)
                                         t)
                     (list *ct-image* 1)))
; One uncovered record gives a capture, not the no-op: the link over record 4
; is added under generation 2 and, with select, the marker moves to it.
(assert-event (equal (car (fn-ccc-capture-link *ct-h* 4 4 1 *ct-db*)) :ok))
(assert-event (equal (fn-ccc-boundary (cadr (fn-ccc-capture-link *ct-h* 4 4 1 *ct-db*)))
                     5))
(assert-event (let ((e (fn-ccc-pack-effect *ct-image* 1 2
                                           (fn-ccc-capture-link *ct-h* 4 4 1 *ct-db*)
                                           t)))
                (and (not (equal (car e) *ct-image*))
                     (equal (cadr e) 2)
                     (equal (cdr (car e)) *ct-image*))))
; Teeth: without its one hypothesis (the chain's boundary is the whole
; history), the no-op conclusion fails; the witness is one uncovered record.
(must-fail
 (thm (equal (fn-ccc-capture-link records lower lf gen digest)
             (list :nothing-uncovered lower))
      :hints (("Goal" :in-theory (enable fn-ccc-capture-link)))))
(must-fail
 (thm (equal (fn-ccc-capture-link *ct-h* 4 4 1 *ct-db*)
             (list :nothing-uncovered 4))))

; ---------------------------------------------------------------------------
; The chain program's between-links cut, `pack-chain-link'
; (fn-ccc-chain-link-cut-walks-the-extended-chain,
; fn-ccc-chain-link-cut-reopens-to-the-history).  The host publishes and
; selects link A under generation 0 on a store with no chain, then link B
; under generation 1: a two-link compaction.
(defconst *ct-links* (list (list 0 *ct-fa* *ct-da*) (list 1 *ct-fb* *ct-db*)))
(defconst *ct-run* (fn-ccc-chain-run nil (fn-ccc-chain-program *ct-links*)))
; The cut follows each link's selection: steps 2 and 5.
(assert-event (equal (fn-ccc-chain-program *ct-links*)
                     (list (list :publish (car *ct-links*)) (list :select 0)
                           (list :cut "pack-chain-link")
                           (list :publish (cadr *ct-links*)) (list :select 1)
                           (list :cut "pack-chain-link"))))

; Reachable witness at the second cut (N = 2, FUEL 0, OLD nil): the complete
; antecedent of both keystones, then both conclusions.
(assert-event (and (posp 2) (<= 2 (len *ct-links*)) (natp 0)
                   (not (equal nil :bad))
                   (fn-ccc-entry-triplesp (take 2 *ct-links*))
                   (fn-ccc-new-links-okp (revappend (take 2 *ct-links*) nil) nil *ct-bound*)
                   (no-duplicatesp-equal
                    (fn-ccc-entries-generations (revappend (take 2 *ct-links*) nil)))
                   (equal (revappend (take 2 *ct-links*) nil) *ct-chain*)
                   (not (equal *ct-entries* :bad))
                   (fn-ccc-links-okp *ct-entries*)
                   (fn-ccc-prefixp (fn-ccc-links-events *ct-entries*) *ct-h*)
                   (true-listp *ct-h*)
                   (<= 0 (len (fn-ccc-links-events *ct-entries*)))
                   (fn-ccp-contiguousp *ct-observed* 0)
                   (fn-ccc-pairs-match *ct-observed* *ct-h*)
                   (equal (+ 0 (len *ct-observed*)) (len *ct-h*))
                   (fn-cc-valid-suffixp (fn-ccc-chain-summary *ct-entries*)
                                        (fn-cc-observation-suffix *ct-observed* 5) 6)))
(assert-event (let ((image (nth 5 *ct-run*)))
                (and (equal image (nth 4 *ct-run*))
                     (equal (cdr image) 1)
                     (equal (fn-ccc-walk (car image) (cdr image) 2 *ct-bound*) *ct-chain*)
                     (equal (fn-ccc-observe-chain
                             (fn-ccc-walk (car image) (cdr image) 2 *ct-bound*)
                             *ct-observed* 6 *ct-bound*)
                            (list :ok *ct-h* 6)))))
; And at the first cut (N = 1): link A alone is selected and walked.
(assert-event (let ((image (nth 2 *ct-run*)))
                (and (equal image (nth 1 *ct-run*))
                     (equal (cdr image) 0)
                     (equal (fn-ccc-walk (car image) (cdr image) 1 *ct-bound*)
                            (list (car *ct-links*))))))

; Without the order (the host's chain names each predecessor): B published
; and selected first, then A.  The triples, the distinct generations and the
; bound hold; the order fails; the image selects A alone, not the chain the
; host consed, and the reopen misses B's records.
(defconst *ct-links-swapped* (list (cadr *ct-links*) (car *ct-links*)))
(defconst *ct-run-swapped*
  (fn-ccc-chain-run nil (fn-ccc-chain-program *ct-links-swapped*)))
(assert-event (and (fn-ccc-entry-triplesp (take 2 *ct-links-swapped*))
                   (no-duplicatesp-equal
                    (fn-ccc-entries-generations (revappend (take 2 *ct-links-swapped*) nil)))
                   (not (fn-ccc-new-links-okp (revappend (take 2 *ct-links-swapped*) nil)
                                              nil *ct-bound*))))
(local (must-fail (defthm ct-link-cut-without-order
                    (equal (fn-ccc-walk (car (nth 5 *ct-run-swapped*))
                                        (cdr (nth 5 *ct-run-swapped*)) 2 *ct-bound*)
                           (revappend (take 2 *ct-links-swapped*) nil)))))
(assert-event (not (equal (fn-ccc-walk (car (nth 5 *ct-run-swapped*))
                                        (cdr (nth 5 *ct-run-swapped*)) 2 *ct-bound*)
                           (revappend (take 2 *ct-links-swapped*) nil))))
; With every covered file reclaimed (the empty observation, N = 5, the
; reopen's hardest case) the swapped image reopens to A's three records, not
; the history; the same observation over the host's chain answers it.
(assert-event (equal (fn-ccc-observe-chain *ct-chain* nil 6 *ct-bound*)
                     (list :ok *ct-h* 6)))
(local (must-fail (defthm ct-link-cut-reopen-without-order
                    (equal (fn-ccc-observe-chain
                            (fn-ccc-walk (car (nth 5 *ct-run-swapped*))
                                         (cdr (nth 5 *ct-run-swapped*)) 2 *ct-bound*)
                            nil 6 *ct-bound*)
                           (list :ok *ct-h* 6)))))
(assert-event (not (equal (fn-ccc-observe-chain
                           (fn-ccc-walk (car (nth 5 *ct-run-swapped*))
                                        (cdr (nth 5 *ct-run-swapped*)) 2 *ct-bound*)
                           nil 6 *ct-bound*)
                          (list :ok *ct-h* 6))))

; Without distinct generations: B published under A's generation 0.  The
; order holds (B names 0); the walk from 0 reads B again and again and runs
; out of fuel.
(defconst *ct-links-reused* (list (car *ct-links*) (list 0 *ct-fb* *ct-db*)))
(defconst *ct-run-reused*
  (fn-ccc-chain-run nil (fn-ccc-chain-program *ct-links-reused*)))
(assert-event (and (fn-ccc-entry-triplesp (take 2 *ct-links-reused*))
                   (fn-ccc-new-links-okp (revappend (take 2 *ct-links-reused*) nil)
                                         nil *ct-bound*)
                   (not (no-duplicatesp-equal
                         (fn-ccc-entries-generations
                          (revappend (take 2 *ct-links-reused*) nil))))))
(local (must-fail (defthm ct-link-cut-without-fresh-generations
                    (equal (fn-ccc-walk (car (nth 5 *ct-run-reused*))
                                        (cdr (nth 5 *ct-run-reused*)) 2 *ct-bound*)
                           (revappend (take 2 *ct-links-reused*) nil)))))
(assert-event (not (equal (fn-ccc-walk (car (nth 5 *ct-run-reused*))
                                        (cdr (nth 5 *ct-run-reused*)) 2 *ct-bound*)
                           (revappend (take 2 *ct-links-reused*) nil))))

; Without a readable chain below: B alone on a store whose selected
; generation 0 has no file.  The order (B names 0) and the rest hold; the
; walk below B fails.
(defconst *ct-links-orphan* (list (cadr *ct-links*)))
(defconst *ct-run-orphan*
  (fn-ccc-chain-run (cons nil 0) (fn-ccc-chain-program *ct-links-orphan*)))
(assert-event (and (equal (fn-ccc-walk nil 0 0 *ct-bound*) :bad)
                   (fn-ccc-entry-triplesp (take 1 *ct-links-orphan*))
                   (fn-ccc-new-links-okp (revappend (take 1 *ct-links-orphan*) nil)
                                         0 *ct-bound*)
                   (no-duplicatesp-equal
                    (fn-ccc-entries-generations
                     (revappend (take 1 *ct-links-orphan*) :bad)))))
(local (must-fail (defthm ct-link-cut-without-old-chain
                    (equal (fn-ccc-walk (car (nth 2 *ct-run-orphan*))
                                        (cdr (nth 2 *ct-run-orphan*)) 1 *ct-bound*)
                           (revappend (take 1 *ct-links-orphan*) :bad)))))
(assert-event (not (equal (fn-ccc-walk (car (nth 2 *ct-run-orphan*))
                                        (cdr (nth 2 *ct-run-orphan*)) 1 *ct-bound*)
                           (revappend (take 1 *ct-links-orphan*) :bad))))

; Without the host's triples: an entry with a fourth element.  The walk
; answers the triple it read, not the entry.
(defconst *ct-links-long* (list (list 0 *ct-fa* *ct-da* :extra)))
(defconst *ct-run-long*
  (fn-ccc-chain-run nil (fn-ccc-chain-program *ct-links-long*)))
(assert-event (and (not (fn-ccc-entry-triplesp (take 1 *ct-links-long*)))
                   (fn-ccc-new-links-okp (revappend (take 1 *ct-links-long*) nil)
                                         nil *ct-bound*)
                   (no-duplicatesp-equal
                    (fn-ccc-entries-generations (revappend (take 1 *ct-links-long*) nil)))))
(local (must-fail (defthm ct-link-cut-without-triples
                    (equal (fn-ccc-walk (car (nth 2 *ct-run-long*))
                                        (cdr (nth 2 *ct-run-long*)) 1 *ct-bound*)
                           (revappend (take 1 *ct-links-long*) nil)))))
(assert-event (not (equal (fn-ccc-walk (car (nth 2 *ct-run-long*))
                                        (cdr (nth 2 *ct-run-long*)) 1 *ct-bound*)
                           (revappend (take 1 *ct-links-long*) nil))))
; Not toothed: POSP N, N <= (LEN LINKS) and NATP FUEL.  Past the last cut the
; image is nil (no cut there); they are not proved redundant, so they stay.
