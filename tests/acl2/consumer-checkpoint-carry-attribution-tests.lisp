(in-package "ACL2")
(include-book "../../books/consumer-checkpoint-carry-attribution")
(local (include-book "consumer-checkpoint-carry-map-tests"))

; Ghost infos share the real parser ABI. These are literal provenance teeth,
; not an observation of a wire parser; its same-parse boundary is separate.
(defconst *ccmat-list-info* (fn-ccmt-info *ccmt-list-rows*))
(defconst *ccmat-list-wrong* (cons (fn-scs-atom 1) (cdr *ccmat-list-info*)))
(defconst *ccmat-list-collapsed* (list (fn-scs-summary *ccmt-list-rows*)))
;@positive fn-ccma-actual-list-target-is-complete-annotation
(assert-event
 (and (fn-scsr-info-provenancep *ccmat-list-info* *ccmt-list-rows*)
      (fn-ccma-coveredp :list *ccmt-list-rows* *ccmat-list-info*)
      (equal (fn-ccmm-target :list *ccmt-list-rows* *ccmat-list-info*)
             (fn-caam-list-annotation *ccmt-list-rows*))))
;@hypothesis-removal fn-ccma-actual-list-target-is-complete-annotation parser-provenance
; Corrupted root carry; all child coverage remains present.
(assert-event
 (and (not (fn-scsr-info-provenancep *ccmat-list-wrong* *ccmt-list-rows*))
      (fn-ccma-coveredp :list *ccmt-list-rows* *ccmat-list-wrong*)
      (not (equal (fn-ccmm-target :list *ccmt-list-rows* *ccmat-list-wrong*)
                   (fn-caam-list-annotation *ccmt-list-rows*)))))
;@hypothesis-removal fn-ccma-actual-list-target-is-complete-annotation child-coverage
; Genuine provenance of a root-only leaf does not manufacture child infos.
(assert-event
 (and (fn-scsr-info-provenancep *ccmat-list-collapsed* *ccmt-list-rows*)
      (not (fn-ccma-coveredp :list *ccmt-list-rows* *ccmat-list-collapsed*))
      (not (equal (fn-ccmm-target :list *ccmt-list-rows* *ccmat-list-collapsed*)
                   (fn-caam-list-annotation *ccmt-list-rows*)))))

(defconst *ccmat-trie* (fn-cp-nth 2 (fn-cp-nth 2 *carfct-fence*)))
(defconst *ccmat-trie-info* (fn-ccmt-info *ccmat-trie*))
(defconst *ccmat-trie-wrong* (cons (fn-scs-atom 1) (cdr *ccmat-trie-info*)))
(defconst *ccmat-trie-collapsed* (list (fn-scs-summary *ccmat-trie*)))
;@positive fn-ccma-actual-trie-target-is-complete-annotation
(assert-event
 (and (consp *ccmat-trie*)
      (fn-scsr-info-provenancep *ccmat-trie-info* *ccmat-trie*)
      (fn-ccma-coveredp :trie *ccmat-trie* *ccmat-trie-info*)
      (equal (fn-ccmm-target :trie *ccmat-trie* *ccmat-trie-info*)
             (fn-cait-annotation *ccmat-trie*))))
;@hypothesis-removal fn-ccma-actual-trie-target-is-complete-annotation parser-provenance
; Corrupted root carry; all child coverage remains present.
(assert-event
 (and (not (fn-scsr-info-provenancep *ccmat-trie-wrong* *ccmat-trie*))
      (fn-ccma-coveredp :trie *ccmat-trie* *ccmat-trie-wrong*)
      (not (equal (fn-ccmm-target :trie *ccmat-trie* *ccmat-trie-wrong*)
                   (fn-cait-annotation *ccmat-trie*)))))
;@hypothesis-removal fn-ccma-actual-trie-target-is-complete-annotation child-coverage
(assert-event
 (and (fn-scsr-info-provenancep *ccmat-trie-collapsed* *ccmat-trie*)
      (not (fn-ccma-coveredp :trie *ccmat-trie* *ccmat-trie-collapsed*))
      (not (equal (fn-ccmm-target :trie *ccmat-trie* *ccmat-trie-collapsed*)
                   (fn-cait-annotation *ccmat-trie*)))))
