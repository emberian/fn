; Source teeth for the actual parallel carry mutator, not owner funding.
(in-package "ACL2")
(include-book "../../books/consumer-account-index-carry")

(defun fn-caitt-conclusion (name value carry trie metadata)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (trie1 metadata1)
    (fn-cait-put-octets name value carry trie metadata)
    (and (equal trie1 (fn-cai-put-octets name value trie))
         (equal metadata1 (fn-cait-annotation trie1))
         (equal (fn-cait-carry metadata1) (fn-scs-summary trie1)))))

(defconst *caitt-row* '(:account-binding (:account (65) (1 2 3) t (4 5)) nil))
(defconst *caitt-carry* (fn-scs-summary *caitt-row*))
(defconst *caitt-a*
 (mv-let (trie metadata) (fn-cait-put-octets '(65) *caitt-row* *caitt-carry* nil nil)
   (list trie metadata)))
(defconst *caitt-trie* (mv-nth 0 *caitt-a*))
(defconst *caitt-metadata* (mv-nth 1 *caitt-a*))

; Reachable positive witness: complete antecedents and both carry conclusions.
(assert-event
 (and (fn-cais-alphabet-triep *caitt-trie*)
      (equal *caitt-metadata* (fn-cait-annotation *caitt-trie*))
      (equal *caitt-carry* (fn-scs-summary *caitt-row*))
      (fn-caitt-conclusion '(65 66) *caitt-row* *caitt-carry*
                           *caitt-trie* *caitt-metadata*)))

; Value refinement has no invariant hypotheses, including corrupt metadata.
(assert-event
 (mv-let (trie metadata)
   (fn-cait-put-octets '(66) *caitt-row* nil *caitt-trie* nil)
   (declare (ignore metadata))
   (equal trie (fn-cai-put-octets '(66) *caitt-row* *caitt-trie*))))

; Metadata-hypothesis removal: corrupt the untouched branch value annotation.
(defconst *caitt-bad-metadata*
 (list (car *caitt-metadata*) (fn-scs-atom nil)
       (caddr *caitt-metadata*) (cadddr *caitt-metadata*)))
(assert-event
 (and (fn-cais-alphabet-triep *caitt-trie*)
      (equal *caitt-carry* (fn-scs-summary *caitt-row*))
      (not (equal *caitt-bad-metadata* (fn-cait-annotation *caitt-trie*)))
      (not (fn-caitt-conclusion '(66) *caitt-row* *caitt-carry*
                                *caitt-trie* *caitt-bad-metadata*))))

; New-value-carry hypothesis removal, retaining exact old annotations/alphabet.
(assert-event
 (and (fn-cais-alphabet-triep *caitt-trie*)
      (equal *caitt-metadata* (fn-cait-annotation *caitt-trie*))
      (not (equal (fn-scs-atom nil) (fn-scs-summary *caitt-row*)))
      (not (fn-caitt-conclusion '(66) *caitt-row* (fn-scs-atom nil)
                                *caitt-trie* *caitt-metadata*))))

; Alphabet-hypothesis removal: a cons key is not a scalar trie key.
(defconst *caitt-bad-trie* (list (cons '(1) *caitt-row*)))
(defconst *caitt-bad-trie-metadata* (fn-cait-annotation *caitt-bad-trie*))
(assert-event
 (and (not (fn-cais-alphabet-triep *caitt-bad-trie*))
      (equal *caitt-bad-trie-metadata* (fn-cait-annotation *caitt-bad-trie*))
      (equal *caitt-carry* (fn-scs-summary *caitt-row*))
      (not (fn-caitt-conclusion '(66) *caitt-row* *caitt-carry*
                                *caitt-bad-trie* *caitt-bad-trie-metadata*))))

; Terminal and character branches remain distinct under prefix insertion.
(defconst *caitt-ab*
 (mv-let (trie metadata)
   (fn-cait-put-octets '(65 66) '(:other) (fn-scs-summary '(:other))
                       *caitt-trie* *caitt-metadata*)
   (list trie metadata)))
(assert-event
 (and (equal (fn-cai-get-octets '(65) (mv-nth 0 *caitt-ab*)) *caitt-row*)
      (equal (fn-cai-get-octets '(65 66) (mv-nth 0 *caitt-ab*)) '(:other))
      (fn-caitt-conclusion '(65) '(:replacement) (fn-scs-summary '(:replacement))
                           (mv-nth 0 *caitt-ab*) (mv-nth 1 *caitt-ab*))))
