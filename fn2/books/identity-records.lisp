; Layer C §4a: the identity record's folds (rulings 3 and 7 of
; IDENTITY-ACROSS-PEERS-20261030.md). Both are keyed by octets: the name N
; = (namespace, exact name octets) and, for a candidate, N with the content
; identity C = (profile, algorithm, digest). Every value is an integer: a
; candidate is named by its ordinal under N, assigned by the summary's
; :admit when the content is new, so the decision compares ordinals.
; The evidence and receipt facts (union) are the next step of §4a.
(in-package "ACL2")
(include-book "runs-schema")
(fn2-book-layer :c)

; Per name N: the selected candidate and the first local acceptance (0 is
; none), the last resolution applied, and the locally known counts.
; :admit is one transaction's whole admission under N: NE new evidence
; rows, NC 1 when the content is new (its ordinal H is then candidates + 1,
; else OLDH, the candidate row's), NR new receipts, EST 1 to establish a
; local acceptance (only while nothing is selected). :import counts an
; imported receipt; it never selects. :resolve selects candidate H under
; resolution E. :gap counts a recorded coverage gap.
(defrunschema fn2-identity-summary :id 13
 :key ((namespace (:id namespace)) (name (:octets 250)))
 :value ((selected (:id candidate)) (first-local (:id candidate)) (resolution (:id event))
         (candidates :u60) (evidence :u60) (receipts :u60) (gaps :u60))
 :merge :latest
 :fold (:events ((:admit (namespace name ne nc nr est oldh h) :assign ((h (if (= nc 0) oldh (+ candidates 1))))
                  :when (and (<= nc 1) (and (<= est 1) (or (= est 0) (= selected 0))))
                  :set ((candidates (+ candidates nc)) (evidence (+ evidence ne)) (receipts (+ receipts nr))
                        (selected (if (= est 1) h selected))
                        (first-local (if (and (= est 1) (= first-local 0)) h first-local))))
                 (:import (namespace name nr) :when (< 0 nr) :set ((receipts (+ receipts nr))))
                 (:resolve (namespace name h e) :when (and (< 0 h) (<= h candidates)) :set ((selected h) (resolution e)))
                 (:gap (namespace name g) :when (< 0 g) :set ((gaps (+ gaps g)))))
        :init :empty :coverage :history-start
        :observe (selected first-local resolution candidates evidence receipts gaps)))

; Per candidate (N, C): its ordinal H under N, its evidence count, whether a
; binding qualifies it and whether a receipt of this domain holds it.
(defrunschema fn2-identity-candidates :id 12
 :key ((namespace (:id namespace)) (name (:octets 250)) (profile :u8) (algorithm :u8) (digest :digest))
 :value ((h (:id candidate)) (evidence :u60) (qualified :bool) (local :bool))
 :merge :latest
 :fold (:events ((:admit (namespace name profile algorithm digest ch ne q l)
                  :when (and (< 0 ch) (and (or (= h 0) (= h ch)) (and (<= q 1) (<= l 1))))
                  :set ((h ch) (evidence (+ evidence ne)) (qualified (max qualified q)) (local (max local l)))))
        :init :empty :coverage :history-start
        :observe (h evidence qualified local)))
