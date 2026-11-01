; Layer C §4a: the identity record (rulings 3 and 7 of
; IDENTITY-ACROSS-PEERS-20261030.md; fn2/docs/c-ordered-runs.md §4a).
; - N, the name: (namespace, the exact name octets). Netnews is namespace 1.
; - C, the content identity: (profile, algorithm, digest), the named
;   subject's digest.
; - O, an origin: B's envelope (format-events.lisp): lineage, domain,
;   incarnation, and a position.
; - E, an occurrence: O's (lineage, domain, incarnation) and the occurrence.
; Evidence and history entries are immutable union facts. Candidates and the
; summary are folds that commit in the facts' publication. The article index
; is this domain's first local acceptance of N. Every fold value is an
; integer: a candidate is named by its ordinal under N, assigned by the
; summary when the content is new. The decision (machines-c-groups.lisp) is
; two exact reads: the summary, then the candidate.
(in-package "ACL2")
(include-book "runs-assemble")
(include-book "ribbon")
(fn2-book-layer :c)

(defconst *fn2-identity-namespace-netnews* 1)
; The content profile of a POST's subject (D25: the authored source) and the
; digest algorithm the upload computes (BLAKE3).
(defconst *fn2-identity-profile-source* 1)
(defconst *fn2-identity-algorithm-blake3* 1)
; This node's single domain, as B's envelope writes it (commit-format.lisp).
(defconst *fn2-identity-lineage* 0)
(defconst *fn2-identity-domain* 0)
(defconst *fn2-identity-incarnation* 1)

; One observation of a binding of N to C, or of a reason it does not bind.
(defrunschema fn2-identity-evidence :id 1
 :key ((namespace (:id namespace)) (name (:octets 250)) (profile :u8) (algorithm :u8) (digest :digest)
       (lineage (:id lineage)) (domain (:id domain)) (incarnation (:id incarnation)) (occurrence (:id occurrence)))
 :value ((kind (:enum fn2-identity-evidence-kind (:binding :invalid-signature :out-of-scope :resolution)))
         (issuer (:id principal)))
 :merge :union)

; A domain's history entry (RFC 5537 §3.3): origin O accepted C as N, on
; the evidence occurrence EVIDENCE, as O's article ARTICLE.
(defrunschema fn2-identity-history :id 11
 :key ((namespace (:id namespace)) (name (:octets 250)) (profile :u8) (algorithm :u8) (digest :digest)
       (lineage (:id lineage)) (domain (:id domain)) (incarnation (:id incarnation)) (position (:id position)))
 :value ((evidence (:id occurrence)) (article (:id article)))
 :merge :union)

; Per name N: the selected candidate (0 is none), the last resolution
; applied, and the locally known counts. :admit is one transaction's whole
; admission under N: NE new evidence rows and NR new history entries (the
; freshness of the same transaction's facts), EST 1 for a local acceptance
; (only while nothing is selected), OLDH the candidate's ordinal before (0
; when the content is new: its ordinal H is then candidates + 1). :import
; counts an imported history entry; it never selects. :resolve selects
; candidate H under resolution E. :gap counts a recorded coverage gap.
(defrunschema fn2-identity-summary :id 13
 :key ((namespace (:id namespace)) (name (:octets 250)))
 :value ((selected (:id candidate)) (resolution (:id event))
         (candidates :u60) (evidence :u60) (history :u60) (gaps :u60))
 :merge :latest
 :fold (:events ((:admit (namespace name ne nr est oldh h) :assign ((h (if (= oldh 0) (+ candidates 1) oldh)))
                  :when (and (<= est 1) (and (or (= est 0) (= selected 0)) (<= oldh candidates)))
                  :set ((candidates (+ candidates (if (= oldh 0) 1 0))) (evidence (+ evidence ne)) (history (+ history nr))
                        (selected (if (= est 1) h selected))))
                 (:import (namespace name nr) :when (< 0 nr) :set ((history (+ history nr))))
                 (:resolve (namespace name h e) :when (and (< 0 h) (<= h candidates)) :set ((selected h) (resolution e)))
                 (:gap (namespace name g) :when (< 0 g) :set ((gaps (+ gaps g)))))
        :init :empty :coverage :history-start
        :observe (selected resolution candidates evidence history gaps)))

; Per candidate (N, C): its ordinal H under N (CH, from the summary's
; :admit), its evidence count, whether a binding qualifies it and whether
; this domain's history entry holds it.
(defrunschema fn2-identity-candidates :id 12
 :key ((namespace (:id namespace)) (name (:octets 250)) (profile :u8) (algorithm :u8) (digest :digest))
 :value ((h (:id candidate)) (evidence :u60) (qualified :bool) (local :bool))
 :merge :latest
 :fold (:events ((:admit (namespace name profile algorithm digest ch ne q l)
                  :when (and (< 0 ch) (and (or (= h 0) (= h ch)) (and (<= q 1) (<= l 1))))
                  :set ((h ch) (evidence (+ evidence ne)) (qualified (max qualified q)) (local (max local l)))))
        :init :empty :coverage :history-start
        :observe (h evidence qualified local)))

; This domain's first local acceptance of N: the candidate H and the
; article. A second local acceptance of N is :duplicate at stage. It is
; local (the article is this node's), and it is what ARTICLE <message-id>
; reads; the article is the commit position, so it is written at bind.
(defrunschema fn2-identity-article :id 14
 :key ((namespace (:id namespace)) (name (:octets 250)))
 :value ((h (:id candidate)) (article (:id article)))
 :merge :unique)

; ---------------------------------------------------------------------------
; The decision row (one per transaction, the transaction's own row): its
; phase, the owner its query's octets are read under (QK QS QG), and what
; the two reads found: the summary (SFOUND, SELECTED, CANDIDATES, GAPS) and
; the candidate (CFOUND, H, EVIDENCE, QUALIFIED, LOCAL).
(defcolumns fn2-id-decides
 ((phase (:enum fn2-id-decide-phase (:idle :summary :candidate :done)))
  (qk :u8) (qs :u32) (qg :u60)
  (sfound :bool) (selected :u60) (candidates :u60) (gaps :u60)
  (cfound :bool) (h :u60) (evidence :u60) (qualified :bool) (local :bool)))

; The verdict, in §4a's precedence: :duplicate when this domain's history
; holds (N, C); :evidence when a qualified binding is known and not held
; here; :conflict when the selection names another content; else :stored
; (eligible for admission).
(defun fn2-id-verdict (selected h qualified local)
 (declare (xargs :guard t))
 (cond ((equal local 1) :duplicate)
       ((equal qualified 1) :evidence)
       ((and (not (equal selected 0)) (not (equal selected h))) :conflict)
       (t :stored)))
; The selection relation of (N, C): :none, :same or :other.
(defun fn2-id-selection (selected h)
 (declare (xargs :guard t))
 (cond ((equal selected 0) :none) ((equal selected h) :same) (t :other)))
