; Witnesses for books/admission-memory.lisp (K-ADMIT; Builder M, memory
; landing 3+4, 2026-10-09).
;
; The small preset's profile (16,384 transactions, 8 MiB of history) on the
; production image's measured floor (as tests/acl2/memory-model-tests.lisp),
; W13's 1,000 POSTs as the carried totals, and a HELD row interned on a local
; arena as the article's row.  The memory gate at this store admits the
; article at 380 MiB and refuses it one octet under its edge, the reopen's
; need after the commit (the edge is derived, never pinned: D27),
; while the transactions (1,000 of 16,384) and the
; history (7,648,000 of 8,388,608 octets) admit it: the word is then :memory.
; The same store at the transactions' ceiling (16,384 committed) or at the
; history's ceiling (8,388,608 octets) is refused by T or by H before the
; memory is asked.
(in-package "ACL2")
(include-book "../../books/admission-memory")
(include-book "../../books/records-attach")
(include-book "../../books/catalog-record")
(include-book "../../books/defkeystone")
(include-book "std/testing/assert-bang" :dir :system)

(defun adt-wire (n)
  (declare (xargs :guard t :verify-guards nil))
  (let ((n (nfix n)))
    (fn-record-make (mod n 3) (mod n 5) (mod n 7)
                    (concatenate 'string "<adt-" (coerce (explode-nonnegative-integer n 10 nil) 'string) "@example.invalid>")
                    (make-list (mod n 11) :initial-element (+ 65 (mod n 26)))
                    (if (evenp n) '("fn.test") '("fn.test" "fn.other"))
                    "o0" "s0" "e0" 4 (+ 841000000 n))))

(defun adt-intern (n fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (row fn-arena) (fn-cat-intern-list (adt-wire n) nil 0 fn-arena)
    (mv row fn-arena)))

(defun adt-held-row (n)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (row fn-arena)
      (adt-intern n fn-arena)
      row)))

(defconst *adt-row* (adt-held-row 11))
(defconst *adt-record* (adt-wire 5))
(assert-event (fn-held-p *adt-row*))

(defconst *adt-p* *fn-heap-small-profile*)
(defconst *adt-img* (list (* 100 1048576) (* 23 1048576) 1090519))
(defconst *adt-cfg* (list 32 t 8388608 8388608 nil 0 8388608 16 nil 64))
(defun adt-posts (k)
  (let ((hc (* k (+ (* 8 600) (* 12 40)))))
    (fn-mm-make-tot k (* k 2048) hc k 0 (* k 2300) (* k 2400) (+ (* k 2048) hc (* k 320))
                    :resident)))
(defconst *adt-tot* (adt-posts 1000))
(defconst *adt-380m* (* 380 1048576))
; the used count, the carried octets and the debt the owner hands the budget
(defconst *adt-used* 1000)
(defconst *adt-bytes* (fn-mm-tot-charge *adt-tot*))
(defconst *adt-debt* 0)
(defconst *adt-after* (fn-adm-after *adt-tot* *adt-row*))
(defconst *adt-edge* (max (fn-mm-sum *adt-p* *adt-img* *adt-cfg* *adt-after*)
                          (fn-mm-reopen-need *adt-p* *adt-img* *adt-cfg* *adt-after*)))
; the limit one octet under the edge: the memory alone refuses there
(defconst *adt-under* (1- *adt-edge*))

; The figures the prose above quotes.
(assert-event (equal *adt-bytes* 7648000))
(assert-event (equal (fn-mm-sum *adt-p* *adt-img* *adt-cfg* *adt-after*) 294011109))
(assert-event (equal *adt-edge* (fn-mm-reopen-need *adt-p* *adt-img* *adt-cfg* *adt-after*)))
(assert-event (< *adt-edge* *adt-380m*))
(assert-event (equal (fn-adm-residency *adt-tot*) :resident))

; The three resources at the figures above.
(assert-event (fn-cvec-article-transactions-admitp *adt-p* *adt-used* *adt-debt*))
(assert-event (fn-cvec-article-history-admitp
               *adt-p* *adt-bytes*
               (fn-sbud-article-gate-figure (len (fn-record-payload *adt-record*))
                                            (len (fn-record-groups *adt-record*)))
               *adt-debt*))
(assert-event (fn-adm-memory-admitp *adt-p* *adt-img* *adt-cfg* *adt-380m* *adt-tot* *adt-row*))
(assert-event (not (fn-adm-memory-admitp *adt-p* *adt-img* *adt-cfg* *adt-under* *adt-tot* *adt-row*)))
; T refuses at the ceiling, H refuses at its ceiling
(assert-event (not (fn-cvec-article-transactions-admitp *adt-p* 16384 *adt-debt*)))
(assert-event (not (fn-cvec-article-history-admitp
                    *adt-p* 8388608
                    (fn-sbud-article-gate-figure (len (fn-record-payload *adt-record*))
                                                 (len (fn-record-groups *adt-record*)))
                    *adt-debt*)))

; --- K-ADMIT (1) --------------------------------------------------------------
; The keystone has no hypothesis, so `defteeth' (which wants a labelled
; hypothesis to remove) does not apply: the satisfiable witness, the three
; ways the budget refuses and the two mutations are asserted directly.
(defmacro adt-k1 (limit used bytes)
  `(list (fn-sbud-admitp (fn-adm-article-budget *adt-p* *adt-img* *adt-cfg* ,limit ,used ,bytes
                                                *adt-record* *adt-debt* *adt-tot* *adt-row*)
                         ,used)
         (and (fn-cvec-article-transactions-admitp *adt-p* ,used *adt-debt*)
              (fn-cvec-article-history-admitp
               *adt-p* ,bytes
               (fn-sbud-article-gate-figure (len (fn-record-payload *adt-record*))
                                            (len (fn-record-groups *adt-record*)))
               *adt-debt*)
              (fn-adm-memory-admitp *adt-p* *adt-img* *adt-cfg* ,limit *adt-tot* *adt-row*))
         (and (fn-cvec-article-transactions-admitp *adt-p* ,used *adt-debt*)
              (fn-cvec-article-history-admitp
               *adt-p* ,bytes
               (fn-sbud-article-gate-figure (len (fn-record-payload *adt-record*))
                                            (len (fn-record-groups *adt-record*)))
               *adt-debt*))
         (fn-adm-memory-admitp *adt-p* *adt-img* *adt-cfg* ,limit *adt-tot* *adt-row*)))
; (budget admits, the three admit, T and H admit, memory admits)
; all three admit: the budget admits (the reachable witness)
(assert-event (equal (adt-k1 *adt-380m* *adt-used* *adt-bytes*) '(t t t t)))
; the memory alone refuses: the budget refuses
(assert-event (equal (adt-k1 *adt-under* *adt-used* *adt-bytes*) '(nil nil t nil)))
; T alone refuses
(assert-event (equal (adt-k1 *adt-380m* 16384 *adt-bytes*) '(nil nil nil t)))
; H alone refuses
(assert-event (equal (adt-k1 *adt-380m* *adt-used* 8388608) '(nil nil nil t)))
; mutation: a budget that never asks the memory admits where the model refuses
; (under the edge: the conclusion's conjunction of T and H alone is t, the budget is nil)
(assert-event (not (equal (car (adt-k1 *adt-under* *adt-used* *adt-bytes*))
                          (caddr (adt-k1 *adt-under* *adt-used* *adt-bytes*)))))
; mutation: a budget that admits whenever the memory does, over a store out
; of transactions (16,384 committed): the memory admits and the budget refuses
(assert-event (not (equal (car (adt-k1 *adt-380m* 16384 *adt-bytes*))
                          (cadddr (adt-k1 *adt-380m* 16384 *adt-bytes*)))))

; --- K-ADMIT (2) --------------------------------------------------------------
(defteeth fn-adm-article-word-under-the-budget-names-the-resource
  :claim (let* ((tx (fn-cvec-article-transactions-admitp profile used debt))
                (hx (fn-cvec-article-history-admitp
                     profile bytes-used
                     (fn-sbud-article-gate-figure (len (fn-record-payload record))
                                                  (len (fn-record-groups record)))
                     debt))
                (mx (fn-adm-memory-admitp profile img cfg limit tot row))
                (w (fn-adm-article-word :unaffordable profile img cfg limit used bytes-used
                                        record debt tot row)))
           (((refused (not (fn-sbud-admitp (fn-adm-article-budget profile img cfg limit used
                                                                  bytes-used record debt tot row)
                                           used))))
            (and (member-equal w '(:unaffordable :history-exhausted :memory))
                 (iff (equal w :unaffordable) (not tx))
                 (iff (equal w :history-exhausted) (and tx (not hx)))
                 (iff (equal w :memory) (and tx hx (not mx))))))
  :subject fn-adm-article-word
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-under*)
            (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
            (tot *adt-tot*) (row *adt-row*))
  :breaks ((refused ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-380m*)
                     (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                     (tot *adt-tot*) (row *adt-row*))))
  :mutations ((word-without-memory
               (:conclusion (let* ((w (fn-adm-article-word :unaffordable profile img cfg limit used bytes-used
                                                           record debt tot row)))
                              (member-equal w '(:unaffordable :history-exhausted))))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-under*)
                (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                (tot *adt-tot*) (row *adt-row*))
               :fault "a refusal word with no :memory: the memory's refusal reported as :unaffordable")
              (memory-named-ahead-of-the-transactions
               (:conclusion (let* ((mx (fn-adm-memory-admitp profile img cfg limit tot row))
                                   (w (fn-adm-article-word :unaffordable profile img cfg limit used bytes-used
                                                           record debt tot row)))
                              (iff (equal w :memory) (not mx))))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-under*)
                (used 16384) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                (tot *adt-tot*) (row *adt-row*))
               :fault "a word that names the memory whenever it refuses, ahead of a store out of transactions")))

; The word is each resource's at its own ceiling, and :memory only when T and H admit.
(assert-event (equal (fn-adm-article-word :unaffordable *adt-p* *adt-img* *adt-cfg* *adt-under*
                                          *adt-used* *adt-bytes* *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :memory))
(assert-event (equal (fn-adm-article-word :unaffordable *adt-p* *adt-img* *adt-cfg* *adt-under*
                                          16384 *adt-bytes* *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :unaffordable))
(assert-event (equal (fn-adm-article-word :unaffordable *adt-p* *adt-img* *adt-cfg* *adt-under*
                                          *adt-used* 8388608 *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :history-exhausted))
; a word other than :unaffordable passes through (fn-adm-article-word-passes-other-words)
(assert-event (equal (fn-adm-article-word :corrupt *adt-p* *adt-img* *adt-cfg* *adt-under*
                                           *adt-used* *adt-bytes* *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :corrupt))

; --- K-ADMIT (3) --------------------------------------------------------------
(defteeth fn-adm-admitted-row-keeps-the-gate
  :claim (((admitted (fn-sbud-admitp (fn-adm-article-budget profile img cfg limit used bytes-used
                                                            record debt tot row)
                                     used)))
          (and (<= (fn-mm-sum profile img cfg (fn-adm-after tot row)) limit)
               (<= (fn-mm-reopen-need profile img cfg (fn-adm-after tot row)) limit)))
  :subject fn-adm-article-budget
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-380m*)
            (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
            (tot *adt-tot*) (row *adt-row*))
  :breaks ((admitted ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-under*)
                      (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                      (tot *adt-tot*) (row *adt-row*))))
  :mutations ((gate-strictly-under-limit
               (:conclusion (and (< (fn-mm-sum profile img cfg (fn-adm-after tot row)) limit)
                                 (< (fn-mm-reopen-need profile img cfg (fn-adm-after tot row)) limit)))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-edge*)
                (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                (tot *adt-tot*) (row *adt-row*))
               :fault "a gate that wants strict room under LIMIT: the store the budget admitted at exactly LIMIT would be called over it")))

; --- THE RUN'S CAPACITY (ruling (b), 2026-10-10) ------------------------------
; At 230 MiB all 32 connections fit. At the exact eighteen-holder edge,
; article replies bind and a nineteenth fails. The 250 MiB store samples
; remain at 32 through 400 posts; 500 no longer fits. For the antitone
; teeth, 230 MiB holds 32 at the empty store and 26 at 200 posts.
(defconst *adt-230m* (* 230 1048576))
(defconst *adt-250m* (* 250 1048576))
(defconst *adt-128m* (* 128 1048576))
(defconst *adt-empty* (adt-posts 0))
(defconst *adt-big* (adt-posts 200))
; Exact funded edge at 18 holders: the nineteen-holder mutant must fail.
(defconst *adt-cap-edge*
  (max (fn-mm-sum *adt-p* *adt-img* (fn-adm-cfg-at *adt-cfg* 18) *adt-empty*)
       (fn-mm-reopen-need *adt-p* *adt-img* (fn-adm-cfg-at *adt-cfg* 18) *adt-empty*)))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-230m* *adt-empty*) 32))
(assert-event (equal (fn-adm-capacity-binding *adt-p* *adt-img* *adt-cfg* *adt-230m* *adt-empty*)
                     :configured))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-380m* *adt-tot*) 32))
(assert-event (equal (fn-adm-capacity-binding *adt-p* *adt-img* *adt-cfg* *adt-380m* *adt-tot*)
                     :configured))
(assert-event (null (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-128m* *adt-empty*)))
(assert-event (equal (fn-adm-capacity-binding *adt-p* *adt-img* *adt-cfg* *adt-128m* *adt-empty*)
                     :store))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* *adt-empty*) 32))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* (adt-posts 100)) 32))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* (adt-posts 200)) 32))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* *adt-big*) 32))
(assert-event (<= (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* (adt-posts 400))
                  (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* *adt-big*)))
(assert-event (null (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* (adt-posts 500))))
(assert-event (equal (fn-adm-capacity-line *adt-p* *adt-img* *adt-cfg* *adt-128m* *adt-empty*)
                     "refused memory-cannot-hold-the-store capacity=0 of 32 bound-by=store sum=204 MB limit=128 MB"))
(assert-event (equal (fn-adm-capacity-line *adt-p* *adt-img* *adt-cfg* *adt-230m* *adt-empty*)
                     "memory capacity=32 of 32 bound-by=configured sum=226 MB limit=230 MB"))

(defteeth fn-adm-capacity-fits
  :claim (((fits (fn-adm-capacity profile img cfg limit tot)))
          (let ((c (fn-adm-capacity profile img cfg limit tot)))
            (and (natp c)
                 (<= c (fn-mm-cfg-connections cfg))
                 (fn-mm-gate-p profile img (fn-adm-cfg-at cfg c) limit tot))))
  :subject fn-adm-capacity
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-cap-edge*)
            (tot *adt-empty*))
  :breaks ((fits ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-128m*)
                  (tot *adt-empty*))))
  :mutations ((the-gate-holds-one-more
               (:conclusion (fn-mm-gate-p profile img
                                          (fn-adm-cfg-at cfg (+ 1 (fn-adm-capacity profile img cfg limit tot)))
                                          limit tot))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-cap-edge*)
                (tot *adt-empty*))
               :fault "a capacity one below the count the gate holds at: the run would admit fewer readers than the memory holds, or, read the other way, one more than it holds")))

(defteeth fn-adm-capacity-is-the-most
  :claim (((counted (natp j))
           (within (<= j (fn-mm-cfg-connections cfg)))
           (holds (fn-mm-gate-p profile img (fn-adm-cfg-at cfg j) limit tot)))
          (let ((c (fn-adm-capacity profile img cfg limit tot)))
            (and (natp c) (<= j c))))
  :subject fn-adm-capacity
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-cap-edge*)
            (tot *adt-empty*) (j 18))
  :breaks ((counted ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-cap-edge*)
                     (tot *adt-empty*) (j 37/2)))
           (within ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-380m*)
                    (tot *adt-empty*) (j 33)))
           (holds ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-cap-edge*)
                   (tot *adt-empty*) (j 19))))
  :mutations ((capacity-is-always-c
               (:conclusion (equal (fn-adm-capacity profile img cfg limit tot)
                                   (fn-mm-cfg-connections cfg)))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-cap-edge*)
                (tot *adt-empty*) (j 18))
               :fault "a run that prices its configured C whatever the limit: at 39c86eb48 the 2 GiB node refused every POST by the memory")
              (strictly-more
               (:conclusion (< j (fn-adm-capacity profile img cfg limit tot)))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-cap-edge*)
                (tot *adt-empty*) (j 18))
               :fault "a capacity past the last count the gate holds at")))

(defteeth fn-adm-capacity-antitone-in-the-store
  :claim (((smaller (fn-mm-tot-le a b))
           (fits (fn-adm-capacity profile img cfg limit b)))
          (and (natp (fn-adm-capacity profile img cfg limit a))
               (<= (fn-adm-capacity profile img cfg limit b)
                   (fn-adm-capacity profile img cfg limit a))))
  :subject fn-adm-capacity
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
            (a *adt-empty*) (b *adt-big*))
  :breaks ((smaller ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
                     (a *adt-big*) (b *adt-empty*)))
           (fits ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-128m*)
                  (a *adt-empty*) (b *adt-big*))))
  :mutations ((capacity-grows-with-the-store
               (:conclusion (<= (fn-adm-capacity profile img cfg limit a)
                                (fn-adm-capacity profile img cfg limit b)))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
                (a *adt-empty*) (b *adt-big*))
               :fault "a store that grows and frees connections")))

; --- K-BOUND AGGREGATE (revision 8): fn-mm-profile-bound-holds-every-admitted-store ----
; The article of adt-wire with a payload of K octets, interned on a local arena.
(defun adt-big-row (n k)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (row fn-arena)
      (fn-cat-intern-list
       (fn-record-make (mod n 3) (mod n 5) (mod n 7) "<adt-big@example.invalid>"
                       (make-list k :initial-element 66) '("fn.test") "o0" "s0" "e0" 4 841000000)
       nil 0 fn-arena)
      row)))
(defun adt-w-hyps (records p)
  (declare (xargs :verify-guards nil))
  (list (<= (len records) (nfix (fn-bs-profile-max-transactions p)))
        (<= (fn-sbud-record-octets records) (nfix (fn-bs-profile-max-history-octets p)))
        (fn-adm-rows-within records p)))
(defun adt-w-concl (records p r)
  (declare (xargs :verify-guards nil))
  (fn-mm-tot-le (fn-ct-charged records r) (fn-mm-profile-bound-tot p r)))
; Satisfiable witness: two held rows with payloads (7 and 10 octets), every hypothesis true at the
; small preset, the conclusion true at both residencies.
(defconst *adt-wrow-a* (adt-held-row 7))
(defconst *adt-wrow-b* (adt-held-row 10))
(defconst *adt-w-rows* (list *adt-wrow-a* *adt-wrow-b*))
(defconst *adt-w-octets* (fn-sbud-record-octets *adt-w-rows*))
(assert-event (consp *adt-w-rows*))
(assert-event (< 0 *adt-w-octets*))
(assert-event (equal (adt-w-hyps *adt-w-rows* *adt-p*) '(t t t)))
(assert-event (adt-w-concl *adt-w-rows* *adt-p* :resident))
(assert-event (adt-w-concl *adt-w-rows* *adt-p* :paged))
; Teeth, one per hypothesis: drop it (the other two stay true) and the conclusion fails.  Every
; profile below is VALID (fn-bs-profile-validp): an invalid one reads as the empty profile.
; T: one transaction less than the store holds, at the least T a valid profile has (the open
; suffix, 128): one more copy of the first row than that.
(defconst *adt-w-t* (fn-bs-pf *fn-bs-pf-max-open-suffix* *adt-p*))
(defconst *adt-w-many* (make-list (1+ *adt-w-t*) :initial-element *adt-wrow-a*))
(defconst *adt-w-p-t* (fn-bs-profile-put *fn-bs-pf-max-transactions* *adt-w-t* *adt-p*))
(assert-event (fn-bs-profile-validp *adt-w-p-t*))
(assert-event (equal (adt-w-hyps *adt-w-many* *adt-w-p-t*) '(nil t t)))
(assert-event (not (adt-w-concl *adt-w-many* *adt-w-p-t* :resident)))
; H: one article whose charge is one octet past the least H a valid profile has (the record octets).
(defconst *adt-w-h* (fn-bs-pf *fn-bs-pf-max-record-octets* *adt-p*))
(defconst *adt-w-big* (list (adt-big-row 1 (1+ *adt-w-h*))))
(defconst *adt-w-p-h* (fn-bs-profile-put *fn-bs-pf-max-history-octets* *adt-w-h* *adt-p*))
(assert-event (fn-bs-profile-validp *adt-w-p-h*))
(assert-event (< *adt-w-h* (fn-sbud-record-octets *adt-w-big*)))
(assert-event (equal (adt-w-hyps *adt-w-big* *adt-w-p-h*) '(t nil t)))
(assert-event (not (adt-w-concl *adt-w-big* *adt-w-p-h* :resident)))
; The per-row invariant: T x G memberships fall short of the store's, G one group short of the
; first row's memberships at the least valid T.
(defconst *adt-w-rows-r* (make-list *adt-w-t* :initial-element *adt-wrow-a*))
(defconst *adt-w-p-r*
  (fn-bs-profile-put *fn-bs-pf-max-groups-per-article*
                     (1- (fn-mm-tot-memberships (fn-ct-row-tot *adt-wrow-a* :resident)))
                     *adt-w-p-t*))
(assert-event (fn-bs-profile-validp *adt-w-p-r*))
(assert-event (equal (adt-w-hyps *adt-w-rows-r* *adt-w-p-r*) '(t t nil)))
(assert-event (not (adt-w-concl *adt-w-rows-r* *adt-w-p-r* :resident)))
; Counterexample search.  The cgen test? on the statement found 0 counterexamples in 1000 examples
; (449 satisfied the hypotheses, all with empty stores), so it is not the evidence.  This is: every
; row of 24 held rows and 2 large ones (payload H-floor / 2 and H-floor + 1), repeated 1, 2, T-floor - 1,
; T-floor, T-floor + 1 times, and every ordered pair of them, over the grid of valid profiles
; T in {floor, floor + 1, 2 floor, 16384}, H in {floor, floor + 1, 2 floor, 8388608},
; G in {1, 2, 3, 16}, at both residencies.  Cases, cases whose hypotheses hold, violations.
(defun adt-hrows (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil (cons (adt-held-row (1- n)) (adt-hrows (1- n)))))
(defconst *adt-sweep-rows*
  (append (adt-hrows 24)
          (list (adt-big-row 2 (floor *adt-w-h* 2)) (adt-big-row 3 (1+ *adt-w-h*)))))
(defun adt-prof (a b c)
  (declare (xargs :verify-guards nil))
  (fn-bs-profile-put *fn-bs-pf-max-groups-per-article* c
    (fn-bs-profile-put *fn-bs-pf-max-history-octets* b
      (fn-bs-profile-put *fn-bs-pf-max-transactions* a *adt-p*))))
(defun adt-one (records p acc)
  (declare (xargs :verify-guards nil))
  (let* ((hy (not (member-equal nil (adt-w-hyps records p))))
         (bad (and hy (not (and (adt-w-concl records p :resident) (adt-w-concl records p :paged))))))
    (list (1+ (car acc)) (+ (cadr acc) (if hy 1 0)) (+ (caddr acc) (if bad 1 0)))))
(defun adt-gs (records a b gs acc)
  (declare (xargs :verify-guards nil))
  (if (atom gs) acc (adt-gs records a b (cdr gs) (adt-one records (adt-prof a b (car gs)) acc))))
(defun adt-hs (records a hs acc)
  (declare (xargs :verify-guards nil))
  (if (atom hs) acc (adt-hs records a (cdr hs) (adt-gs records a (car hs) '(1 2 3 16) acc))))
(defun adt-ts (records ts acc)
  (declare (xargs :verify-guards nil))
  (if (atom ts) acc
    (adt-ts records (cdr ts)
            (adt-hs records (car ts)
                    (list *adt-w-h* (1+ *adt-w-h*) (* 2 *adt-w-h*) 8388608) acc))))
(defconst *adt-sweep-ts* (list *adt-w-t* (1+ *adt-w-t*) (* 2 *adt-w-t*) 16384))
(defun adt-pairs (x ys)
  (declare (xargs :verify-guards nil))
  (if (atom ys) nil (cons (list x (car ys)) (adt-pairs x (cdr ys)))))
(defun adt-lists (xs ys acc)
  (declare (xargs :verify-guards nil))
  (if (atom xs) acc
    (adt-lists (cdr xs) ys
      (append (list (list (car xs))
                    (make-list 2 :initial-element (car xs))
                    (make-list (1- *adt-w-t*) :initial-element (car xs))
                    (make-list *adt-w-t* :initial-element (car xs))
                    (make-list (1+ *adt-w-t*) :initial-element (car xs)))
              (adt-pairs (car xs) ys)
              acc))))
(defun adt-run (lists acc)
  (declare (xargs :verify-guards nil))
  (if (atom lists) acc (adt-run (cdr lists) (adt-ts (car lists) *adt-sweep-ts* acc))))
(defconst *adt-sweep-lists* (adt-lists *adt-sweep-rows* *adt-sweep-rows* nil))
(defconst *adt-sweep* (adt-run *adt-sweep-lists* '(0 0 0)))
(assert-event (equal (car *adt-sweep*) (* (len *adt-sweep-lists*) 4 4 4)))
(assert-event (< 0 (cadr *adt-sweep*)))
(assert-event (< (cadr *adt-sweep*) (car *adt-sweep*)))
(assert-event (equal (caddr *adt-sweep*) 0))

; --- THE HANDLE SPACE (K-BOUND P3, landing 4b) ---------------------------------
; The last admitted batch ends exactly at the largest u64 count; one handle more
; is refused.  The witness is a fresh arena's count (0) and the POST's N (1).
(defconst *adt-u64-top* (1- (expt 2 64)))
(assert-event (fn-adm-handle-room-p (- *adt-u64-top* 1) 1))
(assert-event (not (fn-adm-handle-room-p *adt-u64-top* 1)))
(defteeth fn-adm-handle-room-is-u64-room
  :claim (((room (fn-adm-handle-room-p count n)))
          (and (unsigned-byte-p 64 count)
               (unsigned-byte-p 64 (+ count n))))
  :subject fn-adm-handle-room-p
  :witness ((count 0) (n 1))
  :breaks ((room ((count *adt-u64-top*) (n 1))))
  :mutations ((one-handle-more
               (:conclusion (unsigned-byte-p 64 (+ count n 1)))
               ((count (- *adt-u64-top* 1)) (n 1))
               :fault "a decision with no spare handle: the batch that ends at the largest u64 count would be called one handle short")))

; L-RUN-LAUNCH (PRF-1268's statement since the connection budget retired): the gate's handshake allowance
; is the live limit or the handshakes still in flight, the larger.  Witness: a TLS run whose limit was
; lowered to 4 with 12 handshakes in flight.  Mutation: the live limit alone, which releases the eight
; still-active handshakes' scratch.
(defconst *admt-hs-cfg* '(32 t 8388608 8388608 nil 0 0 4 nil 64 nil nil 0))
(defkeystone admt-holding-handshakes-charges-every-handshake
  (<= (* (nfix h) (if (fn-mm-cfg-tlsp cfg) *fn-cbud-handshake-scratch-octets* 0))
      (fn-cbud-handshake-octets (fn-mm-cfg-tlsp (fn-adm-cfg-holding-handshakes cfg h))
                                (fn-mm-cfg-handshakes (fn-adm-cfg-holding-handshakes cfg h))))
  :id "PRF-1268"
  :restates fn-adm-cfg-holding-handshakes-charges-every-handshake
  :subject fn-adm-cfg-holding-handshakes
  :witness ((cfg *admt-hs-cfg*) (h 12))
  :mutations ((the-live-limit-alone
               (:conclusion (<= (* (nfix h) (if (fn-mm-cfg-tlsp cfg) *fn-cbud-handshake-scratch-octets* 0))
                                (fn-cbud-handshake-octets (fn-mm-cfg-tlsp cfg) (fn-mm-cfg-handshakes cfg))))
               ((cfg *admt-hs-cfg*) (h 12))
               :fault "a lowered limit releases the still-active handshakes' scratch (the held record's job before L-RUN-LAUNCH)"))
  :hints (("Goal" :by fn-adm-cfg-holding-handshakes-charges-every-handshake)))

; K-RUN-LAUNCH: the run's capacity is found by halving, not by walking from C.  At
; C = 4,000,000 the walk spends C - C' + 1 gate evaluations (the owner was killed
; walking it at configure); the search spends at most (+ 2 (integer-length C)).
; Nothing is pinned: C' is derived by the search and by the walk, and the two are
; compared, and the evaluations are counted by a logic-only twin of the search.
(defconst *adt-c-4m* 4000000)
(defconst *adt-cfg-4m* (fn-adm-cfg-at *adt-cfg* *adt-c-4m*))

(defun adt-search-count (profile img cfg limit tot lo hi)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (nfix hi) (nfix lo)))
                  :hints (("Goal" :in-theory (disable fn-adm-search-mid fn-mm-gate-p fn-adm-cfg-at)
                           :use ((:instance fn-adm-search-mid-bounds))))))
  (if (< (nfix lo) (nfix hi))
      (let ((r (if (fn-mm-gate-p profile img (fn-adm-cfg-at cfg (fn-adm-search-mid lo hi)) limit tot)
                   (adt-search-count profile img cfg limit tot (1+ (fn-adm-search-mid lo hi)) hi)
                 (adt-search-count profile img cfg limit tot lo (fn-adm-search-mid lo hi)))))
        (cons (car r) (1+ (cdr r))))
    (cons (if (zp lo) nil (1- lo)) 0)))

(defconst *adt-search-4m*
  (fn-adm-capacity *adt-p* *adt-img* *adt-cfg-4m* *adt-230m* *adt-empty*))
(defconst *adt-count-4m*
  (adt-search-count *adt-p* *adt-img* *adt-cfg-4m* *adt-230m* *adt-empty* 0 (1+ *adt-c-4m*)))
; the twin counts the search it twins
(assert-event (equal (car *adt-count-4m*) *adt-search-4m*))
; the search found a capacity, below the configured 4,000,000 (the limit binds)
(assert-event (and (natp *adt-search-4m*) (< *adt-search-4m* *adt-c-4m*)))
; the gate holds at C' and fails at C' + 1 (the walk's C', by antitonicity)
(assert-event (fn-mm-gate-p *adt-p* *adt-img* (fn-adm-cfg-at *adt-cfg-4m* *adt-search-4m*) *adt-230m* *adt-empty*))
(assert-event (not (fn-mm-gate-p *adt-p* *adt-img* (fn-adm-cfg-at *adt-cfg-4m* (1+ *adt-search-4m*))
                                 *adt-230m* *adt-empty*)))
; the walk answers the same
; Keep the exact closed equality to the reference walk. Its certified
; equivalence theorem proves it without executing four million reference
; iterations; the real search and its counted twin are evaluated above.
(defthm adt-reference-walk-agrees-at-four-million
  (equal (fn-adm-capacity-walk *adt-p* *adt-img* *adt-cfg-4m* *adt-230m* *adt-empty*)
                     *adt-search-4m*)
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '((:executable-counterpart fn-adm-capacity))
                                             (theory 'minimal-theory))
           :use ((:instance fn-adm-capacity-is-the-walk
                            (profile *adt-p*) (img *adt-img*) (cfg *adt-cfg-4m*)
                            (limit *adt-230m*) (tot *adt-empty*))))))
; and the search spent at most (+ 2 (integer-length C)) gate evaluations; each descent is one gate
; evaluation and the closing step evaluates none
(assert-event (<= (cdr *adt-count-4m*) (+ 2 (integer-length *adt-c-4m*))))
; no capacity at all is also found in the same bound
(assert-event (null (fn-adm-capacity *adt-p* *adt-img* *adt-cfg-4m* *adt-128m* *adt-empty*)))
(assert-event (<= (cdr (adt-search-count *adt-p* *adt-img* *adt-cfg-4m* *adt-128m* *adt-empty*
                                            0 (1+ *adt-c-4m*)))
                  (+ 2 (integer-length *adt-c-4m*))))

; M22 approved whole witnesses and old-behavior teeth, unchanged.
(include-book "../../books/heap-command")
(include-book "../../books/runtime-contract-host-pool")
(include-book "../../books/catalog-record")
(include-book "../../books/records-attach")
(defconst *m22-profile* *fn-heap-small-profile*)

(defconst *m22-img* '(104857600 24117248 1090519))

(defconst *m22-cfg* '(32 t 8388608 8388608 nil 0 8388608 16 nil 64))

(defconst *m22-empty* '(0 0 0 0 0 0 0 0 :resident))

(defconst *m22-lowered-cfg* (fn-adm-cfg-at *m22-cfg* 1))

(assert-event
  (and (equal (fn-adm-priced-connections 32 1 1) 32)
       (<= 32 (fn-adm-priced-connections 32 1 1))
       (not (<= 32 (min 1 1)))))

(assert-event
  (and (<= 0 (fn-adm-reader-count 32 0))
       (equal (fn-adm-priced-connections 0 32 0) (fn-adm-reader-count 32 0))
       (equal (fn-adm-priced-connections 0 32 0) 0)
       ; The old fn-owner-memory-gate's POSP branch returned configured C.
       (not (equal (if (posp 0) (min 32 0) 32) 0))))

(assert-event
  (let* ((held 32)
         (cfg (fn-adm-priced-cfg *m22-lowered-cfg* held 1))
         (limit (max (fn-mm-sum *m22-profile* *m22-img* cfg *m22-empty*)
                     (fn-mm-reopen-need *m22-profile* *m22-img* cfg *m22-empty*))))
    (and (fn-mm-gate-p *m22-profile* *m22-img* cfg limit *m22-empty*)
         (<= (fn-mm-need *m22-profile* *m22-img* cfg *m22-empty* held held
                         (fn-heap-article-slots *m22-profile*)
                         (fn-cbud-handshake-slots t 16) t)
             limit))))

(assert-event
  (let* ((old *m22-lowered-cfg*)
         (limit (max (fn-mm-sum *m22-profile* *m22-img* old *m22-empty*)
                     (fn-mm-reopen-need *m22-profile* *m22-img* old *m22-empty*))))
    (and (fn-mm-gate-p *m22-profile* *m22-img* old limit *m22-empty*)
         ; Teeth: the OLD gate passes, but its actual held instant exceeds it.
         (< limit (fn-mm-need *m22-profile* *m22-img* old *m22-empty* 32 32
                              (fn-heap-article-slots *m22-profile*)
                              (fn-cbud-handshake-slots t 16) t)))))

(assert-event
  (let* ((limit (* 128 *fn-heap-mib*))
         (found (fn-adm-capacity *m22-profile* *m22-img* *m22-cfg* limit *m22-empty*))
         (cap (fn-adm-installed-capacity *m22-profile* *m22-img* *m22-cfg* limit *m22-empty*)))
    (and (null found) (natp cap) (equal cap 0)
         (equal cap (if (natp found) found 0))
         (or (equal cap 0)
             (and (equal cap found) (<= cap 32)
                  (fn-mm-gate-p *m22-profile* *m22-img*
                                (fn-adm-cfg-at *m22-cfg* cap) limit *m22-empty*)))
         (not (equal (if (posp found) found 1) cap)))))

(assert-event
  (let* ((limit (* 250 *fn-heap-mib*))
         (found (fn-adm-capacity *m22-profile* *m22-img* *m22-cfg* limit *m22-empty*))
         (cap (fn-adm-installed-capacity *m22-profile* *m22-img* *m22-cfg* limit *m22-empty*)))
    (and (posp found) (natp cap) (equal cap found) (<= cap 32)
         (fn-mm-gate-p *m22-profile* *m22-img* (fn-adm-cfg-at *m22-cfg* cap)
                       limit *m22-empty*))))

(assert-event
  (let* ((xs (fn-exp-initial)) (address '(2 . (127 0 0 1)))
         (limits (fn-adm-exposure-limits nil 1024 nil nil 0))
         (old (fn-exp-limits nil 1024 nil nil))
         (one (fn-exp-limits nil 1 nil nil)))
    (and (equal (fn-exp-lim-total limits) 0)
         (equal (car (fn-exp-admit-decision xs limits 0 address 0)) :refuse)
         (equal (car (fn-exp-admit-decision xs old 0 address 0)) :admit)
         (equal (car (fn-exp-admit-decision xs one 0 address 0)) :admit))))

(defun m22-intern-row (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (row fn-arena)
    (fn-cat-intern-list
      (fn-record-make 2 1 4 "<adt-11@example.invalid>" nil
                      '("fn.test" "fn.other") "o0" "s0" "e0" 4 841000011)
      nil 0 fn-arena)
    (mv row fn-arena)))

(defun m22-held-row ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (row fn-arena) (m22-intern-row fn-arena) row)))

(assert-event
  (let ((row (m22-held-row)) (limit (* 4096 *fn-heap-mib*)))
    (and (fn-held-p row)
         (not (fn-adm-run-memory-admitp *m22-profile* *m22-img* *m22-cfg*
                                       limit *m22-empty* row 0 0))
         ; Teeth: the old POSP-as-absent projection prices full configured C
         ; and actually admits this fitting VALID row despite installed 0.
         (fn-adm-memory-admitp *m22-profile* *m22-img*
           (fn-adm-cfg-at *m22-cfg* (if (posp 0) (min 32 0) 32))
           limit *m22-empty* row))))

(assert-event
  (let* ((held 0) (cfg *m22-lowered-cfg*)
         (lease (* 4096 (fn-hl-article-capl *m22-profile* 1048576)))
         (bare (fn-adm-priced-cfg cfg held 1))
         (charged (fn-adm-priced-cfg (fn-adm-retained-runtime-cfg cfg lease) held 1))
         (limit (max (fn-mm-sum *m22-profile* *m22-img* charged *m22-empty*)
                     (fn-mm-reopen-need *m22-profile* *m22-img* charged *m22-empty*)))
         (old-limit (max (fn-mm-sum *m22-profile* *m22-img* bare *m22-empty*)
                         (fn-mm-reopen-need *m22-profile* *m22-img* bare *m22-empty*)))
         (instant (fn-mm-need *m22-profile* *m22-img* bare *m22-empty* held held
                     (fn-heap-article-slots *m22-profile*)
                     (fn-cbud-handshake-slots t 16) t)))
    (and (natp lease) (posp lease)
         (fn-mm-gate-p *m22-profile* *m22-img* charged limit *m22-empty*)
         (<= (+ lease instant) limit)
         ; Old behavior drops the bank's charge with no return receipt.
         (fn-mm-gate-p *m22-profile* *m22-img* bare old-limit *m22-empty*)
         (< old-limit (+ lease instant)))))

(assert-event
  (and (equal (fn-adm-reader-count 32 nil) 32)
       (equal (fn-adm-reader-count 32 0) 0)
       (equal (fn-adm-memory-owner-bound 1024 nil) 1024)
       (equal (fn-adm-memory-owner-bound 1024 0) 0)
       (equal (fn-adm-priced-connections 32 32 0) 32)
       (not (equal (if (posp 0) (min 32 0) 32) 0))))

(assert-event
  (let* ((cfg (fn-adm-cfg-at *m22-cfg* 0))
         (limit (* 250 *fn-heap-mib*))
         (found (fn-adm-capacity *m22-profile* *m22-img* cfg limit *m22-empty*))
         (cap (fn-adm-installed-capacity *m22-profile* *m22-img* cfg limit *m22-empty*))
         (expected (concatenate 'string
          "refused memory-cannot-hold-the-store capacity=0 of 0 bound-by="
          (string-downcase (symbol-name
            (fn-adm-capacity-binding *m22-profile* *m22-img* cfg limit *m22-empty*)))
          " sum=" (fn-adm-mb-up (fn-mm-sum *m22-profile* *m22-img* cfg *m22-empty*))
          " MB limit=" (fn-adm-mb-down limit) " MB")))
    (and (equal found 0) (equal cap 0)
         (equal (fn-adm-installed-capacity-line *m22-profile* *m22-img* cfg limit *m22-empty*) expected)
         (not (equal (fn-adm-capacity-line *m22-profile* *m22-img* cfg limit *m22-empty*) expected)))))

; M22 behavioral twins; the wiring equality is deliberately not an event.

(defconst *m22-priced-cfg* (fn-adm-priced-cfg *m22-lowered-cfg* 32 1))
(defconst *m22-held-limit* (max (fn-mm-sum *m22-profile* *m22-img* *m22-priced-cfg* *m22-empty*)
                               (fn-mm-reopen-need *m22-profile* *m22-img* *m22-priced-cfg* *m22-empty*)))
(defconst *m22-lease* (* 4096 (fn-hl-article-capl *m22-profile* 1048576)))
(defconst *m22-lease-cfg* (fn-adm-priced-cfg (fn-adm-retained-runtime-cfg *m22-lowered-cfg* *m22-lease*) 0 1))
(defconst *m22-lease-limit* (max (fn-mm-sum *m22-profile* *m22-img* *m22-lease-cfg* *m22-empty*)
                                (fn-mm-reopen-need *m22-profile* *m22-img* *m22-lease-cfg* *m22-empty*)))
(defkeystone m22-adm-priced-connections-cover-held
  (<= (nfix held) (fn-adm-priced-connections held configured capacity))
 :id "PRF-10018"
 :rule-classes nil
 :restates fn-adm-priced-connections-cover-held
 :subject fn-adm-priced-connections
 :witness ((held 32) (configured 1) (capacity 1))
 :mutations ((old-behavior (:conclusion (<= (nfix held) (fn-adm-reader-count configured capacity))) ((held 32) (configured 1) (capacity 1)) :fault "the old min(C,Cprime) drops 31 held connections"))
 :hints (("Goal" :by fn-adm-priced-connections-cover-held)))

(defkeystone m22-adm-priced-connections-equal-reader-count-when-covered
  (implies (<= (nfix held) (fn-adm-reader-count configured capacity))
           (equal (fn-adm-priced-connections held configured capacity)
                  (fn-adm-reader-count configured capacity)))
 :id "PRF-10018"
 :rule-classes nil
 :restates fn-adm-priced-connections-equal-reader-count-when-covered
 :subject fn-adm-priced-connections
 :witness ((held 0) (configured 32) (capacity 0))
 :hyps (covered)
 :breaks ((covered ((held 32) (configured 1) (capacity 1))))
 :mutations ((old-behavior (:conclusion (equal (if (posp capacity) (min (nfix configured) capacity) (nfix configured)) (fn-adm-reader-count configured capacity))) ((held 0) (configured 32) (capacity 0)) :fault "POSP treats installed zero as absent"))
 :hints (("Goal" :by fn-adm-priced-connections-equal-reader-count-when-covered)))

(defkeystone m22-adm-priced-gate-bounds-the-held-instant
(let ((priced (fn-adm-priced-cfg cfg held capacity)))
    (implies (fn-mm-gate-p profile img priced limit tot)
             (<= (fn-mm-need profile img priced tot
                            (nfix held) (nfix held)
                            (fn-heap-article-slots profile)
                            (fn-cbud-handshake-slots
                              (fn-mm-cfg-tlsp priced)
                              (fn-mm-cfg-handshakes priced))
                            publishing)
                 limit)))
 :id "PRF-10018"
 :rule-classes nil
 :restates fn-adm-priced-gate-bounds-the-held-instant
 :subject fn-adm-priced-cfg
 :witness ((profile *m22-profile*) (img *m22-img*) (cfg *m22-lowered-cfg*) (tot *m22-empty*) (held 32) (capacity 1) (publishing t) (limit *m22-held-limit*))
 :hyps (holding)
 :breaks ((holding ((profile *m22-profile*) (img *m22-img*) (cfg *m22-lowered-cfg*) (tot *m22-empty*) (held 32) (capacity 1) (publishing t) (limit 0))))
 :mutations ((old-behavior (:conclusion (<= (fn-mm-need profile img (fn-adm-cfg-at cfg (fn-adm-reader-count (fn-mm-cfg-connections cfg) capacity)) tot (nfix held) (nfix held) (fn-heap-article-slots profile) (fn-cbud-handshake-slots (fn-mm-cfg-tlsp cfg) (fn-mm-cfg-handshakes cfg)) publishing)
 (max (fn-mm-sum profile img (fn-adm-cfg-at cfg (fn-adm-reader-count (fn-mm-cfg-connections cfg) capacity)) tot) (fn-mm-reopen-need profile img cfg tot)))) ((profile *m22-profile*) (img *m22-img*) (cfg *m22-lowered-cfg*) (tot *m22-empty*) (held 32) (capacity 1) (publishing t) (limit *m22-held-limit*)) :fault "the old gate prices min(C,Cprime), admitting a bound below the held instant"))
 :hints (("Goal" :by fn-adm-priced-gate-bounds-the-held-instant)))

(defkeystone m22-adm-priced-gate-holds-the-retained-lease
(let* ((bare (fn-adm-priced-cfg cfg held capacity))
         (charged (fn-adm-priced-cfg
                    (fn-adm-retained-runtime-cfg cfg lease-octets)
                    held capacity)))
    (implies (fn-mm-gate-p profile img charged limit tot)
             (<= (+ (nfix lease-octets)
                    (fn-mm-need profile img bare tot (nfix held) (nfix held)
                      (fn-heap-article-slots profile)
                      (fn-cbud-handshake-slots
                        (fn-mm-cfg-tlsp bare) (fn-mm-cfg-handshakes bare))
                      publishing))
                 limit)))
 :id "PRF-10018"
 :rule-classes nil
 :restates fn-adm-priced-gate-holds-the-retained-lease
 :subject fn-adm-priced-cfg
 :witness ((profile *m22-profile*) (img *m22-img*) (cfg *m22-lowered-cfg*) (tot *m22-empty*) (held 0) (capacity 1) (publishing t) (lease-octets *m22-lease*) (limit *m22-lease-limit*))
 :hyps (holding)
 :breaks ((holding ((profile *m22-profile*) (img *m22-img*) (cfg *m22-lowered-cfg*) (tot *m22-empty*) (held 0) (capacity 1) (publishing t) (lease-octets *m22-lease*) (limit 0))))
 :mutations ((old-behavior (:conclusion (<= (+ (nfix lease-octets) (fn-mm-need profile img (fn-adm-priced-cfg cfg held capacity) tot (nfix held) (nfix held) (fn-heap-article-slots profile) (fn-cbud-handshake-slots (fn-mm-cfg-tlsp cfg) (fn-mm-cfg-handshakes cfg)) publishing))
(max (fn-mm-sum profile img (fn-adm-priced-cfg cfg held capacity) tot) (fn-mm-reopen-need profile img (fn-adm-priced-cfg cfg held capacity) tot)))) ((profile *m22-profile*) (img *m22-img*) (cfg *m22-lowered-cfg*) (tot *m22-empty*) (held 0) (capacity 1) (publishing t) (lease-octets *m22-lease*) (limit *m22-lease-limit*)) :fault "the old gate erases the allocated lease bank when the reader limit falls"))
 :hints (("Goal" :by fn-adm-priced-gate-holds-the-retained-lease)))

(defkeystone m22-adm-installed-capacity-is-proved-or-zero
  (let ((found (fn-adm-capacity profile img cfg limit tot))
        (installed (fn-adm-installed-capacity profile img cfg limit tot)))
    (and (natp installed)
         (equal installed (if (natp found) found 0))
         (or (equal installed 0)
             (and (equal installed found)
                  (<= installed (fn-mm-cfg-connections cfg))
                  (fn-mm-gate-p profile img (fn-adm-cfg-at cfg installed)
                                limit tot)))))
 :id "PRF-10019"
 :rule-classes nil
 :restates fn-adm-installed-capacity-is-proved-or-zero
 :subject fn-adm-installed-capacity
 :witness ((profile *m22-profile*) (img *m22-img*) (cfg *m22-cfg*) (limit (* 128 *fn-heap-mib*)) (tot *m22-empty*))
 :mutations ((old-behavior (:conclusion (equal (fn-adm-installed-capacity profile img cfg limit tot) (let ((found (fn-adm-capacity profile img cfg limit tot))) (if (posp found) found 1)))) ((profile *m22-profile*) (img *m22-img*) (cfg *m22-cfg*) (limit (* 128 *fn-heap-mib*)) (tot *m22-empty*)) :fault "the old fallback installs 1 when no count fits"))
 :hints (("Goal" :by fn-adm-installed-capacity-is-proved-or-zero)))

(defkeystone m22-adm-zero-capacity-refuses-new-readers
  (let ((limits (fn-adm-exposure-limits v maximum publicp auth-required 0)))
    (and (equal (fn-exp-lim-total limits) 0)
         (equal (car (fn-exp-admit-decision xs limits held address now))
                :refuse)))
 :id "PRF-10019"
 :rule-classes nil
 :restates fn-adm-zero-capacity-refuses-new-readers
 :subject fn-adm-exposure-limits
 :witness ((v nil) (maximum 1024) (publicp nil) (auth-required nil) (xs (fn-exp-initial)) (held 0) (address '(2 . (127 0 0 1))) (now 0))
 :mutations ((old-behavior (:conclusion (equal (car (fn-exp-admit-decision xs (fn-exp-limits v maximum publicp auth-required) held address now)) :refuse)) ((v nil) (maximum 1024) (publicp nil) (auth-required nil) (xs (fn-exp-initial)) (held 0) (address '(2 . (127 0 0 1))) (now 0)) :fault "the old reader policy treats zero capacity as absent"))
 :hints (("Goal" :by fn-adm-zero-capacity-refuses-new-readers)))

(defkeystone m22-adm-zero-capacity-refuses-records
  (not (fn-adm-run-memory-admitp profile img cfg limit tot row held 0))
 :id "PRF-10019"
 :rule-classes nil
 :restates fn-adm-zero-capacity-refuses-records
 :subject fn-adm-run-memory-admitp
 :witness ((profile *m22-profile*) (img *m22-img*) (cfg *m22-cfg*) (limit (* 4096 *fn-heap-mib*)) (tot *m22-empty*) (row (m22-held-row)) (held 0))
 :mutations ((old-behavior (:conclusion (not (fn-adm-memory-admitp profile img cfg limit tot row))) ((profile *m22-profile*) (img *m22-img*) (cfg *m22-cfg*) (limit (* 4096 *fn-heap-mib*)) (tot *m22-empty*) (row (m22-held-row)) (held 0)) :fault "the old gate admits a fitting valid row while capacity is zero"))
 :hints (("Goal" :by fn-adm-zero-capacity-refuses-records)))

(defkeystone m22-adm-absent-capacity-and-zero-are-distinct
  (and (equal (fn-adm-reader-count configured nil) (nfix configured))
       (equal (fn-adm-reader-count configured 0) 0)
       (equal (fn-adm-memory-owner-bound maximum nil) (nfix maximum))
       (equal (fn-adm-memory-owner-bound maximum 0) 0)
       (equal (fn-adm-priced-connections held configured 0) (nfix held)))
 :id "PRF-10019"
 :rule-classes nil
 :restates fn-adm-absent-capacity-and-zero-are-distinct
 :subject fn-adm-reader-count
 :witness ((configured 32) (maximum 1024) (held 32))
 :mutations ((old-behavior (:conclusion (equal (if (posp 0) (min (nfix configured) 0) (nfix configured)) 0)) ((configured 32) (maximum 1024) (held 32)) :fault "the old POSP projection returns configured C at installed zero"))
 :hints (("Goal" :by fn-adm-absent-capacity-and-zero-are-distinct)))

(defkeystone m22-adm-installed-zero-has-the-zero-diagnostic
  (implies (equal (fn-adm-installed-capacity profile img cfg limit tot) 0)
    (equal (fn-adm-installed-capacity-line profile img cfg limit tot)
      (concatenate 'string
        "refused memory-cannot-hold-the-store capacity=0 of "
        (fn-heap-decimal (fn-mm-cfg-connections cfg))
        " bound-by="
        (string-downcase (symbol-name
          (fn-adm-capacity-binding profile img cfg limit tot)))
        " sum=" (fn-adm-mb-up
          (fn-mm-sum profile img (fn-adm-cfg-at cfg 0) tot))
        " MB limit=" (fn-adm-mb-down limit) " MB")))
 :id "PRF-10019"
 :rule-classes nil
 :restates fn-adm-installed-zero-has-the-zero-diagnostic
 :subject fn-adm-installed-capacity-line
 :witness ((profile *m22-profile*) (img *m22-img*) (cfg (fn-adm-cfg-at *m22-cfg* 0)) (limit (* 250 *fn-heap-mib*)) (tot *m22-empty*))
 :hyps (zero)
 :breaks ((zero ((profile *m22-profile*) (img *m22-img*) (cfg *m22-cfg*) (limit (* 250 *fn-heap-mib*)) (tot *m22-empty*))))
 :mutations ((old-behavior (:conclusion (equal (fn-adm-capacity-line profile img cfg limit tot) (fn-adm-installed-capacity-line profile img cfg limit tot))) ((profile *m22-profile*) (img *m22-img*) (cfg (fn-adm-cfg-at *m22-cfg* 0)) (limit (* 250 *fn-heap-mib*)) (tot *m22-empty*)) :fault "raw search result zero was described as a successful capacity"))
 :hints (("Goal" :by fn-adm-installed-zero-has-the-zero-diagnostic)))
