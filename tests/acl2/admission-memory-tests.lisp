; Witnesses for books/admission-memory.lisp (K-ADMIT; Builder M, memory
; landing 3+4, 2026-10-09).
;
; The small preset's profile (16,384 transactions, 8 MiB of history) on the
; production image's measured floor (as tests/acl2/memory-model-tests.lisp),
; W13's 1,000 POSTs as the carried totals, and a HELD row interned on a local
; arena as the article's row.  The memory gate at this store admits the
; article at 380 MiB and refuses it at 340 MiB (the reopen's need after the
; commit is 358,953,114 octets, the sum 318,054,629 with the OVER window at
; A-OVER-WINDOW-FIT's one line), while the transactions (1,000 of 16,384) and the
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
(defconst *adt-340m* (* 340 1048576))
; the used count, the carried octets and the debt the owner hands the budget
(defconst *adt-used* 1000)
(defconst *adt-bytes* (fn-mm-tot-charge *adt-tot*))
(defconst *adt-debt* 0)
(defconst *adt-after* (fn-adm-after *adt-tot* *adt-row*))
(defconst *adt-edge* (max (fn-mm-sum *adt-p* *adt-img* *adt-cfg* *adt-after*)
                          (fn-mm-reopen-need *adt-p* *adt-img* *adt-cfg* *adt-after*)))

; The figures the prose above quotes.
(assert-event (equal *adt-bytes* 7648000))
(assert-event (equal (fn-mm-sum *adt-p* *adt-img* *adt-cfg* *adt-after*) 318054629))
(assert-event (< *adt-340m* *adt-edge*))
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
(assert-event (not (fn-adm-memory-admitp *adt-p* *adt-img* *adt-cfg* *adt-340m* *adt-tot* *adt-row*)))
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
(assert-event (equal (adt-k1 *adt-340m* *adt-used* *adt-bytes*) '(nil nil t nil)))
; T alone refuses
(assert-event (equal (adt-k1 *adt-380m* 16384 *adt-bytes*) '(nil nil nil t)))
; H alone refuses
(assert-event (equal (adt-k1 *adt-380m* *adt-used* 8388608) '(nil nil nil t)))
; mutation: a budget that never asks the memory admits where the model refuses
; (340 MiB: the conclusion's conjunction of T and H alone is t, the budget is nil)
(assert-event (not (equal (car (adt-k1 *adt-340m* *adt-used* *adt-bytes*))
                          (caddr (adt-k1 *adt-340m* *adt-used* *adt-bytes*)))))
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
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-340m*)
            (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
            (tot *adt-tot*) (row *adt-row*))
  :breaks ((refused ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-380m*)
                     (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                     (tot *adt-tot*) (row *adt-row*))))
  :mutations ((word-without-memory
               (:conclusion (let* ((w (fn-adm-article-word :unaffordable profile img cfg limit used bytes-used
                                                           record debt tot row)))
                              (member-equal w '(:unaffordable :history-exhausted))))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-340m*)
                (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                (tot *adt-tot*) (row *adt-row*))
               :fault "a refusal word with no :memory: the memory's refusal reported as :unaffordable")
              (memory-named-ahead-of-the-transactions
               (:conclusion (let* ((mx (fn-adm-memory-admitp profile img cfg limit tot row))
                                   (w (fn-adm-article-word :unaffordable profile img cfg limit used bytes-used
                                                           record debt tot row)))
                              (iff (equal w :memory) (not mx))))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-340m*)
                (used 16384) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                (tot *adt-tot*) (row *adt-row*))
               :fault "a word that names the memory whenever it refuses, ahead of a store out of transactions")))

; The word is each resource's at its own ceiling, and :memory only when T and H admit.
(assert-event (equal (fn-adm-article-word :unaffordable *adt-p* *adt-img* *adt-cfg* *adt-340m*
                                          *adt-used* *adt-bytes* *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :memory))
(assert-event (equal (fn-adm-article-word :unaffordable *adt-p* *adt-img* *adt-cfg* *adt-340m*
                                          16384 *adt-bytes* *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :unaffordable))
(assert-event (equal (fn-adm-article-word :unaffordable *adt-p* *adt-img* *adt-cfg* *adt-340m*
                                          *adt-used* 8388608 *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :history-exhausted))
; a word other than :unaffordable passes through (fn-adm-article-word-passes-other-words)
(assert-event (equal (fn-adm-article-word :corrupt *adt-p* *adt-img* *adt-cfg* *adt-340m*
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
  :breaks ((admitted ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-340m*)
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
; 230 MiB with an empty store: C' is 18 of 32, bound by the OVER window (one
; line's octet-list window a holder under A-OVER-WINDOW-FIT, 667,648 octets
; with the fixed part's 500,736); 380 MiB holds W13's 1,000 POSTs at all 32;
; 128 MiB holds no connection (the sum with none is 204 MB): the run refuses.
; The store antitone at 250 MiB: 32 at 0 posts, 29 at 100, 27 at 200, 22 at
; 300, none at 400.
(defconst *adt-230m* (* 230 1048576))
(defconst *adt-250m* (* 250 1048576))
(defconst *adt-128m* (* 128 1048576))
(defconst *adt-empty* (adt-posts 0))
(defconst *adt-big* (adt-posts 300))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-230m* *adt-empty*) 18))
(assert-event (equal (fn-adm-capacity-binding *adt-p* *adt-img* *adt-cfg* *adt-230m* *adt-empty*)
                     :over-window))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-380m* *adt-tot*) 32))
(assert-event (equal (fn-adm-capacity-binding *adt-p* *adt-img* *adt-cfg* *adt-380m* *adt-tot*)
                     :configured))
(assert-event (null (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-128m* *adt-empty*)))
(assert-event (equal (fn-adm-capacity-binding *adt-p* *adt-img* *adt-cfg* *adt-128m* *adt-empty*)
                     :store))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* *adt-empty*) 32))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* (adt-posts 100)) 29))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* (adt-posts 200)) 27))
(assert-event (equal (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* *adt-big*) 22))
(assert-event (null (fn-adm-capacity *adt-p* *adt-img* *adt-cfg* *adt-250m* (adt-posts 400))))
(assert-event (equal (fn-adm-capacity-line *adt-p* *adt-img* *adt-cfg* *adt-128m* *adt-empty*)
                     "refused memory-cannot-hold-the-store capacity=0 of 32 bound-by=store sum=204 MB limit=128 MB"))
(assert-event (equal (fn-adm-capacity-line *adt-p* *adt-img* *adt-cfg* *adt-230m* *adt-empty*)
                     "memory capacity=18 of 32 bound-by=over-window sum=229 MB limit=230 MB"))

(defteeth fn-adm-capacity-fits
  :claim (((fits (fn-adm-capacity profile img cfg limit tot)))
          (let ((c (fn-adm-capacity profile img cfg limit tot)))
            (and (natp c)
                 (<= c (fn-mm-cfg-connections cfg))
                 (fn-mm-gate-p profile img (fn-adm-cfg-at cfg c) limit tot))))
  :subject fn-adm-capacity
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
            (tot *adt-empty*))
  :breaks ((fits ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-128m*)
                  (tot *adt-empty*))))
  :mutations ((the-gate-holds-one-more
               (:conclusion (fn-mm-gate-p profile img
                                          (fn-adm-cfg-at cfg (+ 1 (fn-adm-capacity profile img cfg limit tot)))
                                          limit tot))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
                (tot *adt-empty*))
               :fault "a capacity one below the count the gate holds at: the run would admit fewer readers than the memory holds, or, read the other way, one more than it holds")))

(defteeth fn-adm-capacity-is-the-most
  :claim (((counted (natp j))
           (within (<= j (fn-mm-cfg-connections cfg)))
           (holds (fn-mm-gate-p profile img (fn-adm-cfg-at cfg j) limit tot)))
          (let ((c (fn-adm-capacity profile img cfg limit tot)))
            (and (natp c) (<= j c))))
  :subject fn-adm-capacity
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
            (tot *adt-empty*) (j 18))
  :breaks ((counted ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
                     (tot *adt-empty*) (j 37/2)))
           (within ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-380m*)
                    (tot *adt-empty*) (j 33)))
           (holds ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
                   (tot *adt-empty*) (j 19))))
  :mutations ((capacity-is-always-c
               (:conclusion (equal (fn-adm-capacity profile img cfg limit tot)
                                   (fn-mm-cfg-connections cfg)))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
                (tot *adt-empty*) (j 18))
               :fault "a run that prices its configured C whatever the limit: at 39c86eb48 the 2 GiB node refused every POST by the memory")
              (strictly-more
               (:conclusion (< j (fn-adm-capacity profile img cfg limit tot)))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-230m*)
                (tot *adt-empty*) (j 18))
               :fault "a capacity past the last count the gate holds at")))

(defteeth fn-adm-capacity-antitone-in-the-store
  :claim (((smaller (fn-mm-tot-le a b))
           (fits (fn-adm-capacity profile img cfg limit b)))
          (and (natp (fn-adm-capacity profile img cfg limit a))
               (<= (fn-adm-capacity profile img cfg limit b)
                   (fn-adm-capacity profile img cfg limit a))))
  :subject fn-adm-capacity
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-250m*)
            (a *adt-empty*) (b *adt-big*))
  :breaks ((smaller ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-250m*)
                     (a *adt-big*) (b *adt-empty*)))
           (fits ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-128m*)
                  (a *adt-empty*) (b *adt-big*))))
  :mutations ((capacity-grows-with-the-store
               (:conclusion (<= (fn-adm-capacity profile img cfg limit a)
                                (fn-adm-capacity profile img cfg limit b)))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-250m*)
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
