; Witnesses for books/admission-memory.lisp (K-ADMIT; Builder M, memory
; landing 3+4, 2026-10-09).
;
; The small preset's profile (16,384 transactions, 8 MiB of history) on the
; production image's measured floor (as tests/acl2/memory-model-tests.lisp),
; W13's 1,000 POSTs as the carried totals, and a HELD row interned on a local
; arena as the article's row.  The memory gate at this store admits the
; article at 7 GiB and refuses it at 6 GiB (the model's need after the commit
; is 7,128,064,229 octets), while the transactions (1,000 of 16,384) and the
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
(defconst *adt-7g* (* 7 1024 1048576))
(defconst *adt-6g* (* 6 1024 1048576))
; the used count, the carried octets and the debt the owner hands the budget
(defconst *adt-used* 1000)
(defconst *adt-bytes* (fn-mm-tot-charge *adt-tot*))
(defconst *adt-debt* 0)
(defconst *adt-after* (fn-adm-after *adt-tot* *adt-row*))
(defconst *adt-edge* (max (fn-mm-sum *adt-p* *adt-img* *adt-cfg* *adt-after*)
                          (fn-mm-reopen-need *adt-p* *adt-img* *adt-cfg* *adt-after*)))

; The figures the prose above quotes.
(assert-event (equal *adt-bytes* 7648000))
(assert-event (equal (fn-mm-sum *adt-p* *adt-img* *adt-cfg* *adt-after*) 7128064229))
(assert-event (< *adt-6g* *adt-edge*))
(assert-event (< *adt-edge* *adt-7g*))
(assert-event (equal (fn-adm-residency *adt-tot*) :resident))

; The three resources at the figures above.
(assert-event (fn-cvec-article-transactions-admitp *adt-p* *adt-used* *adt-debt*))
(assert-event (fn-cvec-article-history-admitp
               *adt-p* *adt-bytes*
               (fn-sbud-article-gate-figure (len (fn-record-payload *adt-record*))
                                            (len (fn-record-groups *adt-record*)))
               *adt-debt*))
(assert-event (fn-adm-memory-admitp *adt-p* *adt-img* *adt-cfg* *adt-7g* *adt-tot* *adt-row*))
(assert-event (not (fn-adm-memory-admitp *adt-p* *adt-img* *adt-cfg* *adt-6g* *adt-tot* *adt-row*)))
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
(assert-event (equal (adt-k1 *adt-7g* *adt-used* *adt-bytes*) '(t t t t)))
; the memory alone refuses: the budget refuses
(assert-event (equal (adt-k1 *adt-6g* *adt-used* *adt-bytes*) '(nil nil t nil)))
; T alone refuses
(assert-event (equal (adt-k1 *adt-7g* 16384 *adt-bytes*) '(nil nil nil t)))
; H alone refuses
(assert-event (equal (adt-k1 *adt-7g* *adt-used* 8388608) '(nil nil nil t)))
; mutation: a budget that never asks the memory admits where the model refuses
; (6 GiB: the conclusion's conjunction of T and H alone is t, the budget is nil)
(assert-event (not (equal (car (adt-k1 *adt-6g* *adt-used* *adt-bytes*))
                          (caddr (adt-k1 *adt-6g* *adt-used* *adt-bytes*)))))
; mutation: a budget that admits whenever the memory does, over a store out
; of transactions (16,384 committed): the memory admits and the budget refuses
(assert-event (not (equal (car (adt-k1 *adt-7g* 16384 *adt-bytes*))
                          (cadddr (adt-k1 *adt-7g* 16384 *adt-bytes*)))))

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
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-6g*)
            (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
            (tot *adt-tot*) (row *adt-row*))
  :breaks ((refused ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-7g*)
                     (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                     (tot *adt-tot*) (row *adt-row*))))
  :mutations ((word-without-memory
               (:conclusion (let* ((w (fn-adm-article-word :unaffordable profile img cfg limit used bytes-used
                                                           record debt tot row)))
                              (member-equal w '(:unaffordable :history-exhausted))))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-6g*)
                (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                (tot *adt-tot*) (row *adt-row*))
               :fault "a refusal word with no :memory: the memory's refusal reported as :unaffordable")
              (memory-named-ahead-of-the-transactions
               (:conclusion (let* ((mx (fn-adm-memory-admitp profile img cfg limit tot row))
                                   (w (fn-adm-article-word :unaffordable profile img cfg limit used bytes-used
                                                           record debt tot row)))
                              (iff (equal w :memory) (not mx))))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-6g*)
                (used 16384) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                (tot *adt-tot*) (row *adt-row*))
               :fault "a word that names the memory whenever it refuses, ahead of a store out of transactions")))

; The word is each resource's at its own ceiling, and :memory only when T and H admit.
(assert-event (equal (fn-adm-article-word :unaffordable *adt-p* *adt-img* *adt-cfg* *adt-6g*
                                          *adt-used* *adt-bytes* *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :memory))
(assert-event (equal (fn-adm-article-word :unaffordable *adt-p* *adt-img* *adt-cfg* *adt-6g*
                                          16384 *adt-bytes* *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :unaffordable))
(assert-event (equal (fn-adm-article-word :unaffordable *adt-p* *adt-img* *adt-cfg* *adt-6g*
                                          *adt-used* 8388608 *adt-record* *adt-debt* *adt-tot* *adt-row*)
                     :history-exhausted))
; a word other than :unaffordable passes through (fn-adm-article-word-passes-other-words)
(assert-event (equal (fn-adm-article-word :corrupt *adt-p* *adt-img* *adt-cfg* *adt-6g*
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
  :witness ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-7g*)
            (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
            (tot *adt-tot*) (row *adt-row*))
  :breaks ((admitted ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-6g*)
                      (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                      (tot *adt-tot*) (row *adt-row*))))
  :mutations ((gate-strictly-under-limit
               (:conclusion (and (< (fn-mm-sum profile img cfg (fn-adm-after tot row)) limit)
                                 (< (fn-mm-reopen-need profile img cfg (fn-adm-after tot row)) limit)))
               ((profile *adt-p*) (img *adt-img*) (cfg *adt-cfg*) (limit *adt-edge*)
                (used *adt-used*) (bytes-used *adt-bytes*) (record *adt-record*) (debt *adt-debt*)
                (tot *adt-tot*) (row *adt-row*))
               :fault "a gate that wants strict room under LIMIT: the store the budget admitted at exactly LIMIT would be called over it")))
