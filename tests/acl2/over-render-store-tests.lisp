; KL8: a satisfiable two-row store (filed and reclaimed), plus removals
; of the parse and retained-length premises. The reference runner checks
; the entire antecedent and enumerates the conclusion at every row.
; KL7c: a closed equality and a framing-removal tooth at the same instance.

(in-package "ACL2")
(include-book "../../books/over-render-store")
(include-book "filed-catalog-tests")

(assert-event
 (equal (fn-ovr-over-capl 0 0 0)
        (+ 2 (fn-ovr-nov-line-header-bound 0 0 nil) (fn-ovr-frame-max))))
(assert-event
 (not (equal (fn-ovr-over-capl 0 0 0)
             (+ 2 (fn-ovr-nov-line-header-bound 0 0 nil)))))

(defun kl8-row-okp (i a limits fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((article (fn-cat-row-article i fn-arena fn-cat))
         (payload (fn-nntp-article-bytes article fn-arena)))
    (if (or (fn-nntp-article-tombstonep article fn-arena)
            (and (fn-o1-article-within-headerp article payload)
                 (fn-article-result-okp (fn-article-parse-under payload limits))
                 (<= (len payload) (nfix a))))
        t nil)))
(defun kl8-rows-okp (i a limits fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (if (< i (fn-cat-count fn-cat))
      (and (kl8-row-okp i a limits fn-arena fn-cat) (kl8-rows-okp (+ 1 i) a limits fn-arena fn-cat))
    t))
(defun kl8-run (oc payloads a limits agent fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((own (fn-ocfg-owner oc))
         (rows (fn-sf-records (fn-sn-files (fn-own-store own))))
         (view (fn-own-view own))
         (stored (fn-o1-stored-header-limits limits agent))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (history (fn-cat-history-articles rows fn-arena))
         (fn-cat (fn-cat-clear fn-cat))
         (fn-cat (fn-sca-load-held-rows rows (fn-midx-build (fn-state-articles (fn-own-view-archive view)))
                                        fn-arena fn-cat)))
    (mv (list (fn-cat-count fn-cat)                                             ; 0
              (fn-ocl-relation oc)                                              ; 1 relation, conjunct
              (if (fn-own-store-idlep (fn-own-store own)) t nil)                ; 2 relation, conjunct
              (fn-cat-history-relation history fn-arena fn-cat)                 ; 3 relation, conjunct
              (fn-o1-records-filed-or-reclaimedp history)                       ; 4 premise (C, K1c)
              (fn-o1-cat-positionalp fn-cat)                                    ; 5 premise
              (fn-ovr-records-parse-or-reclaimedp history stored)               ; 6 premise (C)
              (fn-ovr-records-within-octets-or-reclaimedp history a)            ; 7 premise (M)
              (kl8-rows-okp 0 a stored fn-arena fn-cat))                        ; 8 the conclusion
        fn-arena fn-cat)))
(defun kl8-exec (ws a limits agent)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat) (kl8-run (p4-open ws) (p4-payloads ws) a limits agent fn-arena fn-cat)
          (mv r fn-arena)))
      r)))

(defconst *kl8-limits* (fn-article-limits 0 0 0))   ; sealed limits; stored = (7, 7, 2236 + 2 len(agent))
(defconst *kl8-agent* "news.example")
;; a filed article with nine header fields: over the stored seven at sealed fields 0
(defconst *kl8-src9*
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" (coerce '(#\Return #\Newline) 'string)
                "Newsgroups: fn.test,fn.letters" (coerce '(#\Return #\Newline) 'string)
                "Subject: s" (coerce '(#\Return #\Newline) 'string)
                "Message-ID: <w9@b.example>" (coerce '(#\Return #\Newline) 'string)
                "X-A: 1" (coerce '(#\Return #\Newline) 'string)
                "X-B: 2" (coerce '(#\Return #\Newline) 'string)
                "X-C: 3" (coerce '(#\Return #\Newline) 'string)
                "X-D: 4" (coerce '(#\Return #\Newline) 'string)
                "X-E: 5" (coerce '(#\Return #\Newline) 'string)
                (coerce '(#\Return #\Newline) 'string) "body" (coerce '(#\Return #\Newline) 'string))))
(defconst *kl8-w9* (p3-record 1 "<w9@b.example>" *kl8-src9* '("fn.test" "fn.letters")))
(defconst *kl8-h9* (list *p3-w0* *kl8-w9*))

;; satisfiable: a filed row and a reclaimed (tombstone) row; every premise, the conclusion at both rows
(assert-event (equal (kl8-exec *p5-hz* 100000 *kl8-limits* *kl8-agent*) '(2 t t t t t t t t)))
;; removal of the parse premise: the nine-field article, every other premise holds, the conclusion fails
(assert-event (equal (kl8-exec *kl8-h9* 100000 *kl8-limits* *kl8-agent*) '(2 t t t t t nil t nil)))
;; removal of the length premise: A below the filed payload's length
(assert-event (equal (kl8-exec *p5-hz* 10 *kl8-limits* *kl8-agent*) '(2 t t t t t t nil nil)))
