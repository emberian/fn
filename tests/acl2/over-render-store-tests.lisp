; KL8: a satisfiable two-row store (filed and reclaimed), plus removals
; of the parse and retained-length premises. The reference runner checks
; the entire antecedent and enumerates the conclusion at every row.
; KL7c: a closed equality and a framing-removal tooth at the same instance.

(in-package "ACL2")
(include-book "../../books/over-render-store")
(include-book "../../books/over-render-plan")
(include-book "../../books/defkeystone")
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

; O10 uses the same recovered owner and catalog load as KL8. These logic
; helpers expose the non-executable relations through the live getters.
(defun ovrs-payloads (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (cons (fn-record-payload (car records)) (ovrs-payloads (cdr records)))
    nil))

(defun ovrs-scol-check-from (i fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (fn-cat-count fn-cat) (nfix i)))))
  (if (and (natp i) (< i (fn-cat-count fn-cat)))
      (and (fn-scol-row-okp (fn-cat-at i fn-cat) fn-arena)
           (ovrs-scol-check-from (+ 1 i) fn-arena fn-cat))
    t))

(defun ovrs-owner-relation-check (oc fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((s (fn-own-store (fn-ocfg-owner oc)))
         (history (fn-cat-history-articles (fn-sf-records (fn-sn-files s)) fn-arena)))
    (and (fn-ocl-relation oc)
         (if (fn-own-store-idlep s)
             (fn-cat-history-relation history fn-arena fn-cat)
           (fn-cat-history-prefix-relation history fn-arena fn-cat)))))

(defun ovrs-host-observe (ws hdr group k top server v a fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((oc (p4-open ws))
         (own (fn-ocfg-owner oc))
         (rows (fn-sf-records (fn-sn-files (fn-own-store own))))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many (ovrs-payloads ws) fn-arena))
         (fn-cat (fn-cat-clear fn-cat))
         (fn-cat (fn-sca-load-held-rows
                  rows (fn-midx-build (fn-state-articles (fn-own-view-archive (fn-own-view own))))
                  fn-arena fn-cat))
         (records (fn-cat-history-articles rows fn-arena))
         (stored (fn-o1-stored-header-limits *kl8-limits* *kl8-agent*))
         (line (- (fn-ovr-over-capl hdr *fn-record-max-payload* (len server))
                  (fn-ovr-frame-max))))
    (mv (list (and (fn-arena-p fn-arena) (ovrs-scol-check-from 0 fn-arena fn-cat))
              (ovrs-owner-relation-check oc fn-arena fn-cat)
              (fn-o1-records-filed-or-reclaimedp records)
              (fn-o1-cat-positionalp fn-cat)
              (fn-ovr-records-parse-or-reclaimedp records stored)
              (<= (nfix (fn-article-limit-octets stored)) (nfix hdr))
              (natp v)
              (fn-ovr-probes-within group k top server v line fn-arena fn-cat)
              (fn-ovr-probe-len group k server v fn-arena fn-cat)
              line
              (fn-ovr-records-within-octets-or-reclaimedp records a)
              (if (fn-nntp-article-tombstonep
                   (fn-cat-row-article 0 fn-arena fn-cat) fn-arena) t nil))
        fn-arena fn-cat)))

(defun ovrs-host-exec (ws hdr group k top server v a)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (with-local-stobj fn-cat
        (mv-let (answer fn-arena fn-cat)
          (ovrs-host-observe ws hdr group k top server v a fn-arena fn-cat)
          (mv answer fn-arena)))
      answer)))

(defconst *ovrs-stored-hdr*
  (fn-article-limit-octets (fn-o1-stored-header-limits *kl8-limits* *kl8-agent*)))

(with-guard-checking-event
 :none
 (assert-event
  (let ((answer (ovrs-host-exec *p5-hz* *ovrs-stored-hdr* "fn.test" 1 1
                              (fn-record-string-octets *kl8-agent*) 2 *fn-record-max-payload*)))
    (and (equal (take 8 answer) '(t t t t t t t t))
         (< 0 (nth 8 answer))
         (nth 10 answer)))))

; T2 changes only A on the same valid, non-reclaimed record. Reclaiming
; that record selects the tombstone arm even at A = 0.
(with-guard-checking-event
 :none
 (assert-event
  (let* ((live (ovrs-host-exec (list *p3-w0*) *ovrs-stored-hdr* "fn.test" 1 1
                             (fn-record-string-octets *kl8-agent*) 1
                             (- (len (fn-record-payload *p3-w0*)) 1)))
         (reclaimed (ovrs-host-exec (list (fn-rclp-tombstoned *p3-w0*))
                                  *ovrs-stored-hdr* "fn.test" 1 1
                                  (fn-record-string-octets *kl8-agent*) 1 0)))
    (and (fn-record-p *p3-w0*)
         (equal (take 8 live) '(t t t t t t t t))
         (not (nth 10 live))
         (not (nth 11 live))
         (nth 10 reclaimed)
         (nth 11 reclaimed)
         (equal (nth 8 reclaimed) 0)))))

(defkeystone ovrs-served-records-within-the-record-ceiling
  (fn-ovr-records-within-octets-or-reclaimedp
   (fn-cat-history-articles (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) fn-arena)
   *fn-record-max-payload*)
  :restates fn-ovr-served-records-within-the-record-ceiling
  :subject fn-ovr-plan-lease-quantum
  :witness ((oc (p4-open *p5-hz*)) (payloads (ovrs-payloads *p5-hz*)))
  :stobjs ((fn-arena (fn-arn-seal-many payloads fn-arena)))
  :breaks nil
  :mutations
  ((lowered-admission-bound
    (:conclusion
     (fn-ovr-records-within-octets-or-reclaimedp
      (fn-cat-history-articles (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) fn-arena)
      (- (len (fn-record-payload *p3-w0*)) 1)))
    ((oc (p4-open (list *p3-w0*))) (payloads (ovrs-payloads (list *p3-w0*))))
    :fault "sizing retained records by an admission bound lowered below a live payload")
   (reclaimed-arm-omitted
    (:conclusion
     (<= (len (fn-record-payload
               (car (fn-cat-history-articles
                     (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) fn-arena))))
         0))
    ((oc (p4-open (list (fn-rclp-tombstoned *p3-w0*))))
     (payloads (ovrs-payloads (list (fn-rclp-tombstoned *p3-w0*)))))
    :fault "omitting the reclaimed disjunct applies the zero-octet bound to tombstone bytes"))
  :hints (("Goal" :by fn-ovr-served-records-within-the-record-ceiling)))
