; Teeth for books/replay-historical-limits.lisp (row S1 item 3, lane
; limits-live-8, PRF-1026).  The history is config-physical-replay-tests':
; two retention events and an article at txid 7 under the default
; configuration, a capacity decrease and increase.  After the article is
; accepted, a record lowers max-article-octets to 1, below the article's
; size; the open replays the article all the same, exactly as under the
; history that keeps the limit.  The hypothesis-removal witness rewrites a
; :set-capacity value instead: the capacity is decided historically, and the
; open's node changes.

(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/replay-historical-limits")
(include-book "held-rows-tests")

(defconst *rhl-t-stamp* *fn-cfg-default-stamp*)
(defconst *rhl-t-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-cpr" "subject" "evidence" 10))
(defconst *rhl-t-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-cpr" "subject" "evidence" 0))
(defconst *rhl-t-decrease*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *rhl-t-stamp*))
(defconst *rhl-t-increase*
  (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *rhl-t-stamp*))
(defconst *rhl-t-article-wire*
  (fn-record-make 2 7 7 "<cpr@example.invalid>" '(65) '("fn.test")
                  "archive-cpr" "subject" "evidence" 2 841000000))
(defconst *rhl-t-events*
  (fn-hrt-rows (list *rhl-t-undertake* *rhl-t-release* *rhl-t-article-wire*)
               nil 0))
(defconst *rhl-t-prefix* (take 2 *rhl-t-events*))
(defconst *rhl-t-suffix* (nthcdr 2 *rhl-t-events*))

; After the article (txid 7), at txid 8: max-article-octets lowered to 1,
; against a history that sets it to 1 MiB.
(defconst *rhl-t-lowered*
  (fn-cfg-record-make 3 8 4 (list (fn-cfg-set-limit "max-article-octets" 1))
                      *rhl-t-stamp*))
(defconst *rhl-t-kept*
  (fn-cfg-record-make 3 8 4 (list (fn-cfg-set-limit "max-article-octets" 1048576))
                      *rhl-t-stamp*))
(defconst *rhl-t-configs-lowered*
  (list *fn-cfg-default-record* *rhl-t-decrease* *rhl-t-increase* *rhl-t-lowered*))
(defconst *rhl-t-configs-kept*
  (list *fn-cfg-default-record* *rhl-t-decrease* *rhl-t-increase* *rhl-t-kept*))

(defun rhl-t-open-fold (configs)
  ; The configuration fold the host's open returns first.
  (fn-sco-cpr-finish
   (fn-sco-cpr (car (fn-rii-sco-extend-open (fn-sco-capture configs *rhl-t-prefix*)
                                            configs *rhl-t-suffix* 8)))
   configs))

(defun rhl-t-articles (r)
  (fn-state-articles (fn-node-acceptance (fn-cnode-node (fn-replay-result-node r)))))

; The article's size exceeds the lowered limit.
(assert-event (< 1 (len (fn-record-encode-impl *rhl-t-article-wire*))))

; Positive witness, fn-rhl-extend-open-is-limit-free: the antecedent (an
; admitted history; two configuration histories differing only in a
; :set-limit value, and differing) and the conclusion.
(assert-event
 (and (fn-sn-observed-historyp 8 (append *rhl-t-prefix* *rhl-t-suffix*))
      (fn-rhl-configs-variantp *rhl-t-configs-lowered* *rhl-t-configs-kept*)
      (not (equal *rhl-t-configs-lowered* *rhl-t-configs-kept*))
      (equal (fn-rhl-blank-result (rhl-t-open-fold *rhl-t-configs-lowered*))
             (fn-rhl-blank-result (rhl-t-open-fold *rhl-t-configs-kept*)))))

; What the equality carries: the lowered history's open is :ok at position 7
; (four configurations, three events), serves the lowered limit, and holds
; the article accepted before the lowering.
(assert-event
 (let ((r (rhl-t-open-fold *rhl-t-configs-lowered*)))
   (and (equal (fn-replay-result-kind r) :ok)
        (equal (fn-cfg-limit (fn-cfg-value (fn-cnode-config (fn-replay-result-node r)))
                             "max-article-octets")
               1)
        (consp (rhl-t-articles r))
        (equal (rhl-t-articles r)
               (rhl-t-articles (rhl-t-open-fold *rhl-t-configs-kept*))))))

; Hypothesis-removal witness: the :set-capacity 20 row rewritten to 1.  The
; retained hypothesis holds, the omitted one fails, and so does the
; conclusion: the article no longer fits the capacity in force at its
; position, and the open refuses it.
(defconst *rhl-t-configs-capacity*
  (list *fn-cfg-default-record* *rhl-t-decrease*
        (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 1)) *rhl-t-stamp*)
        *rhl-t-kept*))
(assert-event
 (and (fn-sn-observed-historyp 8 (append *rhl-t-prefix* *rhl-t-suffix*))
      (not (fn-rhl-configs-variantp *rhl-t-configs-capacity* *rhl-t-configs-kept*))
      (not (equal (fn-rhl-blank-result (rhl-t-open-fold *rhl-t-configs-capacity*))
                  (fn-rhl-blank-result (rhl-t-open-fold *rhl-t-configs-kept*))))
      (equal (fn-replay-result-kind (rhl-t-open-fold *rhl-t-configs-capacity*))
             :fault)))
