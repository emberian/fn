; fn: witnesses and teeth for books/owner-reclaim-pass.lisp (Q16 (a), lane
; online-reclaim-3): the installing pass's credit, swap word, cuts, rerun,
; rebuild and swapped owner.
(in-package "ACL2")
(include-book "../../books/owner-reclaim-pass")
(include-book "must-fail-checked")
(include-book "arena-lift")
; The owner fixture's store (*rpt-s*, its arena *rpt-payloads*, its history's
; octets rpt-events) and the expiring context over it (*xt-ctx*).
(include-book "expiry-tests")

; -----------------------------------------------------------------------------
; 1. The credit (lane reclaim-funding, 2026-10-04;
; planning/design/reclaim-funding-2026-10-04.md).  Every call below is with
; the operator's opt-in (LIVE = t, `[resources] reclaim_live = true', D53);
; the refusals without it are section 1b.  A ledger with 10^6 octets
; of budget, 1,000 held by a connection, 500 by the open batch, and an
; owner's work reserve (the completion reserve) of 200,000.
(defconst *orcp-t-ops* (list (cons (fn-mca-conn-key 3) (cons 0 1000))
                             (cons :open (cons 0 500))))
(defconst *orcp-t-l* (fn-mcr-make 1000000 100000 0 200000 0 0 *orcp-t-ops* 0 nil))
(assert-event (fn-mcr-fundedp *orcp-t-l*))
; The demand over 3 records charging 1,000 octets: 10,416 a record and the
; same for the walk's chunk, 4,640 a tombstone, 12 a charged octet.
(assert-event (equal (fn-heap-reclaim-demand-octets 3 1000) (+ (* 10416 6) (* 4640 3) 12000)))
(assert-event (equal (fn-heap-reclaim-demand-octets 3 1000) 88416))
; The chunk term saturates at the walk's quantum.
(assert-event (equal (fn-heap-reclaim-demand-octets 2000 0) (+ (* 10416 3024) (* 4640 2000))))
(assert-event (equal (fn-heap-reclaim-chunk-rows) 1024))

; KEYSTONES fn-orcp-reserve-keeps-funded, fn-orcp-reserve-holds-the-estimate
; and fn-orcp-reserve-keeps-the-articles-room, positive witness: admitted,
; funded, the pass holds its demand, the connection and the open batch hold
; what they held, the funded total (the articles' room) is unchanged and the
; completion reserve is the demand less.
(defconst *orcp-t-r* (fn-orcp-reserved-credits *orcp-t-l* 3 1000 t))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-l* 3 1000 t)) :ok))
(assert-event (fn-mcr-fundedp *orcp-t-r*))
(assert-event (equal (fn-mcr-credit-of :reclaim (fn-mcr-ops *orcp-t-r*)) 88416))
(assert-event (equal (fn-mcr-credit-of (fn-mca-conn-key 3) (fn-mcr-ops *orcp-t-r*)) 1000))
(assert-event (equal (fn-mcr-credit-of :open (fn-mcr-ops *orcp-t-r*)) 500))
(assert-event (equal (fn-mcr-total *orcp-t-r*) (fn-mcr-total *orcp-t-l*)))
(assert-event (equal (fn-mcr-budget *orcp-t-r*) (fn-mcr-budget *orcp-t-l*)))
(assert-event (equal (fn-mcr-completion *orcp-t-r*) (- 200000 88416)))
; Mutation: a reservation that took the connection's credit is not this one.
(must-fail-checked
 (assert-event (equal (fn-mcr-credit-of (fn-mca-conn-key 3) (fn-mcr-ops *orcp-t-r*)) 0)))
; Mutation (K3): the reservation before this lane, a resize of :reclaim out of
; the budget's free room, takes the articles' room by the whole demand.
(must-fail-checked
 (assert-event (equal (fn-mcr-total (cadr (fn-mcr-resize *orcp-t-l* :reclaim 88416)))
                      (fn-mcr-total *orcp-t-l*))))

; fn-orcp-reserve-refused-by-name: a demand past the reserve is refused by
; name and the ledger is kept; the boundary is the reserve exactly
; (76,416 + 12 x 10,298 = 199,992 admitted, 12 more refused).
(assert-event (equal (fn-orcp-reserve *orcp-t-l* 3 20000 t) '(:refused :completion-reserve-exhausted)))
(assert-event (equal (fn-orcp-reserved-credits *orcp-t-l* 3 20000 t) *orcp-t-l*))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-l* 3 10298 t)) :ok))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-l* 3 10299 t)) :refused))
; A second pass while one holds the reserve is refused by name.
(assert-event (equal (fn-orcp-reserve *orcp-t-r* 3 1000 t) '(:refused :operation-already-admitted)))

; fn-orcp-release-frees-the-pass and fn-orcp-release-of-reserve-is-pass-free:
; nothing held after, funded, the reserve and every operation as before.
(defconst *orcp-t-back* (fn-orcp-release *orcp-t-r*))
(assert-event (equal (fn-mcr-credit-of :reclaim (fn-mcr-ops *orcp-t-back*)) 0))
(assert-event (fn-mcr-fundedp *orcp-t-back*))
(assert-event (equal (fn-mcr-completion *orcp-t-back*) 200000))
(assert-event (equal (fn-mcr-ops *orcp-t-back*) *orcp-t-ops*))

; KEYSTONE fn-orcp-profile-admitted-reclaim-is-funded on a run's ledger
; (fn-mca-initial-is-pass-free).  The S152 store: the development preset at
; T = 16,384 and H = 64 MiB (tests/test_native_reclaim_walk.py's PROFILE),
; the production core, the 64 MiB nursery cap.
(defconst *orcp-t-core* '(200411640 . 114644864))
(defconst *orcp-t-s152* (fn-bs-profile-resolve
                         (list :development (list (cons *fn-bs-pf-max-transactions* 16384)
                                                  (cons *fn-bs-pf-max-history-octets* 67108864)))
                         nil))
(assert-event (fn-bs-profile-admittedp *orcp-t-s152*))
(defconst *orcp-t-run* (fn-mca-initial *orcp-t-s152* *orcp-t-core* 67108864 t))
(assert-event (fn-mca-pass-free-p *orcp-t-run* *orcp-t-s152* t))
; The S152 run: 2,100 articles charging 7,077,639 octets, demand 127,215,252.
(assert-event (equal (fn-heap-reclaim-demand-octets 2100 7077639) 127215252))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-run* 2100 7077639 t)) :ok))
; And the store at the profile's bounds.
(assert-event (equal (car (fn-orcp-reserve *orcp-t-run* 16384 67108864 t)) :ok))
; RED BEFORE (the witness the keystone must kill): the reservation before
; this lane, 64 x h resized out of the articles' pool, refuses the S152 run
; (estimate 452,968,896) on this ledger, and on the development preset's own
; run refuses 64 x 53,777 octets.
(assert-event (equal (fn-mcr-resize *orcp-t-run* :reclaim (* 64 7077639))
                     '(:refused :memory-budget-exhausted)))
(assert-event (equal (fn-mcr-resize (fn-mca-initial *fn-bs-profile-development* *orcp-t-core* 67108864 t)
                                    :reclaim (* 64 53777))
                     '(:refused :memory-budget-exhausted)))
; K2: the articles' steps leave the reserve to the pass -- a connection
; mid-article, then its submission taken and sealed.
(defconst *orcp-t-busy*
  (fn-mca-seal (fn-mca-take (cadr (fn-mcr-resize *orcp-t-run* (fn-mca-conn-key 7)
                                                 (fn-heap-article-reserve-octets *orcp-t-s152*)))
                            7 (fn-heap-article-reserve-octets *orcp-t-s152*))))
(assert-event (fn-mca-pass-free-p *orcp-t-busy* *orcp-t-s152* t))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-busy* 16384 67108864 t)) :ok))
; Hypothesis removal (pass-free): a ledger whose :reclaim already holds an
; entry refuses.
(must-fail-checked
 (assert-event (equal (car (fn-orcp-reserve (fn-orcp-reserved-credits *orcp-t-run* 1 0 t)
                                            2100 7077639 t))
                      :ok)))
; Hypothesis removal (C <= H, N <= T): on the small preset the owner's work
; reserve is the demand at the bounds exactly (its open's transient is
; smaller), so one charged octet or one record past the bounds is refused.
(defconst *orcp-t-small-run* (fn-mca-initial *fn-heap-small-profile* *orcp-t-core* 67108864 t))
(assert-event (equal (fn-mca-owner-octets *fn-heap-small-profile* t)
                     (fn-heap-reclaim-demand-octets 16384 8388608)))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-small-run* 16384 8388608 t)) :ok))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-small-run* 16384 8388609 t)) :refused))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-small-run* 16385 8388608 t)) :refused))

;; 1b. Without the opt-in (D53: live reclaim is refused by name, offline
;; reclaim stays).  fn-orcp-reserve-refused-without-the-opt-in: the same
;; ledger and store the opt-in admitted above is refused :offline-only and
;; nothing is borrowed; fn-orcp-request-word-*: an installing pass
;; (`store reclaim', `--recorded') is refused before anything is recorded,
;; the dry run and the opted-in answer are the pass's own.
(assert-event (equal (fn-orcp-reserve *orcp-t-l* 3 1000 nil) '(:refused :offline-only)))
(assert-event (equal (fn-orcp-reserved-credits *orcp-t-l* 3 1000 nil) *orcp-t-l*))
(assert-event (equal (fn-orcp-request-word :recorded nil :ok) :offline-only))
(assert-event (equal (fn-orcp-request-word :reclaim nil :ok) :offline-only))
(assert-event (equal (fn-orcp-request-word :dry-run nil :ok) :ok))
(assert-event (equal (fn-orcp-request-word :recorded t :ok) :ok))
(assert-event (equal (fn-orcp-request-word :reclaim t :busy) :busy))
; Mutation: a request word that ignored the opt-in admits the installing pass.
(must-fail-checked
 (assert-event (equal (fn-orcp-request-word :recorded nil :ok) :ok)))
; Without the opt-in the run's ledger holds only the open's transient: the
; small preset's off ledger is pass-free for itself but not for a live pass
; (its completion reserve is the open's 130,023,424, not the demand
; 358,006,784), so the reserve really is absent and not merely unused.
(defconst *orcp-t-small-off* (fn-mca-initial *fn-heap-small-profile* *orcp-t-core* 67108864 nil))
(assert-event (fn-mca-pass-free-p *orcp-t-small-off* *fn-heap-small-profile* nil))
(assert-event (not (fn-mca-pass-free-p *orcp-t-small-off* *fn-heap-small-profile* t)))
(assert-event (equal (fn-mcr-completion *orcp-t-small-off*)
                     (fn-mca-owner-octets *fn-heap-small-profile* nil)))
(assert-event (equal (fn-mcr-completion *orcp-t-small-off*) 130023424))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-small-off* 16384 8388608 t)) :refused))

; -----------------------------------------------------------------------------
; 2. The swap word.  KEYSTONE fn-orcp-swap-only-over-the-capture: the
; positive witness asserts every conclusion; each hypothesis-removal
; witness fails one condition alone and is not a swap.
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 9 *rpt-s* t 0) :swap))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 8 9 *rpt-s* t 0) :delta))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 10 *rpt-s* t 0) :delta))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 9 (fn-sn-with-topic *rpt-s* nil) t 0)
                     :delta))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 9 *rpt-s* nil 0) :busy))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 9 *rpt-s* t 1) :readers))
(must-fail-checked
 (assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 8 9 *rpt-s* t 0) :swap)))

; fn-orcp-swapped-history-is-the-offline-rewrite on the fixture: at a swap
; the rewrite of the captured rows is the offline rewrite of the rows now.
(bpr-lift fn-orc-rows-octets 1)
(bpr-lift fn-orc-rewrite-rows 2)
(defconst *orcp-t-rows* (fn-sf-records (fn-sn-files *rpt-s*)))
(defmacro orcp-t-new () '(in-arena-fn-orc-rewrite-rows *rpt-payloads* *orcp-t-rows* *xt-ctx*))
(assert-event (equal (in-arena-fn-orc-rows-octets *rpt-payloads* (orcp-t-new))
                     (fn-rclp-events (in-arena-fn-orc-rows-octets *rpt-payloads* *orcp-t-rows*)
                                     *xt-ctx*)))
(assert-event (not (equal (in-arena-fn-orc-rows-octets *rpt-payloads* (orcp-t-new))
                          (in-arena-fn-orc-rows-octets *rpt-payloads* *orcp-t-rows*))))

; -----------------------------------------------------------------------------
; 3. The cuts, and the rerun.
(assert-event (equal (fn-orcp-cut-outcome :captured) :old))
(assert-event (equal (fn-orcp-cut-outcome :rebuilt) :old))
(assert-event (equal (fn-orcp-cut-outcome :installed) :new))
(assert-event (equal (fn-orcp-cut-outcome :released) :new))
(assert-event (equal (fn-orcp-cut-outcome :elsewhere) :unknown))
(must-fail-checked (assert-event (equal (fn-orcp-cut-outcome :staged) :new)))

; KEYSTONE fn-orcp-rerun-rewrites-nothing: three articles expire; a rerun
; over the rewritten rows has the same octets.
(assert-event (equal (len (fn-rclp-rewritten-msgids (rpt-events) *xt-ctx*)) 3))
(assert-event (equal (in-arena-fn-orc-rows-octets
                      *rpt-payloads*
                      (in-arena-fn-orc-rewrite-rows *rpt-payloads* (orcp-t-new) *xt-ctx*))
                     (in-arena-fn-orc-rows-octets *rpt-payloads* (orcp-t-new))))

; -----------------------------------------------------------------------------
; 4. The rebuild (owner-checkpoint-open-tests' image: two retention events,
; two configuration records).  KEYSTONE fn-orcp-rebuild-is-the-full-open on
; a reachable owner, not :fault.
(defconst *orcp-t-events*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-orcp" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-orcp" "subject" "evidence" 0)))
(defconst *orcp-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(defconst *orcp-t-rebuilt* (fn-orcp-rebuild *orcp-t-events* *orcp-t-configs* 8 4))
(assert-event (not (equal (cadr *orcp-t-rebuilt*) :fault)))
(assert-event (equal (cadr *orcp-t-rebuilt*)
                     (fn-ock-recover-full *orcp-t-configs* 8 *orcp-t-events* 4)))
(assert-event (equal (car *orcp-t-rebuilt*)
                     (fn-sco-capture *orcp-t-configs* *orcp-t-events*)))
; Mutation: the rebuild of a shorter history is not the full open's.
(must-fail-checked
 (assert-event (equal (cadr (fn-orcp-rebuild (cdr *orcp-t-events*) *orcp-t-configs* 8 4))
                      (fn-ock-recover-full *orcp-t-configs* 8 *orcp-t-events* 4))))

; KEYSTONE fn-orcp-swapped-store-is-the-full-open: the live owner is the
; open of the first event only; swapped with the rebuild, it serves the full
; open's Store and keeps the live owner's next id and (empty) connections.
(defconst *orcp-t-live*
  (fn-ocfg-owner (fn-ock-recover-full *orcp-t-configs* 8 (list (car *orcp-t-events*)) 4)))
(defconst *orcp-t-swapped*
  (fn-orcp-swapped-owner *orcp-t-live* (fn-ocfg-owner (cadr *orcp-t-rebuilt*))))
(assert-event (equal (fn-own-store *orcp-t-swapped*)
                     (fn-own-store (fn-ocfg-owner (fn-ock-recover-full *orcp-t-configs* 8
                                                                       *orcp-t-events* 4)))))
(assert-event (not (equal (fn-own-store *orcp-t-swapped*) (fn-own-store *orcp-t-live*))))
(assert-event (equal (fn-own-next-id *orcp-t-swapped*) (fn-own-next-id *orcp-t-live*)))
(assert-event (equal (fn-own-conns *orcp-t-swapped*) nil))
