; Teeth for books/peer-carriage.lisp and books/peer-carriage-rows.lisp
; (PRF-099): a reachable witness for each keystone and one must-fail per
; hypothesis showing the conclusion fails without it.
(in-package "ACL2")
(include-book "../../books/peer-carriage")
(include-book "peer-authored-accept-tests")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The budget rows

(defconst *pcb-old-rows*
  (list (list "relay" "path-identity" "relay.example" 0)
        (list "relay" "carries-principal" *pat-hex-principal* 0)
        (list "relay" "carried-budget-charge" "" 1)
        (list "relay" "carried-budget-count" "" 1)))
(assert-event (equal (fn-pcb-peer-budget "relay" *pcb-old-rows*) '(1 1)))
(assert-event (null (fn-pcb-peer-budget "other" *pcb-old-rows*)))
; A boundary with one row of the two has no budget.
(assert-event (null (fn-pcb-budget-of-rows (butlast *pcb-old-rows* 1))))

; fn-pcb-budget-after-extension: the operator's rows replace the old budget,
; and the carried list and every other row stay.
(defconst *pcb-extended*
  (fn-pcb-extend-rows *pcb-old-rows* (fn-pcb-budget-rows "relay" 5 3)))
(assert-event (equal (fn-pcb-budget-of-rows *pcb-extended*) '(5 3)))
(assert-event (equal (fn-pa-carried-sources *pcb-extended*) *pat-carries*))
(assert-event (equal (len *pcb-extended*) 4))
; Tooth (natp): a budget that is not a natural reads as no budget.
(must-fail
 (assert-event
  (equal (fn-pcb-budget-of-rows
          (fn-pcb-extend-rows *pcb-old-rows* (fn-pcb-budget-rows "relay" -1 3)))
         '(-1 3))))

; A carried list grows across requests: a second `peer carries' adds its
; principal and keeps the first; repeating a principal adds nothing.
(defconst *pcb-other-hex*
  "0808080808080808080808080808080808080808080808080808080808080808")
(defconst *pcb-grown*
  (fn-pcb-extend-rows *pcb-extended*
                      (list (list "relay" "carries-principal" *pcb-other-hex* 0)
                            (list "relay" "carries-principal"
                                  *pat-hex-principal* 0))))
(assert-event (equal (len (fn-pa-carried-sources *pcb-grown*)) 2))
(assert-event (equal (fn-pcb-budget-of-rows *pcb-grown*) '(5 3)))

; fn-pcb-peer-budget-after-extend-delta over a configuration value.
(defconst *pcb-value*
  (fn-cfg-value-make nil 0 nil nil nil *pcb-old-rows* nil nil nil nil))
(assert-event
 (equal (fn-pcb-peer-budget
         "relay"
         (fn-cfg-peers
          (fn-cfg-apply-delta *pcb-value* 1 nil
                              (fn-pcb-extend-delta
                               "relay" (fn-pcb-budget-rows "relay" 5 3)
                               (fn-cfg-peers *pcb-value*)))))
        '(5 3)))
; Tooth (the peer exists): an extension never creates a boundary.
(assert-event (null (fn-pcb-extend-delta "nobody" (fn-pcb-budget-rows "nobody" 5 3)
                                         (fn-cfg-peers *pcb-value*))))
(must-fail
 (assert-event
  (equal (fn-pcb-peer-budget
          "nobody"
          (fn-cfg-peers
           (fn-cfg-apply-delta *pcb-value* 1 nil
                               (fn-pcb-extend-delta
                                "nobody" (fn-pcb-budget-rows "nobody" 5 3)
                                (fn-cfg-peers *pcb-value*)))))
         '(5 3))))

; -----------------------------------------------------------------------------
; The admission decision: each outcome by its own name.

(assert-event (equal (fn-pcb-admission '(10 2) '(0 . 0) 4) :within))
(assert-event (equal (fn-pcb-admission '(10 2) '(4 . 2) 1)
                     '(:refused :carried-count-exhausted)))
(assert-event (equal (fn-pcb-admission '(10 2) '(8 . 1) 4)
                     '(:refused :carried-octets-exhausted)))
(assert-event (equal (fn-pcb-admission nil '(0 . 0) 1)
                     '(:refused :carried-budget-unset)))
(must-fail (assert-event (equal (fn-pcb-admission nil '(0 . 0) 1) :within)))

; -----------------------------------------------------------------------------
; The projection and the carried cache

(defconst *pcb-evidence* "gateway-peer-evidence")
(defconst *pcb-charge* (fn-charge-for-payload (len *pat-relayed*)))
(assert-event (equal (fn-pcb-event-carriage *pat-carried-event*)
                     (cons *pcb-evidence* *pcb-charge*)))
; An enrolled (:verified) composite is not carried and counts nothing.
(assert-event (null (fn-pcb-event-carriage *pat-event*)))
(assert-event (null (fn-pcb-event-carriage *pat-forged-verified*)))
(defconst *pcb-records* (list *pat-event* *pat-carried-event*))
(assert-event (equal (fn-pcb-usage *pcb-records* *pcb-evidence*)
                     (cons *pcb-charge* 1)))
(assert-event (equal (fn-pcb-usage *pcb-records* "peer-transit:other")
                     (cons 0 0)))

; fn-pcb-carried-usage-is-the-projection: a valid cache over the first
; record, extended over both.
(defconst *pcb-cache* (cons 1 (fn-pcb-tally-records (list *pat-event*) nil)))
(assert-event (fn-pcb-cache-validp *pcb-cache* *pcb-records*))
(assert-event (equal (fn-pcb-tally-get *pcb-evidence*
                                       (fn-pcb-usage-extend *pcb-cache*
                                                            *pcb-records*))
                     (fn-pcb-usage *pcb-records* *pcb-evidence*)))
; Tooth (cache validity): a cache that skips the carried record it claims to
; cover reads a usage the Store does not hold.
(defconst *pcb-stale-cache* (cons 2 nil))
(assert-event (not (fn-pcb-cache-validp *pcb-stale-cache* *pcb-records*)))
(must-fail
 (assert-event (equal (fn-pcb-tally-get *pcb-evidence*
                                        (fn-pcb-usage-extend *pcb-stale-cache*
                                                             *pcb-records*))
                      (fn-pcb-usage *pcb-records* *pcb-evidence*))))
; fn-pcb-extended-cache-is-valid and fn-pcb-cache-valid-after-commit.
(assert-event (fn-pcb-cache-validp
               (cons 2 (fn-pcb-usage-extend *pcb-cache* *pcb-records*))
               *pcb-records*))
(assert-event (fn-pcb-cache-validp *pcb-cache*
                                   (append *pcb-records* (list *pat-event*))))

; -----------------------------------------------------------------------------
; The gated event and the trace

(defmacro pcb-gated (budget usage)
  `(fn-pcb-carried-event
    2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
    '("fn.test") *pat-obligation* *pat-subject* *pcb-evidence* *pcb-charge*
    nil *pat-carries* (fn-clock-observation 1 841000000000 0 t)
    ,budget ,usage))

(assert-event (equal (pcb-gated (list *pcb-charge* 1) '(0 . 0))
                     *pat-carried-event*))
(assert-event (equal (pcb-gated (list *pcb-charge* 1) (cons 0 1))
                     '(:refused :carried-count-exhausted)))
(assert-event (equal (pcb-gated (list (1- *pcb-charge*) 1) '(0 . 0))
                     '(:refused :carried-octets-exhausted)))
(assert-event (equal (pcb-gated nil '(0 . 0))
                     '(:refused :carried-budget-unset)))

; fn-pcb-carried-history-within-budget, witness: one carried record under a
; budget of exactly its charge and one article.
(defconst *pcb-budget* (list *pcb-charge* 1))
(assert-event (fn-pcb-admitted-from *pcb-records* (cons 0 0) *pcb-budget*
                                    *pcb-evidence*))
(assert-event (<= (cdr (fn-pcb-usage *pcb-records* *pcb-evidence*))
                  (cadr *pcb-budget*)))
; Tooth (admitted): a history with the carried record twice was not admitted
; under a one-article budget, and it is over that budget.
(defconst *pcb-twice* (list *pat-carried-event* *pat-carried-event*))
(assert-event (not (fn-pcb-admitted-from *pcb-twice* (cons 0 0) *pcb-budget*
                                         *pcb-evidence*)))
(must-fail
 (assert-event (<= (cdr (fn-pcb-usage *pcb-twice* *pcb-evidence*))
                   (cadr *pcb-budget*))))
; Tooth (budgetp): with a budget that is no budget, an admitted history
; (no carried record) is not bounded by it.
(assert-event (fn-pcb-admitted-from (list *pat-event*) (cons 0 0) '(-1 -1)
                                    *pcb-evidence*))
(must-fail
 (assert-event (<= (car (fn-pcb-usage (list *pat-event*) *pcb-evidence*))
                   (car '(-1 -1)))))
; fn-pcb-no-budget-history-carries-nothing: the carried record is not
; admitted without a budget.
(assert-event (not (fn-pcb-admitted-from (list *pat-carried-event*) (cons 0 0)
                                         nil *pcb-evidence*)))

; fn-pcb-carried-event-keeps-history-admitted: committing what the gate
; returned keeps the history admitted; the second is refused and adds
; nothing the projection counts.
(make-event
 `(defconst *pcb-h1*
    ',(list (pcb-gated *pcb-budget* (fn-pcb-usage nil *pcb-evidence*)))))
(assert-event (fn-pcb-admitted-from *pcb-h1* (cons 0 0) *pcb-budget*
                                    *pcb-evidence*))
(make-event
 `(defconst *pcb-h2*
    ',(append *pcb-h1*
              (list (pcb-gated *pcb-budget*
                               (fn-pcb-usage *pcb-h1* *pcb-evidence*))))))
(assert-event (equal (cadr *pcb-h2*) '(:refused :carried-count-exhausted)))
(assert-event (fn-pcb-admitted-from *pcb-h2* (cons 0 0) *pcb-budget*
                                    *pcb-evidence*))
; Tooth (the usage handed in is the projection): a gate handed a stale zero
; usage builds a second event, and the history is no longer admitted.
(make-event
 `(defconst *pcb-h2-stale*
    ',(append *pcb-h1* (list (pcb-gated *pcb-budget* '(0 . 0))))))
(must-fail
 (assert-event (fn-pcb-admitted-from *pcb-h2-stale* (cons 0 0) *pcb-budget*
                                     *pcb-evidence*)))

; -----------------------------------------------------------------------------
; The refusal classes

; unsupported-profile: the carrier's nine items decode but name suite 2.
; The field is folded at 64 octets, as a received carrier is.
(defun pcb-fold (octets)
  (declare (xargs :mode :program))
  (if (<= (len octets) 64)
      (append octets '(13 10))
    (append (take 64 octets) '(13 10 32) (pcb-fold (nthcdr 64 octets)))))

(make-event
 (let* ((parsed (fn-article-parse *pat-relayed*))
        (article (fn-article-result-article parsed))
        (field (fn-hc-find-name *fn-hc-name* (fn-article-fields article)))
        (value (fn-article-field-unfolded-value field))
        (bin (fn-stx-val (fn-stx-b64-decode-exact (fn-stx-strip-wsp value))))
        (patched (cons (car bin) (cons 2 (cddr bin))))
        (b64 (fn-stx-b64-encode patched)))
   `(defconst *pcb-unsupported*
      ',(append (fn-record-string-octets "FN-Authorship: ")
                (pcb-fold b64)
                *tha-root-source*))))
(assert-event (equal (fn-pa-carrier-kind *pcb-unsupported*) :present))
(assert-event (equal (fn-pa-current-plan *pcb-unsupported* *pat-snapshots* nil nil)
                     '(:refused :carrier)))
(assert-event (fn-pcb-unsupported-profilep *pcb-unsupported*))
(assert-event (not (fn-pcb-unsupported-profilep *pat-malformed*)))

; One witness per class.
(assert-event (equal (fn-pcb-refusal-class *pcb-unsupported* *pat-snapshots*
                                           nil nil nil)
                     :unsupported-profile))
(assert-event (equal (fn-pcb-refusal-class *pat-malformed* *pat-snapshots*
                                           nil nil nil)
                     :malformed))
(assert-event (equal (fn-pcb-refusal-class *pat-relayed* nil nil nil nil)
                     :no-local-binding))
(assert-event (equal (fn-pcb-refusal-class *pat-relayed* *pat-snapshots* nil
                                           :refused :verified)
                     :signature-failed))
(assert-event (equal (fn-pcb-refusal-class *pat-relayed* *pat-snapshots* nil
                                           :verified :refused)
                     :signature-failed))
; A revoked principal has no local binding either.
(assert-event (equal (fn-pcb-refusal-class *pat-relayed*
                                           (cons *pat-revoked* *pat-snapshots*)
                                           *pat-carries* nil nil)
                     :no-local-binding))

; fn-pcb-present-carrier-not-accepted-has-a-class: one tooth per hypothesis.
; Carrier absent: the unsigned arm has no class.
(must-fail
 (assert-event (member-equal (fn-pcb-refusal-class *tha-root-source*
                                                   *pat-snapshots* nil nil nil)
                             *fn-pcb-refusal-classes*)))
; Carried for the boundary: held, no refusal class.
(must-fail
 (assert-event (member-equal (fn-pcb-refusal-class *pat-relayed* nil
                                                   *pat-carries* nil nil)
                             *fn-pcb-refusal-classes*)))
; Accepted under both observations: no class.
(must-fail
 (assert-event (member-equal (fn-pcb-refusal-class *pat-relayed* *pat-snapshots*
                                                   nil :verified :verified)
                             *fn-pcb-refusal-classes*)))
; fn-pcb-bound-carrier-with-a-failed-primitive-is-signature-failed, tooth
; (the :ok arm): the same failed observation on an unbound carrier is
; no-local-binding, not signature-failed.
(must-fail
 (assert-event (equal (fn-pcb-refusal-class *pat-relayed* nil nil
                                            :refused :refused)
                      :signature-failed)))

; =============================================================================
; Packet 4 (PRF-124): fn-pcb-admission-verdict names every input's class.
; One reachable witness per verdict.
(assert-event (equal (fn-pcb-admission-verdict *tha-root-source* *pat-snapshots*
                                               nil nil nil)
                     :unsigned))
(assert-event (equal (fn-pcb-admission-verdict *pat-relayed* nil *pat-carries*
                                               nil nil)
                     :carried))
(assert-event (equal (fn-pcb-admission-verdict *pat-malformed* *pat-snapshots*
                                               nil nil nil)
                     :malformed))
(assert-event (equal (fn-pcb-admission-verdict *pat-relayed* *pat-snapshots* nil
                                               :refused :verified)
                     :cryptographically-invalid))
(assert-event (equal (fn-pcb-admission-verdict *pat-relayed* nil nil nil nil)
                     :unenrolled))
(assert-event (equal (fn-pcb-admission-verdict *pcb-unsupported* *pat-snapshots*
                                               nil nil nil)
                     :unsupported-profile))
(assert-event (equal (fn-pcb-admission-verdict *pat-relayed* *pat-snapshots* nil
                                               :verified :verified)
                     :verified))
; The inner hypothesis (a present carrier): without it the verdict is
; :unsigned, which the conclusion excludes for present carriers.
(assert-event (equal (fn-pa-carrier-kind *tha-root-source*) :absent))
(must-fail
 (assert-event (not (equal (fn-pcb-admission-verdict *tha-root-source*
                                                     *pat-snapshots* nil nil nil)
                           :unsigned))))
; :verified needs BOTH observations: one refused is not :verified.
(must-fail
 (assert-event (equal (fn-pcb-admission-verdict *pat-relayed* *pat-snapshots* nil
                                                :verified :refused)
                      :verified)))
; A carried input is never :verified, even under verified observations.
(must-fail
 (assert-event (equal (fn-pcb-admission-verdict *pat-relayed* nil *pat-carries*
                                                :verified :verified)
                      :verified)))
