; fn: witnesses and teeth for books/reclaim-note.lisp (PKT-855): the reclaim's
; note, published in the instant's record, over the reclaiming fixture of
; tests/acl2/store-reclaim-pack-tests and the lifts of
; tests/acl2/reclaim-instant-tests.
(in-package "ACL2")
(include-book "../../books/reclaim-note")
(include-book "must-fail-checked")
(include-book "store-log-reclaim-tests")
(bpr-lift fn-rci-decide-stream 5)

(defmacro rcnt-cfg (rule)
  `(fn-cfg-make 1 (fn-cfg-apply (fn-cfg-value (fn-cfg-initial)) 1 0 (fn-rcl-rule-deltas ,rule))))
(defmacro rcnt-acc (ctx) `(fn-rcls-fold (rpt-events) ,ctx (fn-rcls-init)))
; The decision `store reclaim' takes at the clock 0 (the fixture's instant),
; over the fixture's history of (len (rpt-events)) records.
(defmacro rcnt-d ()
  `(in-arena-fn-lgr-decide-stream *rpt-payloads* *rpt-profile* *rpt-rule* 0
                                  *rpt-s* (rcnt-acc *rpt-ctx*) nil))
(defmacro rcnt-count () `(len (rpt-events)))
(defmacro rcnt-v (text)
  `(fn-cfg-value (fn-rcn-recorded-config (rcnt-cfg *rpt-rule*) 1 0 2 0 0 ,text)))
(defmacro rcnt-recheck (v count)
  `(fn-rcn-check ,v ,count
                 (in-arena-fn-rci-decide-stream *rpt-payloads* *rpt-profile* ,v
                                                *rpt-s* (rcnt-acc *rpt-ctx*) nil)))

; The decision reclaims (not degenerate): one Message-ID, octets freed.
(assert-event (equal (car (rcnt-d)) :reclaim))
(assert-event (consp (nth 1 (rcnt-d))))
(assert-event (posp (rcnt-count)))
; The note of the decision is publishable and names the instant and counts.
(defmacro rcnt-text () `(fn-rcn-of-decision 0 (rcnt-count) (rcnt-d)))
(assert-event (fn-rcn-representablep (rcnt-text)))
(assert-event (fn-rcn-prefixp "at=1 history=" (rcnt-text)))
(assert-event (fn-cfg-delta-listp (fn-rcn-deltas 0 (rcnt-text))))

; fn-rcn-recorded-note-reads-back, reachable: the whole conclusion.
(assert-event (fn-rci-instantp 0))
(assert-event (and (fn-rci-recordedp (rcnt-v (rcnt-text)))
                   (equal (fn-rci-config-now (rcnt-v (rcnt-text))) 0)
                   (equal (fn-rcl-config-rule (rcnt-v (rcnt-text))) *rpt-rule*)
                   (equal (fn-rcn-config-note (rcnt-v (rcnt-text))) (rcnt-text))))

; fn-rcn-recorded-note-checks, reachable and not degenerate: the rerun over
; the record checks the note (:checked, since the decision reclaims).
(assert-event (equal (rcnt-recheck (rcnt-v (rcnt-text)) (rcnt-count)) :checked))

; Teeth.  A note over another history length, or of another decision, at the
; recorded instant is refused by name; the conclusion fails for it.
(defmacro rcnt-foreign () `(fn-rcn-of-decision 0 (+ 1 (rcnt-count)) (rcnt-d)))
(assert-event (not (equal (rcnt-foreign) (rcnt-text))))
(assert-event (equal (rcnt-recheck (rcnt-v (rcnt-foreign)) (rcnt-count)) :reclaim-note-mismatch))
(must-fail-checked
 (assert-event (equal (rcnt-recheck (rcnt-v (rcnt-foreign)) (rcnt-count)) :checked)))
(defmacro rcnt-other () `(fn-rcn-of-decision 0 (rcnt-count) (list :reclaim '("<other@x>") 1 nil)))
(assert-event (equal (rcnt-recheck (rcnt-v (rcnt-other)) (rcnt-count)) :reclaim-note-mismatch))
; A note of an earlier instant (the live pass records its instant alone) is
; not checked.
(defmacro rcnt-earlier () `(fn-rcn-of-decision 7 (rcnt-count) (rcnt-d)))
(assert-event (equal (rcnt-recheck (rcnt-v (rcnt-earlier)) (rcnt-count)) :unchecked))
; Hypothesis removal (fn-rci-instantp): recorded at a non-instant, the
; configuration's instant is not the one the note names, and nothing checks.
(assert-event (not (fn-rci-instantp :late)))
(assert-event (not (equal (fn-rci-config-now
                           (fn-cfg-value (fn-rcn-recorded-config (rcnt-cfg *rpt-rule*) 1 0 2 0 :late (rcnt-text))))
                          :late)))
; The configuration admits the note delta only non-empty.
(assert-event (equal (fn-cfg-reclaim-note-reason (fn-cfg-reclaim-note "")) :reclaim-note))
(assert-event (null (fn-cfg-reclaim-note-reason (fn-cfg-reclaim-note (rcnt-text)))))

; fn-rcn-live-note-checks (PRF-1049): the owner's two records (the instant at
; generation 2, then the note at generation 3 with other coordinates).
; Reachable and not degenerate: the whole conclusion, :checked.
(defmacro rcnt-live (text)
  `(fn-cfg-value (fn-rcn-live-config (rcnt-cfg *rpt-rule*) 1 0 2 0 0 2 5 3 9 ,text)))
(assert-event (fn-cfg-delta-listp (fn-rcn-note-deltas (rcnt-text))))
(assert-event (and (equal (fn-rcn-config-note (rcnt-live (rcnt-text))) (rcnt-text))
                   (equal (fn-rci-config-now (rcnt-live (rcnt-text))) 0)
                   (equal (rcnt-recheck (rcnt-live (rcnt-text)) (rcnt-count)) :checked)))
; The live and the offline forms leave the same limits.
(assert-event (equal (fn-cfg-limits (rcnt-live (rcnt-text)))
                     (fn-cfg-limits (rcnt-v (rcnt-text)))))
; Teeth: the live form with a foreign note is refused by name; with no note
; record (the instant alone, before this packet) the rerun is :unchecked.
(assert-event (equal (rcnt-recheck (rcnt-live (rcnt-foreign)) (rcnt-count)) :reclaim-note-mismatch))
(assert-event (equal (rcnt-recheck (fn-cfg-value (fn-rci-recorded-config (rcnt-cfg *rpt-rule*) 1 0 2 0 0))
                                   (rcnt-count))
                     :unchecked))
; Hypothesis removal (fn-rci-instantp): the instant recorded at :late is not
; the note's; the rerun does not check.
(assert-event (not (equal (rcnt-recheck (fn-cfg-value (fn-rcn-live-config (rcnt-cfg *rpt-rule*)
                                                                          1 0 2 0 :late 2 5 3 9
                                                                          (rcnt-text)))
                                        (rcnt-count))
                          :checked)))
