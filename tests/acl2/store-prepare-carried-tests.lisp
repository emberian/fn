; fn: witnesses and teeth for books/store-prepare-carried.lisp's keystone,
; fn-store-prepare-interned-carried-is-prepare-interned (the standalone store's
; POST prepare, host/store-node-host.lisp fn-store-sn-prepare).
;
; The stores are store-prepare-correspondence-tests': *spc-second-reserved* is
; reached from fn-sn-initial by the host's transitions (one article committed,
; a second reservation), *spc-stale* is that store with its node replaced by
; an empty one (a CORRUPTED state, labelled).  The arena is a local one
; holding the committed article's payload at handle 0, so the entry interns
; the offered wire record at handle 1.
(in-package "ACL2")
(include-book "../../books/store-prepare-carried")
(include-book "must-fail-checked")
(include-book "store-prepare-correspondence-tests")

;; One entry on a fresh local arena holding the committed payload at handle 0:
;; (store count-after bytes-at-1).  CARRIEDP picks the host's entry
;; (fn-store-prepare-interned-carried) or books/store-intern's.
(defun spca-run-in (carriedp s w fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events (list *spc-first-wire*) nil 0 fn-arena)
    (declare (ignore rows))
    (mv-let (next fn-arena)
      (if carriedp
          (fn-store-prepare-interned-carried s w fn-arena)
        (fn-store-prepare-interned s w fn-arena))
      (mv (list next (fn-arena-count fn-arena)
                (if (< 1 (fn-arena-count fn-arena))
                    (fn-arena-payload 1 fn-arena)
                  :none))
          fn-arena))))

(defun spca-run (carriedp s w)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (spca-run-in carriedp s w fn-arena)
      out)))

; Reachable POSITIVE witness.  Antecedent: the store is related.  Conclusion:
; both results agree (the store, the arena's count, the sealed bytes).  Not
; vacuous: the entry stages the offered record (the store changes, the arena
; grows by the offered payload at handle 1).
(assert-event (fn-snt-relation *spc-second-reserved*))
(defconst *spca-carried* (spca-run t *spc-second-reserved* *spc-second-wire*))
(defconst *spca-entry* (spca-run nil *spc-second-reserved* *spc-second-wire*))
(assert-event (equal *spca-carried* *spca-entry*))
(assert-event (equal (fn-sf-phase (fn-sn-files (nth 0 *spca-carried*))) :record-staged))
(assert-event (equal (nth 1 *spca-carried*) 2))
(assert-event (equal (nth 2 *spca-carried*) (fn-record-payload *spc-second-wire*)))
(assert-event (equal (fn-record-payload
                      (fn-sf-record-candidate (fn-sn-files (nth 0 *spca-carried*))))
                     1))

; A related REFUSAL: the duplicate Message-ID at the right counters.  Both
; entries refuse, and neither seals.
(defconst *spca-dup-carried* (spca-run t *spc-second-reserved* *spc-duplicate-wire*))
(assert-event (equal *spca-dup-carried*
                     (spca-run nil *spc-second-reserved* *spc-duplicate-wire*)))
(assert-event (equal (nth 0 *spca-dup-carried*) *spc-second-reserved*))
(assert-event (equal (nth 1 *spca-dup-carried*) 1))

; HYPOTHESIS REMOVAL (CORRUPTED state).  The retained structure holds
; (fn-sn-statep), the omitted hypothesis fails (not fn-snt-relation), and the
; conclusion fails: the stale node accepts the duplicate, so the carried
; entry stages and seals it while the entry's replay of the durable history
; refuses it.
(assert-event (fn-sn-statep *spc-stale*))
(assert-event (not (fn-snt-relation *spc-stale*)))
(defconst *spca-stale-carried* (spca-run t *spc-stale* *spc-duplicate-wire*))
(defconst *spca-stale-entry* (spca-run nil *spc-stale* *spc-duplicate-wire*))
(assert-event (equal (fn-sf-phase (fn-sn-files (nth 0 *spca-stale-carried*))) :record-staged))
(assert-event (equal (nth 0 *spca-stale-entry*) *spc-stale*))
(must-fail-checked
 (assert-event (equal *spca-stale-carried* *spca-stale-entry*)))

; fn-store-prepare-interned-carried-is-next-then-seal (no hypothesis): the
; host's two steps -- the decision over the arena's count, then the seal of
; the record's payload iff the store changed -- give the entry's results, on
; an accepting store (the seal happens) and a refusing one (no seal).
(defun spca-split-in (s w fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events (list *spc-first-wire*) nil 0 fn-arena)
    (declare (ignore rows))
    (let ((next (fn-store-prepare-carried-next s w (fn-arena-count fn-arena))))
      (let ((fn-arena (if (equal next s) fn-arena
                        (fn-arena-seal-list (fn-record-payload w) fn-arena))))
        (mv (list next (fn-arena-count fn-arena)
                  (if (< 1 (fn-arena-count fn-arena))
                      (fn-arena-payload 1 fn-arena)
                    :none))
            fn-arena)))))

(defun spca-split (s w)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (spca-split-in s w fn-arena)
      out)))

(assert-event (equal (spca-split *spc-second-reserved* *spc-second-wire*) *spca-carried*))
(assert-event (equal (nth 1 (spca-split *spc-second-reserved* *spc-second-wire*)) 2))
(assert-event (equal (spca-split *spc-second-reserved* *spc-duplicate-wire*) *spca-dup-carried*))
(assert-event (equal (nth 1 (spca-split *spc-second-reserved* *spc-duplicate-wire*)) 1))
