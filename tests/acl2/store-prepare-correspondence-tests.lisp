; Teeth for the live-store prepare correspondence.

(in-package "ACL2")
(include-book "../../books/store-prepare-correspondence")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; A reachable, non-degenerate witness with one durable record already in the
; history.  The second prepare therefore separates the projection from an
; empty-history special case.
(defconst *spc-groups* '("fn.letters" "fn.test"))
(defconst *spc-first*
  (fn-record-make 0 0 0 "<spc-first@example.invalid>" '(65 66)
                  *spc-groups* "spc-pin-1" "spc-subject-1"
                  "spc-release-1" 2 841000000))
(defconst *spc-second*
  (fn-record-make 1 1 1 "<spc-second@example.invalid>" '(67 68)
                  '("fn.test") "spc-pin-2" "spc-subject-2"
                  "spc-release-2" 1 841000000))

(defun spc-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                 :frontier-file :ok)
                       :frontier-replace :ok)
            :frontier-directory :ok))

(defconst *spc-first-reserved* (spc-reserve (fn-sn-initial *spc-groups* 10)))
(defconst *spc-first-staged* (fn-spc-prepare *spc-first-reserved* *spc-first*))
(defconst *spc-first-completing*
  (fn-sn-io (fn-sn-io (fn-sn-io *spc-first-staged* :record-file :ok)
                       :record-link :ok)
            :record-directory :ok))
(defconst *spc-ready-one* (fn-sn-finish *spc-first-completing*))
(defconst *spc-second-reserved* (spc-reserve *spc-ready-one*))
(defconst *spc-second-fast* (fn-spc-prepare *spc-second-reserved* *spc-second*))
(defconst *spc-second-spec* (fn-sn-prepare *spc-second-reserved* *spc-second*))

(assert-event (fn-snt-relation *spc-second-reserved*))
(assert-event (equal (len (fn-sf-records (fn-sn-files *spc-second-reserved*))) 1))
(assert-event (equal *spc-second-fast* *spc-second-spec*))
(assert-event (equal (fn-sf-phase (fn-sn-files *spc-second-fast*)) :record-staged))
(assert-event (fn-sn-record-bindsp (fn-sn-node *spc-second-fast*) *spc-second*))
(assert-event (equal (fn-record-encode
                      (fn-sf-record-candidate (fn-sn-files *spc-second-fast*)))
                     (fn-record-encode
                      (fn-sf-record-candidate (fn-sn-files *spc-second-spec*)))))

; The exact candidate predicate remains executable.  A wrong sequence is a
; no-op in both implementations and never becomes pending bytes.
(defconst *spc-wrong-sequence*
  (fn-record-make 9 1 1 "<spc-second@example.invalid>" '(67 68)
                  '("fn.test") "spc-pin-2" "spc-subject-2"
                  "spc-release-2" 1 841000000))
(assert-event
 (equal (fn-spc-prepare *spc-second-reserved* *spc-wrong-sequence*)
        *spc-second-reserved*))
(assert-event
 (equal (fn-sn-prepare *spc-second-reserved* *spc-wrong-sequence*)
        *spc-second-reserved*))

; Candidate shape alone is insufficient.  This record has the exact next
; counters but reuses the committed Message-ID, so the prepared live node has
; no matching proposal and both transitions refuse it.
(defconst *spc-duplicate*
  (fn-record-make 1 1 1 "<spc-first@example.invalid>" '(67 68)
                  '("fn.test") "spc-pin-2" "spc-subject-2"
                  "spc-release-2" 1 841000000))
(assert-event
 (fn-sf-candidatep *spc-duplicate*
                   (fn-sf-records (fn-sn-files *spc-second-reserved*))
                   (fn-sf-frontier (fn-sn-files *spc-second-reserved*))))
(assert-event
 (not (fn-sn-record-bindsp
       (fn-sn-prepare-node (fn-sn-node *spc-second-reserved*) *spc-duplicate*)
       *spc-duplicate*)))
(assert-event
 (equal (fn-spc-prepare *spc-second-reserved* *spc-duplicate*)
        *spc-second-reserved*))

; Sole keystone hypothesis tooth.  A structural state with the real files and
; a stale empty node is not related.  The stale node accepts the duplicate,
; so the projection stages it; replay of the actual durable history rejects
; it and the specification stays put.  Therefore the equality conclusion is
; false when fn-snt-relation is removed.
(defconst *spc-stale*
  (fn-sn-make *spc-groups* 10 (fn-sn-files *spc-second-reserved*)
              (fn-node-initial-state *spc-groups* 10)
              nil (fn-stx-index-empty)))
(assert-event (fn-sn-statep *spc-stale*))
(assert-event (not (fn-snt-relation *spc-stale*)))
(assert-event
 (equal (fn-sf-phase
         (fn-sn-files (fn-spc-prepare *spc-stale* *spc-duplicate*)))
        :record-staged))
(assert-event
 (equal (fn-sn-prepare *spc-stale* *spc-duplicate*) *spc-stale*))
(must-fail
 (assert-event
  (equal (fn-spc-prepare *spc-stale* *spc-duplicate*)
         (fn-sn-prepare *spc-stale* *spc-duplicate*))))

; The process-root chain is executable: observed recovery establishes the
; relation and each actual post-open mutator, including the fast prepare,
; retains it without evaluating the relation in the transition.
(defconst *spc-opened*
  (fn-sn-open-observed *spc-groups* 10 1 (list *spc-first*)))
(defconst *spc-open-events*
  '((:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
    (:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
    (:io :recovery-barrier :ok)
    (:io :start-frontier nil) (:io :frontier-file :ok)
    (:io :frontier-replace :ok) (:io :frontier-directory :ok)))
(assert-event (fn-sn-open-okp *spc-opened*))
(assert-event
 (fn-snt-relation
  (fn-spc-run (fn-sn-open-state *spc-opened*) *spc-open-events*)))
