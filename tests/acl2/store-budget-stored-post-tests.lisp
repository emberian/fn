; fn: witnesses and teeth for books/store-budget-stored-post.lisp (records-flip,
; flip-L1-3): the served POST keeps the stored-bytes condition.
;
; The run is two POSTs through the entries, from fn-sn-initial: the stage
; (fn-store-prepare-interned over a local arena), the host's publication words
; (fn-sn-io) and the finish (fn-sn-finish).  A run's arena is the payloads of
; PRIOR (the wire records the run staged, in order).  The hypothesis-removal
; witnesses pair a REACHED store with the arena as it stood before a seal (a
; MIS-PAIRED ARENA: the host never pairs a store with an older arena), so the
; relation fails there and each keystone's conclusion fails with it.
(in-package "ACL2")
(include-book "../../books/store-budget-stored-post")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sbsp-groups* '("fn.letters" "fn.test"))
(defconst *sbsp-w1*
  (fn-record-make 0 0 0 "<sbsp1@example.invalid>" '(65 66) *sbsp-groups*
                  "p1" "s1" "r1" 2 841000000))
(defconst *sbsp-w2*
  (fn-record-make 1 1 1 "<sbsp2@example.invalid>" '(67 68 69 70 71) *sbsp-groups*
                  "p2" "s2" "r2" 2 841000000))
(assert-event (and (fn-record-p *sbsp-w1*) (fn-record-p *sbsp-w2*)))

(defun sbsp-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun sbsp-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))

; The relation of S over the arena holding PRIOR's payloads.
(defun sbsp-okp-in (s prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (mv (fn-sbud-store-extents-okp s fn-arena) fn-arena)))
(defun sbsp-okp (s prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (ok fn-arena) (sbsp-okp-in s prior fn-arena) ok)))

; The stage over the arena holding PRIOR's payloads: the relation before,
; the store after, the relation after over the arena after, the arena's
; count after.
(defun sbsp-stage-in (s w prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (let ((before (fn-sbud-store-extents-okp s fn-arena)))
      (mv-let (next fn-arena)
        (fn-store-prepare-interned s w fn-arena)
        (mv (list before next (fn-sbud-store-extents-okp next fn-arena)
                  (fn-arena-count fn-arena))
            fn-arena)))))
(defun sbsp-stage (s w prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena) (sbsp-stage-in s w prior fn-arena) out)))

; -----------------------------------------------------------------------------
; The run.

(defconst *sbsp-s0* (sbsp-reserve (fn-sn-initial *sbsp-groups* 10)))
(assert-event (equal (fn-sf-phase (fn-sn-files *sbsp-s0*)) :reserved))

; POST 1, the stage (fn-store-prepare-interned-keeps-the-stored-octets,
; reachable): the relation holds before (empty history, empty arena) and
; after; the store took the row (phase :record-staged, the row at handle 0)
; and the arena grew to 1.
(defconst *sbsp-st1* (sbsp-stage *sbsp-s0* *sbsp-w1* nil))
(defconst *sbsp-s1* (nth 1 *sbsp-st1*))
(assert-event (equal (nth 0 *sbsp-st1*) t))
(assert-event (equal (fn-sf-phase (fn-sn-files *sbsp-s1*)) :record-staged))
(assert-event (equal (fn-record-payload (fn-sf-record-candidate (fn-sn-files *sbsp-s1*))) 0))
(assert-event (equal (nth 3 *sbsp-st1*) 1))
(assert-event (equal (nth 2 *sbsp-st1*) t))

; The publish (fn-sn-io-keeps-the-stored-octets, reachable): three words,
; the last the directory barrier that appends the row to the history; the
; relation holds before and after over the arena holding W1's payload.
(defconst *sbsp-s2* (sbsp-publish *sbsp-s1*))
(assert-event (equal (sbsp-okp *sbsp-s1* (list *sbsp-w1*)) t))
(assert-event (equal (fn-sf-phase (fn-sn-files *sbsp-s2*)) :completing))
(assert-event (equal (len (fn-sf-records (fn-sn-files *sbsp-s2*))) 1))
(assert-event (equal (sbsp-okp *sbsp-s2* (list *sbsp-w1*)) t))

; The finish (fn-sn-finish-keeps-the-stored-octets, reachable).
(defconst *sbsp-s3* (fn-sn-finish *sbsp-s2*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sbsp-s3*)) :ready))
(assert-event (equal (sbsp-okp *sbsp-s3* (list *sbsp-w1*)) t))
; What the relation buys: the budget counts the 2 octets the arena holds.
(assert-event (equal (fn-sbud-bytes-used *sbsp-s3*) 2))

; POST 2 on the grown history: the row at handle 1.
(defconst *sbsp-s4* (sbsp-reserve *sbsp-s3*))
(defconst *sbsp-st5* (sbsp-stage *sbsp-s4* *sbsp-w2* (list *sbsp-w1*)))
(defconst *sbsp-s5* (nth 1 *sbsp-st5*))
(assert-event (equal (nth 0 *sbsp-st5*) t))
(assert-event (equal (fn-sf-phase (fn-sn-files *sbsp-s5*)) :record-staged))
(assert-event (equal (fn-record-payload (fn-sf-record-candidate (fn-sn-files *sbsp-s5*))) 1))
(assert-event (equal (nth 3 *sbsp-st5*) 2))
(assert-event (equal (nth 2 *sbsp-st5*) t))
(defconst *sbsp-s7* (fn-sn-finish (sbsp-publish *sbsp-s5*)))
(assert-event (equal (len (fn-sf-records (fn-sn-files *sbsp-s7*))) 2))
(assert-event (equal (sbsp-okp *sbsp-s7* (list *sbsp-w1* *sbsp-w2*)) t))
(assert-event (equal (fn-sbud-bytes-used *sbsp-s7*) 7))

; A refused stage keeps the relation too: the staged store is not :reserved.
(defconst *sbsp-st-refused* (sbsp-stage *sbsp-s5* *sbsp-w2* (list *sbsp-w1*)))
(assert-event (equal (nth 1 *sbsp-st-refused*) *sbsp-s5*))
(assert-event (equal (nth 3 *sbsp-st-refused*) 1))

; -----------------------------------------------------------------------------
; HYPOTHESIS REMOVAL (the relation), each over a MIS-PAIRED ARENA.

; fn-store-prepare-interned-keeps-the-stored-octets.  Retained: fn-arena-p
; (a local stobj).  Omitted: the relation of *sbsp-s4* over the EMPTY arena
; fails (the history's row names handle 0, outside it).  Conclusion: the
; stage still takes W2 (the prepare reads no bytes), at handle 0, whose
; sealed bytes are W2's 5 where the history row counts W1's 2: fails.
(defconst *sbsp-st-bad* (sbsp-stage *sbsp-s4* *sbsp-w2* nil))
(assert-event (equal (nth 0 *sbsp-st-bad*) nil))
(assert-event (equal (fn-sf-phase (fn-sn-files (nth 1 *sbsp-st-bad*))) :record-staged))
(must-fail (assert-event (nth 2 *sbsp-st-bad*)))

; fn-sn-io-keeps-the-stored-octets (one hypothesis).  Omitted: the staged
; row's handle is outside the empty arena.  Conclusion: fails after the
; publish words.
(assert-event (equal (sbsp-okp *sbsp-s1* nil) nil))
(must-fail (assert-event (sbsp-okp *sbsp-s2* nil)))

; fn-sn-finish-keeps-the-stored-octets (one hypothesis).
(assert-event (equal (sbsp-okp *sbsp-s2* nil) nil))
(must-fail (assert-event (sbsp-okp *sbsp-s3* nil)))

; fn-arena-p (both stage keystones): the stobj's own recognizer, which every
; live arena satisfies; no removal witness is claimed for it.

; -----------------------------------------------------------------------------
; The owner's POST (fn-pcar-sbud-prepare-keeps-the-stored-octets): an owner
; over the reached store *sbsp-s4*; the row fn-intern-row-at makes of W2 at the
; arena's count; the seal when the store changed.  DEV'S carried prepare
; (books/owner-prepare-carried.lisp fn-pcar-spc-prepare, 2026-09-27) still
; asks fn-rcon-record-p of what it stages, so on dev it refuses the row and
; this witness reaches the REFUSAL branch (store and arena unchanged); once
; flip-L6's carried prepare stages held rows it reaches the STAGING branch
; (row at handle 1, W2's payload sealed).  The assertions below hold on both
; branches, and the keystone's proof covers both.
(defconst *sbsp-oc* (fn-ocfg-make (fn-own-start *sbsp-s4* 4) nil nil nil))
(assert-event (equal (fn-sbud-oc-store *sbsp-oc*) *sbsp-s4*))

(defun sbsp-owner-in (oc w prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (let* ((s (fn-sbud-oc-store oc))
           (before (fn-sbud-store-extents-okp s fn-arena))
           (row (fn-intern-row-at w (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                  (fn-arena-count fn-arena)))
           (next (fn-pcar-sbud-prepare oc row 100)))
      (if (equal (fn-sbud-oc-store next) s)
          (mv (list before (fn-sbud-oc-store next)
                    (fn-sbud-store-extents-okp (fn-sbud-oc-store next) fn-arena))
              fn-arena)
        (let ((fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))
          (mv (list before (fn-sbud-oc-store next)
                    (fn-sbud-store-extents-okp (fn-sbud-oc-store next) fn-arena))
              fn-arena))))))
(defun sbsp-owner (oc w prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena) (sbsp-owner-in oc w prior fn-arena) out)))

(defconst *sbsp-own* (sbsp-owner *sbsp-oc* *sbsp-w2* (list *sbsp-w1*)))
(assert-event (equal (nth 0 *sbsp-own*) t))
(assert-event (equal (nth 2 *sbsp-own*) t))
; Removal of the relation: the empty arena.
(defconst *sbsp-own-bad* (sbsp-owner *sbsp-oc* *sbsp-w2* nil))
(assert-event (equal (nth 0 *sbsp-own-bad*) nil))
(must-fail (assert-event (nth 2 *sbsp-own-bad*)))
