; Teeth of books/reclaim-fold-contexts.lisp
; fn-rfc-the-open-interns-at-the-fold-contexts: the open's interned rows
; carry, row by row, the context the fold decides at their position.
;
; THE LOG (tests/acl2/store-checkpoint-fold-tests.lisp *scft-log*): enroll
; (a keyring snapshot, generation 1), article A, rotate (generation 2),
; article B, opened on an arena already holding one payload, so the handles
; start at 1.  The claim has no hypothesis, so there is no removal.  The
; mutation checks every row against the context of the LAST identity, which
; is what a store that re-contexts every row at a rotation would hold
; (fn-sn-set-keyring, books/store-node.lisp); A was interned at generation 1,
; so the mutated claim is false.
(in-package "ACL2")
(include-book "store-checkpoint-fold-tests")
(include-book "../../books/reclaim-fold-contexts")
; The owner fixture whose rewrite under *xt-ctx* tombstones three articles
; (*ort-rows* over *rpt-payloads*), for fn-rfc-the-rewrite-keeps-the-fold-contexts.
(include-book "owner-reclaim-tests")

(defun rfct-open-check (id ws dicts h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (acc fn-arena)
    (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)
    (mv (fn-orcr-fold-contexts-okp (fn-ssr-rows acc) id h fn-arena) fn-arena)))
(defun rfct-open-check-last (id ws dicts h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (acc fn-arena)
    (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)
    (mv (fn-orcr-fold-contexts-okp (fn-ssr-rows acc)
                                   (fn-replay-identity-loop (fn-ssr-rows acc) id) h fn-arena)
        fn-arena)))

; Non-vacuity: the open interns A and B as held rows (two retained rows the
; claim checks), at handles 1 and 2.
(assert-event
 (let ((rows (car (scft-worker *scft-log* *scft-id0* (list '(9 9))))))
   (and (equal (len rows) 4)
        (fn-held-p (nth 1 rows)) (fn-held-p (nth 3 rows))
        (equal (fn-record-payload (nth 1 rows)) 1)
        (equal (fn-record-payload (nth 3 rows)) 2)
        (not (equal (fn-held-context (nth 1 rows)) (fn-held-context (nth 3 rows)))))))

(defteeth fn-rfc-the-open-interns-at-the-fold-contexts
  :subject fn-ssr-intern-step
  :claim
  (()
   (fn-orcr-fold-contexts-okp
    (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
    id h
    (mv-nth 1 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena))))
  :witness ((id *scft-id0*) (ws *scft-log*) (dicts nil) (h 0) (prior (list '(9 9))))
  :stobjs ((fn-arena (sckat-seal-all prior fn-arena)))
  :stobj-checks
  (((fn-orcr-fold-contexts-okp
     (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
     id h
     (mv-nth 1 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
    (rfct-open-check id ws dicts h fn-arena)
    :hints (("Goal" :in-theory '(rfct-open-check))))
   ((fn-orcr-fold-contexts-okp
     (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
     (fn-replay-identity-loop
      (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
      id)
     h
     (mv-nth 1 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
    (rfct-open-check-last id ws dicts h fn-arena)
    :hints (("Goal" :in-theory '(rfct-open-check-last)))))
  :mutations
  ((contexts-at-the-last-identity
    (:conclusion
     (fn-orcr-fold-contexts-okp
      (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
      (fn-replay-identity-loop
       (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
       id)
      h
      (mv-nth 1 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena))))
    () :fault "Every retained row is checked at the context of the last identity, as a store that re-contexts its rows at a rotation holds them.")))

(defteeth-check (fn-rfc-the-open-interns-at-the-fold-contexts))

; fn-rfc-the-rewrite-keeps-the-fold-contexts (part 1 of
; RECLAIM-FOLD-CONTEXTS-CARRIED): the reclaim rewrite keeps the premise.
;
; POSITIVE WITNESS: the owner fixture's three held rows (*ort-rows* over
; *rpt-payloads*) hold the premise, and *xt-ctx* rewrites all three into
; tombstone records (owner-reclaim-tests asserts the rewrite changes them);
; the rewritten rows hold it.  No retained row follows a rewritten one there,
; so the identity half is exercised by the mutation below.
; THE LOG *rfct-log*: enroll (generation 1), article A, article R, rotate
; (generation 2), article B, opened from *scft-id0*.  *rfct-ok-rows* is the
; open with R's row replaced by the record R itself (its intern is the same
; held row at the live count); *rfct-g1-rows* holds B interned at generation
; 1, a context the fold does not decide at B's position.
; REMOVAL (premise): *rfct-g1-rows* fails the premise, and under *xt-ctx0*
; (no policy: nothing rewritten) the rewritten rows fail it too.
; MUTATION: a rewrite that turned the rotation into a record, the fault a
; store event decoding as a record would cause, leaves B checked at
; generation 1: false at *rfct-ok-rows*.
(defconst *rfct-r*
  (fn-record-make 2 2 2 "<mid@example>" '(67 13 10) '("fn.test") "o3" "s3" "e3" 1 841000002))
(make-event `(defconst *rfct-rot*
               ',(fn-hl-enroll-event 3 3 3 2 *scft-principal* *scft-keys2* (list *scft-enroll*))))
(defconst *rfct-b*
  (fn-record-make 4 4 4 "<after@example>" '(66 13 10) '("fn.test") "o2" "s2" "e2" 1 841000001))
(defconst *rfct-log* (list *scft-enroll* *scft-a* *rfct-r* *rfct-rot* *rfct-b*))
(make-event `(defconst *rfct-open* ',(scft-worker *rfct-log* *scft-id0* nil)))
(defconst *rfct-ok-rows*
  (let ((o (car *rfct-open*)))
    (list (nth 0 o) (nth 1 o) *rfct-r* (nth 3 o) (nth 4 o))))
(make-event
 `(defconst *rfct-g1-rows*
    ',(let* ((o (car *rfct-open*))
             (seed (fn-ssr-seed (fn-replay-identity-loop (list (nth 0 o)) *scft-id0*))))
        (list (nth 0 o) (nth 1 o) *rfct-r* (nth 3 o)
              (fn-intern-row-at *rfct-b* (fn-ssr-at 1 seed) (fn-ssr-at 2 seed)
                                (fn-record-payload (nth 4 o)))))))
(defconst *rfct-r3* (fn-record-make 3 3 3 "<rot@example>" (quote (68 13 10)) (quote ("fn.test")) "o4" "s4" "e4" 1 841000003))
(defun rfct-premise (rows id fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv (fn-orcr-fold-contexts-okp rows id (fn-arena-count fn-arena) fn-arena) fn-arena))
(defun rfct-carried (rows id ctx fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv (fn-orcr-fold-contexts-okp (fn-orc-rewrite-rows rows ctx fn-arena) id
                                 (fn-arena-count fn-arena) fn-arena)
      fn-arena))
(defun rfct-carried-mutant (rows id ctx fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv (fn-orcr-fold-contexts-okp (update-nth 3 *rfct-r3* (fn-orc-rewrite-rows rows ctx fn-arena)) id
                                 (fn-arena-count fn-arena) fn-arena)
      fn-arena))
(defteeth fn-rfc-the-rewrite-keeps-the-fold-contexts
  :subject fn-orc-rewrite-rows
  :claim
  (((premise (fn-orcr-fold-contexts-okp rows id (fn-arena-count fn-arena) fn-arena)))
   (fn-orcr-fold-contexts-okp (fn-orc-rewrite-rows rows ctx fn-arena) id
                              (fn-arena-count fn-arena) fn-arena))
  :witness ((rows *ort-rows*) (id nil) (ctx *xt-ctx*) (prior *rpt-payloads*))
  :stobjs ((fn-arena (sckat-seal-all prior fn-arena)))
  :stobj-checks
  (((fn-orcr-fold-contexts-okp rows id (fn-arena-count fn-arena) fn-arena)
    (rfct-premise rows id fn-arena)
    :hints (("Goal" :in-theory '(rfct-premise))))
   ((fn-orcr-fold-contexts-okp (fn-orc-rewrite-rows rows ctx fn-arena) id
                               (fn-arena-count fn-arena) fn-arena)
    (rfct-carried rows id ctx fn-arena)
    :hints (("Goal" :in-theory '(rfct-carried))))
   ((fn-orcr-fold-contexts-okp (update-nth 3 *rfct-r3* (fn-orc-rewrite-rows rows ctx fn-arena)) id
                               (fn-arena-count fn-arena) fn-arena)
    (rfct-carried-mutant rows id ctx fn-arena)
    :hints (("Goal" :in-theory '(rfct-carried-mutant)))))
  :witness-unguarded "fn-orc-rewrite-row decodes through the record codec's attachment"
  :breaks
  ((premise ((rows *rfct-g1-rows*) (id *scft-id0*) (ctx *xt-ctx0*) (prior (cadr *rfct-open*)))))
  :mutations
  ((rewrite-tombstones-a-keyring-event
    (:conclusion
     (fn-orcr-fold-contexts-okp (update-nth 3 *rfct-r3* (fn-orc-rewrite-rows rows ctx fn-arena)) id
                                (fn-arena-count fn-arena) fn-arena))
    ((rows *rfct-ok-rows*) (id *scft-id0*) (ctx *xt-ctx0*) (prior (cadr *rfct-open*)))
    :fault "A rewrite that turned the keyring rotation into a record (a store event decoding as a record) leaves the rotation unapplied, so the later article is checked at the old generation.")))

(defteeth-check (fn-rfc-the-rewrite-keeps-the-fold-contexts))
