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
