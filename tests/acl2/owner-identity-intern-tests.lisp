; Teeth for books/owner-identity-intern.lisp (lane signed-post, PRF-292):
; the signed POST's composite over a flipped owner (tests/acl2/
; owner-signed-post-tests.lisp's reachable trace: an enrolled Store, a
; served POST carrying a valid FN-Authorship carrier, taken by the owner).
(in-package "ACL2")
(include-book "../../books/owner-identity-intern")
(include-book "owner-signed-post-tests")
(include-book "std/testing/must-fail" :dir :system)

(bpr-lift fn-ocfg-step 2)

; The owner at the identity prepare: the taken POST with the frontier
; reserved (the first four Store events of ospt-store-events).
(make-event
 `(defconst *oiit-reserved*
    ',(in-arena-fn-own-run *sr-arena* *ospt-taken*
                           (take 4 (ospt-store-events *ospt-event*)))))
(defconst *oiit-s* (fn-own-store *oiit-reserved*))
(defconst *oiit-h* (len *sr-arena*))
(make-event `(defconst *oiit-row* ',(fn-oii-identity-row *ospt-event* (fn-sn-keyring *oiit-s*)
                       (fn-sn-keyring-generation *oiit-s*) *oiit-h*)))
(defconst *oiit-oc* (fn-ocfg-make *oiit-reserved* *ospt-config* nil nil))

; -- fn-oii-composite-row-is-held: reachable positive witness.
(assert-event (and (fn-stxa-p *ospt-event*)
                   (fn-record-p (fn-replay-composite-record *ospt-event*))
                   (natp (fn-sn-keyring-generation *oiit-s*))))
(assert-event (and (fn-oii-identity-sealsp *ospt-event*)
                   (fn-hstxa-p *oiit-row*)
                   (equal (fn-hstxa-stxa *oiit-row*) *ospt-event*)))
; D25: the octets the host seals are the relayed article's, the octets the
; poster sent after injection (the carrier and signatures inside them).
(assert-event (equal (fn-oii-identity-payload *ospt-event*) *ospt-staged*))
; A keyring snapshot interns to itself and seals nothing.
(assert-event (let ((k (car (fn-sn-keyring-snapshots *oiit-s*))))
                (and (fn-stxk-p k)
                     (not (fn-oii-identity-sealsp k))
                     (equal (fn-oii-identity-row k nil 0 *oiit-h*) k))))

; -- The regression (every signed POST refused 441 from the flip to this
; lane): the wire composite the owner built never passes the identity
; prepare's gate; the interned row does.
(assert-event (fn-snt-relation *oiit-s*))
(assert-event (equal (fn-ccar-sn-prepare-identity *oiit-s* *ospt-event*) *oiit-s*))
(assert-event (not (equal (fn-ccar-sn-prepare-identity *oiit-s* *oiit-row*) *oiit-s*)))

; -- KEYSTONE fn-oii-ocfg-prepare-identity-is-intern-then-step: reachable
; positive witness, antecedent and conclusion.
(assert-event (fn-own-relation (fn-ocfg-owner *oiit-oc*)))
(make-event `(defconst *oiit-staged* ',(fn-oii-ocfg-prepare-identity *oiit-oc* *ospt-event* *oiit-h*)))
(assert-event
 (equal *oiit-staged*
        (in-arena-fn-ocfg-step *sr-arena* *oiit-oc*
                               (list :store (list :prepare-identity *oiit-row*)))))
; and the entry staged the row (the Store changed).
(assert-event (not (equal (fn-own-store (fn-ocfg-owner *oiit-staged*)) *oiit-s*)))

; Mutation witness (a handle other than the arena's count): the row names a
; payload the seal will not put there, and the step over the intern's row
; is not what the entry staged.
(make-event `(defconst *oiit-row-off* ',(fn-oii-identity-row *ospt-event* (fn-sn-keyring *oiit-s*)
                       (fn-sn-keyring-generation *oiit-s*) (+ 1 *oiit-h*))))
(assert-event (not (equal *oiit-row-off* *oiit-row*)))
(assert-event
 (not (equal (fn-oii-ocfg-prepare-identity *oiit-oc* *ospt-event* (+ 1 *oiit-h*))
             (in-arena-fn-ocfg-step *sr-arena* *oiit-oc*
                                    (list :store (list :prepare-identity *oiit-row*))))))

; -- The staged owner completes to the signed verdict
; (fn-osp-signed-post-finish-records-its-verdict's conclusion) over the
; interned row, with its payload sealed at the row's handle.
(defconst *oiit-arena* (append *sr-arena* (list *ospt-staged*)))
(make-event
 `(defconst *oiit-completing*
    ',(in-arena-fn-own-run *oiit-arena* (fn-ocfg-owner *oiit-staged*)
                           (nthcdr 5 (ospt-store-events *ospt-event*)))))
(assert-event (fn-sn-completion-enabledp (fn-own-store *oiit-completing*)))
(assert-event (equal (fn-sn-completion-record (fn-own-store *oiit-completing*)) *oiit-row*))
(assert-event (in-arena-ospt-finish-conclusion *oiit-arena* *oiit-completing*
                                               *ospt-staged* *ospt-snapshots*))

; -- keystone-audit 2026-09-27: fn-oii-identity-row-is-the-intern and
; fn-oii-seal-is-the-intern-arena (no hypotheses) on the reachable
; composite and on a keyring snapshot, over the arena of the trace: the
; entry's row is the intern's, which seals the relayed article at the
; arena's count exactly when the event seals (a snapshot seals nothing).
(defun oiit-intern-in (payloads w keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((fn-arena (fn-arn-seal-many payloads fn-arena))
         (h (fn-arena-count fn-arena)))
    (mv-let (row fn-arena)
      (fn-intern-event w keyring generation fn-arena)
      (mv (list h row (fn-arena-count fn-arena)
                (if (< h (fn-arena-count fn-arena)) (fn-arena-payload h fn-arena) :none))
          fn-arena))))
(defun oiit-intern (payloads w keyring generation)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (oiit-intern-in payloads w keyring generation fn-arena)
      r)))
(make-event
 `(defconst *oiit-intern*
    ',(oiit-intern *sr-arena* *ospt-event* (fn-sn-keyring *oiit-s*)
                   (fn-sn-keyring-generation *oiit-s*))))
(assert-event
 (and (equal (nth 0 *oiit-intern*) *oiit-h*)
      (equal (nth 1 *oiit-intern*) *oiit-row*)
      (fn-oii-identity-sealsp *ospt-event*)
      (equal (nth 2 *oiit-intern*) (+ 1 *oiit-h*))
      (equal (nth 3 *oiit-intern*) (fn-oii-identity-payload *ospt-event*))))
(defconst *oiit-snapshot* (car (fn-sn-keyring-snapshots *oiit-s*)))
(make-event
 `(defconst *oiit-intern-k* ',(oiit-intern *sr-arena* *oiit-snapshot* nil 0)))
(assert-event
 (and (not (fn-oii-identity-sealsp *oiit-snapshot*))
      (equal (nth 1 *oiit-intern-k*)
             (fn-oii-identity-row *oiit-snapshot* nil 0 (nth 0 *oiit-intern-k*)))
      (equal (nth 2 *oiit-intern-k*) (nth 0 *oiit-intern-k*))))
