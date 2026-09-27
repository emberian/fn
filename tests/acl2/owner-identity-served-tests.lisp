; Teeth for books/owner-identity-served.lisp (AW round 13, signed-post x
; prepare-served): the identity prepare the host calls
; (host/owner-host.lisp fn-owner-prepare-identity: fn-oiis-prepare-identity
; over the wire value and the arena's count) and its two events,
; fn-oiis-prepare-identity-preserves-invariant (KEYSTONE) and
; fn-oiis-prepare-identity-unfolds.  The owners and the signed composites are
; owner-prepare-served-events-tests' reachable fixtures: the configured owner
; with the author enrolled (*pse-k2-reserved*), the same with fn.test retired
; by a live completion (*pse-t2-reserved*), and the wire composite ACL2
; builds for the signed article filed in fn.test (fn-pa-authorized-event).
(in-package "ACL2")
(include-book "../../books/owner-identity-served")
(include-book "owner-prepare-served-events-tests")

; The handle the host passes: the arena's count (fn-arena-count fn-arena) of
; the fixtures' arena.
(defun ois-count (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-arena-count fn-arena))
(bpr-lift ois-count 0)
(defconst *ois-h* (in-arena-ois-count *sr-arena*))
(defun ois-row (oc w)
  (let ((s (lgt-store oc)))
    (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) *ois-h*)))
(assert-event (natp *ois-h*))

; -----------------------------------------------------------------------------
; fn-oiis-prepare-identity-preserves-invariant.  REACHABLE POSITIVE WITNESS:
; the wire composite of the signed article (fn.test served), through the
; host's entry at the arena's count: the invariant holds before, the
; interned row is a retained composite carrying the wire value, the row is
; served, the Store stages exactly that row, and the invariant holds after.
(make-event `(defconst *ois-row* ',(ois-row *pse-k2-reserved* *pse-comp*)))
(make-event `(defconst *ois-staged*
               ',(fn-oiis-prepare-identity *pse-k2-reserved* *pse-comp* *ois-h*)))
(assert-event (fn-stxa-p *pse-comp*))
(assert-event (fn-lgoc-invariantp *pse-k2-reserved*))
(assert-event (equal (lgt-phase *pse-k2-reserved*) :reserved))
(assert-event (fn-hstxa-p *ois-row*))
(assert-event (equal (fn-hstxa-stxa *ois-row*) *pse-comp*))
(assert-event (fn-oii-identity-sealsp *pse-comp*))
(assert-event (fn-psrv-event-servedp (fn-ocfg-config *pse-k2-reserved*) *ois-row*))
(assert-event (equal (lgt-phase *ois-staged*) :record-staged))
(assert-event (equal (pse-candidate *ois-staged*) *ois-row*))
(assert-event (fn-lgoc-invariantp *ois-staged*))
; fn-oiis-prepare-identity-unfolds, served branch: signed-post's prepare.
(assert-event (equal *ois-staged*
                     (fn-oii-ocfg-prepare-identity *pse-k2-reserved* *pse-comp* *ois-h*)))
; ... and the publication completes it (order, finish) with the invariant.
(make-event `(defconst *ois-ordered* ',(fn-olr-ocfg-order *ois-staged*)))
(make-event `(defconst *ois-finished* ',(in-arena-pse-finish *sr-arena* *ois-ordered*)))
(assert-event (fn-lgoc-invariantp *ois-ordered*))
(assert-event (equal (lgt-phase *ois-finished*) :ready))
(assert-event (fn-lgoc-invariantp *ois-finished*))

; -----------------------------------------------------------------------------
; REFUSAL (reachable): the retired group, refused by name.  fn.test retired
; by a live completion, the author enrolled; the wire composite of the
; article filed in fn.test: the interned row is not served, the entry leaves
; the owner unchanged (the host's word :refused) and the invariant holds.
; fn-oiis-prepare-identity-unfolds, unserved branch: signed-post's prepare
; alone stages it and breaks the invariant.
(make-event `(defconst *ois-t-row* ',(ois-row *pse-t2-reserved* *pse-t-comp*)))
(assert-event (fn-lgoc-invariantp *pse-t2-reserved*))
(assert-event (fn-hstxa-p *ois-t-row*))
(assert-event (not (fn-psrv-event-servedp (fn-ocfg-config *pse-t2-reserved*) *ois-t-row*)))
(assert-event (equal (fn-oiis-prepare-identity *pse-t2-reserved* *pse-t-comp* *ois-h*)
                     *pse-t2-reserved*))
(assert-event (fn-lgoc-invariantp
               (fn-oiis-prepare-identity *pse-t2-reserved* *pse-t-comp* *ois-h*)))
(assert-event (equal (lgt-phase (fn-oii-ocfg-prepare-identity *pse-t2-reserved* *pse-t-comp* *ois-h*))
                     :record-staged))
(assert-event (not (fn-lgoc-invariantp
                    (fn-oii-ocfg-prepare-identity *pse-t2-reserved* *pse-t-comp* *ois-h*))))

; -----------------------------------------------------------------------------
; REFUSAL: the WIRE composite where the interned row is expected.  The served
; prepare over the wire value (not fn-oii-identity-row of it) stages nothing
; on the served owner -- the flipped Store stages rows only -- and its served
; test over the wire value passes whatever the groups (a wire composite is
; not held), which is why the entry tests the row.
(assert-event (not (fn-hstxa-p *pse-comp*)))
(assert-event (equal (fn-psrv-prepare-identity *pse-k2-reserved* *pse-comp*) *pse-k2-reserved*))
(assert-event (fn-psrv-event-servedp (fn-ocfg-config *pse-t2-reserved*) *pse-t-comp*))
(assert-event (equal (fn-psrv-prepare-identity *pse-t2-reserved* *pse-t-comp*) *pse-t2-reserved*))

; -----------------------------------------------------------------------------
; HYPOTHESIS fn-lgoc-invariantp removed (CORRUPTED-STATE witness): the served
; owner with its Store's topic prefix counter moved to 99 (owner-log-ocl-tests'
; lgt-with-topic; fn-sn-statep and the identity prepare's gate do not read
; it): the invariant fails, the entry still stages the row, and the
; conclusion fails.
(defconst *ois-bad* (lgt-with-topic *pse-k2-reserved* 99))
(make-event `(defconst *ois-bad-staged*
               ',(fn-oiis-prepare-identity *ois-bad* *pse-comp* *ois-h*)))
(assert-event (not (fn-lgoc-invariantp *ois-bad*)))
(assert-event (equal (lgt-phase *ois-bad-staged*) :record-staged))
(assert-event (not (fn-lgoc-invariantp *ois-bad-staged*)))
