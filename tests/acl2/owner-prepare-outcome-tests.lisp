; Teeth for books/owner-prepare-outcome.lisp (lane host-decisions-2, packet
; A): the owner entries the host calls answer their own word.  For each
; entry: a REACHABLE witness of each word over owners the log route's host
; steps reach (owner-log-ocl-tests' configured owner, prepare-served's and
; host-decisions' staged owners), asserting the word, that NEXT is the owner
; the host installed before, and that the word equals the before/after
; comparison the host line made (each keystone's conclusion, literally).
; The begin keystone's one hypothesis (a non-NIL connection identifier) has
; a CORRUPTED-STATE removal witness.
(in-package "ACL2")
(include-book "owner-prepare-served-abort-tests")
(include-book "../../books/owner-prepare-outcome")

; The host's former store comparison, and its core comparison.
(defun pot-store-word (before next refusal)
  (if (equal (lgt-store next) (lgt-store before)) refusal :prepared))
(defun pot-core-word (before next word)
  (if (equal (fn-ocfg-owner next) (fn-ocfg-owner before)) :refused word))

; The stobj entries, lifted over a local arena (tests/acl2/arena-lift.lisp).
(defun pot-retention (oc e fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (w n) (fn-pout-prepare-retention oc e fn-arena) (list w n)))
(bpr-lift pot-retention 2)
(defun pot-consumer (oc e fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (w n) (fn-pout-prepare-consumer oc e fn-arena) (list w n)))
(bpr-lift pot-consumer 2)
(defun pot-refuse (oc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (w n) (fn-pout-refuse-reservation oc fn-arena) (list w n)))
(bpr-lift pot-refuse 1)
(defun pot-abort (oc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (w n) (fn-pout-known-abort oc fn-arena) (list w n)))
(bpr-lift pot-abort 1)
(defun pot-begin (oc id fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (w n) (fn-pout-begin oc id fn-arena) (list w n)))
(bpr-lift pot-begin 2)
(defun pot-declare (oc name fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (w n) (fn-pout-declare-group oc name fn-arena) (list w n)))
(bpr-lift pot-declare 2)
(defun pot-article (oc record budget carry)
  (mv-let (w n) (fn-pout-prepare-article oc record budget carry) (list w n)))
(defun pot-identity (oc w h)
  (declare (xargs :verify-guards nil))
  (mv-let (x n) (fn-pout-prepare-identity oc w h) (list x n)))
(defun pot-topic (oc e)
  (mv-let (w n) (fn-pout-prepare-topic oc e) (list w n)))

; -----------------------------------------------------------------------------
; fn-pout-prepare-article-answers-the-store-change.
; REACHABLE :prepared: the served article at :reserved (prepare-served's
; *pst-prepared*).
(defconst *pot-art* (pot-article *lgt-reserved* *acar-t-record* 1000000
                                                       (pst-carry *lgt-reserved*)))
(assert-event (equal (first *pot-art*) :prepared))
(assert-event (equal (second *pot-art*) *pst-prepared*))
(assert-event (equal (lgt-phase (second *pot-art*)) :record-staged))
(assert-event (equal (first *pot-art*)
                     (pot-store-word *lgt-reserved* (second *pot-art*)
                                     (fn-psrv-refusal-kind *lgt-reserved* *acar-t-record* 1000000))))
; REACHABLE :refused: the retired group (the served test).
(defconst *pot-art-r* (pot-article *lgt-r-reserved* *acar-t-record* 1000000
                                                         (pst-carry *lgt-r-reserved*)))
(assert-event (equal (first *pot-art-r*) :refused))
(assert-event (equal (second *pot-art-r*) *lgt-r-reserved*))
(assert-event (equal (first *pot-art-r*)
                     (pot-store-word *lgt-r-reserved* (second *pot-art-r*)
                                     (fn-psrv-refusal-kind *lgt-r-reserved* *acar-t-record* 1000000))))
; REACHABLE :unaffordable: the served article at budget 0.
(defconst *pot-art-u* (pot-article *lgt-reserved* *acar-t-record* 0
                                                         (pst-carry *lgt-reserved*)))
(assert-event (equal (first *pot-art-u*) :unaffordable))
(assert-event (equal (lgt-store (second *pot-art-u*)) (lgt-store *lgt-reserved*)))
(assert-event (equal (first *pot-art-u*)
                     (pot-store-word *lgt-reserved* (second *pot-art-u*)
                                     (fn-psrv-refusal-kind *lgt-reserved* *acar-t-record* 0))))
; REACHABLE :refused: a second article while one is staged.
(defconst *pot-art-2* (pot-article *pst-prepared* *acar-t-record* 1000000
                                                         (pst-carry *pst-prepared*)))
(assert-event (equal (first *pot-art-2*) :refused))
(assert-event (equal (first *pot-art-2*)
                     (pot-store-word *pst-prepared* (second *pot-art-2*)
                                     (fn-psrv-refusal-kind *pst-prepared* *acar-t-record* 1000000))))

; -----------------------------------------------------------------------------
; fn-pout-prepare-identity-answers-the-store-change.
; REACHABLE :prepared: the signed composite at the arena's count
; (owner-identity-served-tests' *ois-staged*).
(make-event `(defconst *pot-id* ',(pot-identity *pse-k2-reserved* *pse-comp* *ois-h*)))
(assert-event (equal (first *pot-id*) :prepared))
(assert-event (equal (second *pot-id*) *ois-staged*))
(assert-event (equal (first *pot-id*) (pot-store-word *pse-k2-reserved* (second *pot-id*) :refused)))
; REACHABLE :refused: the composite filed in the retired fn.test.
(make-event `(defconst *pot-id-r* ',(pot-identity *pse-t2-reserved* *pse-t-comp* *ois-h*)))
(assert-event (equal (first *pot-id-r*) :refused))
(assert-event (equal (second *pot-id-r*) *pse-t2-reserved*))
(assert-event (equal (first *pot-id-r*) (pot-store-word *pse-t2-reserved* (second *pot-id-r*) :refused)))

; -----------------------------------------------------------------------------
; fn-pout-prepare-topic-answers-the-store-change.
(defconst *pot-topic* (pot-topic *lgt-reserved* *pse-topic-event*))
(assert-event (equal (first *pot-topic*) :prepared))
(assert-event (equal (second *pot-topic*) *pse-topic-staged*))
(assert-event (equal (first *pot-topic*) (pot-store-word *lgt-reserved* (second *pot-topic*) :refused)))
; REACHABLE :refused: the same event while it is staged.
(defconst *pot-topic-r* (pot-topic *pse-topic-staged* *pse-topic-event*))
(assert-event (equal (first *pot-topic-r*) :refused))
(assert-event (equal (second *pot-topic-r*) *pse-topic-staged*))
(assert-event (equal (first *pot-topic-r*)
                     (pot-store-word *pse-topic-staged* (second *pot-topic-r*) :refused)))

; -----------------------------------------------------------------------------
; fn-pout-prepare-retention-answers-the-store-change.
(defconst *pot-ret* (in-arena-pot-retention *sr-arena* *lgt-reserved* *pst-ret-event*))
(assert-event (equal (first *pot-ret*) :prepared))
(assert-event (equal (second *pot-ret*) *pst-ret-staged*))
(assert-event (equal (first *pot-ret*) (pot-store-word *lgt-reserved* (second *pot-ret*) :refused)))
; REACHABLE :refused: no reservation (the owner at :ready).
(defconst *pot-ret-r* (in-arena-pot-retention *sr-arena* *lgt-oc0* *pst-ret-event*))
(assert-event (equal (lgt-phase *lgt-oc0*) :ready))
(assert-event (equal (first *pot-ret-r*) :refused))
(assert-event (equal (first *pot-ret-r*) (pot-store-word *lgt-oc0* (second *pot-ret-r*) :refused)))

; -----------------------------------------------------------------------------
; fn-pout-prepare-consumer-answers-the-store-change.
(defconst *pot-con* (in-arena-pot-consumer *sr-arena* *lgt-reserved* *pse-consumer-event*))
(assert-event (equal (first *pot-con*) :prepared))
(assert-event (equal (second *pot-con*) *pse-consumer-staged*))
(assert-event (equal (first *pot-con*) (pot-store-word *lgt-reserved* (second *pot-con*) :refused)))
(defconst *pot-con-r* (in-arena-pot-consumer *sr-arena* *lgt-oc0* *pse-consumer-event*))
(assert-event (equal (first *pot-con-r*) :refused))
(assert-event (equal (first *pot-con-r*) (pot-store-word *lgt-oc0* (second *pot-con-r*) :refused)))

; -----------------------------------------------------------------------------
; fn-pout-refuse-reservation-answers-the-host-test (the host's test was:
; :reserved before, the Store changed, :ready after).
(defun pot-refuse-host-word (before next)
  (if (and (equal (lgt-phase before) :reserved)
           (not (equal (lgt-store next) (lgt-store before)))
           (equal (lgt-phase next) :ready))
      :refused
    :fault))
(defconst *pot-refuse* (in-arena-pot-refuse *sr-arena* *lgt-reserved*))
(assert-event (fn-sn-refuse-reservation-enabledp
               (lgt-store *lgt-reserved*)
               (1- (fn-sf-frontier (fn-sn-files (lgt-store *lgt-reserved*))))))
(assert-event (equal (first *pot-refuse*) :refused))
(assert-event (equal (lgt-phase (second *pot-refuse*)) :ready))
(assert-event (equal (first *pot-refuse*) (pot-refuse-host-word *lgt-reserved* (second *pot-refuse*))))
; REACHABLE :fault: nothing reserved.
(defconst *pot-refuse-f* (in-arena-pot-refuse *sr-arena* *lgt-oc0*))
(assert-event (equal (first *pot-refuse-f*) :fault))
(assert-event (equal (first *pot-refuse-f*) (pot-refuse-host-word *lgt-oc0* (second *pot-refuse-f*))))

; -----------------------------------------------------------------------------
; fn-pout-known-abort-answers-the-host-test.
(defconst *pot-abort* (in-arena-pot-abort *sr-arena* *pse-topic-staged*))
(assert-event (equal (first *pot-abort*) :aborted))
(assert-event (equal (second *pot-abort*) *psa-topic-aborted*))
(assert-event (equal (first *pot-abort*) (psa-word *pse-topic-staged* (second *pot-abort*))))
(defconst *pot-abort-a* (in-arena-pot-abort *sr-arena* *pst-prepared*))
(assert-event (equal (first *pot-abort-a*) :aborted))
(assert-event (equal (first *pot-abort-a*) (psa-word *pst-prepared* (second *pot-abort-a*))))
; REACHABLE :fault: nothing staged.
(defconst *pot-abort-f* (in-arena-pot-abort *sr-arena* *lgt-reserved*))
(assert-event (equal (first *pot-abort-f*) :fault))
(assert-event (equal (first *pot-abort-f*) (psa-word *lgt-reserved* (second *pot-abort-f*))))

; -----------------------------------------------------------------------------
; fn-pout-begin-answers-the-host-test.  The reader connection of the
; configured owner at :ready.
(defconst *pot-conn-id* (fn-own-conn-id (car (fn-own-conns (fn-ocfg-owner *lgt-oc0*)))))
(assert-event (natp *pot-conn-id*))
(defconst *pot-begin* (in-arena-pot-begin *sr-arena* *lgt-oc0* *pot-conn-id*))
(assert-event (equal (first *pot-begin*) :begun))
(assert-event (equal (fn-own-pending (fn-ocfg-owner (second *pot-begin*))) *pot-conn-id*))
(assert-event (equal (first *pot-begin*) (pot-core-word *lgt-oc0* (second *pot-begin*) :begun)))
; REACHABLE :refused: a second begin while one is pending, and an unknown id.
(defconst *pot-begin-2* (in-arena-pot-begin *sr-arena* (second *pot-begin*) *pot-conn-id*))
(assert-event (equal (first *pot-begin-2*) :refused))
(assert-event (equal (first *pot-begin-2*) (pot-core-word (second *pot-begin*) (second *pot-begin-2*) :begun)))
(defconst *pot-begin-u* (in-arena-pot-begin *sr-arena* *lgt-oc0* 999))
(assert-event (equal (first *pot-begin-u*) :refused))
(assert-event (equal (first *pot-begin-u*) (pot-core-word *lgt-oc0* (second *pot-begin-u*) :begun)))
; CORRUPTED-STATE hypothesis-removal witness: a connection whose identifier
; is NIL (the host's are naturals).  The hypothesis fails, the gate admits,
; and the conclusion fails: the begin at NIL leaves the owner as it was, so
; the comparison said :refused where the gate says :begun.
(defconst *pot-nil-oc*
  (let ((o (fn-ocfg-owner *lgt-oc0*)))
    (fn-ocfg-with-owner
     *lgt-oc0*
     (fn-own-make (fn-own-store o) (fn-own-view o)
                  (list (cons nil (cdr (car (fn-own-conns o)))))
                  (fn-own-next-id o) (fn-own-max-conns o) nil
                  (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                  (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                  (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))))
(defconst *pot-begin-nil* (in-arena-pot-begin *sr-arena* *pot-nil-oc* nil))
(assert-event (fn-pout-begin-admitsp *pot-nil-oc* nil))
(assert-event (equal (first *pot-begin-nil*) :begun))
(assert-event (not (equal (first *pot-begin-nil*)
                          (pot-core-word *pot-nil-oc* (second *pot-begin-nil*) :begun))))

; -----------------------------------------------------------------------------
; fn-pout-declare-group-answers-the-host-test.  The configured owner after
; a clock observation (the host observes before every socket read).
(defconst *pot-clocked* (fn-ocfg-observe *lgt-oc0* *pse-obs*))
(assert-event (not (fn-clock-observationp (fn-own-clock (fn-ocfg-owner *lgt-oc0*)))))
(assert-event (fn-clock-observationp (fn-own-clock (fn-ocfg-owner *pot-clocked*))))
(defconst *pot-decl* (in-arena-pot-declare *sr-arena* *pot-clocked* "fn.pot"))
(assert-event (equal (first *pot-decl*) :declared))
(assert-event (equal (first *pot-decl*) (pot-core-word *pot-clocked* (second *pot-decl*) :declared)))
; REACHABLE :refused: the same name again, and any name without a clock.
(defconst *pot-decl-2* (in-arena-pot-declare *sr-arena* (second *pot-decl*) "fn.pot"))
(assert-event (equal (first *pot-decl-2*) :refused))
(assert-event (equal (first *pot-decl-2*)
                     (pot-core-word (second *pot-decl*) (second *pot-decl-2*) :declared)))
(defconst *pot-decl-n* (in-arena-pot-declare *sr-arena* *lgt-oc0* "fn.pot"))
(assert-event (equal (first *pot-decl-n*) :refused))
(assert-event (equal (first *pot-decl-n*) (pot-core-word *lgt-oc0* (second *pot-decl-n*) :declared)))
