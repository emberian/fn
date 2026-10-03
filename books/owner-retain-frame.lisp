; owner-retain-frame.lisp -- the owner's carried relation as a writer profile
; (lane def-entry, 2026-10-03): the frame every owner writer's preservation
; proof shares, in a book, and the profile `def-carried-writer' reads, so
; that a writer of host/owner-host.lisp is one declaration,
;
;   (def-owner-writer fn-owner-close
;     :opens (fn-owner-callback-close)
;     :via (fn-ohr-step-close-preserves-carried-relation
;           fn-owner-callback-close-branch-unfolds))
;
; and, through the owner's step transition (a host function, so named at
; the writer),
;
;   (def-owner-writer fn-owner-take
;     :opens (fn-owner-put-credits)
;     :step (fn-owner-step (list :take) fn-ohr-step-take-preserves-carried-relation))
;
; in host/owner-retain-host.lisp (which includes this book), where stage 5
; wrote the proof by hand (lanedumps/stage-5.md; ten writers, 229 lines).
;
; THE CARRIER today is the ACL2 state: fn-owner-retain-statep
; (books/owner-retain-transitions.lisp) reads the globals 'fn-owner and
; 'fn-owner-retain-carry, written only by the two installers
; fn-owner-install-ocfg (books/owner-obligation-state.lisp) and
; fn-owner-retain-carry-put (books/owner-retain-state.lisp).  Stage 5's
; carrier move puts both into their own stobj; then this profile's
; :invariant, :installers, :at and :frame change and every def-owner-writer
; declaration stays as it is (the carried formal and the returned state are
; the world's, never declared).
;
; THE FRAME, one rewrite rule per write the owner's writers make beside the
; carried value or through an installer:
;   fn-orh-retain-statep-of-other-global-put      a put of any other global
;   fn-orh-retain-statep-of-install-ocfg          the owner installed, given fn-lgoc-invariantp
;   fn-orh-retain-statep-of-retain-carry-put      the carry installed, given fn-prc-carryp
;   fn-orh-retain-statep-of-install-served-effects  the served effects' globals
;   fn-orh-retain-statep-of-put-credits           the credits global
; and the bridge fn-owner-retain-statep-implies-lgoc, from the relation to
; the configured owner's invariant, at which the model keystones of
; books/owner-host-relation.lisp (fn-ohr-*) are instantiated (:at).
;
; The profile's :row is the pilot def-carried row fn-owner-retain-carried
; (books/owner-retain-carried.lisp): a writer's guard conjuncts over the
; state are checked against its bridges at expansion, and
; (def-carried-writers-row fn-owner-retain-carried-host :profile
; fn-owner-retain :from fn-owner-retain-carried), in the image world after
; the declarations, writes the row whose completeness over fn-interfaces
; raw dispatch (D40) is decided by.

(in-package "ACL2")
(include-book "def-carried-writer")
(include-book "owner-retain-carried")      ; the pilot row; owner-retain-transitions
(include-book "owner-connection-callbacks") ; fn-owner-callback-install-effects, -put-credits

(include-book "owner-retain-writer-frame")

(defthm fn-orh-retain-statep-of-install-served-effects
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (fn-owner-callback-install-effects effects state)))
  :hints (("Goal" :in-theory '(fn-owner-callback-install-effects
                               fn-owner-install-served-effects
                               fn-orh-retain-statep-of-other-global-put))))

(defthm fn-orh-retain-statep-of-put-credits
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (fn-owner-put-credits l state)))
  :hints (("Goal" :in-theory '(fn-owner-put-credits
                               fn-orh-retain-statep-of-other-global-put))))


; -----------------------------------------------------------------------------
; The profile.

(def-carried-profile fn-owner-retain
  :invariant fn-owner-retain-statep
  :installers (fn-owner-install-ocfg fn-owner-retain-carry-put)
  :carried-globals (fn-owner fn-owner-retain-carry)
  :at ((oc (fn-owner-ocfg state)))
  :bridge fn-owner-retain-statep-implies-lgoc
  :frame (fn-orh-retain-statep-of-other-global-put
          fn-orh-retain-statep-of-install-ocfg
          fn-orh-retain-statep-of-retain-carry-put
          fn-orh-retain-statep-of-install-served-effects
          fn-orh-retain-statep-of-put-credits)
  :theory (mv-nth nth zp car-cons cdr-cons
           (:executable-counterpart zp) (:executable-counterpart equal))
  ; the guard proofs: the accessors' frame and the store projection the
  ; carried conjuncts read (a writer adds its own :guard-theory)
  :guard-theory (fn-owner-ocfg-of-other-global-put fn-owner-bound-of-other-global-put
                 fn-owner-retain-carry-of-other-global-put
                 fn-owner-bound-of-install-ocfg fn-owner-ocfg-of-install-ocfg
                 fn-owner-retain-carry-of-install-ocfg
                 fn-owner-retain-statep-implies-entry-guard fn-sbud-oc-store)
  ; no :step here: fn-owner-step is host/owner-host.lisp's, absent from any
  ; book world; a writer through it says :step (fn-owner-step EVENT THM)
  :row fn-owner-retain-carried
  :suffix retain-state)

(defmacro def-owner-writer (fn &rest kvs)
  `(def-carried-writer ,fn :profile fn-owner-retain ,@kvs))
