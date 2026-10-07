;; fn: the owner's process record across the owner steps and the recovery
;; install (lane owner-globals-28).  books/owner-process.lisp defines the
;; record; this book proves where it travels.
;;
;;  (a) KEEPS: the owner steps that build their result with fn-own-make carry
;;      the input owner's record unchanged (fn-oproc-*-keeps-proc), so only
;;      fn-own-with-proc writes it (fn-oproc-own-with-proc-proc), and a fresh
;;      owner starts with the initial record (fn-oproc-own-start-proc-initial).
;;      Teeth: a mutant that resets the record to the initial one is false at
;;      a witness whose record is not the initial one.
;;  (b) CARRY: the recovery installs the owner the wrapper builds with
;;      fn-owner-carry-proc, and what is installed carries the record the
;;      process already had (fn-owner-recovery-carries-proc; the install
;;      installs the recovered ocfg exactly: fn-owner-install-extended-
;;      installs-oc, in books/owner-recovery-retain.lisp).
;;  (c) The serial's bump is the host's (host/owner-retain-host.lisp,
;;      fn-owner-sco-capture-serial-is-next).
(in-package "ACL2")
(include-book "owner-recovery-retain")
(include-book "owner-host-relation")
(include-book "defkeystone")

; -----------------------------------------------------------------------------
; (a) The writer, the fresh owner, the steps.

(defthm fn-oproc-own-with-proc-proc
  (equal (fn-own-proc (fn-own-with-proc o proc)) proc)
  :hints (("Goal" :in-theory (enable fn-own-with-proc))))

(defthm fn-oproc-own-with-proc-keeps-every-other-field
  (and (equal (fn-own-store (fn-own-with-proc o proc)) (fn-own-store o))
       (equal (fn-own-view (fn-own-with-proc o proc)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-with-proc o proc)) (fn-own-conns o))
       (equal (fn-own-next-id (fn-own-with-proc o proc)) (fn-own-next-id o))
       (equal (fn-own-max-conns (fn-own-with-proc o proc)) (fn-own-max-conns o))
       (equal (fn-own-pending (fn-own-with-proc o proc)) (fn-own-pending o))
       (equal (fn-own-ledger-field (fn-own-with-proc o proc)) (fn-own-ledger-field o))
       (equal (fn-own-clock (fn-own-with-proc o proc)) (fn-own-clock o))
       (equal (fn-own-facts (fn-own-with-proc o proc)) (fn-own-facts o))
       (equal (fn-own-config (fn-own-with-proc o proc)) (fn-own-config o))
       (equal (fn-own-queue (fn-own-with-proc o proc)) (fn-own-queue o))
       (equal (fn-own-inflight (fn-own-with-proc o proc)) (fn-own-inflight o))
       (equal (fn-own-feeds (fn-own-with-proc o proc)) (fn-own-feeds o))
       (equal (fn-own-node-secret (fn-own-with-proc o proc)) (fn-own-node-secret o))
       (equal (fn-own-refused (fn-own-with-proc o proc)) (fn-own-refused o)))
  :hints (("Goal" :in-theory (enable fn-own-with-proc))))


; the steps
(defthm fn-oproc-refresh-keeps-proc
  (equal (fn-own-proc (fn-own-refresh o)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-refresh))))

(defthm fn-oproc-set-conns-keeps-proc
  (equal (fn-own-proc (fn-own-set-conns o conns)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-set-conns))))

(defthm fn-oproc-enqueue-keeps-proc
  (equal (fn-own-proc (fn-own-enqueue o sub)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-enqueue))))

(defthm fn-oproc-close-keeps-proc
  (equal (fn-own-proc (fn-own-close o id)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-close))))

(defthm fn-oproc-begin-keeps-proc
  (equal (fn-own-proc (fn-own-begin o id)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-begin))))

(defthm fn-oproc-store-step-keeps-proc
  (equal (fn-own-proc (fn-own-store-step o event)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-store-step))))

(defthm fn-oproc-complete-keeps-proc
  (equal (fn-own-proc (fn-own-complete o)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-complete))))

(defthm fn-oproc-reopen-keeps-proc
  (equal (fn-own-proc (fn-own-reopen o frontier records)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-reopen))))

(defthm fn-oproc-observe-keeps-proc
  (equal (fn-own-proc (fn-own-observe o obs)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-observe))))

(defthm fn-oproc-declare-group-keeps-proc
  (equal (fn-own-proc (fn-own-declare-group o name)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-declare-group))))

(defthm fn-oproc-with-feeds-keeps-proc
  (equal (fn-own-proc (fn-own-with-feeds o feeds)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-with-feeds))))

(defthm fn-oproc-configure-keeps-proc
  (equal (fn-own-proc (fn-own-configure o config)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-configure))))

(defthm fn-oproc-with-node-secret-keeps-proc
  (equal (fn-own-proc (fn-own-with-node-secret o secret)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-with-node-secret))))

(defthm fn-oproc-take-submission-keeps-proc
  (equal (fn-own-proc (fn-own-take-submission o)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-take-submission))))

(defthm fn-oproc-control-outcome-keeps-proc
  (equal (fn-own-proc (fn-own-control-outcome o word)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-control-outcome))))

(defthm fn-oproc-advance-result-keeps-proc
  (equal (fn-own-proc (cdr (fn-own-advance-result o id))) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-advance-result))))
(defthm fn-oproc-advance-keeps-proc
  (equal (fn-own-proc (fn-own-advance o id)) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-advance))))

(defthm fn-oproc-open-keeps-proc
  (equal (fn-own-proc (cdr (fn-own-open o acfg))) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-open))))

(defthm fn-oproc-open-peer-keeps-proc
  (equal (fn-own-proc (cdr (fn-own-open-peer o peer cfg acfg))) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-open-peer))))

(defthm fn-oproc-outcome-keeps-proc
  (equal (fn-own-proc (cdr (fn-own-outcome o id word))) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-outcome))))

(defthm fn-oproc-transit-outcome-keeps-proc
  (equal (fn-own-proc (cdr (fn-own-transit-outcome o id kind reason word))) (fn-own-proc o))
  :hints (("Goal" :in-theory (enable fn-own-transit-outcome))))

(defthm fn-oproc-own-start-proc-initial
  (equal (fn-own-proc (fn-own-start store max-conns)) (fn-oproc-initial))
  :hints (("Goal" :in-theory (enable fn-own-start))))

;; The teeth of the steps whose construction is one fn-own-make and whose
;; arguments are plain values: the claim is false of the mutant that resets the
;; record to the initial one at an owner whose record is not the initial one.
(defteeth fn-oproc-configure-keeps-proc
  :claim (() (equal (fn-own-proc (fn-own-configure o config)) (fn-own-proc o)))
  :subject fn-own-configure
  :witness ((o (fn-own-make nil nil nil 0 4 nil nil nil nil nil nil nil nil nil nil (fn-oproc-make t 7)))
            (config nil))
  :breaks ()
  :mutations ((resets-the-record
               (:conclusion (equal (fn-own-proc (fn-own-configure o config)) (fn-oproc-initial)))
               ((o (fn-own-make nil nil nil 0 4 nil nil nil nil nil nil nil nil nil nil (fn-oproc-make t 7)))
                (config nil))
               :fault "a step that rebuilds the owner with the initial record")))
(defteeth fn-oproc-set-conns-keeps-proc
  :claim (() (equal (fn-own-proc (fn-own-set-conns o conns)) (fn-own-proc o)))
  :subject fn-own-set-conns
  :witness ((o (fn-own-make nil nil nil 0 4 nil nil nil nil nil nil nil nil nil nil (fn-oproc-make t 7)))
            (conns nil))
  :breaks ()
  :mutations ((resets-the-record
               (:conclusion (equal (fn-own-proc (fn-own-set-conns o conns)) (fn-oproc-initial)))
               ((o (fn-own-make nil nil nil 0 4 nil nil nil nil nil nil nil nil nil nil (fn-oproc-make t 7)))
                (conns nil))
               :fault "a step that rebuilds the owner with the initial record")))
(defteeth fn-oproc-with-feeds-keeps-proc
  :claim (() (equal (fn-own-proc (fn-own-with-feeds o feeds)) (fn-own-proc o)))
  :subject fn-own-with-feeds
  :witness ((o (fn-own-make nil nil nil 0 4 nil nil nil nil nil nil nil nil nil nil (fn-oproc-make t 7)))
            (feeds nil))
  :breaks ()
  :mutations ((resets-the-record
               (:conclusion (equal (fn-own-proc (fn-own-with-feeds o feeds)) (fn-oproc-initial)))
               ((o (fn-own-make nil nil nil 0 4 nil nil nil nil nil nil nil nil nil nil (fn-oproc-make t 7)))
                (feeds nil))
               :fault "a step that rebuilds the owner with the initial record")))
(defteeth fn-oproc-with-node-secret-keeps-proc
  :claim (() (equal (fn-own-proc (fn-own-with-node-secret o secret)) (fn-own-proc o)))
  :subject fn-own-with-node-secret
  :witness ((o (fn-own-make nil nil nil 0 4 nil nil nil nil nil nil nil nil nil nil (fn-oproc-make t 7)))
            (secret nil))
  :breaks ()
  :mutations ((resets-the-record
               (:conclusion (equal (fn-own-proc (fn-own-with-node-secret o secret)) (fn-oproc-initial)))
               ((o (fn-own-make nil nil nil 0 4 nil nil nil nil nil nil nil nil nil nil (fn-oproc-make t 7)))
                (secret nil))
               :fault "a step that rebuilds the owner with the initial record")))

; -----------------------------------------------------------------------------
; (b) The carry.

(defthm fn-owner-carry-proc-of-fault
  (equal (fn-owner-carry-proc :fault state) :fault)
  :hints (("Goal" :in-theory (enable fn-owner-carry-proc))))

(defthm fn-owner-carry-proc-not-fault
  (implies (and (boundp-global 'fn-owner state) (not (equal oc :fault)))
           (not (equal (fn-owner-carry-proc oc state) :fault)))
  :hints (("Goal" :in-theory (enable fn-owner-carry-proc fn-ocfg-with-owner
                                     fn-ocfg-make))))

(defthm fn-owner-carry-proc-proc
  (implies (and (boundp-global 'fn-owner state) (not (equal oc :fault)))
           (equal (fn-own-proc (fn-ocfg-owner (fn-owner-carry-proc oc state)))
                  (fn-own-proc (fn-ocfg-owner (f-get-global 'fn-owner state)))))
  :hints (("Goal" :in-theory (enable fn-owner-carry-proc fn-ocfg-with-owner
                                     fn-own-with-proc fn-owner-core))))

(defthm fn-owner-carry-proc-keeps-store-and-view
  (and (equal (fn-own-store (fn-ocfg-owner (fn-owner-carry-proc oc state)))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-view (fn-ocfg-owner (fn-owner-carry-proc oc state)))
              (fn-own-view (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-owner-carry-proc fn-ocfg-with-owner
                                     fn-own-with-proc))))

(defthm fn-onb-open-okp-reads-store-and-view-only
  (implies (and (equal (fn-own-store a) (fn-own-store b))
                (equal (fn-own-view a) (fn-own-view b)))
           (equal (fn-onb-open-okp a) (fn-onb-open-okp b)))
  :hints (("Goal" :in-theory (enable fn-onb-open-okp))))

(defthm fn-owner-carry-proc-keeps-open-okp
  (equal (fn-onb-open-okp (fn-ocfg-owner (fn-owner-carry-proc oc state)))
         (fn-onb-open-okp (fn-ocfg-owner oc)))
  :hints (("Goal" :use (fn-owner-carry-proc-keeps-store-and-view
                        (:instance fn-onb-open-okp-reads-store-and-view-only
                                   (a (fn-ocfg-owner (fn-owner-carry-proc oc state)))
                                   (b (fn-ocfg-owner oc))))
           :in-theory (disable fn-onb-open-okp-reads-store-and-view-only))))

(defthm fn-owner-carry-proc-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-owner-carry-proc oc state)))
  :hints (("Goal" :cases ((and (boundp-global 'fn-owner state) (not (equal oc :fault))))
           :in-theory (e/d (fn-owner-carry-proc)
                           (fn-ocfg-with-owner fn-ocfg-fault fn-ocfg-close fn-ocfg-advance
                            fn-ocfg-reconfigure fn-ocfg-pass fn-osb-install
                            fn-bs-profile-admittedp))
           :use ((:instance fn-ohr-with-proc-preserves-carried-relation
                            (oc oc)
                            (proc (fn-own-proc (fn-owner-core state))))))))

; KEYSTONE (b).  The recovery wrapper installs the owner it builds through
; fn-owner-carry-proc (host/owner-host.lisp fn-owner-recover-extended and
; fn-owner-recover-from-store-open, the two callers of
; fn-owner-install-extended); the process record after the install is the one
; before it, so the capture serial stays monotone across a second owner
; install of the process.  Premises: an owner was installed (else the fresh
; owner's initial record stands) and the install is not refused; both are
; the cases the claim is about.
(defthm fn-owner-recovery-carries-proc
  (implies (and (boundp-global 'fn-owner state)
                (not (equal oc :fault))
                (fn-onb-open-okp (fn-ocfg-owner oc)))
           (equal (fn-owner-proc
                   (mv-nth 5 (fn-owner-install-extended
                              (fn-owner-carry-proc oc state)
                              extended key fn-arena fn-cat fn-hist state)))
                  (fn-owner-proc state)))
  :hints (("Goal" :use ((:instance fn-owner-install-extended-installs-oc
                                   (oc (fn-owner-carry-proc oc state)))
                        (:instance fn-owner-install-extended-binds-owner
                                   (oc (fn-owner-carry-proc oc state)))
                        fn-owner-carry-proc-not-fault
                        fn-owner-carry-proc-proc
                        fn-owner-carry-proc-keeps-open-okp)
           :in-theory (e/d (fn-owner-proc fn-owner-core-is-configured-owner-by-definition)
                           (fn-owner-install-extended fn-owner-carry-proc)))))
