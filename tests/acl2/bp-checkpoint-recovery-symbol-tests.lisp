; Malformed stored-data witness, not a reachable healthy producer fixture.
; Typed recovery refuses an unknown handoff symbol with a named verdict.
; This is a tightened acceptance boundary, not legacy all-input equivalence.
(in-package "ACL2")
(include-book "../../books/bp-node-rotation")
(defconst *fn-bpckrs-config*
  (fn-bpn-config (cons :dtn '(47 47 102 110 45 97 47)) 3600000 2 32 1048576))
(defconst *fn-bpckrs-base* (fn-bpn-initial-machine-state *fn-bpckrs-config* 4 1048576))
(defconst *fn-bpckrs-state* (fn-bpnf-state *fn-bpckrs-base* nil nil nil nil nil nil 0 0))
(defconst *fn-bpckrs-corrupt*
  (fn-bpnr-checkpoint 1 nil '(:bpck-unknown-symbol-witness) nil 0 0))
(assert-event
 (let* ((plan (list :selected *fn-bpckrs-corrupt*))
        (event (append (fn-bpnr-recover-auto-event *fn-bpckrs-state* nil :ready nil plan)
                       '((:initialize))))
        (answer (fn-bpnp-step *fn-bpckrs-state* event)))
   (and (fn-bpnr-checkpointp *fn-bpckrs-corrupt*)
        (fn-bpnr-enc *fn-bpckrs-corrupt* 32)
        (not (fn-bpnf-handoffp :bpck-unknown-symbol-witness))
        (fn-bpn-machine-statep *fn-bpckrs-base*)
        (fn-bpnp-session-listp (fn-bpnp-sessions *fn-bpckrs-state*))
        (true-listp (fn-bpnf-held-list *fn-bpckrs-state*))
        (fn-bpnp-host-eventp event)
        (equal (fn-bpnf-answer-effects answer) '((:restart-fault :handoff-shape)))
        (equal (fn-bpnf-base (fn-bpnf-answer-state answer)) *fn-bpckrs-base*)
        (equal (fn-bpnf-epoch (fn-bpnf-answer-state answer)) 0)
        (null (fn-bpnf-held-list (fn-bpnf-answer-state answer)))
        (null (fn-bpnf-handoffs (fn-bpnf-answer-state answer))))))
(defthm fn-bpckrs-corrupt-encoding-exists
 (consp (fn-bpnr-checkpoint-octets *fn-bpckrs-corrupt* 32))
 :hints (("Goal" :in-theory
          (e/d (fn-bpnr-checkpoint-octets fn-bpnr-checkpoint-prefix)
               (fn-frame-trailer (:executable-counterpart fn-frame-trailer)
                (:executable-counterpart fn-bpnr-checkpoint-octets)))))
 :rule-classes nil)
(defthm fn-bpckrs-encoded-checkpoint-recovery-refuses-unknown-symbol
 (let* ((decoded (fn-bpnr-checkpoint-decode
                  (fn-bpnr-checkpoint-octets *fn-bpckrs-corrupt* 32) 32))
        (plan (list :selected decoded))
        (event (append (fn-bpnr-recover-auto-event *fn-bpckrs-state* nil :ready nil plan)
                       '((:initialize))))
        (answer (fn-bpnp-step *fn-bpckrs-state* event)))
   (and (equal decoded *fn-bpckrs-corrupt*)
        (equal (fn-bpnf-answer-effects answer) '((:restart-fault :handoff-shape)))
        (equal (fn-bpnf-base (fn-bpnf-answer-state answer)) *fn-bpckrs-base*)
        (equal (fn-bpnf-epoch (fn-bpnf-answer-state answer)) 0)
        (null (fn-bpnf-held-list (fn-bpnf-answer-state answer)))
        (null (fn-bpnf-handoffs (fn-bpnf-answer-state answer)))))
 :hints (("Goal" :use (fn-bpckrs-corrupt-encoding-exists (:instance fn-bpnr-checkpoint-decode-of-octets
                                 (ck *fn-bpckrs-corrupt*) (budget 32)))
         :in-theory (disable fn-bpnr-checkpoint-decode fn-bpnr-checkpoint-octets
                             fn-bpnr-checkpoint-decode-of-octets
                             (:executable-counterpart fn-bpnr-checkpoint-octets)
                             (:executable-counterpart fn-bpnr-checkpoint-decode)
                             (:executable-counterpart fn-bpnr-recover-auto-event))))
 :rule-classes nil)
