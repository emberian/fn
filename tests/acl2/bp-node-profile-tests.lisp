; Teeth of books/bp-node-profile.lisp and books/bp-node-profile-replay.lisp
; (PRF-131 part 2): the node's profile, its file, and replay under it.  A
; reachable witness per keystone; per hypothesis a witness that checks the
; retained hypotheses, the failure of the omitted one and of the conclusion,
; then a must-fail of the weakened theorem (its search cut short on purpose:
; the counterexample is the assert-event before it).
(in-package "ACL2")
(include-book "../../books/bp-node-profile-replay")
(include-book "bp-fnbs-family-replay-tests")
(include-book "std/testing/must-fail" :dir :system)

;; ---------------------------------------------------------------------------
;; fn-bpnpf-read-of-octets.  Witness: the profile SCN-067 runs under.
(assert-event
 (and (fn-bpnpf-validp 128 16777216)
      (equal (fn-bpnpf-read t (fn-bpnpf-octets 128 16777216)) '(128 16777216))
      (equal (fn-bpnpf-read nil nil) (list 64 16777216))
      (< (len (fn-bpnpf-octets 16777216 16777216)) (fn-bpnpf-read-bound))))
;; Without validity: zero rows is not a profile; no octets, no profile.
(assert-event
 (and (not (fn-bpnpf-validp 0 16777216))
      (not (equal (fn-bpnpf-read t (fn-bpnpf-octets 0 16777216)) '(0 16777216)))))
(must-fail
 (defthm bpnpft-read-without-validity
   (equal (fn-bpnpf-read t (fn-bpnpf-octets rows octets)) (list rows octets))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))
;; A frame with a trailing octet, or another format, is refused.
(assert-event
 (and (null (fn-bpnpf-read t (append (fn-bpnpf-octets 128 16777216) '(0))))
      (null (fn-bpnpf-read t (fn-frame-fields-octets
                              *fn-bpnpf-spec*
                              (list '(120) 128 16777216))))))

;; ---------------------------------------------------------------------------
;; fn-bpnpf-valid-profile-opens.
(defconst *bpnpft-config*
  (fn-bpn-config (cons :dtn '(47 47 102 110 45 97 47)) 3600000 2 32 1048576))
(assert-event
 (let ((st (fn-bpn-initial-machine-state *bpnpft-config* 128 16777216)))
   (and (fn-bpn-configp *bpnpft-config*) (fn-bpnpf-validp 128 16777216)
        (fn-bpn-machine-statep st)
        (equal (fn-bpn-machine-state-max-jobs st) 128)
        (equal (fn-bpn-machine-state-max-octets st) 16777216))))
;; Without validity: 2^24 + 1 rows opens no machine.
(assert-event
 (and (fn-bpn-configp *bpnpft-config*)
      (not (fn-bpnpf-validp 16777217 16777216))
      (not (fn-bpn-machine-statep
            (fn-bpn-initial-machine-state *bpnpft-config* 16777217 16777216)))))
(must-fail
 (defthm bpnpft-opens-without-validity
   (implies (fn-bpn-configp config)
            (fn-bpn-machine-statep (fn-bpn-initial-machine-state config rows octets)))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))
;; Without a configuration: none opens.
(assert-event
 (and (fn-bpnpf-validp 128 16777216) (not (fn-bpn-configp nil))
      (not (fn-bpn-machine-statep (fn-bpn-initial-machine-state nil 128 16777216)))))
(must-fail
 (defthm bpnpft-opens-without-config
   (implies (fn-bpnpf-validp rows octets)
            (fn-bpn-machine-statep (fn-bpn-initial-machine-state config rows octets)))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------------
;; fn-bpnpf-write-never-lowers.  Witness: default to 128 rows is admitted;
;; 128 back to 32 is refused.
(assert-event
 (let ((w (fn-bpnpf-write-octets (fn-bpnpf-default) 128 16777216)))
   (and w (equal (fn-bpnpf-read t w) '(128 16777216)))))
(assert-event (null (fn-bpnpf-write-octets '(128 16777216) 32 16777216)))
(assert-event (null (fn-bpnpf-write-octets '(128 16777216) 128 1024)))

;; ---------------------------------------------------------------------------
;; fn-bpnpf-replay-past-the-profile-is-refused, over the two durable kind-5
;; rows of the family-replay teeth.  A base whose profile holds one row.
(defun bpnpft-base (rows)
  (let ((b (fn-bpnf-base *bpnff-state*)))
    (fn-bpn-make-machine-state
     (fn-bpn-machine-state-config b) (fn-bpn-machine-state-jobs b)
     (fn-bpn-machine-state-contacts b) (fn-bpn-machine-state-pending b)
     (fn-bpn-machine-state-fenced b) (fn-bpn-machine-state-next-token b)
     rows (fn-bpn-machine-state-max-octets b))))
(defun bpnpft-prefix () (list (car (bpnfr-replay-rows))))
(defun bpnpft-row () (cadr (bpnfr-replay-rows)))
(defun bpnpft-r (rows)
  (fn-bpnf-family-replay-rows-aux (bpnpft-prefix) (bpnpft-base rows) nil nil nil 0))
(assert-event
 (let ((r (bpnpft-r 1)))
   (and (true-listp (bpnpft-prefix))
        (equal (car r) :ready)
        (fn-bpnpf-kind-five-row-fitsp (bpnpft-row) (fn-bpn-nth 1 r)
                                      (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))
        (<= 1 (len (fn-bpn-nth 1 r)))
        (equal (fn-bpnf-family-replay-rows-aux
                (append (bpnpft-prefix) (list (bpnpft-row)))
                (bpnpft-base 1) nil nil nil 0)
               '(:fault :held-beyond-profile)))))
;; Without the bound reached (a profile of two rows): the same rows replay
;; :ready and hold both.
(assert-event
 (let ((r (bpnpft-r 2)))
   (and (equal (car r) :ready)
        (fn-bpnpf-kind-five-row-fitsp (bpnpft-row) (fn-bpn-nth 1 r)
                                      (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))
        (not (<= 2 (len (fn-bpn-nth 1 r))))
        (equal (car (fn-bpnf-family-replay-rows-aux
                     (append (bpnpft-prefix) (list (bpnpft-row)))
                     (bpnpft-base 2) nil nil nil 0))
               :ready)
        (equal (len (nth 1 (fn-bpnf-family-replay-rows-aux
                            (append (bpnpft-prefix) (list (bpnpft-row)))
                            (bpnpft-base 2) nil nil nil 0)))
               2))))
;; Without the row fitting (the first row again: not fresh): a different
;; fault, not the profile's verdict.
(assert-event
 (let ((r (bpnpft-r 1)))
   (and (equal (car r) :ready)
        (not (fn-bpnpf-kind-five-row-fitsp (car (bpnpft-prefix)) (fn-bpn-nth 1 r)
                                           (fn-bpn-nth 3 r) (fn-bpn-nth 4 r)))
        (not (equal (fn-bpnf-family-replay-rows-aux
                     (append (bpnpft-prefix) (bpnpft-prefix))
                     (bpnpft-base 1) nil nil nil 0)
                    '(:fault :held-beyond-profile))))))
