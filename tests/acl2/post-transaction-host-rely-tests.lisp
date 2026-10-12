; HOST-run witnesses and the excluded eight-byte capacity counterexample.
(in-package "ACL2")
(include-book "../../books/post-transaction-host-rely")
(set-verify-guards-eagerness 0)
; This checked instance is precisely the encapsulate's local acceptance witness.
(defun pthrt-acc-begin (txid) (declare (xargs :guard t) (ignore txid)) nil)
(defun pthrt-acc-feed (a bytes) (declare (xargs :guard t) (ignore a bytes)) (mv nil nil))
(defun pthrt-acc-feed-cost (a bytes) (declare (xargs :guard t) (ignore a bytes)) 0)
(defun pthrt-acc-end (a blen) (declare (xargs :guard t) (ignore a blen)) (mv t nil nil 0 nil nil))
(defun pthrt-acc-max-state () (declare (xargs :guard t)) 1)
(defun pthrt-acc-out-max () (declare (xargs :guard t)) 0)
(verify-guards pthrt-acc-begin)
(verify-guards pthrt-acc-feed)
(verify-guards pthrt-acc-feed-cost)
(verify-guards pthrt-acc-end)
(verify-guards pthrt-acc-max-state)
(verify-guards pthrt-acc-out-max)
(defattach (fn-ptx-acc-begin pthrt-acc-begin) (fn-ptx-acc-feed pthrt-acc-feed)
  (fn-ptx-acc-feed-cost pthrt-acc-feed-cost) (fn-ptx-acc-end pthrt-acc-end)
  (fn-ptx-acc-max-state pthrt-acc-max-state) (fn-ptx-acc-out-max pthrt-acc-out-max))

(defconst *pthrt-article* '(70 114 111 109 58 97 13 10 68 97 116 101 58 84 104 117 44 32 49 32 74 97 110 32 49 57 55 48 32 48 48 58 48 48 58 48 48 32 43 48 48 48 48 13 10 78 101 119 115 103 114 111 117 112 115 58 120 13 10 83 117 98 106 101 99 116 58 120 13 10 77 101 115 115 97 103 101 45 73 68 58 60 120 64 121 62 13 10 13 10 120))
(defconst *pthrt-post* (append '(1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) *pthrt-article*))
(defconst *pthrt-red-cfg* '(3 9 8 1 4 1 256 4 8))
(defthm pthrt-red-config-is-valid (fn-rtc-configp *pthrt-red-cfg*))
(defthm pthrt-red-config-is-outside-host-domain
 (not (equal *pthrt-red-cfg*
       (fn-hl-rtc-config profile mcfg q *fn-pth-nstatic* 0 0 *fn-pth-qs* *fn-pth-cs*)))
 :hints (("Goal" :use ((:instance fn-pth-host-config-holds-the-workspace (h 0)))
          :in-theory (union-theories (theory 'minimal-theory)
            '(fn-rtc-capf-static (:executable-counterpart fn-rtc-capf-static)
              (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
              (:executable-counterpart equal))))))
; An observation retains the op, its whole pre/post states, the actual extracted
; owner delivery, refusals and messages. No host decision bypasses requests.
(defun pthrt-drive-op (op q fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard t))
  (let* ((before (fn-rtc-x-state fn-rtc-st))
         (m (fn-rtc-st-mstate 1 fn-rtc-st))
         (w (fn-ptx-message m 1 1 fn-rtc-st)))
    (case (fn-rtc-get 0 op)
      (:complete
       (mv-let (deliveredp ev) (fn-pth-owner-delivery before (fn-rtc-get 1 op) q)
         (mv-let (fn-rtc-st acts refused cost) (fn-pth-x-step* (fn-rtc-get 1 op) q fn-rtc-st)
           (declare (ignore cost))
           (let* ((after (fn-rtc-x-state fn-rtc-st))
                  (w2 (fn-ptx-message (fn-rtc-st-mstate 1 fn-rtc-st) 1 1 fn-rtc-st)))
             (prog2$ (cw "COMPLETE ~x0 owner=~x1 phase ~x2 -> ~x3 acts=~x4 refused=~x5~%"
                          (fn-rtc-get 1 op) deliveredp (fn-ptx-ph m)
                          (fn-ptx-ph (fn-rtc-st-mstate 1 fn-rtc-st)) acts refused)
               (mv fn-rtc-st (list op before after deliveredp ev refused w w2) acts))))))
      (:request
       (if (equal (fn-rtc-get 1 op) 1)
           (mv fn-rtc-st (list op before before nil nil nil w w) nil)
         (mv-let (fn-rtc-st acts refused cost)
           (fn-rtc-x-requests (fn-rtc-get 3 op) (fn-rtc-get 1 op) (fn-rtc-get 2 op) fn-rtc-st)
           (declare (ignore cost))
           (prog2$ (cw "REQUEST id=~x0 inc=~x1 acts=~x2 refused=~x3~%"
                       (fn-rtc-get 1 op) (fn-rtc-get 2 op) acts refused)
             (mv fn-rtc-st (list op before (fn-rtc-x-state fn-rtc-st) nil nil refused w
                            (fn-ptx-message (fn-rtc-st-mstate 1 fn-rtc-st) 1 1 fn-rtc-st)) acts)))))
      (otherwise (mv fn-rtc-st (list op before before nil nil nil w w) nil)))))

(defun pthrt-completion (a)
  (let ((kind (fn-rtc-get 0 a)))
    (append (fn-rtc-key a)
            (list (list :done (if (equal kind :pwrite)
                                 (fn-rtc-h-len (fn-rtc-get 0 (fn-rtc-get 4 a))) 0)))
            (if (equal kind :opened)
                (list (fn-rtc-e-data (car *fn-pth-rely-events0*))) nil))))
(defun pthrt-drain (fuel pending q fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory
                           (union-theories (theory 'minimal-theory)
                             '(nfix zp natp o-p o-finp o<))))))
  (if (or (zp fuel) (atom pending))
      (mv fn-rtc-st nil pending)
    (mv-let (fn-rtc-st obs acts)
      (pthrt-drive-op (list :complete (pthrt-completion (car pending))) q fn-rtc-st)
      (mv-let (fn-rtc-st rest left) (pthrt-drain (1- (nfix fuel)) (append (cdr pending) acts) q fn-rtc-st)
        (mv fn-rtc-st (cons obs rest) left)))))


(defun pthrt-execute (cfg fn-rtc-st)
 (declare (xargs :stobjs fn-rtc-st :guard t))
 (mv-let (fn-rtc-st acts) (fn-pth-x-init cfg fn-rtc-st)
  (mv-let (fn-rtc-st prefix left) (pthrt-drain 8 acts 100000 fn-rtc-st)
   (declare (ignore left))
   (let* ((h (fn-rtc-nhome cfg)) (g (fn-rtc-st-gen h fn-rtc-st))
          (op (list :request 2 1
             (list (list :write h g 0 *pthrt-post*)
                   (list :submit :hand (list h g 0 (len *pthrt-post*)) '(1 1))))))
    (mv-let (fn-rtc-st hand acts) (pthrt-drive-op op 100000 fn-rtc-st)
     (mv-let (fn-rtc-st tail pending) (pthrt-drain 24 acts 100000 fn-rtc-st)
       (declare (ignore pending))
       (mv fn-rtc-st (append prefix (list hand) tail))))))))
(defun pthrt-local (cfg)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-rtc-st
  (mv-let (fn-rtc-st obs) (pthrt-execute cfg fn-rtc-st) obs)))
(make-event (value `(defconst *pthrt-host-observations* ',(pthrt-local *fn-pth-rely-cfg*))))
(make-event (value `(defconst *pthrt-red-observations* ',(pthrt-local *pthrt-red-cfg*))))
(assert-event (equal (nth 5 (nth 6 *pthrt-red-observations*))
                    '((:write 1 1 0 (0 0 0 0 0 0 0 0 0)))))
(defun pthrt-ops (obs)
 (if (consp obs) (cons (car (car obs)) (pthrt-ops (cdr obs))) nil))
(defconst *pthrt-prefix-ops* (pthrt-ops (take 5 *pthrt-host-observations*)))
(defconst *pthrt-ready-state* (nth 1 (nth 5 *pthrt-host-observations*)))
(defconst *pthrt-hand-op* (car (nth 5 *pthrt-host-observations*)))
(defun-nx pthrt-reading-state ()
 (fn-pth-host-run
   (fn-pth-host-run (mv-nth 0 (fn-pth-init *fn-pth-rely-cfg*)) *pthrt-prefix-ops* 100000)
   (list *pthrt-hand-op*) 100000))
(defthm pthrt-host-run-of-append
 (equal (fn-pth-host-run s (append ops0 ops1) q)
        (fn-pth-host-run (fn-pth-host-run s ops0 q) ops1 q))
 :hints (("Goal" :induct (fn-pth-host-run s ops0 q)
          :in-theory (union-theories (theory 'minimal-theory)
                     '(fn-pth-host-run append car-cons cdr-cons)))))
(defthm pthrt-reading-state-is-reachable-by-definition
 (fn-pth-reachablep (pthrt-reading-state))
 :hints (("Goal" :use ((:instance fn-pth-reachablep-suff
    (s (pthrt-reading-state)) (profile *fn-bs-profile-development*)
    (mcfg *fn-pth-rely-mcfg*) (q0 100000)
    (ops0 (append *pthrt-prefix-ops* (list *pthrt-hand-op*))))
        (:instance pthrt-host-run-of-append
          (s (mv-nth 0 (fn-pth-init *fn-pth-rely-cfg*)))
          (ops0 *pthrt-prefix-ops*) (ops1 (list *pthrt-hand-op*)) (q 100000)))
    :in-theory (union-theories (theory 'minimal-theory)
        '(pthrt-reading-state pthrt-host-run-of-append
          (:executable-counterpart fn-rtc-configp) (:executable-counterpart fn-rtc-nstatic)
          (:executable-counterpart fn-hl-rtc-config) (:executable-counterpart binary-append)
          (:executable-counterpart natp))))))
; Fold the concrete prefix one completion at a time, so each proof
; handles one generated dispatch rather than an expanded five-step term.
(make-event
 (cons 'progn
  (loop$ for i in '(0 1 2 3) collect
   (let* ((o (nth i *pthrt-host-observations*))
          (name (intern-in-package-of-symbol
                  (concatenate 'string "PTHRT-PREFIX-STEP-"
                    (coerce (explode-nonnegative-integer i 10 nil) 'string)) 'fn-pth)))
    `(defthm ,name
      (equal (mv-nth 0 (fn-pth-step ',(nth 1 o) ',(nth 1 (nth 0 o)) 100000)) ',(nth 2 o))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             (union-theories
               '(fn-hlm-step fn-hlm-init fn-pth-accept-branch fn-pth-host-run fn-pth-step fn-pth-step* fn-pth-deliver fn-pth-m-step
                 fn-pthm-step fn-ptx-step fn-ptx-step1 fn-ptx-wfp fn-ptx-size-rem
                 fn-ptx-wf-cost car-cons cdr-cons fn-rtc-requests fn-rtc-with-mstate fn-rtc-make
                 fn-rtc-set fn-rtc-mstates fn-rtc-rearm)
               (set-difference-theories (executable-counterpart-theory :here)
                 '((:executable-counterpart fn-hlm-step) (:executable-counterpart fn-pth-accept-branch) (:executable-counterpart fn-pth-reachablep)
                   (:executable-counterpart fn-pth-host-run) (:executable-counterpart fn-pth-step)
                   (:executable-counterpart fn-pth-step*) (:executable-counterpart fn-pth-deliver)
                   (:executable-counterpart fn-pth-m-step) (:executable-counterpart fn-pthm-step)
                   (:executable-counterpart fn-ptx-step) (:executable-counterpart fn-ptx-step1)
                   (:executable-counterpart fn-ptx-wfp) (:executable-counterpart fn-ptx-wf-cost)))))
           :use ((:instance fn-ptx-size-pos (x (fn-ptx-acc-begin 0)))
                 (:instance fn-ptx-acc-begin-bounded (txid 0))))))))))
(make-event
 (let ((o (nth 4 *pthrt-host-observations*)))
  `(defthm pthrt-prefix-request
    (equal (mv-nth 0 (fn-rtc-requests ',(nth 3 (nth 0 o)) 2 1 ',(nth 1 o))) ',(nth 2 o)))))
(make-event
 `(defthm pthrt-prefix-init
   (equal (mv-nth 0 (fn-pth-init *fn-pth-rely-cfg*))
          ',(nth 1 (car *pthrt-host-observations*)))
    :hints (("Goal" :in-theory
      (union-theories (theory 'minimal-theory)
        '((:executable-counterpart fn-pth-init) (:executable-counterpart mv-nth)))))))
(defthm pthrt-prefix-reaches-ready-state
 (equal (fn-pth-host-run (mv-nth 0 (fn-pth-init *fn-pth-rely-cfg*))
                         *pthrt-prefix-ops* 100000) *pthrt-ready-state*)
 :hints (("Goal" :in-theory
   (union-theories (theory 'minimal-theory)
    (union-theories
     '(fn-pth-host-run pthrt-prefix-init pthrt-prefix-request
       pthrt-prefix-step-0 pthrt-prefix-step-1 pthrt-prefix-step-2 pthrt-prefix-step-3
       car-cons cdr-cons)
     (set-difference-theories (executable-counterpart-theory :here)
      '((:executable-counterpart fn-pth-host-run) (:executable-counterpart fn-pth-step))))))))
(defthm pthrt-ready-state-is-invariant
 (fn-pth-invp *pthrt-ready-state*)
 :hints (("Goal" :in-theory
  (union-theories
   '(fn-pth-invp fn-pth-mstates-okp fn-pthm-max-state fn-ptx-max-state
     fn-ptx-acc-max-state-natp max natp car-cons cdr-cons
     (:compound-recognizer natp-compound-recognizer))
   (union-theories (theory 'minimal-theory)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-pth-invp)
       (:executable-counterpart fn-pth-mstates-okp)
       (:executable-counterpart fn-pthm-max-state)
       (:executable-counterpart fn-ptx-max-state))))))))
(defthm pthrt-host-run-one-completion
 (equal (fn-pth-host-run s (list (list :complete e)) q)
        (mv-nth 0 (fn-pth-step s e q)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-host-run fn-rtc-get-of-cons car-cons cdr-cons
    (:executable-counterpart fn-rtc-get) (:executable-counterpart zp)
    (:executable-counterpart nfix))))))
(defthm pthrt-nil-acc-fits
 (fn-ptx-size-rem nil (fn-ptx-acc-max-state))
 :hints (("Goal" :use ((:instance fn-ptx-size-rem-intro
                         (x nil) (n (fn-ptx-acc-max-state)))
                       (:instance fn-ptx-size-pos (x (fn-ptx-acc-begin 0)))
                       (:instance fn-ptx-acc-begin-bounded (txid 0)))
  :in-theory (union-theories (theory 'minimal-theory)
    '(fn-ptx-acc-max-state-natp (:executable-counterpart fn-rtc-size)
      natp (:executable-counterpart natp))))))
(defthm pthrt-reading-state-is-reading
 (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates (pthrt-reading-state)))) :reading)
 :hints (("Goal" :use (pthrt-prefix-reaches-ready-state (:instance fn-pth-owner-delivered-mstate
   (s *pthrt-ready-state*) (e (nth 1 *pthrt-hand-op*)) (q 100000))
   pthrt-nil-acc-fits)
 :in-theory (union-theories (theory 'minimal-theory)
  (union-theories
    '(pthrt-reading-state pthrt-prefix-reaches-ready-state pthrt-ready-state-is-invariant
      pthrt-host-run-one-completion fn-pthm-step fn-ptx-step fn-ptx-step1 fn-ptx-start fn-ptx-mk
      fn-ptx-wfp pthrt-nil-acc-fits fn-ptx-size-rem-intro fn-ptx-acc-max-state-natp fn-ptx-ph fn-rtc-get
      car-cons cdr-cons)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-pth-init) (:executable-counterpart pthrt-reading-state)
       (:executable-counterpart fn-pth-host-run) (:executable-counterpart fn-pth-step)
       (:executable-counterpart fn-pthm-step) (:executable-counterpart fn-ptx-step)
       (:executable-counterpart fn-ptx-step1) (:executable-counterpart fn-ptx-start)
       (:executable-counterpart fn-ptx-wfp))))))))

; R1's old counterexample, with the actual whole-delivery POST-ST added.
(defconst *pthrt-r1-op* (nth 0 (nth 6 *pthrt-host-observations*)))
(defconst *pthrt-r1-m* (nth 1 (fn-rtc-mstates (nth 1 (nth 6 *pthrt-host-observations*)))))
(defconst *pthrt-r1-m2* (nth 1 (fn-rtc-mstates (nth 2 (nth 6 *pthrt-host-observations*)))))
(defconst *pthrt-r1-v* (fn-rtc-view-state 1 1 (nth 1 (nth 6 *pthrt-host-observations*))))
(defconst *pthrt-r1-ev* (nth 4 (nth 6 *pthrt-host-observations*)))
(defconst *pthrt-r1-post-v*
 (fn-rtc-view-state 1 1 (nth 2 (nth 6 *pthrt-host-observations*))))
(defconst *pthrt-r1-trace*
 (list (list *pthrt-r1-ev* *pthrt-r1-v* 100000 :ok *pthrt-r1-post-v*)))
; The only mutation is field 4 := field 1.  It reconstructs exactly the
; old final ST2 convention, while every current trace still has five fields.
(defconst *pthrt-r1-old-mutant-trace*
 (list (update-nth 4 (nth 1 (car *pthrt-r1-trace*))
                   (car *pthrt-r1-trace*))))
(assert-event
 (and (equal (len (car *pthrt-r1-trace*)) 5)
      (equal (take 4 (car *pthrt-r1-old-mutant-trace*))
             (take 4 (car *pthrt-r1-trace*)))
      (equal (nth 4 (car *pthrt-r1-old-mutant-trace*)) *pthrt-r1-v*)
      (equal (nth 4 (car *pthrt-r1-trace*)) *pthrt-r1-post-v*)
      (not (equal *pthrt-r1-v* *pthrt-r1-post-v*))))
; M2 is captured from the actual product executor on this timer, using the
; checked acceptance instance above.  Test fn-ptx-rely on that very pair;
; the constrained signature's attachment is not used as a proof rewrite.
(defthm pthrt-pre-step-post-st-mutant-fails-the-rely
 (not (fn-ptx-rely *pthrt-r1-m* *pthrt-r1-m2* 1 1
                   (nth 1 (car *pthrt-r1-old-mutant-trace*))
                   (nth 4 (car *pthrt-r1-old-mutant-trace*))))
 :hints (("Goal" :in-theory
  (union-theories '(fn-ptx-rely)
   (union-theories (theory 'minimal-theory)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-ptx-rely))))))))
(defthm pthrt-old-final-reading-entry-refutes-the-rely
 (not (fn-ptx-rely *pthrt-r1-m* *pthrt-r1-m2* 1 1 *pthrt-r1-v* *pthrt-r1-v*))
 :hints (("Goal" :use pthrt-pre-step-post-st-mutant-fails-the-rely
          :in-theory
  (union-theories (theory 'minimal-theory)
   '((:executable-counterpart nth) (:executable-counterpart car))))))
(defthm pthrt-real-post-st-keeps-the-rely
 (fn-ptx-rely *pthrt-r1-m* *pthrt-r1-m2* 1 1
              (nth 1 (car *pthrt-r1-trace*))
              (nth 4 (car *pthrt-r1-trace*)))
 :hints (("Goal" :in-theory
  (union-theories '(fn-ptx-rely)
   (union-theories (theory 'minimal-theory)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-ptx-rely))))))))
(assert-event (and (equal (fn-ptx-ph *pthrt-r1-m*) :reading)
                   (equal (fn-ptx-ph *pthrt-r1-m2*) :hashing)
                   (nth 3 (nth 6 *pthrt-host-observations*))
                   (not (nth 5 (nth 6 *pthrt-host-observations*)))))
(value-triple
 (cw "R5 TEETH: s=(pthrt-reading-state), host cfg=~x0 q=100000 ops=(~x1); delivered event=~x2; reading->hashing; old POST-ST:=ST relies NIL; real whole-delivery POST-ST relies T; runtime refused NIL. Checked acceptance is the encapsulate's local witness.~%"
  *fn-pth-rely-cfg* *pthrt-r1-op* *pthrt-r1-ev*))
