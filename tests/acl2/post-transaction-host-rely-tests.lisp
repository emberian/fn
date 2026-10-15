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
(defconst *pthrt-post* (append (fn-pctx-encode '(1 nil nil 0 nil nil 0)) *pthrt-article*))
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
; Amendment 5: the eight-byte homes fail closed before any workspace
; write. The concrete reply contains refusal code 1 and is handed back.
(assert-event
 (let* ((o (nth 6 *pthrt-red-observations*))
        (before (nth 1 o)) (after (nth 2 o))
        (reply (fn-rtc-buffer 8 after)))
  (and (equal (nth 5 o) nil)
       (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates before))) :reading)
       (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates after))) :idle)
       (equal (car (fn-rtc-b-bytes reply)) 1)
       (equal (fn-rtc-b-owner reply) '(:handed 1 1 2 1))
       (equal (fn-rtc-find-use '(:hand 1 1 6) (fn-rtc-uses after))
              '(:hand 1 1 6 (8 3 0 124))))))
(defthm mhalf6-old-red-single-refusal-expectation-is-refuted
 (not (equal (nth 5 (nth 6 *pthrt-red-observations*))
             '((:write 1 1 0 (0 0 0 0 0 0 0 0 0))))) :rule-classes nil)
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
          (:executable-counterpart fn-rtc-st-cfg-okp)
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

; R8: full R6 HOST ops, old acceptance and the actual bounded-extent machine.
; The only old mutation removes the approved extent conjunct; every dispatch
; and executor body is taken from its actual source event.
(defconst *pthrt-r6-open-data*
 (list (list 0 (make-list 32 :initial-element 0) 18446744073709551616 1 0)
       18446744073709555712 '(1 256 256)))
(defun pthrt-r6-completion (a)
 (let ((e (pthrt-completion a)))
  (if (equal (car a) :opened) (update-nth 5 *pthrt-r6-open-data* e) e)))
(defun pthrt-r8-rename (tree alist)
 (declare (xargs :guard t :measure (acl2-count tree)))
 (if (consp tree)
  (cons (pthrt-r8-rename (car tree) alist) (pthrt-r8-rename (cdr tree) alist))
  (let ((pair (assoc-equal tree alist))) (if pair (cdr pair) tree))))
(defun pthrt-r8-remove-extent (tree)
 (declare (xargs :guard t :measure (acl2-count tree)))
 (if (consp tree)
  (if (equal (car tree) '(< (nfix (fn-rtc-get 1 d)) (expt 2 64)))
   (pthrt-r8-remove-extent (cdr tree))
   (cons (pthrt-r8-remove-extent (car tree)) (pthrt-r8-remove-extent (cdr tree)))) tree))
(defun pthrt-r8-count-extent (tree)
 (declare (xargs :guard t :measure (acl2-count tree)))
 (if (equal tree '(< (nfix (fn-rtc-get 1 d)) (expt 2 64))) 1
  (if (consp tree) (+ (pthrt-r8-count-extent (car tree)) (pthrt-r8-count-extent (cdr tree))) 0)))
(make-event
 (let ((event (get-event 'fn-ptx-step1 (w state))))
  (if (equal (pthrt-r8-count-extent event) 1)
   (value '(value-triple :one-authorized-conjunct))
   (er soft 'pthrt-r8-old-open "Expected exactly one extent conjunct."))))
(defun pthrt-r8-copy-events (events alist)
 (declare (xargs :guard t :measure (acl2-count events)))
 (if (consp events)
  (let ((event (car events)))
   (cons (pthrt-r8-rename
          (if (equal (cadr event) 'fn-ptx-step1) (pthrt-r8-remove-extent event) event) alist)
         (pthrt-r8-copy-events (cdr events) alist))) nil))
(make-event
 (let* ((world (w state))
       (alist '((fn-ptx-step1 . pthrt-r6-old-step1) (fn-ptx-step . pthrt-r6-old-step)
               (fn-pthm-step . pthrt-r6-old-machine) (fn-pth-x-deliver . pthrt-r6-old-deliver)
               (fn-pth-x-step* . pthrt-r6-old-layer) (pthrt-drive-op . pthrt-r6-old-drive)
               (pthrt-completion . pthrt-r6-completion) (pthrt-drain . pthrt-r6-old-drain)
               (pthrt-execute . pthrt-r6-old-execute) (pthrt-local . pthrt-r6-old-local)))
       (events (list
          (get-event 'fn-ptx-step1 world)
          (get-event 'fn-ptx-step world)
          (get-event 'fn-pthm-step world)
          (get-event 'fn-pth-x-deliver world)
          (get-event 'fn-pth-x-step* world)
          (get-event 'pthrt-drive-op world)
          (get-event 'pthrt-drain world)
          (get-event 'pthrt-execute world)
          (get-event 'pthrt-local world)
          )))
  (cons 'progn (pthrt-r8-copy-events events alist))))
(make-event (value `(defconst *pthrt-r6-old-observations* ',(pthrt-r6-old-local *fn-pth-rely-cfg*))))
(defconst *pthrt-r6-same-ops* (pthrt-ops *pthrt-r6-old-observations*))
(defun pthrt-r8-run-ops (ops fn-rtc-st)
 (declare (xargs :stobjs fn-rtc-st :guard t))
 (if (consp ops)
  (mv-let (fn-rtc-st obs acts) (pthrt-drive-op (car ops) 100000 fn-rtc-st)
   (declare (ignore acts))
   (mv-let (fn-rtc-st rest) (pthrt-r8-run-ops (cdr ops) fn-rtc-st)
    (mv fn-rtc-st (cons obs rest)))) (mv fn-rtc-st nil)))
(defun pthrt-r8-fixed-execute (ops fn-rtc-st)
 (declare (xargs :stobjs fn-rtc-st :guard t))
 (mv-let (fn-rtc-st acts) (fn-pth-x-init *fn-pth-rely-cfg* fn-rtc-st)
  (declare (ignore acts)) (pthrt-r8-run-ops ops fn-rtc-st)))
(defun pthrt-r8-fixed-local (ops)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-rtc-st (mv-let (fn-rtc-st obs) (pthrt-r8-fixed-execute ops fn-rtc-st) obs)))
(make-event (value `(defconst *pthrt-r6-new-observations* ',(pthrt-r8-fixed-local *pthrt-r6-same-ops*))))
(defthm pthrt-r6-old-open-submits-the-refused-pwrite
 (let ((o (nth 7 *pthrt-r6-old-observations*)))
  (and (nth 3 o)
       (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates (nth 1 o)))) :hashing)
       (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates (nth 2 o)))) :payload-writing)
       (equal (nth 5 o) '((:submit :pwrite (0 1 0 42) (2 18446744073709551616)))))))
(defun pthrt-r8-closed-observations-p (obs)
 (if (consp obs)
  (and (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates (nth 2 (car obs))))) :closed)
       (pthrt-r8-closed-observations-p (cdr obs))) t))
(defthm pthrt-r6-new-open-stays-closed-on-the-same-run
 (and (equal (pthrt-ops *pthrt-r6-new-observations*) *pthrt-r6-same-ops*)
      (pthrt-r8-closed-observations-p *pthrt-r6-new-observations*)))
(defconst *pthrt-r8-open-at-bound*
 (list :opened '(:done 0) 1 1
       (list (list 0 (make-list 32 :initial-element 0) 0 1 0) 18446744073709551616 '(1 256 256))))
(defconst *pthrt-r8-open-below-bound*
 (list :opened '(:done 0) 1 1
       (list (list 0 (make-list 32 :initial-element 0) 0 1 0) 18446744073709551615 '(1 256 256))))
(defthm pthrt-open-at-2^64-stays-closed
 (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-step1 (fn-ptx-closed) *pthrt-r8-open-at-bound* nil 0))) :closed)
 :hints (("Goal" :use pthrt-nil-acc-fits
  :in-theory (union-theories (theory 'minimal-theory)
   (union-theories '(fn-ptx-step1 fn-ptx-wfp fn-ptx-fields-fit fn-ptx-closed
                     fn-ptx-opened fn-ptx-mk pthrt-nil-acc-fits car-cons cdr-cons)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-ptx-step1) (:executable-counterpart fn-ptx-wfp)
       (:executable-counterpart fn-ptx-fields-fit))))))))
(defthm pthrt-open-below-2^64-is-idle
 (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-step1 (fn-ptx-closed) *pthrt-r8-open-below-bound* nil 0))) :idle)
 :hints (("Goal" :use pthrt-nil-acc-fits
  :in-theory (union-theories (theory 'minimal-theory)
   (union-theories '(fn-ptx-step1 fn-ptx-wfp fn-ptx-fields-fit fn-ptx-closed
                     fn-ptx-opened fn-ptx-mk pthrt-nil-acc-fits car-cons cdr-cons)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-ptx-step1) (:executable-counterpart fn-ptx-wfp)
       (:executable-counterpart fn-ptx-fields-fit))))))))
; R7's exact ground refutation of the old unfolding formula remains a test fact.
(defthm pthrt-old-step1-0-formula-is-false
 (not (equal (mv-nth 0 (fn-ptx-step1 (fn-ptx-closed) '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))) nil 0))
         (let* ((id (fn-rtc-ev-id '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (inc (fn-rtc-ev-inc '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (kind (fn-rtc-get 0 '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (out (fn-rtc-get 1 '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (tag (fn-rtc-get 0 out)) (n (fn-rtc-get 1 out)) (ph (fn-ptx-ph (fn-ptx-closed))) (kd (fn-ptx-kd (fn-ptx-closed))) (ext (fn-ptx-ext (fn-ptx-closed))) (nxt (fn-ptx-nxt (fn-ptx-closed))) (m0 (fn-ptx-chg (fn-ptx-closed) :committed nil))) (cond ((eq kind :opened) (if (and (eq ph :closed) (eq tag :done)) (let* ((d (fn-rtc-ev-opened-data '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (m1 (fn-ptx-opened (fn-rtc-get 0 d) (nfix (fn-rtc-get 1 d)) (fn-rtc-get 2 d)))) (if (and (fn-ptx-wfp m1) (<= (fn-ptx-fmax m1) *fn-frame-max-payload*) (equal (len (fn-ptx-kd-last (fn-ptx-kd m1))) 32)) m1 m0)) m0)) ((eq kind :handed) (let* ((hd (fn-rtc-get 6 '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (p (list (fn-ptx-atom (fn-rtc-get 4 '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (fn-ptx-atom (fn-rtc-get 5 '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (fn-rtc-h-buf hd) (fn-rtc-h-len hd)))) (cond ((member-eq ph '(:fenced :closed)) m0) ((eq ph :idle) (mv-nth 0 (fn-ptx-start p nil kd ext (fn-ptx-geo (fn-ptx-closed)) nil))) ((< (len (fn-ptx-q (fn-ptx-closed))) *fn-ptx-k*) (fn-ptx-chg m0 :q (append (true-list-fix (fn-ptx-q (fn-ptx-closed))) (list p)))) (t m0)))) ((and (eq ph :reading) (eq kind :timer)) (mv-nth 0 (fn-ptx-read (fn-ptx-closed) 0 id inc nil))) ((and (eq ph :hashing) (eq kind :timer)) (mv-nth 0 (fn-ptx-hash (fn-ptx-closed) 0 id inc nil))) ((and (eq ph :extending) (eq kind :extend)) (if (eq tag :done) (fn-ptx-chg m0 :ph :extsyncing :evd (fn-ptx-evd+ (fn-ptx-closed) '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (mv-nth 0 (fn-ptx-end m0 :refused kd ext t nil id inc nil)))) ((and (eq ph :extsyncing) (eq kind :fsync)) (if (eq tag :done) (let ((m1 (fn-ptx-chg m0 :ph :payload-writing :k 0 :evd (fn-ptx-evd+ (fn-ptx-closed) '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))))) m1) (mv-nth 0 (fn-ptx-end m0 :refused kd ext t nil id inc nil)))) ((and (eq ph :payload-writing) (eq kind :pwrite)) (let ((k (fn-ptx-k (fn-ptx-closed)))) (cond ((not (and (eq tag :done) (equal n (fn-ptx-span-n k (fn-ptx-closed))))) (mv-nth 0 (fn-ptx-end m0 :uncertain kd ext t nil id inc nil))) (t (let ((m1 (fn-ptx-chg m0 :ph (if (< (+ k 2) (fn-ptx-nspans (fn-ptx-closed))) :payload-writing :log-writing) :k (+ k 1) :evd (fn-ptx-evd+ (fn-ptx-closed) '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))))) m1))))) ((and (eq ph :log-writing) (eq kind :pwrite)) (if (and (eq tag :done) (equal n (fn-ptx-span-n (fn-ptx-k (fn-ptx-closed)) (fn-ptx-closed)))) (fn-ptx-chg m0 :ph :committing :evd (fn-ptx-evd+ (fn-ptx-closed) '(:opened (:done 0) 1 1 ((0 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 18446744073709551616 1 0) 18446744073709555712 (1 256 256))))) (mv-nth 0 (fn-ptx-end m0 :uncertain kd ext t nil id inc nil)))) ((and (eq ph :committing) (eq kind :fsync)) (if (eq tag :done) (mv-nth 0 (fn-ptx-end m0 :posted (fn-ptx-kd-commit kd (fn-rtc-get 1 (fn-ptx-hs (fn-ptx-closed))) (fn-ptx-elen (fn-ptx-closed))) nxt nil t id inc nil)) (mv-nth 0 (fn-ptx-end m0 :uncertain kd ext t nil id inc nil)))) ((eq kind :hand) m0) (t m0)))))
 :hints (("Goal" :use pthrt-nil-acc-fits
  :in-theory (union-theories (theory 'minimal-theory)
   (union-theories '(fn-ptx-step1 fn-ptx-wfp fn-ptx-fields-fit fn-ptx-closed
                     fn-ptx-opened fn-ptx-mk pthrt-nil-acc-fits car-cons cdr-cons)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-ptx-step1) (:executable-counterpart fn-ptx-wfp)
       (:executable-counterpart fn-ptx-fields-fit))))))))
(value-triple (cw "R8 TEETH: full same R6 ops: OLD submits pwrite at 2^64, refused; NEW stays CLOSED. Ext=2^64 CLOSED, ext=2^64-1 IDLE. Old step1-0 formula ground instance refuted.~%"))

; R9 tooth: remove ONLY the chain-octet conjunct, count checked on the source.
(defconst *pthrt-r9-chain-conjunct* '(fn-cbor-octet-listp (fn-ptx-kd-last (fn-ptx-kd m1))))
(defconst *pthrt-r9-open-data*
 (list (list 0 (make-list 32 :initial-element 256) 0 1 0) 0 '(1 256 256)))
(defun pthrt-r9-completion (a)
 (let ((e (pthrt-completion a)))
  (if (equal (car a) :opened) (update-nth 5 *pthrt-r9-open-data* e) e)))
(defun pthrt-r9-count-conjunct (tree conjunct)
 (declare (xargs :guard t :measure (acl2-count tree)))
 (if (equal tree conjunct) 1
  (if (consp tree) (+ (pthrt-r9-count-conjunct (car tree) conjunct)
                       (pthrt-r9-count-conjunct (cdr tree) conjunct)) 0)))
(defun pthrt-r9-remove-conjunct (tree conjunct)
 (declare (xargs :guard t :measure (acl2-count tree)))
 (if (consp tree)
  (if (equal (car tree) conjunct) (pthrt-r9-remove-conjunct (cdr tree) conjunct)
   (cons (pthrt-r9-remove-conjunct (car tree) conjunct)
         (pthrt-r9-remove-conjunct (cdr tree) conjunct))) tree))
(defun pthrt-r9-copy-events (events alist)
 (declare (xargs :guard t :measure (acl2-count events)))
 (if (consp events)
  (cons (pthrt-r8-rename
          (if (equal (cadr (car events)) 'fn-ptx-step1)
           (pthrt-r9-remove-conjunct (car events) *pthrt-r9-chain-conjunct*) (car events)) alist)
        (pthrt-r9-copy-events (cdr events) alist)) nil))
(make-event
 (let* ((world (w state)) (step1 (get-event 'fn-ptx-step1 world))
        (alist '((fn-ptx-step1 . pthrt-r9-old-step1) (fn-ptx-step . pthrt-r9-old-step)
                 (fn-pthm-step . pthrt-r9-old-machine) (fn-pth-x-deliver . pthrt-r9-old-deliver)
                 (fn-pth-x-step* . pthrt-r9-old-layer) (pthrt-drive-op . pthrt-r9-old-drive)
                 (pthrt-completion . pthrt-r9-completion) (pthrt-drain . pthrt-r9-old-drain)
                 (pthrt-execute . pthrt-r9-old-execute) (pthrt-local . pthrt-r9-old-local)))
        (events (list step1 (get-event 'fn-ptx-step world) (get-event 'fn-pthm-step world)
                  (get-event 'fn-pth-x-deliver world) (get-event 'fn-pth-x-step* world)
                  (get-event 'pthrt-drive-op world) (get-event 'pthrt-drain world)
                  (get-event 'pthrt-execute world) (get-event 'pthrt-local world))))
  (if (equal (pthrt-r9-count-conjunct step1 *pthrt-r9-chain-conjunct*) 1)
   (value (cons 'progn (pthrt-r9-copy-events events alist)))
   (er soft 'pthrt-r9-old-chain "Expected exactly one chain-octet conjunct."))))
(make-event (value `(defconst *pthrt-r9-old-observations* ',(pthrt-r9-old-local *fn-pth-rely-cfg*))))
(defconst *pthrt-r9-same-ops* (pthrt-ops *pthrt-r9-old-observations*))
(make-event (value `(defconst *pthrt-r9-new-observations* ',(pthrt-r8-fixed-local *pthrt-r9-same-ops*))))
; Context v2: 91-octet article + 32-octet trailer = 123.
(defconst *pthrt-r9-bad-header*
 (append '(70 78 76 71 1 1 0 0 0 123) (make-list 32 :initial-element 256)))
(defthm pthrt-r9-old-chain-makes-a-request-that-is-not-data-ok
 (let* ((o (nth 6 *pthrt-r9-old-observations*))
        (r (list :write 0 1 0 *pthrt-r9-bad-header*)))
  (and (nth 3 o)
       (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates (nth 1 o)))) :reading)
       (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates (nth 2 o)))) :hashing)
       (equal (nth 5 o) (list r))
       (not (fn-pth-req-data-okp r)))))
; Paired tooth: freeze the old-layout value 152 while the real fixture is 123.
(defconst *pthrt-r9-old-layout-bad-header*
 (append '(70 78 76 71 1 1 0 0 0 152) (make-list 32 :initial-element 256)))
(defthm mhalf7-old-r9-bad-header-expectation-is-refuted
 (not (let* ((o (nth 6 *pthrt-r9-old-observations*))
        (r (list :write 0 1 0 *pthrt-r9-old-layout-bad-header*)))
  (and (nth 3 o)
       (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates (nth 1 o)))) :reading)
       (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates (nth 2 o)))) :hashing)
       (equal (nth 5 o) (list r))
       (not (fn-pth-req-data-okp r))))) :rule-classes nil)

(defthm pthrt-r9-non-octet-chain-new-open-stays-closed-on-the-same-run
 (and (equal (pthrt-ops *pthrt-r9-new-observations*) *pthrt-r9-same-ops*)
      (pthrt-r8-closed-observations-p *pthrt-r9-new-observations*)))
(defconst *pthrt-r9-bad-open* (list :opened '(:done 0) 1 1 *pthrt-r9-open-data*))
(defthm pthrt-r9-open-violates-only-the-added-chain-conjunct
 (let ((m1 (fn-ptx-opened (fn-rtc-get 0 *pthrt-r9-open-data*)
                         (nfix (fn-rtc-get 1 *pthrt-r9-open-data*))
                         (fn-rtc-get 2 *pthrt-r9-open-data*))))
  (and (fn-ptx-wfp m1) (<= (fn-ptx-fmax m1) *fn-frame-max-payload*)
       (< (nfix (fn-rtc-get 1 *pthrt-r9-open-data*)) (expt 2 64))
       (equal (len (fn-ptx-kd-last (fn-ptx-kd m1))) 32)
       (not (fn-cbor-octet-listp (fn-ptx-kd-last (fn-ptx-kd m1))))))
 :hints (("Goal" :use pthrt-nil-acc-fits
  :in-theory (union-theories (theory 'minimal-theory)
   (union-theories '(fn-ptx-wfp fn-ptx-fields-fit fn-ptx-opened fn-ptx-mk
                     pthrt-nil-acc-fits car-cons cdr-cons)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-ptx-wfp) (:executable-counterpart fn-ptx-fields-fit))))))))
(defthm pthrt-r9-non-octet-chain-open-stays-closed
 (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-step1 (fn-ptx-closed) *pthrt-r9-bad-open* nil 0))) :closed)
 :hints (("Goal" :use pthrt-nil-acc-fits
  :in-theory (union-theories (theory 'minimal-theory)
   (union-theories '(fn-ptx-step1 fn-ptx-wfp fn-ptx-fields-fit fn-ptx-closed
                     fn-ptx-opened fn-ptx-mk pthrt-nil-acc-fits car-cons cdr-cons)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-ptx-step1) (:executable-counterpart fn-ptx-wfp)
       (:executable-counterpart fn-ptx-fields-fit))))))))
(value-triple (cw "R9 CHAIN TEETH: exactly one octet conjunct removed; all other open checks hold; OLD request data predicate NIL; NEW same-run owner CLOSED.~%"))

; R10: the R9 listener run under the exact old/new hand-target check.
(defconst *pthrt-r10-sender-conjunct* '(<= 1 (nfix id)))
(defconst *pthrt-r10-r9-ops* '((:REQUEST 0 0 ((:SUBMIT :POOL NIL NIL)))
 (:COMPLETE (:ACCEPT 0 0 1 (:DONE 0)))
 (:COMPLETE (:GRANT 0 0 4 (:DONE 0)))
 (:COMPLETE (:POOL 0 0 2 (:DONE 0)))
 (:REQUEST 0 0
           ((:WRITE 3 2 0
                    (1 0 0 0
                       0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                       0 0 0 0 0 70 114 111 109 58 97 13 10 68
                       97 116 101 58 84 104 117 44 32 49 32 74
                       97 110 32 49 57 55 48 32 48 48 58 48 48
                       58 48 48 32 43 48 48 48 48 13 10 78 101
                       119 115 103 114 111 117 112 115 58 120
                       13 10 83 117 98 106 101 99 116 58 120
                       13 10 77 101 115 115 97 103 101 45 73
                       68 58 60 120 64 121 62 13 10 13 10 120))
            (:SUBMIT :HAND (3 2 0 120) (1 1))))
 (:COMPLETE (:HAND 0 0 5 (:DONE 0)))))
(defun pthrt-r10-copy-old-hand-events (events alist)
 (declare (xargs :guard t :measure (acl2-count events)))
 (if (consp events)
  (cons (pthrt-r8-rename
          (if (member-eq (cadr (car events)) '(fn-rtc-hand-target-okp fn-rtc-x-hand-target-okp))
           (pthrt-r9-remove-conjunct (car events) *pthrt-r10-sender-conjunct*)
           (car events)) alist)
        (pthrt-r10-copy-old-hand-events (cdr events) alist)) nil))
(make-event
 (let* ((world (w state))
        (logical (get-event 'fn-rtc-hand-target-okp world))
        (executable (get-event 'fn-rtc-x-hand-target-okp world))
        (alist '((fn-rtc-hand-target-okp . pthrt-r10-old-hand-target)
                 (fn-rtc-x-hand-target-okp . pthrt-r10-old-x-hand-target)
                 (fn-rtc-x-req-submit . pthrt-r10-old-submit)
                 (fn-rtc-x-request . pthrt-r10-old-request)
                 (fn-rtc-x-requests . pthrt-r10-old-requests)
                 (fn-pth-x-deliver . pthrt-r10-old-deliver)
                 (fn-pth-x-step* . pthrt-r10-old-step)
                 (pthrt-drive-op . pthrt-r10-old-drive)
                 (pthrt-r8-run-ops . pthrt-r10-old-run-ops)
                 (pthrt-r8-fixed-execute . pthrt-r10-old-execute)
                 (pthrt-r8-fixed-local . pthrt-r10-old-local)))
        (events (list logical executable (get-event 'fn-rtc-x-req-submit world)
                 (get-event 'fn-rtc-x-request world) (get-event 'fn-rtc-x-requests world)
                 (get-event 'fn-pth-x-deliver world) (get-event 'fn-pth-x-step* world)
                 (get-event 'pthrt-drive-op world) (get-event 'pthrt-r8-run-ops world)
                 (get-event 'pthrt-r8-fixed-execute world) (get-event 'pthrt-r8-fixed-local world))))
  (if (and (equal (pthrt-r9-count-conjunct logical *pthrt-r10-sender-conjunct*) 1)
           (equal (pthrt-r9-count-conjunct executable *pthrt-r10-sender-conjunct*) 1))
   (value (cons 'progn (pthrt-r10-copy-old-hand-events events alist)))
   (er soft 'pthrt-r10-old-hand "Expected one sender conjunct in each hand check."))))
(make-event (value `(defconst *pthrt-r10-old-observations* ',(pthrt-r10-old-local *pthrt-r10-r9-ops*))))
(make-event (value `(defconst *pthrt-r10-new-observations* ',(pthrt-r8-fixed-local *pthrt-r10-r9-ops*))))
(defthm pthrt-r10-old-hand-check-reproduces-r9-refused-owner-reply
 (let ((o (nth 5 *pthrt-r10-old-observations*)))
  (and (nth 3 o)
       (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates (nth 1 o)))) :closed)
       (equal (nth 5 o) '((:submit :hand (3 3 0 120) (0 0)))))))
(defun pthrt-r10-no-owner-refused-p (obs)
 (if (consp obs)
  (and (implies (nth 3 (car obs)) (not (nth 5 (car obs))))
       (pthrt-r10-no-owner-refused-p (cdr obs))) t))
(defthm pthrt-r10-new-hand-check-refuses-the-listener-before-owner-delivery
 (and (equal (pthrt-ops *pthrt-r10-new-observations*) *pthrt-r10-r9-ops*)
      (equal (nth 5 (nth 4 *pthrt-r10-new-observations*))
             '((:submit :hand (3 2 0 120) (1 1))))
      (not (nth 3 (nth 5 *pthrt-r10-new-observations*)))
      (pthrt-r10-no-owner-refused-p *pthrt-r10-new-observations*)))
(value-triple (cw "R10 R9 TOOTH: exact sender conjunct removed in logical and exec copies, count checked; OLD owner reply refused; NEW listener submit refused, no owner delivery/refusal.~%"))

; M-HALF projection tooth: end-use transfers the hand before the machine call.
; Class 5: context v2 CS = max(6920, 33 + 65634) = 65667; the v1
; fixture used 65663, four octets short (maximal-batch tooth below acceptance).
(defconst *pthrt-mhalf-projection-s* '((3 4 0 1 0 1 66560 3 65667)
 ((0 :LIVE NIL) (1 :LIVE 0) (1 :LIVE 0))
 ((0 (:FREE) NIL)
  (0 (:FREE) NIL)
  (0 (:FREE) NIL)
  (2 (:HANDED 2 1 1 1) (9)))
 ((:HAND 2 1 4 (3 2 0 1))
  (:OPENED 1 1 0 NIL))
 (NIL (:CLOSED 0 NIL
               NIL NIL 0 0 NIL NIL NIL NIL NIL NIL NIL)
      NIL)
 5))
(defconst *pthrt-mhalf-projection-e* '(:HAND 2 1 4 (:DONE 0)))
(defconst *pthrt-mhalf-actual-rs* '((:WRITE 3 3 0 (1)) (:SUBMIT :HAND (3 3 0 1) (2 1))))
(defconst *pthrt-mhalf-old-rs* '((:WRITE 3 0 0 (1)) (:SUBMIT :HAND (3 0 0 1) (2 1))))
(defthm pthrt-mhalf-actual-owner-request-value
 (equal (fn-pth-owner-requests *pthrt-mhalf-projection-s* *pthrt-mhalf-projection-e* 100000) *pthrt-mhalf-actual-rs*)
 :hints (("Goal" :use pthrt-nil-acc-fits
  :in-theory (union-theories (theory 'minimal-theory)
   (union-theories
    '(fn-pth-owner-requests fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
      fn-ptx-wfp fn-ptx-fields-fit fn-ptx-mk fn-ptx-answer fn-rtc-view-state
      pthrt-nil-acc-fits car-cons cdr-cons mv-nth)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-pth-owner-requests) (:executable-counterpart fn-pth-m-step)
       (:executable-counterpart fn-pthm-step) (:executable-counterpart fn-ptx-step)
       (:executable-counterpart fn-ptx-step1) (:executable-counterpart fn-ptx-wfp)
       (:executable-counterpart fn-ptx-fields-fit))))))))
(defthm pthrt-mhalf-old-preview-request-value
 (equal (mv-nth 1 (fn-pth-m-step (fn-rtc-mstate 1 *pthrt-mhalf-projection-s*)
              (mv-nth 1 (fn-pth-owner-delivery *pthrt-mhalf-projection-s* *pthrt-mhalf-projection-e* 100000))
              (fn-rtc-view-state 1 (fn-rtc-s-inc (fn-rtc-slot 1 *pthrt-mhalf-projection-s*)) *pthrt-mhalf-projection-s*)
              (nfix 100000))) *pthrt-mhalf-old-rs*)
 :hints (("Goal" :use pthrt-nil-acc-fits
  :in-theory (union-theories (theory 'minimal-theory)
   (union-theories
    '(fn-pth-owner-delivery fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
      fn-ptx-wfp fn-ptx-fields-fit fn-ptx-mk fn-ptx-answer fn-rtc-view-state
      pthrt-nil-acc-fits car-cons cdr-cons mv-nth)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-pth-m-step) (:executable-counterpart fn-pthm-step)
       (:executable-counterpart fn-ptx-step) (:executable-counterpart fn-ptx-step1)
       (:executable-counterpart fn-ptx-wfp) (:executable-counterpart fn-ptx-fields-fit))))))))
(defthm pthrt-mhalf-old-preview-differs-and-corrected-projection-holds
 (let* ((s *pthrt-mhalf-projection-s*) (e *pthrt-mhalf-projection-e*) (q 100000)
        (ev (mv-nth 1 (fn-pth-owner-delivery s e q))) (inc (fn-rtc-ev-inc ev))
        (s1 (fn-rtc-end-use s e))
        (d (if (eq (fn-rtc-e-kind e) :accept)
               (fn-rtc-with-mstate 1 (fn-rtc-m-init)
                 (fn-rtc-with-slot 1 (list inc :live (fn-rtc-get 1 (fn-rtc-get 1 ev))) s1))
             s1)))
  (and (mv-nth 0 (fn-pth-owner-delivery s e q))
       (not (equal (fn-pth-owner-requests s e q)
         (mv-nth 1 (fn-pth-m-step (fn-rtc-mstate 1 s) ev
           (fn-rtc-view-state 1 (fn-rtc-s-inc (fn-rtc-slot 1 s)) s) (nfix q)))))
       (equal (fn-pth-owner-requests s e q)
         (mv-nth 1 (fn-pth-m-step (fn-rtc-mstate 1 d) ev
           (fn-rtc-view-state 1 inc d) (nfix q))))))
 :rule-classes nil
 :hints (("Goal" :use (pthrt-mhalf-actual-owner-request-value
                        pthrt-mhalf-old-preview-request-value
    (:instance fn-pth-owner-requests-are-the-step-request-list
      (s *pthrt-mhalf-projection-s*) (e *pthrt-mhalf-projection-e*) (q 100000)))
  :in-theory (union-theories (theory 'minimal-theory)
   (union-theories '(car-cons cdr-cons)
    (set-difference-theories (executable-counterpart-theory :here)
     '((:executable-counterpart fn-pth-owner-requests)
       (:executable-counterpart fn-pth-m-step)
       (:executable-counterpart fn-pthm-step)
       (:executable-counterpart fn-ptx-step)
       (:executable-counterpart fn-ptx-step1)
       (:executable-counterpart fn-ptx-wfp)
       (:executable-counterpart fn-ptx-fields-fit))))))))

; P13: admitted-domain inhabitation and the excluded huge-slot tooth.
; Ground excluded-domain tooth: no 2^64-slot state is materialized.
(defconst *r11-id-u64* (expt 2 64))
(defconst *r11-id-mcfg* (list *r11-id-u64* nil 0 0 nil 0 0 0 nil 0 1))
(defconst *r11-id-cfg*
 (fn-hl-rtc-config *fn-bs-profile-development* *r11-id-mcfg* 100000
                   *fn-pth-nstatic* 0 0 *fn-pth-qs* *fn-pth-cs*))
(defthm r11-host-config-does-not-bound-slot-id
 (and (fn-rtc-configp *r11-id-cfg*)
      (< *r11-id-u64* (fn-rtc-nslots *r11-id-cfg*))))
(defthm r11-bounded-inc-does-not-type-reply-target
 (not (fn-pth-req-data-okp
       (list :submit :hand '(3 1 0 1) (list *r11-id-u64* 1)))))
(defthm r11-closed-owner-reply-copies-unbounded-sender-id
 (equal (nth 1 (mv-nth 1
         (fn-ptx-step (fn-ptx-closed)
           (list :handed '(:done 0) 1 1 *r11-id-u64* 1 '(3 1 0 0)) nil 100000)))
        (list :submit :hand '(3 0 0 1) (list *r11-id-u64* 1)))
 :hints (("Goal" :use pthrt-nil-acc-fits
   :in-theory (union-theories (theory 'minimal-theory)
     (union-theories
      '(fn-ptx-step fn-ptx-step1 fn-ptx-wfp fn-ptx-fields-fit fn-ptx-mk
        fn-ptx-answer fn-ptx-closed pthrt-nil-acc-fits car-cons cdr-cons mv-nth)
      (set-difference-theories (executable-counterpart-theory :here)
       '((:executable-counterpart fn-ptx-step) (:executable-counterpart fn-ptx-step1)
         (:executable-counterpart fn-ptx-wfp) (:executable-counterpart fn-ptx-fields-fit))))))))

(defthm r11-current-hand-target-check-does-not-bound-sender-id
 (fn-rtc-hand-target-okp '(1 1) *r11-id-u64*
  (fn-rtc-make *r11-id-cfg* nil nil nil nil 0)))
(defthm r11-reply-data-demands-both-source-scalars-below-u64
 (implies (and (natp fid) (<= 1 fid) (natp finc))
  (iff (fn-pth-req-data-okp (list :submit :hand '(3 1 0 1) (list fid finc)))
       (and (< fid (expt 2 64)) (< finc (expt 2 64)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-req-data-okp fn-rtc-kind-extrap fn-rtc-extrap fn-rtc-handlep
    fn-rtc-h-off fn-rtc-get natp len true-listp mv-nth car-cons cdr-cons
    (:executable-counterpart expt) (:executable-counterpart equal)
    (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-buffered-kind-p)
    (:executable-counterpart zp) (:executable-counterpart nfix))))))

(defthm pthrt-p13-huge-config-is-not-admitted
 (and (fn-rtc-configp *r11-id-cfg*)
      (equal (fn-rtc-nslots *r11-id-cfg*) (+ 2 (expt 2 64)))
      (not (fn-rtc-st-cfg-okp *r11-id-cfg*))
      (not (fn-rtc-extrap (list (expt 2 64) 1)))))

(defthm pthrt-p13-reading-config-is-admitted
 (fn-rtc-st-cfg-okp *fn-pth-rely-cfg*))
(defconst *pthrt-p13-default-cfg*
 (fn-hl-rtc-config *fn-bs-profile-defaults* *fn-pth-rely-mcfg* 100000
                  *fn-pth-nstatic* 0 0 *fn-pth-qs* *fn-pth-cs*))
(defthm pthrt-p13-default-config-is-admitted
 (fn-rtc-st-cfg-okp *pthrt-p13-default-cfg*))
(defthm pthrt-p13-development-initial-state-is-reachable
 (fn-pth-reachablep (mv-nth 0 (fn-pth-init *fn-pth-rely-cfg*)))
 :hints (("Goal" :use ((:instance fn-pth-reachablep-suff
  (s (mv-nth 0 (fn-pth-init *fn-pth-rely-cfg*)))
  (profile *fn-bs-profile-development*) (mcfg *fn-pth-rely-mcfg*) (q0 100000) (ops0 nil)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-host-run pthrt-p13-reading-config-is-admitted
     (:executable-counterpart fn-rtc-st-cfg-okp)
     (:executable-counterpart fn-hl-rtc-config)
     (:executable-counterpart fn-rtc-configp)
     (:executable-counterpart fn-rtc-nstatic)
     (:executable-counterpart natp))))))
(defthm pthrt-p13-default-initial-state-is-reachable
 (fn-pth-reachablep (mv-nth 0 (fn-pth-init *pthrt-p13-default-cfg*)))
 :hints (("Goal" :use ((:instance fn-pth-reachablep-suff
  (s (mv-nth 0 (fn-pth-init *pthrt-p13-default-cfg*)))
  (profile *fn-bs-profile-defaults*) (mcfg *fn-pth-rely-mcfg*) (q0 100000) (ops0 nil)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-host-run pthrt-p13-default-config-is-admitted
     (:executable-counterpart fn-rtc-st-cfg-okp)
     (:executable-counterpart fn-hl-rtc-config)
     (:executable-counterpart fn-rtc-configp)
     (:executable-counterpart fn-rtc-nstatic)
     (:executable-counterpart natp))))))

; P14: ACQ teeth replacing P13's current-contract obstruction.
; The old acquire/complement retain the S2 cause as historical mutants.

; A finite host request with a typed, but non-current, listener incarnation.
(defun p13-request-domain-scene (fn-rtc-st)
 (declare (xargs :stobjs fn-rtc-st :guard t :verify-guards nil))
 (mv-let (fn-rtc-st acts) (fn-pth-x-init *fn-pth-rely-cfg* fn-rtc-st)
  (declare (ignore acts))
  (let ((before (fn-rtc-x-state fn-rtc-st)))
   (mv-let (fn-rtc-st acts refused cost)
    (fn-rtc-x-requests '((:acquire 3)) 0 1 fn-rtc-st)
    (declare (ignore acts cost))
    (mv fn-rtc-st (list before (fn-rtc-x-state fn-rtc-st) refused))))))
(defun p13-request-domain-local ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-rtc-st
  (mv-let (fn-rtc-st result) (p13-request-domain-scene fn-rtc-st) result)))
(with-guard-checking-event nil
 (make-event
  (value `(defconst *p13-request-domain-result* ',(p13-request-domain-local)))))
(defconst *p13-request-domain-before* (nth 0 *p13-request-domain-result*))
(defconst *p13-request-domain-after* (nth 1 *p13-request-domain-result*))
(defconst *p13-request-domain-op* '(:request 0 1 ((:acquire 3))))

(defun p14-old-req-acquire (r id inc s)
  (declare (xargs :guard t))
  (let* ((h (fn-rtc-get 1 r)) (b (fn-rtc-buffer h s)))
    (if (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
             (equal (fn-rtc-home h (fn-rtc-config s)) (nfix id))
             (equal (fn-rtc-b-owner b) '(:free)))
        (mv (fn-rtc-with-buffer h (list (+ 1 (fn-rtc-b-gen b)) (list :workspace id inc) nil) s)
            nil nil 1)
      (mv s nil (list r) 1))))
(defun p14-acquire-without-posp (r id inc s)
  (declare (xargs :guard t))
  (let* ((h (fn-rtc-get 1 r)) (b (fn-rtc-buffer h s)))
    (if (and (fn-rtc-live-p id inc s)
             (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
             (equal (fn-rtc-home h (fn-rtc-config s)) (nfix id))
             (equal (fn-rtc-b-owner b) '(:free)))
        (mv (fn-rtc-with-buffer h (list (+ 1 (fn-rtc-b-gen b)) (list :workspace id inc) nil) s) nil nil 1)
      (mv s nil (list r) 1))))
(defun p14-acquire-without-live-p (r id inc s)
  (declare (xargs :guard t))
  (let* ((h (fn-rtc-get 1 r)) (b (fn-rtc-buffer h s)))
    (if (and (posp id)
             (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
             (equal (fn-rtc-home h (fn-rtc-config s)) (nfix id))
             (equal (fn-rtc-b-owner b) '(:free)))
        (mv (fn-rtc-with-buffer h (list (+ 1 (fn-rtc-b-gen b)) (list :workspace id inc) nil) s) nil nil 1)
      (mv s nil (list r) 1))))
(defun p14-old-req-state-okp (r id inc s)
 (let* ((h (fn-rtc-get 1 r)) (g (fn-rtc-get 2 r)) (off (fn-rtc-get 3 r))
        (b (fn-rtc-buffer h s)))
  (case (fn-rtc-get 0 r)
   (:acquire (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                  (equal (fn-rtc-home h (fn-rtc-config s)) (nfix id))
                  (equal (fn-rtc-b-owner b) '(:free))))
   (:write (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner b) (list :workspace id inc))
                (equal (fn-rtc-b-gen b) g)
                (<= off (len (fn-rtc-b-bytes b)))
                (<= (+ off (len (fn-rtc-get 4 r))) (fn-rtc-buf-cap h (fn-rtc-config s)))))
   (:release (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                  (equal (fn-rtc-b-owner b) (list :workspace id inc))
                  (equal (fn-rtc-b-gen b) g)))
   (:close (and (fn-rtc-live-p id inc s) (< (fn-rtc-nstatic (fn-rtc-config s)) (nfix id))))
   (:cancel (and (fn-rtc-current-p id inc s)
                 (fn-rtc-kind-out-p (fn-rtc-get 1 r) id inc (fn-rtc-uses s))))
   (:submit
    (let* ((kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)) (extra (fn-rtc-get 3 r))
           (h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s)) (o (fn-rtc-b-owner b))
           (own (equal o (list :workspace id inc))))
     (and (fn-rtc-live-p id inc s)
          (implies (eq kind :hand)
                   (and (<= 1 (nfix id))
                        (< (fn-rtc-get 0 extra) (fn-rtc-nslots (fn-rtc-config s)))
                        (not (equal (fn-rtc-get 0 extra) (nfix id)))
                        (implies (< (fn-rtc-nstatic (fn-rtc-config s)) (nfix id))
                                 (<= (fn-rtc-get 0 extra) (fn-rtc-nstatic (fn-rtc-config s))))))
          (or (eq kind :hand)
              (not (fn-rtc-kind-out-p (if (eq kind :pool) :wait kind) id inc (fn-rtc-uses s))))
          (if (or (eq kind :pool) (not (fn-rtc-buffered-kind-p kind))) t
            (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                 (equal (fn-rtc-b-gen b) (fn-rtc-h-gen hd))
                 (cond ((member-eq kind *fn-rtc-in-kinds*)
                        (and own (<= (fn-rtc-h-off hd) (len (fn-rtc-b-bytes b)))
                             (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                                 (fn-rtc-buf-cap h (fn-rtc-config s)))))
                       ((eq kind :hand) (and own (equal (fn-rtc-h-len hd) (len (fn-rtc-b-bytes b)))))
                       (t (and (or own (equal o (list :leased id inc :out)))
                               (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd)) (len (fn-rtc-b-bytes b)))
                               (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                                   (fn-rtc-buf-cap h (fn-rtc-config s)))))))))))
   (otherwise nil))))
(verify-guards p13-request-domain-scene)
(verify-guards p13-request-domain-local)
(verify-guards p14-old-req-acquire)
(verify-guards p14-acquire-without-posp)
(verify-guards p14-acquire-without-live-p)

(defthm p14-development-init-is-the-fixture-before
 (equal (mv-nth 0 (fn-pth-init *fn-pth-rely-cfg*)) *p13-request-domain-before*)
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '((:executable-counterpart fn-pth-init) (:executable-counterpart mv-nth))))))

; Complete historical after-state printed by c6s/request-domain-guards.log:55–68.
; This literal is independent of the old acquire body being tested.
(defconst *p14-acq-S2-after*
 '((3 4 0 1 0 1 66560 3 65667)
   ((0 :live nil) (1 :live 0) (0 :free nil))
   ((0 (:free) nil) (0 (:free) nil) (0 (:free) nil) (1 (:workspace 0 1) nil))
   ((:accept 0 0 1 nil) (:opened 1 1 0 nil))
   (nil (:closed 0 nil nil nil 0 0 nil nil nil nil nil nil nil) nil) 2))
(defthm p14-acq-T1-old-acquire-reproduces-whole-S2-after-state
 (equal (mv-nth 0 (p14-old-req-acquire '(:acquire 3) 0 1 *p13-request-domain-before*))
        *p14-acq-S2-after*)
 :rule-classes nil)

(defthm p14-acq-T1-old-acquire-takes-both-listener-pairs
 (and (equal (fn-rtc-slot 0 *p13-request-domain-before*) '(0 :live nil))
      (equal (mv-nth 2 (p14-old-req-acquire '(:acquire 3) 0 1 *p13-request-domain-before*)) nil)
      (equal (mv-nth 2 (p14-old-req-acquire '(:acquire 3) 0 0 *p13-request-domain-before*)) nil)
      (equal (fn-rtc-buffer 3 (mv-nth 0 (p14-old-req-acquire '(:acquire 3) 0 1 *p13-request-domain-before*)))
             '(1 (:workspace 0 1) nil))
      (equal (fn-rtc-buffer 3 (mv-nth 0 (p14-old-req-acquire '(:acquire 3) 0 0 *p13-request-domain-before*)))
             '(1 (:workspace 0 0) nil))
      (not (fn-pth-invp (mv-nth 0 (p14-old-req-acquire '(:acquire 3) 0 1 *p13-request-domain-before*)))))
 :rule-classes nil)
(defthm p14-acq-T1-real-requests-refuse-both-with-no-state-change
 (and (equal (mv-nth 0 (fn-rtc-requests '((:acquire 3)) 0 1 *p13-request-domain-before*)) *p13-request-domain-before*)
      (equal (mv-nth 2 (fn-rtc-requests '((:acquire 3)) 0 1 *p13-request-domain-before*)) '((:acquire 3)))
      (equal (mv-nth 0 (fn-rtc-requests '((:acquire 3)) 0 0 *p13-request-domain-before*)) *p13-request-domain-before*)
      (equal (mv-nth 2 (fn-rtc-requests '((:acquire 3)) 0 0 *p13-request-domain-before*)) '((:acquire 3)))
      (equal *p13-request-domain-after* *p13-request-domain-before*)
      (equal (nth 2 *p13-request-domain-result*) '((:acquire 3))))
 :rule-classes nil)

; T2 is a request-arm tooth: this closing state is not claimed reachable.
(defconst *p14-acq-closing*
 (fn-rtc-with-slot 1 '(1 :closing 0) *p13-request-domain-before*))
(defthm p14-acq-T2-closing-at-current-incarnation-is-refused
 (and (fn-rtc-current-p 1 1 *p14-acq-closing*)
      (equal (fn-rtc-home 0 (fn-rtc-config *p14-acq-closing*)) 1)
      (equal (fn-rtc-b-owner (fn-rtc-buffer 0 *p14-acq-closing*)) '(:free))
      (equal (mv-nth 0 (fn-rtc-requests '((:acquire 0)) 1 1 *p14-acq-closing*)) *p14-acq-closing*)
      (equal (mv-nth 2 (fn-rtc-requests '((:acquire 0)) 1 1 *p14-acq-closing*)) '((:acquire 0))))
 :rule-classes nil)

; A home-0 buffer is acquirable by nobody, which matches fn-rtc-pool-okp
; (a workspace owner has posp id); this is not lost capacity.
(defthm p14-acq-T3-live-positive-caller-acquires-own-development-home
 (and (posp 1) (fn-rtc-live-p 1 1 *p13-request-domain-before*)
      (equal (fn-rtc-home 0 (fn-rtc-config *p13-request-domain-before*)) 1)
      (equal (fn-rtc-b-owner (fn-rtc-buffer 0 *p13-request-domain-before*)) '(:free))
      (equal (mv-nth 2 (fn-rtc-requests '((:acquire 0)) 1 1 *p13-request-domain-before*)) nil)
      (equal (fn-rtc-buffer 0 (mv-nth 0 (fn-rtc-requests '((:acquire 0)) 1 1 *p13-request-domain-before*)))
             '(1 (:workspace 1 1) nil)))
 :rule-classes nil)
(defthm p14-acq-T4-posp-removal-revives-current-listener-case
 (and (fn-rtc-live-p 0 0 *p13-request-domain-before*)
      (equal (mv-nth 2 (p14-acquire-without-posp '(:acquire 3) 0 0 *p13-request-domain-before*)) nil)
      (equal (fn-rtc-buffer 3 (mv-nth 0 (p14-acquire-without-posp '(:acquire 3) 0 0 *p13-request-domain-before*)))
             '(1 (:workspace 0 0) nil))
      (equal (mv-nth 2 (fn-rtc-req-acquire '(:acquire 3) 0 0 *p13-request-domain-before*)) '((:acquire 3))))
 :rule-classes nil)
(defthm p14-acq-T4-live-p-removal-revives-positive-stale-caller-case
 (and (equal (fn-rtc-slot 1 *p13-request-domain-before*) '(1 :live 0))
      (posp 1) (not (fn-rtc-live-p 1 2 *p13-request-domain-before*))
      (equal (fn-rtc-home 0 (fn-rtc-config *p13-request-domain-before*)) 1)
      (equal (mv-nth 2 (p14-acquire-without-live-p '(:acquire 0) 1 2 *p13-request-domain-before*)) nil)
      (equal (fn-rtc-buffer 0 (mv-nth 0 (p14-acquire-without-live-p '(:acquire 0) 1 2 *p13-request-domain-before*)))
             '(1 (:workspace 1 2) nil))
      (equal (mv-nth 0 (fn-rtc-req-acquire '(:acquire 0) 1 2 *p13-request-domain-before*)) *p13-request-domain-before*)
      (equal (mv-nth 2 (fn-rtc-req-acquire '(:acquire 0) 1 2 *p13-request-domain-before*)) '((:acquire 0))))
 :rule-classes nil)

; Retain the two P14 S2 negations against the old complement; this small
; model fixture is unchanged and neither factor requires reachability.
(defconst *p14-factor-state*
 '((3 4 0 1 0 1 66560 3 65667)
   ((0 :live nil) (1 :live 0) (0 :free nil))
   ((0 (:free) nil) (0 (:free) nil) (0 (:free) nil) (0 (:free) nil))
   nil (nil nil nil) 0))
(defthm p14-frozen-acquire-factor-is-ground-false
 (not
  (implies (equal (fn-rtc-get 0 '(:acquire 3)) :acquire)
   (iff (not (mv-nth 2 (fn-rtc-req-acquire '(:acquire 3) 0 1 *p14-factor-state*)))
    (and (fn-pth-req-data-okp '(:acquire 3))
         (p14-old-req-state-okp '(:acquire 3) 0 1 *p14-factor-state*)))))
 :rule-classes nil)
(defthm p14-frozen-dispatched-factor-is-ground-false
 (not
  (iff (not (mv-nth 2 (fn-rtc-request '(:acquire 3) 0 1 *p14-factor-state*)))
   (and (fn-pth-req-data-okp '(:acquire 3))
        (p14-old-req-state-okp '(:acquire 3) 0 1 *p14-factor-state*))))
 :rule-classes nil)
(defthm p14-new-complement-satisfies-both-factors-on-the-same-state
 (and
  (implies (equal (fn-rtc-get 0 '(:acquire 3)) :acquire)
   (iff (not (mv-nth 2 (fn-rtc-req-acquire '(:acquire 3) 0 1 *p14-factor-state*)))
    (and (fn-pth-req-data-okp '(:acquire 3))
         (fn-pth-req-state-okp '(:acquire 3) 0 1 *p14-factor-state*))))
  (iff (not (mv-nth 2 (fn-rtc-request '(:acquire 3) 0 1 *p14-factor-state*)))
   (and (fn-pth-req-data-okp '(:acquire 3))
        (fn-pth-req-state-okp '(:acquire 3) 0 1 *p14-factor-state*))))
 :rule-classes nil)

; R11 ruling: redundancy control and selector exhaustion teeth.
(defun p15-accept-without-exhaustion (s1 out q)
  (declare (xargs :guard t))
  (let ((j (fn-rtc-free-slot 0 (fn-rtc-slots s1)))
        (r (fn-rtc-get 1 out)))
    (if (and (eq (fn-rtc-get 0 out) :done) j (natp r) (< r (expt 2 64)))
        (let* ((jinc (+ 1 (fn-rtc-s-inc (fn-rtc-slot j s1))))
               (s2 (fn-rtc-with-mstate
                    j (fn-rtc-m-init)
                    (fn-rtc-with-slot j (list jinc :live r) s1))))
          (mv-let (s3 acts refused c)
            (fn-rtc-deliver s2 j jinc (fn-rtc-ev :accept out j jinc nil) q)
            (mv-let (s4 acts2) (fn-rtc-rearm s3)
              (mv s4 (append acts acts2) refused c))))
      (mv-let (s2 acts2) (fn-rtc-rearm s1)
        (mv s2 acts2 nil 0)))))
(verify-guards p15-accept-without-exhaustion)
(defconst *p15-r11-exhausted*
 '((3 4 0 1 0 1 66560 3 65667)
   ((0 :live nil) (1 :live 0) (18446744073709551615 :free nil))
   ((0 (:free) nil) (0 (:free) nil) (0 (:free) nil) (0 (:free) nil))
   nil (nil nil nil) 0))
(value-triple
 (mv-let (after acts refused cost)
  (p15-accept-without-exhaustion *p15-r11-exhausted* '(:done 0) 100000)
  (cw "P15_R11_LITERAL selector=~x0 mutant-slot=~x1 acts=~x2 refused=~x3 cost=~x4~%"
   (fn-rtc-free-slot 0 (fn-rtc-slots *p15-r11-exhausted*))
   (fn-rtc-slot 2 after) acts refused cost)))
(defthm p15-literal-exhaustion-mutant-does-not-select-the-exhausted-slot
 (and (not (fn-rtc-free-slot 0 (fn-rtc-slots *p15-r11-exhausted*)))
      (equal (fn-rtc-slot 2 (mv-nth 0 (p15-accept-without-exhaustion *p15-r11-exhausted* '(:done 0) 100000)))
             '(18446744073709551615 :free nil))
      (equal (p15-accept-without-exhaustion *p15-r11-exhausted* '(:done 0) 100000)
             (fn-rtc-accept-branch *p15-r11-exhausted* '(:done 0) 100000))))
(defthm p15-accept-exhaustion-conjunct-is-implied-by-selector
 (implies (fn-rtc-free-slot 0 (fn-rtc-slots s))
  (fn-rtc-inc-roomp (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s)) s)))
 :hints (("Goal" :use
   ((:instance fn-rtc-free-slot-has-incarnation-room (i 0) (slots (fn-rtc-slots s)))
    (:instance fn-rtc-free-slot-index-type (i 0) (slots (fn-rtc-slots s))))
   :in-theory (union-theories (theory 'minimal-theory)
     '(fn-rtc-slot nfix natp posp default-+-1 default-+-2 unicity-of-0 fix commutativity-of-+
       (:type-prescription fn-rtc-free-slot) (:executable-counterpart binary-+) (:executable-counterpart unary--))))))
(defthm p15-literal-exhaustion-mutant-is-identical-for-every-state
 (equal (p15-accept-without-exhaustion s out q) (fn-rtc-accept-branch s out q))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(p15-accept-without-exhaustion fn-rtc-accept-branch
     p15-accept-exhaustion-conjunct-is-implied-by-selector)))))

; R11 RULED: remove the one exhaustion property at its selector and branch sites.
; The original branch-only mutant is retained above as a redundancy control.
(defun p15b-slot-selectable-without-exhaustion (slot)
 (declare (xargs :guard t))
 (eq (fn-rtc-s-status slot) :free))
(defun p15b-free-slot-without-exhaustion (i slots)
  (declare (xargs :guard (natp i) :measure (len slots)
    :hints (("Goal" :in-theory
      (union-theories (theory 'minimal-theory)
        '(len o< o-finp o-p natp (:type-prescription len)))))
    :guard-hints (("Goal" :in-theory
      (union-theories (theory 'minimal-theory)
        '(natp default-+-1 default-+-2))))))
  (if (consp slots)
      (if (and (not (zp i)) (p15b-slot-selectable-without-exhaustion (car slots)))
          i
        (p15b-free-slot-without-exhaustion (+ 1 i) (cdr slots)))
    nil))
(defun p15b-accept-without-exhaustion (s1 out q)
  (declare (xargs :guard t))
  (let ((j (p15b-free-slot-without-exhaustion 0 (fn-rtc-slots s1)))
        (r (fn-rtc-get 1 out)))
    (if (and (eq (fn-rtc-get 0 out) :done) j (natp r) (< r (expt 2 64)))
        (let* ((jinc (+ 1 (fn-rtc-s-inc (fn-rtc-slot j s1))))
               (s2 (fn-rtc-with-mstate
                    j (fn-rtc-m-init)
                    (fn-rtc-with-slot j (list jinc :live r) s1))))
          (mv-let (s3 acts refused c)
            (fn-rtc-deliver s2 j jinc (fn-rtc-ev :accept out j jinc nil) q)
            (mv-let (s4 acts2) (fn-rtc-rearm s3)
              (mv s4 (append acts acts2) refused c))))
      (mv-let (s2 acts2) (fn-rtc-rearm s1)
        (mv s2 acts2 nil 0)))))
(verify-guards p15b-slot-selectable-without-exhaustion)
(verify-guards p15b-free-slot-without-exhaustion)
(verify-guards p15b-accept-without-exhaustion)
; Small ground selector teeth, not claims that these states are reachable.
(defthm p15b-r11-exhaustion-removal-selects-a-retired-slot
 (let ((slots '((0 :live nil) (1 :live 0)
                (18446744073709551615 :free nil) (0 :free nil))))
  (and (fn-rtc-slotp (fn-rtc-get 2 slots))
       (not (fn-rtc-inc-roomp (fn-rtc-get 2 slots)))
       (equal (p15b-free-slot-without-exhaustion 0 slots) 2)
       (equal (fn-rtc-free-slot 0 slots) 3)
       (equal (+ 1 (fn-rtc-s-inc
                     (fn-rtc-get (p15b-free-slot-without-exhaustion 0 slots) slots)))
              18446744073709551616)
       (not (fn-rtc-u64p 18446744073709551616))))
 :rule-classes nil)
(defthm p15b-r11-retired-never-selected
 (let ((slots '((0 :live nil) (1 :live 0) (18446744073709551615 :free nil))))
  (and (fn-rtc-slotp (fn-rtc-get 2 slots))
       (not (fn-rtc-slot-selectablep (fn-rtc-get 2 slots)))
       (equal (p15b-free-slot-without-exhaustion 0 slots) 2)
       (not (fn-rtc-free-slot 0 slots))))
 :rule-classes nil)

; The same ruled mutant actually overflows; all request/delivery frames below
; are local to this proof, with no machine behavior assumption.
(encapsulate ()
(local
(defthm p15b-r11-mv0-cons-by-definition
 (equal (mv-nth 0 (cons a b)) a)
 :hints (("Goal" :in-theory (enable mv-nth)))))
(local
(defthm p15b-r11-request-inc-frame
 (equal (fn-rtc-s-inc (fn-rtc-slot j (mv-nth 0 (fn-rtc-request r id inc s))))
        (fn-rtc-s-inc (fn-rtc-slot j s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
    fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-live-p
    fn-rtc-slot-of-with fn-rtc-slot-accessors fn-rtc-issue-frame
    (:type-prescription fn-rtc-s-inc) (:type-prescription fn-rtc-nstatic) nfix natp car-cons cdr-cons mv-nth))))))
(local
(defthm p15b-r11-requests-inc-frame
 (equal (fn-rtc-s-inc (fn-rtc-slot j (mv-nth 0 (fn-rtc-requests rs id inc s))))
        (fn-rtc-s-inc (fn-rtc-slot j s)))
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-requests p15b-r11-request-inc-frame mv-nth car-cons cdr-cons))))))
(local
(defthm p15b-r11-deliver-inc-frame
 (equal (fn-rtc-s-inc (fn-rtc-slot j (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
        (fn-rtc-s-inc (fn-rtc-slot j s)))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-deliver p15b-r11-requests-inc-frame fn-rtc-slot-of-with p15b-r11-mv0-cons-by-definition car-cons cdr-cons))))))
(defthm p15b-r11-mutant-accept-reaches-incarnation-2^64
 (let ((after (mv-nth 0 (p15b-accept-without-exhaustion *p15-r11-exhausted* '(:done 0) 100000))))
  (and (fn-rtc-slotp (fn-rtc-slot 2 *p15-r11-exhausted*))
       (equal (fn-rtc-s-inc (fn-rtc-slot 2 *p15-r11-exhausted*)) 18446744073709551615)
       (equal (fn-rtc-s-inc (fn-rtc-slot 2 after)) 18446744073709551616)
       (not (fn-rtc-u64p (fn-rtc-s-inc (fn-rtc-slot 2 after))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) p15b-accept-without-exhaustion p15b-r11-deliver-inc-frame
    fn-rtc-slot-of-rearm fn-rtc-slot-of-with fn-rtc-slot-accessors
    car-cons cdr-cons p15b-r11-mv0-cons-by-definition
    (:executable-counterpart p15b-free-slot-without-exhaustion)
    (:executable-counterpart fn-rtc-slots) (:executable-counterpart fn-rtc-get)
    (:executable-counterpart fn-rtc-slot) (:executable-counterpart fn-rtc-slotp)
    (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-u64p)
    (:executable-counterpart nfix) (:executable-counterpart natp)
    (:executable-counterpart expt) (:executable-counterpart binary-+)
    (:executable-counterpart len) (:executable-counterpart <))))))
)

; Exercise the actual executable host begin, with a small allocated state.
; :last-valid reaches LIVE incarnation 2^64-1; :exhausted never allocates it again.
(defun p15b-r11-host-scene (mode fn-rtc-st)
 (declare (xargs :stobjs fn-rtc-st :guard t))
 (mv-let (fn-rtc-st okp left)
  (fn-hld-init *fn-bs-profile-development* '(3 nil 0 0 nil 0 0 0 nil 0 3) 4 fn-rtc-st)
  (declare (ignore left))
  (let* ((fn-rtc-st (fn-rtc-st-set-slot 2
                    (if (eq mode :last-valid) '(18446744073709551614 :free nil)
                      '(18446744073709551615 :free nil)) fn-rtc-st))
         (fn-rtc-st (fn-rtc-st-set-slot 3 (if (eq mode :skip) '(0 :free nil)
                     '(18446744073709551615 :free nil)) fn-rtc-st))
         (fn-rtc-st (fn-rtc-st-set-slot 4 '(18446744073709551615 :free nil) fn-rtc-st))
         (fn-rtc-st (if (eq mode :exhausted) (fn-rtc-st-set-uses nil fn-rtc-st) fn-rtc-st))
         (before (fn-rtc-x-state fn-rtc-st)))
   (mv-let (fn-rtc-st id inc pending) (fn-hld-begin 7 fn-rtc-st)
    (mv fn-rtc-st (list okp before (fn-rtc-x-state fn-rtc-st) id inc pending))))))
(defun p15b-r11-host-fixture (mode)
 (declare (xargs :guard t))
 (with-local-stobj fn-rtc-st
  (mv-let (fn-rtc-st result) (p15b-r11-host-scene mode fn-rtc-st) result)))
(verify-guards p15b-r11-host-scene)
(verify-guards p15b-r11-host-fixture)
(make-event
 (let ((last-valid (p15b-r11-host-fixture :last-valid))
       (exhausted (p15b-r11-host-fixture :exhausted))
       (skip (p15b-r11-host-fixture :skip)))
  `(progn
    (defconst *p15b-r11-last-valid* ',last-valid)
    (defconst *p15b-r11-exhausted* ',exhausted)
    (defconst *p15b-r11-skip* ',skip))))
(with-guard-checking-event nil
 (assert-event
  (let* ((r *p15b-r11-last-valid*) (s (nth 1 r)) (s2 (nth 2 r)))
   (and (car r) (fn-hll-invp s) (fn-hll-invp s2)
        (fn-rtc-inc-roomp (fn-rtc-slot 2 s))
        (equal (nth 3 r) 2) (equal (nth 4 r) 18446744073709551615)
        (equal (fn-rtc-slot 2 s2) '(18446744073709551615 :live 7))
        (fn-rtc-u64p (fn-rtc-s-inc (fn-rtc-slot 2 s2)))
        (not (fn-rtc-inc-roomp (fn-rtc-slot 2 s2)))))))
(with-guard-checking-event nil
 (assert-event
  (let* ((r *p15b-r11-exhausted*) (s (nth 1 r)) (s2 (nth 2 r)))
   (and (car r) (fn-hll-invp s) (fn-hll-invp s2)
        (fn-rtc-slots-exhaustedp 0 1 (fn-rtc-slots s))
        (not (fn-rtc-free-slot 0 (fn-rtc-slots s)))
        (equal (nth 3 r) nil) (equal (nth 4 r) :rtc-slots-exhausted)
        (equal (nth 5 r) nil) (equal s2 s)))))

(with-guard-checking-event nil
 (assert-event
  (let* ((r *p15b-r11-skip*) (s (nth 1 r)) (s2 (nth 2 r)))
   (and (car r) (fn-hll-invp s) (fn-hll-invp s2)
        (equal (fn-rtc-free-slot 0 (fn-rtc-slots s)) 3)
        (equal (nth 3 r) 3) (equal (nth 4 r) 1)
        (equal (fn-rtc-slot 2 s2) '(18446744073709551615 :free nil))
        (equal (fn-rtc-slot 3 s2) '(1 :live 7))))))

; ID+INC: the whole antecedent and a biting reachability-removal witness.
(defthm p15b-live-slot-u64-whole-antecedent-witness
 (and (fn-pth-reachablep *p13-request-domain-before*)
      (natp 1)
      (< 1 (fn-rtc-nslots (fn-rtc-config *p13-request-domain-before*)))
      (equal (fn-rtc-s-status (fn-rtc-slot 1 *p13-request-domain-before*)) :live)
      (< 1 (expt 2 64))
      (< (fn-rtc-s-inc (fn-rtc-slot 1 *p13-request-domain-before*)) (expt 2 64)))
 :rule-classes nil
 :hints (("Goal" :use (pthrt-p13-development-initial-state-is-reachable
                      p14-development-init-is-the-fixture-before)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:executable-counterpart fn-rtc-nslots) (:executable-counterpart fn-rtc-config)
     (:executable-counterpart fn-rtc-slot) (:executable-counterpart fn-rtc-s-status)
     (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart natp)
     (:executable-counterpart expt) (:executable-counterpart <)
     (:executable-counterpart equal))))))
; Removing reachability admits a live slot past the incarnation domain, even
; under the same admitted configuration and all the remaining hypotheses.
(defconst *p15b-scalar-unreachable*
 (fn-rtc-with-slot 2 '(18446744073709551616 :live 0) *p13-request-domain-before*))
(defthm p15b-live-slot-u64-reachability-removal-tooth
 (and (fn-rtc-st-cfg-okp (fn-rtc-config *p15b-scalar-unreachable*))
      (natp 2)
      (< 2 (fn-rtc-nslots (fn-rtc-config *p15b-scalar-unreachable*)))
      (equal (fn-rtc-s-status (fn-rtc-slot 2 *p15b-scalar-unreachable*)) :live)
      (not (and (< 2 (expt 2 64))
                (< (fn-rtc-s-inc (fn-rtc-slot 2 *p15b-scalar-unreachable*)) (expt 2 64))))
      (not (fn-pth-reachablep *p15b-scalar-unreachable*)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pth-live-slot-inc-below-2^64
   (s *p15b-scalar-unreachable*) (id 2)))
  :in-theory (union-theories (theory 'minimal-theory)
   '((:executable-counterpart fn-rtc-st-cfg-okp)
     (:executable-counterpart fn-rtc-nslots) (:executable-counterpart fn-rtc-config)
     (:executable-counterpart fn-rtc-slot) (:executable-counterpart fn-rtc-s-status)
     (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart natp)
     (:executable-counterpart expt) (:executable-counterpart <)
     (:executable-counterpart equal))))))


; I-AMEND-1: the evaluated S2 injection is excluded; exact old-I mutant bites.
; Injected state, not claimed reachable. The actual executor remains unchanged.
(make-event
 (let* ((world (w state))
        (ev (get-event 'fn-pth-i-post-state world))
        (clause '(implies flight (fn-cbor-octet-listp (fn-rtc-get 1 (fn-ptx-hs m)))))
        (names '((fn-pth-i-post-state . p15f-old-i-post-state) (fn-pth-i . p15f-old-i))))
  (if (equal (pthrt-r9-count-conjunct ev clause) 1)
   (value (list 'progn
    (pthrt-r8-rename (pthrt-r9-remove-conjunct ev clause) names)
    (pthrt-r8-rename (get-event 'fn-pth-i world) names)))
   (er soft 'p15f-old-i "Expected exactly the I-AMEND-1 clause."))))

(defun p15f-find-committing (obs)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp obs)
  (if (equal (fn-ptx-ph (fn-rtc-mstate 1 (nth 1 (car obs)))) :committing)
   (car obs) (p15f-find-committing (cdr obs))) nil))

(defun p15f-before-committing-ops (obs)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp obs)
  (if (equal (fn-ptx-ph (fn-rtc-mstate 1 (nth 1 (car obs)))) :committing)
   nil (cons (car (car obs)) (p15f-before-committing-ops (cdr obs)))) nil))

(defun p15f-commit-trailer-scene (fn-rtc-st)
 (declare (xargs :stobjs fn-rtc-st :guard t :verify-guards nil))
 (mv-let (fn-rtc-st observations)
  (pthrt-r8-fixed-execute (p15f-before-committing-ops *pthrt-host-observations*) fn-rtc-st)
  (declare (ignore observations))
  (let* ((original (fn-rtc-x-state fn-rtc-st))
         (m (fn-rtc-st-mstate 1 fn-rtc-st))
         (hs (fn-ptx-hs m))
         (bad-m (fn-ptx-chg m :hs (list (fn-rtc-get 0 hs) (make-list 32 :initial-element 256) (fn-rtc-get 2 hs))))
         (fn-rtc-st (fn-rtc-st-set-mstate 1 bad-m fn-rtc-st))
         (before (fn-rtc-x-state fn-rtc-st))
         (e (nth 1 (nth 0 (p15f-find-committing *pthrt-host-observations*))))
         (before-st-p (fn-rtc-st-p fn-rtc-st))
         (landing-unchanged (equal (fn-rtc-landed e before) e)))
   (mv-let (fn-rtc-st acts refused cost) (fn-pth-x-step* e 100000 fn-rtc-st)
    (declare (ignore acts cost))
    (let* ((after (fn-rtc-x-state fn-rtc-st)) (ma (fn-rtc-mstate 1 after)))
     (mv fn-rtc-st
      (list :original-old-I (p15f-old-i original) :before-old-I (p15f-old-i before) :after-old-I (p15f-old-i after)
            :original-I (fn-pth-i original) :original-okp (fn-ptx-okp m)
            :before-I (fn-pth-i before) :before-okp (fn-ptx-okp bad-m)
            :before-st-p before-st-p :landing-unchanged landing-unchanged
            :completion e :acts-on (fn-rtc-acts-on-p before e)
            :after-I (fn-pth-i after) :after-phase (fn-ptx-ph ma)
            :after-chain-octets (fn-cbor-octet-listp (fn-ptx-kd-last (fn-ptx-kd ma)))
            :refused refused :original original :before before :after after)))))))

(defun p15f-commit-trailer-fixture ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-rtc-st
  (mv-let (fn-rtc-st result) (p15f-commit-trailer-scene fn-rtc-st) result)))

(with-guard-checking-event nil
 (make-event
  (value (list 'defconst '*p15f-i-commit-tooth* (list 'quote (p15f-commit-trailer-fixture))))))

(with-guard-checking-event nil
 (assert-event
  (let ((r *p15f-i-commit-tooth*))
   (and (cadr (member-eq :original-I r)) (cadr (member-eq :original-old-I r))
        (cadr (member-eq :original-okp r))
        (not (cadr (member-eq :before-I r))) (cadr (member-eq :before-old-I r))
        (cadr (member-eq :before-okp r)) (cadr (member-eq :before-st-p r))
        (equal (cadr (member-eq :completion r)) '(:fsync 1 1 12 (:done 0)))
        (cadr (member-eq :landing-unchanged r)) (cadr (member-eq :acts-on r))
        (not (cadr (member-eq :refused r)))
        (equal (cadr (member-eq :after-phase r)) :idle)
        (not (cadr (member-eq :after-chain-octets r)))
        (not (cadr (member-eq :after-I r))) (not (cadr (member-eq :after-old-I r)))))))
