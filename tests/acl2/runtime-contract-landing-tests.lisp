; fn: witnesses for books/runtime-contract-landing.lisp (the host's landing
; of input into an :in-leased buffer).
;
; What this book is evidence FOR.  The four landing keystones are not vacuous
; and have teeth: on a reachable-shaped layer state (`rtcz-scene': slot 1 live
; with a :recv outstanding on buffer 0, :in-leased; buffer 1 free, a
; workspace of slot 1, or :out-leased to a :send of slot 1; slot 2 free with
; the listener's :accept armed) every hypothesis holds and the conclusion
; holds; dropping the :in-leased hypothesis of the hiding theorem makes the
; owning instance's view change; landing octets other than the ones the completion
; reports makes the contract see other octets; a splice that would grow a
; buffer past its capacity is refused rather than breaking the invariant.
;
; The witnesses use concrete copies of the machine-dependent contract
; functions, with the encapsulate's own constant, non-committing machine.
; The layer's copier renames their original definitions; no attachment is
; needed. The logical splice is evaluated through `fn-rtc-st$a-splice',
; the export's logic. `rtcz-model-invp' and `rtcz-model-step*' are this
; concrete instance's contract predicates and step.
;
; The ACL2 `test?' counterexample search (acl2s/cgen) over these scenes, run
; in the REPL (build/vertical-runs/landing/testq2.lsp, testq3.lsp): 2000
; examples each for L1, L2 (with its then-current view corollary) and L3 with the
; executable step equality, 2000 of 2000 satisfying the hypotheses, no
; counterexample; and with the :in-leased hypothesis removed (h = 1) or the
; landed octets replaced, test? finds counterexamples within 56 and 8 tries.

(in-package "ACL2")
(include-book "../../books/runtime-contract-layer")
(include-book "std/testing/assert-bang" :dir :system)

(defun rtcz-init () (declare (xargs :guard t)) nil)
(defun rtcz-static-init (j) (declare (xargs :guard t) (ignore j)) nil)
(defun rtcz-step (m ev pool q) (declare (xargs :guard t) (ignore m ev pool q)) (mv nil nil 0))
(defun rtcz-committedp (m) (declare (xargs :guard t) (ignore m)) nil)
(defun rtcz-c () (declare (xargs :guard t)) 0)
(defun rtcz-max-reqs () (declare (xargs :guard t)) 0)
(defun rtcz-max-state () (declare (xargs :guard t)) 1)
(make-event
 (let* ((machine '((fn-rtc-m-init . rtcz-init) (fn-rtc-m-static-init . rtcz-static-init)
                   (fn-rtc-m-step . rtcz-step) (fn-rtc-m-committedp . rtcz-committedp)
                   (fn-rtc-m-c . rtcz-c) (fn-rtc-m-max-reqs . rtcz-max-reqs)
                   (fn-rtc-m-max-state . rtcz-max-state)))
        (copies (fn-rtc-layer-alist 'rtcz-model *fn-rtc-layer-spec-fns*))
        (alist (append machine copies)))
   (cons 'progn (fn-rtc-layer-copies *fn-rtc-layer-spec-fns* :spec alist (w state)))))

(defun rtcz-octets (l n)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom l)) nil
    (cons (mod (nfix (car l)) 256) (rtcz-octets (cdr l) (- n 1)))))

(defun rtcz-scene (g off len b0 k b1 inc)
  (declare (xargs :guard t))
  (let* ((cap 8)
         (b0 (rtcz-octets b0 cap))
         (off (min (nfix off) (len b0)))
         (len (min (nfix len) (- cap off)))
         (g (nfix g)) (inc (+ 1 (nfix inc)))
         (b1 (rtcz-octets b1 cap))
         (k (mod (nfix k) 3))
         (buf1 (case k (0 (list 0 '(:free) b1))
                 (1 (list 3 (list :workspace 1 inc) b1))
                 (t (list 4 (list :leased 1 inc :out) b1))))
         (uses (append (list (list :recv 1 inc 0 (list 0 g off len)))
                       (if (equal k 2) (list (list :send 1 inc 1 (list 1 4 0 (len b1)))) nil)
                       (list (list :accept 0 0 2 nil)))))
    (list '(3 2 8 0 1 0 8) (list '(0 :live nil) (list inc :live 5) '(0 :free nil))
          (list (list g (list :leased 1 inc :in) b0) buf1) uses '(nil nil nil) 3)))

; The scene used below: buffer 0 holds "AB", the :recv's handle is (0 1 2 6),
; buffer 1 is slot 1's workspace holding (9).
(defconst *rtcz-st* (rtcz-scene 1 2 6 '(65 66) 1 '(9) 0))
(defconst *rtcz-data* '(67 68 69))
(defconst *rtcz-e* '(:recv 1 1 0 (:done 3)))

(assert! (rtcz-model-invp *rtcz-st*))
(assert! (fn-rtc-in-leased-p 0 *rtcz-st*))

; L1 positive: the landing at the handle keeps the invariant; so does a
; splice into the workspace.
(assert! (rtcz-model-invp (fn-rtc-st$a-splice 0 2 *rtcz-data* *rtcz-st*)))
(assert! (rtcz-model-invp (fn-rtc-st$a-splice 1 1 '(7 7 7) *rtcz-st*)))
; L1 mutation: writing the octets past the capacity by hand (what a splice
; refuses) breaks the invariant; the export leaves the state unchanged.
(assert! (not (rtcz-model-invp (fn-rtc-with-buffer 0 (list 1 '(:leased 1 1 :in) '(65 66 1 2 3 4 5 6 7))
                                               *rtcz-st*))))
(assert! (equal (fn-rtc-st$a-splice 0 2 '(1 2 3 4 5 6 7) *rtcz-st*) *rtcz-st*))

; L2 positive: the landing changes the octets of buffer 0 and nothing a
; machine sees.
(assert! (not (equal (fn-rtc-st$a-splice 0 2 *rtcz-data* *rtcz-st*) *rtcz-st*)))
(assert! (fn-rtc-pools-agree-off-in-leases-p (fn-rtc-pool *rtcz-st*)
                                             (fn-rtc-pool (fn-rtc-st$a-splice 0 2 *rtcz-data* *rtcz-st*))))
(defun rtcz-every-view-kept (i n s0 s1)
  (declare (xargs :guard (and (natp i) (natp n))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (let ((i (nfix i)) (n (nfix n)))
    (if (>= i n) t
      (let ((inc (fn-rtc-s-inc (fn-rtc-slot i s0))))
        (and (equal (fn-rtc-view i inc s1) (fn-rtc-view i inc s0))
             (rtcz-every-view-kept (+ 1 i) n s0 s1))))))
(assert! (rtcz-every-view-kept 0 (fn-rtc-nslots (fn-rtc-config *rtcz-st*))
                             *rtcz-st* (fn-rtc-st$a-splice 0 2 *rtcz-data* *rtcz-st*)))
(assert! (equal (fn-rtc-view 9 9 (fn-rtc-st$a-splice 0 2 *rtcz-data* *rtcz-st*))
                (fn-rtc-view 9 9 *rtcz-st*)))
; L2 removal of the :in-leased hypothesis: a splice into the workspace
; (buffer 1) is visible in the owning instance's view.
(assert! (not (fn-rtc-in-leased-p 1 *rtcz-st*)))
(assert! (not (equal (fn-rtc-view 1 1 (fn-rtc-st$a-splice 1 1 '(7) *rtcz-st*))
                     (fn-rtc-view 1 1 *rtcz-st*))))

; L3 positive: every hypothesis, and the contract sees exactly the landed
; octets.
(assert! (let ((u (fn-rtc-find-use (fn-rtc-key *rtcz-e*) (fn-rtc-uses *rtcz-st*))))
           (and (fn-rtc-completionp *rtcz-e*) u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (equal (fn-rtc-get 1 (fn-rtc-e-outcome *rtcz-e*)) (len *rtcz-data*))
                (<= (len *rtcz-data*) (fn-rtc-h-len (fn-rtc-u-hd u)))
                (equal (fn-rtc-landed *rtcz-e* (fn-rtc-st$a-splice (fn-rtc-h-buf (fn-rtc-u-hd u))
                                                                   (fn-rtc-h-off (fn-rtc-u-hd u))
                                                                   *rtcz-data* *rtcz-st*))
                       (fn-rtc-with-data *rtcz-e* *rtcz-data*))
                (equal (fn-rtc-e-data (fn-rtc-with-data *rtcz-e* *rtcz-data*)) '(67 68 69)))))
; L3 teeth: the host lands other octets than the completion's; the contract
; sees those, not *rtcz-data*.
(assert! (not (equal (fn-rtc-landed *rtcz-e* (fn-rtc-st$a-splice 0 2 '(1 2 3) *rtcz-st*))
                     (fn-rtc-with-data *rtcz-e* *rtcz-data*))))
; L3 teeth: a count beyond the landed octets (:done 3 against a landing of
; two) is not the landed data either.
(assert! (not (equal (fn-rtc-landed *rtcz-e* (fn-rtc-st$a-splice 0 2 '(67 68) *rtcz-st*))
                     (fn-rtc-with-data *rtcz-e* '(67 68)))))

; L4's right side: the contract's step of the completion carrying the
; octets returns buffer 0 to slot 1's workspace at generation 2 holding
; "ABCDE", and ends the :recv.
(assert! (mv-let (s3 acts refused cost)
           (rtcz-model-step* (fn-rtc-st$a-splice 0 2 *rtcz-data* *rtcz-st*)
                         (fn-rtc-with-data *rtcz-e* *rtcz-data*) 5)
           (declare (ignore acts refused cost))
           (and (equal (fn-rtc-buffer 0 s3) '(2 (:workspace 1 1) (65 66 67 68 69)))
                (not (fn-rtc-find-use '(:recv 1 1 0) (fn-rtc-uses s3)))
                (rtcz-model-invp s3))))

; L5 (`fn-rtc-landing-then-step-is-the-contract-step'): the landing then the
; step is the contract's step from the state before the landing.  Positive:
; the live connection's :recv.
(assert! (equal (mv-list 4 (rtcz-model-step* (fn-rtc-st$a-splice 0 2 *rtcz-data* *rtcz-st*)
                              (fn-rtc-with-data *rtcz-e* *rtcz-data*) 5))
                (mv-list 4 (rtcz-model-step* *rtcz-st* (fn-rtc-with-data *rtcz-e* *rtcz-data*) 5))))
; And when the completion does not act on a live instance: slot 1 draining
; with its :recv outstanding (the cross-review's state, 2026-10-09).  The
; buffer returns :free holding the landed octet on both sides.
(defconst *rtcz-drain* '((2 1 1 0 1 0 1) ((0 :live nil) (1 :draining 7)) ((1 (:leased 1 1 :in) nil))
                         ((:recv 1 1 0 (0 1 0 1))) (nil nil) 1))
(defconst *rtcz-drain-e* '(:recv 1 1 0 (:done 1)))
(assert! (rtcz-model-invp *rtcz-drain*))
(assert! (not (fn-rtc-acts-on-p *rtcz-drain* *rtcz-drain-e*)))
(assert! (equal (mv-list 4 (rtcz-model-step* (fn-rtc-st$a-splice 0 0 '(42) *rtcz-drain*)
                              (fn-rtc-with-data *rtcz-drain-e* '(42)) 5))
                (mv-list 4 (rtcz-model-step* *rtcz-drain* (fn-rtc-with-data *rtcz-drain-e* '(42)) 5))))
(assert! (equal (fn-rtc-buffer 0 (car (mv-list 2 (rtcz-model-step *rtcz-drain* (fn-rtc-with-data *rtcz-drain-e* '(42)) 5))))
                '(2 (:free) (42))))

; Amendment 1 regressions: neither an outstanding hand nor an unconsumed
; pool grant permits host input. Their exact-length/empty-byte invariants hold.
(defconst *rtcz-pinned-hand*
  '((3 2 8 1 1 0 8) ((0 :live nil) (1 :live 0) (1 :live 7))
    ((1 (:handed 1 1 2 1) (65)) (0 (:free) nil))
    ((:hand 1 1 0 (0 1 0 1))) (nil nil nil) 1))
(defconst *rtcz-pinned-pool*
  '((2 1 0 0 0 1 8) ((0 :live nil) (1 :live 7))
    ((1 (:leased 1 1 :in) nil)) ((:pool 1 1 0 (0 1 0 0))) (nil nil) 1))
(assert! (and (rtcz-model-invp *rtcz-pinned-hand*)
              (not (fn-rtc-splice-okp 0 1 '(66) *rtcz-pinned-hand*))
              (equal (fn-rtc-st$a-splice 0 1 '(66) *rtcz-pinned-hand*) *rtcz-pinned-hand*)))
(assert! (and (rtcz-model-invp *rtcz-pinned-pool*) (fn-rtc-in-leased-p 0 *rtcz-pinned-pool*)
              (not (fn-rtc-splice-okp 0 0 '(42) *rtcz-pinned-pool*))
              (equal (fn-rtc-st$a-splice 0 0 '(42) *rtcz-pinned-pool*) *rtcz-pinned-pool*)))
