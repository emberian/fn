; Signed MEM-013 witnesses, including the live concrete keystone subject.
(in-package "ACL2")
(include-book "../../books/history-image-concrete-proof")
(include-book "../../books/history-image-size")
(local (include-book "arithmetic/top" :dir :system))

(defconst *m13-fresh* '(nil nil nil nil nil nil))   ; the empty pgs-mem
(defconst *m13-c0*                                   ; the empty fn-hrecs$c
  '((nil nil nil nil nil nil) nil 0 0 0 (0 0 0 0 0) (1 1 1 1 1) 0 0 nil 0 0))
(defconst *m13-h3* '((:other 1 nil) (:other 2 nil) (:other 3 nil)))

;
; The entries are stobj-let functions, which have no ground logic value (update-fn-hrc-pgs is
; non-exec), so teeth on them RUN on the live fn-hrecs$c (assert-event, tests/acl2 style);
; S accepted this form for the keystone's positive tooth (audit of fd741adbc).
; fn-hrs-rel is a defun-nx and cannot run: the run asserts its conjuncts that can (img 1,
; nimg = len h, empty suffix, canonical lens/starts/npages, words = fn-hp-iw, all dirty), and
; the rel's own placement and vhold conjuncts are the ground defthm (a') on the pgs-level build.
(defun m13-dirty-live (p np pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (and (natp p) (natp np) (<= p np) (<= np (pgs-d-length pgs-mem)))
                  :measure (nfix (- (nfix np) (nfix p)))))
  (if (zp (- (nfix np) (nfix p)))
      t
    (and (equal (pgs-di p pgs-mem) 1) (m13-dirty-live (+ 1 (nfix p)) np pgs-mem))))

(defun m13-words-live (j iw pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (and (natp j) (true-listp iw) (<= (+ j (len iw)) (pgs-w-length pgs-mem)))
                  :measure (acl2-count iw)))
  (if (atom iw)
      t
    (and (equal (pgs-wi j pgs-mem) (car iw)) (m13-words-live (+ 1 (nfix j)) (cdr iw) pgs-mem))))

(defun m13-live-facts (h salt fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard t))
  (let ((np (ec-call (fn-hp-npages h salt)))
        (iw (ec-call (fn-hp-iw h salt))))
    (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
               (r)
               (and (natp np) (true-listp iw)
                    (<= np (pgs-d-length pgs-mem))
                    (<= (len iw) (pgs-w-length pgs-mem))
                    (list (pgs-w-length pgs-mem) (pgs-v-length pgs-mem) (pgs-d-length pgs-mem)
                          (m13-dirty-live 0 np pgs-mem)
                          (m13-words-live 0 iw pgs-mem)))
               r)))

; (a) positive, on the keystone's subject: the whole antecedent and the whole conclusion.
(assert-event
 (mv-let (v fn-hrecs$c) (fn-his-image-build-c *m13-h3* 0 fn-hrecs$c)
   (mv (and (natp 0) (fn-hp-okp *m13-h3* 0)
            (equal v :ok)
            (fn-hrc-wfp fn-hrecs$c)
            (equal (fn-hrc-img fn-hrecs$c) 1)
            (equal (fn-hrc-nimg fn-hrecs$c) (len *m13-h3*))
            (equal (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c))
            (equal (fn-hrc-salt fn-hrecs$c) 0)
            (equal (fn-hrc-lens fn-hrecs$c) (fn-hp-lens *m13-h3* 0))
            (equal (fn-hrc-starts fn-hrecs$c) (fn-hp-starts *m13-h3* 0))
            (equal (fn-hrc-npages fn-hrecs$c) (fn-hp-npages *m13-h3* 0))
            (let ((np (fn-hp-npages *m13-h3* 0)))
              (equal (m13-live-facts *m13-h3* 0 fn-hrecs$c) (list (* 2048 np) np np t t))))
       fn-hrecs$c))
 :stobjs-out '(nil fn-hrecs$c))

; (a') the rel's placement and vhold conjuncts, ground, on the pgs-level build.
(defthm fn-his-image-build-pgs-teeth-rel-conjuncts
  (let* ((res (fn-his-image-build-pgs *m13-h3* 0 *m13-fresh*)) (mem2 (mv-nth 5 res)))
    (and (equal (mv-nth 0 res) :ok)
         (adt-placement-ok (mv-nth 3 res) (mv-nth 2 res) (mv-nth 4 res))
         (fn-hp-vhold 0 (pgs-v-length mem2) mem2
                      (fn-hp-piw *m13-h3* 0 (mv-nth 3 res) (mv-nth 4 res)))
         (equal (nth *pgs-wi* mem2) (fn-hp-iw *m13-h3* 0))))
  :hints (("Goal" :in-theory (enable adt-placement-ok fn-hp-vhold-is-x fn-hp-vhold-x pgs-vi)))
  :rule-classes nil)

; (b) the dirty clause has teeth in the right direction: one clean page breaks it.
(defthm fn-his-image-build-teeth-one-clean-page
  (let* ((np (fn-hp-npages *m13-h3* 0))
         (res (fn-his-image-build-pgs *m13-h3* 0 *m13-fresh*))
         (d (nth *pgs-di* (mv-nth 5 res))))
    (and (fn-his-all-dirty 0 np d)
         (not (fn-his-all-dirty 0 np (update-nth 1 0 d)))
         (not (fn-his-all-dirty 0 np (update-nth (- np 1) 0 d)))))
  :rule-classes nil)

; (c) hypothesis removal for (fn-hp-okp h salt): a record whose tree is not encodable is
; refused BY NAME on the entry, and the concrete holds no image (nothing dropped, nothing
; half-delivered).  Also: the pass-1 lengths agree with the encoder on a real record.
(defconst *m13-bad* '((:other 1 nil) (:other 1/2 nil) (:other 3 nil)))
(assert-event
 (mv-let (v fn-hrecs$c) (fn-his-image-build-c *m13-bad* 0 fn-hrecs$c)
   (mv (and (not (fn-hp-okp *m13-bad* 0))
            (equal v '(:refused :event))
            (equal (fn-hrc-img fn-hrecs$c) 0) (equal (fn-hrc-nimg fn-hrecs$c) 0))
       fn-hrecs$c))
 :stobjs-out '(nil fn-hrecs$c))

(defthm fn-scc-program-len-teeth
  (and (equal (fn-scc-program-len '(:other 1 nil) 0) (len (fn-scc-encode '(:other 1 nil))))
       (equal (fn-scc-program-len '(:other 1 nil) 5) (+ 5 (len (fn-scc-encode '(:other 1 nil)))))
       (equal (fn-scc-program-len "abc" 0) (len (fn-scc-encode "abc"))))
  :rule-classes nil)

; (d) MUTATION witness of the plan check, on the sub-entry (not the keystone's subject): one
; row's length mis-summed (+8 octets in the pool) is refused by name and what it left is not
; the canonical image.  The stepped pass-2 and close are the real ones.
(defthm fn-his-image-build-teeth-missummed-plan
  (let* ((h *m13-h3*) (good (mv-nth 1 (fn-his-plan-all h (list 0 '(0 0 0 0 0)))))
         (bad (list (car good) (update-nth 4 (+ 8 (nth 4 (cadr good))) (cadr good)))))
    (mv-let (v starts np pgs-mem) (fn-his-image-open bad *m13-fresh*)
      (declare (ignore v))
      (mv-let (v pw pgs-mem) (fn-his-place-drive 4 h 0 *fn-his-pw0* starts np pgs-mem)
        (declare (ignore v))
        (mv-let (v pgs-mem) (fn-his-image-close bad pw starts pgs-mem)
          (and (equal v '(:refused :plan-mismatch))
               (not (equal (nth *pgs-wi* pgs-mem) (fn-hp-iw h 0))))))))
  :rule-classes nil)

; (e) HWM: the size claim, on the example (the bound is the statement above), and the
; allocation is exactly the canonical page count, once.
(defthm fn-his-image-build-teeth-size
  (let* ((h *m13-h3*) (np (fn-hp-npages h 0))
         (res (fn-his-image-build-pgs h 0 *m13-fresh*)) (mem2 (mv-nth 5 res)))
    (and (<= np (+ 1 (fn-hp-caps-sum (fn-hp-regs h 0))))
         (< np (+ 6 (/ (* 2 (fn-hp-regs-octets (fn-hp-regs h 0))) 16384)))
         (equal (pgs-w-length mem2) (* 2048 np))))
  :rule-classes nil)

; (f) steppable entries: the quantum is honoured (K rows, then :more with the rest) and
; composes: two runs of 1 then 2 rows = the plan of all three.
(defthm fn-his-plan-run-teeth-quantum
  (let ((p0 (list 0 '(0 0 0 0 0))))
    (mv-let (v1 r1 p1) (fn-his-plan-run 1 *m13-h3* p0)
      (mv-let (v2 r2 p2) (fn-his-plan-run 2 r1 p1)
        (and (equal v1 :more) (equal (len r1) 2) (equal v2 :done) (equal r2 nil)
             (equal p2 (mv-nth 1 (fn-his-plan-all *m13-h3* p0)))))))
  :rule-classes nil)

; (g) hypothesis removal for the fresh store: refused untouched.
(defthm fn-his-image-build-teeth-nonfresh-store
  (let* ((pgs-mem (list '(0) nil nil nil nil nil)))
    (mv-let (v starts np mem2) (fn-his-image-open '(3 (24 24 24 24 40)) pgs-mem)
      (declare (ignore starts np))
      (and (equal v '(:refused :image)) (equal mem2 pgs-mem))))
  :rule-classes nil)
