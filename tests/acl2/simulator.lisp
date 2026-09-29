; Deterministic ACL2 scenarios for the fn logical core.
;
; This is a host-side scenario catalog, not an implementation of acceptance:
; every transition below calls the certified functions from books/acceptance.

(in-package "ACL2")
; The certified acceptance core every scenario below calls.  tools/
; run_simulator.py also includes it; a repeated include-book is redundant.
(include-book "../../books/acceptance")

(defconst *fn-sim-groups* '("fn.letters" "fn.test"))
(defconst *fn-sim-message-id* "<simulator@example.invalid>")
; The payload is a HANDLE into the payload arena (books/acceptance.lisp:
; fn-payload-handle-p, a natural), never an octet list: an octet list here
; made fn-accept-prepare refuse (its natp check) and the acceptance-durable
; scenario read no pending, no article -- red since the arena (found by
; lane resilience-framework-5, 2026-09-29).
(defconst *fn-sim-payload* 4)
(defconst *fn-sim-stamp* 841000000)

(defun fn-sim-acceptance-initial ()
  (fn-initial-state *fn-sim-groups*))

(defun fn-sim-acceptance-prepared ()
  (fn-accept-prepare (fn-sim-acceptance-initial)
                     7
                     *fn-sim-message-id*
                     *fn-sim-payload*
                     *fn-sim-groups*
                     *fn-sim-stamp*))

(defun fn-sim-acceptance-durable ()
  (fn-accept-complete (fn-sim-acceptance-prepared) 0 7 :durable))

(defun fn-sim-acceptance-durable-okp ()
  (let ((initial (fn-sim-acceptance-initial))
        (prepared (fn-sim-acceptance-prepared))
        (durable (fn-sim-acceptance-durable)))
    (and (fn-statep initial)
         (fn-statep prepared)
         (fn-statep durable)
         (equal (fn-state-articles initial) nil)
         (equal (fn-state-articles prepared) nil)
         (equal (len (fn-state-articles durable)) 1)
         (equal (fn-article-stamp (car (fn-state-articles durable)))
                *fn-sim-stamp*)
         (equal (fn-state-next-txid durable) 1)
         (equal (fn-state-fenced durable) nil)
         (equal (fn-acceptedp *fn-sim-message-id*
                              (fn-state-articles durable))
                t))))

; -----------------------------------------------------------------------------
; W7f: the deterministic backend's exhaustive small world (design
; planning/design-resilience-framework-2026-09-29.md, row W7f; lane
; resilience-framework-5).  Two proposals A and B are prepared and completed
; in sequence under an exact schedule: each completion's status (:durable,
; :aborted, :indeterminate) and the generation it is delivered under (the
; one it was prepared under, or a changed one); after an indeterminate
; completion, the recovery result (:committed, :absent) delivered under
; either generation, then the same recovery repeated.  Every schedule runs
; through the executable transitions of books/acceptance from the initial
; state, and after EVERY step the state is a state and its view (the
; published Message-IDs, the pending Message-ID, the fence) is the oracle's.
; The oracle is the contract the book states in words, as a four-field
; machine that knows nothing of txids, watermarks or memberships: a
; completion or recovery means what it names (a mismatched generation
; changes nothing and the proposal stays pending); an indeterminate result
; fences until a matching recovery resolves it; a duplicate or a second
; proposal while one is pending is refused; a repeated recovery is a no-op.
; The run prints one FN_SIM_TRACE line per step and one FN_SIM_RESULT line
; for tools/run_simulator.py (scenario acceptance-world).

(defconst *fn-sim-world-generation* 7)
(defconst *fn-sim-world-statuses* '(:durable :aborted :indeterminate))
(defconst *fn-sim-world-results* '(:committed :absent))

; A step: (:prepare MSGID GEN) | (:complete MSGID GEN STATUS) |
; (:recover MSGID GEN RESULT).  A completion or recovery names the txid the
; proposal's prepare reserved (TXIDS: msgid -> txid, recorded at the prepare).

(defun fn-sim-world-step (s step txids)
  (let ((kind (car step))
        (msgid (cadr step))
        (gen (caddr step))
        (x (cadddr step)))
    (cond ((eq kind :prepare)
           (let* ((txid (fn-state-next-txid s))
                  (s2 (fn-accept-prepare s gen msgid *fn-sim-payload*
                                         *fn-sim-groups* *fn-sim-stamp*)))
             (mv s2 (if (equal s2 s) txids (acons msgid txid txids)))))
          ((eq kind :complete)
           (let ((txid (cdr (assoc-equal msgid txids))))
             (mv (if txid (fn-accept-complete s txid gen x) s) txids)))
          ((eq kind :recover)
           (let ((txid (cdr (assoc-equal msgid txids))))
             (mv (if txid (fn-accept-recover s txid gen x) s) txids)))
          (t (mv s txids)))))

; The oracle: (PUBLISHED PENDING PENDING-GEN FENCED).
(defun fn-sim-oracle-step (step o)
  (let ((kind (car step))
        (m (cadr step))
        (g (caddr step))
        (x (cadddr step))
        (published (car o))
        (pending (cadr o))
        (pgen (caddr o))
        (fenced (cadddr o)))
    (cond ((eq kind :prepare)
           (if (or fenced pending (member-equal m published))
               o
             (list published m g fenced)))
          ((not (and pending (equal pending m) (equal pgen g))) o)
          ((eq kind :complete)
           (cond (fenced o)
                 ((eq x :durable) (list (cons m published) nil nil nil))
                 ((eq x :aborted) (list published nil nil nil))
                 ((eq x :indeterminate) (list published pending pgen t))
                 (t o)))
          ((eq kind :recover)
           (cond ((not fenced) o)
                 ((eq x :committed) (list (cons m published) nil nil nil))
                 ((eq x :absent) (list published nil nil nil))
                 (t o)))
          (t o))))

; The view both sides are compared on: published Message-IDs as a set, the
; pending Message-ID or NIL, the fence.
(defun fn-sim-same-setp (a b)
  (and (subsetp-equal a b) (subsetp-equal b a) (equal (len a) (len b))))

(defun fn-sim-world-agreesp (s o)
  (and (fn-statep s)
       (fn-sim-same-setp (fn-article-msgids (fn-state-articles s)) (car o))
       (equal (and (consp (fn-state-pending s))
                   (fn-pending-msgid (fn-state-pending s)))
              (cadr o))
       (equal (equal (fn-state-fenced s) t) (equal (cadddr o) t))))

(defun fn-sim-world-run (steps s txids o k i)
  ; -> T when every step agrees; prints one trace line per step.
  (if (endp steps)
      t
    (mv-let (s2 txids2)
      (fn-sim-world-step s (car steps) txids)
      (let ((o2 (fn-sim-oracle-step (car steps) o))
            (step (car steps)))
        (prog2$
         (prog2$
          (cw "FN_SIM_ORACLE s=acceptance-world k=~x0 i=~x1 a=~x2 p=~s3 f=~x4 q=~x5~%"
              k i (len (car o2)) (or (cadr o2) "none")
              (if (cadddr o2) t nil)
              (+ (if (member-equal "A" (car o2)) 1 0)
                 (if (member-equal "B" (car o2)) 2 0)))
          (cw "FN_SIM_TRACE s=acceptance-world k=~x0 i=~x1 t=~x2 m=~s3 g=~x4 x=~x5 a=~x6 p=~s7 f=~x8 q=~x9~%"
             k i (car step) (cadr step) (caddr step) (or (cadddr step) '-)
             (len (fn-state-articles s2))
             (if (consp (fn-state-pending s2)) (fn-pending-msgid (fn-state-pending s2)) "none")
             (if (equal (fn-state-fenced s2) t) t nil)
             (+ (if (fn-acceptedp "A" (fn-state-articles s2)) 1 0)
                (if (fn-acceptedp "B" (fn-state-articles s2)) 2 0))))
         (and (fn-sim-world-agreesp s2 o2)
              (fn-sim-world-run (cdr steps) s2 txids2 o2 k (1+ i))))))))

; The schedules.
(defun fn-sim-world-completions (m g statuses acc)
  (if (endp statuses)
      acc
    (fn-sim-world-completions
     m g (cdr statuses)
     (list* (list (list :prepare m g) (list :complete m g (car statuses)))
            (list (list :prepare m g) (list :complete m (1+ g) (car statuses)))
            acc))))

(defun fn-sim-world-recoveries (m g results acc)
  (if (endp results)
      acc
    (fn-sim-world-recoveries
     m g (cdr results)
     (list* (list (list :prepare m g) (list :complete m g :indeterminate)
                  (list :recover m g (car results)) (list :recover m g (car results)))
            ; the first recovery under a changed generation is a no-op; the
            ; repeated one, under the proposal's, resolves it
            (list (list :prepare m g) (list :complete m g :indeterminate)
                  (list :recover m (1+ g) (car results)) (list :recover m g (car results)))
            acc))))

(defun fn-sim-world-proposal (m g)
  (fn-sim-world-recoveries m g *fn-sim-world-results*
                           (fn-sim-world-completions m g *fn-sim-world-statuses* nil)))

(defun fn-sim-world-after (a bs acc)
  (if (endp bs)
      acc
    (fn-sim-world-after a (cdr bs) (cons (append a (car bs)) acc))))

(defun fn-sim-world-cross (as bs acc)
  (if (endp as)
      acc
    (fn-sim-world-cross (cdr as) bs (fn-sim-world-after (car as) bs acc))))

(defun fn-sim-world-schedules ()
  (fn-sim-world-cross (fn-sim-world-proposal "A" *fn-sim-world-generation*)
                      (fn-sim-world-proposal "B" *fn-sim-world-generation*)
                      nil))

(defun fn-sim-world-all (schedules k passed)
  (if (endp schedules)
      passed
    (let ((ok (prog2$
               (cw "FN_SIM_PLAN s=acceptance-world k=~x0 n=~x1~%"
                   k (len (car schedules)))
               (fn-sim-world-run (car schedules) (fn-sim-acceptance-initial) nil
                                (list nil nil nil nil) k 0))))
      (fn-sim-world-all (cdr schedules) (1+ k) (and passed ok)))))

(defun fn-sim-world-report ()
  (let* ((schedules (fn-sim-world-schedules))
         (ok (fn-sim-world-all schedules 0 t)))
    (cw "FN_SIM_RESULT s=acceptance-world r=~s0 n=~x1~%"
        (if ok "passed" "failed") (len schedules))))
