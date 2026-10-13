; fn: witnesses for books/runtime-contract-host-lease.lisp (the host executor of the runtime contract for
; one ARTICLE response: init, begin, settle, quantum, sent, end over the stobj fn-rtc-st).
;
; What this book is evidence FOR.  The seven executor keystones are not vacuous and have teeth:
;   K1 fn-hld-quantum-sends-the-window     K2 fn-hld-init-establishes-invp
;   K3 fn-hld-begin-keeps-invp             K4 fn-hld-settle-keeps-invp
;   K5 fn-hld-sent-keeps-invp              K6 fn-hld-end-keeps-invp
;   K7 fn-hld-quantum-keeps-invp
; Each has a reachable positive witness asserting every hypothesis and the conclusion, a removal witness per
; hypothesis (that hypothesis false, every other one true, the conclusion false, or the reason none can exist),
; and a checked mutation naming the fault it models.
;
; The routes.  The drivers are stobj functions, so a scene is a RUN: each witness function below creates the
; process's stobjs locally (with-local-stobj), runs the real drivers, and reads the state back as the contract's
; list through fn-rtc-x-state (route b: the host's own reachable run, init with a configuration from
; fn-hl-rtc-config, then begin, quantum, sent, end).  fn-hll-invp is executable (the layer copy), so the
; keystones' conclusions are evaluated as written.  Where a hypothesis is about a value no live stobj can take
; (a state that is not fn-rtc-st-p, a window that is not an octet list) the witness uses route a, the logical
; twin the book proves equal (fn-hld-quantum-is-the-quantum-state: the driver's state is fn-hl-quantum-state)
; on the list read back from a live run.  K1's concrete array is a list built from the live state
; (hlt-c-of), checked against the real fn-rtc-st$corr.
;
; A non-invariant state is made by a raw export (fn-rtc-st-set-uses, -set-meta, -set-mstate, -init) that the
; contract's own step function never makes; the mutants are the drivers with one such fault, each a copy of the
; book's driver with the fault named in its comment.
;
; The seeded counterexample search over random run sequences is build/vertical-runs/host-lease/sonnet-teeth/
; search.lsp in the lane; its counts are in that file's header.

(in-package "ACL2")
(include-book "../../books/runtime-contract-host-lease")
(include-book "std/testing/assert-bang" :dir :system)
(local (set-inhibit-warnings "Invariant-risk"))

; ---------------------------------------------------------------------------
; The harness.

; BODY returns (mv result fn-rtc-st fn-dss-out); the stobjs are local to the scene.
(defmacro hlt-scene (body)
  `(with-local-stobj fn-rtc-st
     (mv-let (r fn-rtc-st)
       (with-local-stobj fn-dss-out
         (mv-let (r fn-rtc-st fn-dss-out) ,body (mv r fn-rtc-st)))
       r)))

; 2 + 1 + 3 connections: the listener, the owner, three connection slots; a pool of two leases of 1032 octets.
(defconst *hlt-cfg* '(3 nil 0 0 nil 0 0 0 nil 0 2))
(defconst *hlt-q* 4)
; past the stobj's limits (fn-rtc-st-cfg-okp): 2^32 + 2 slots
(defconst *hlt-big* '(4294967296 nil 0 0 nil 0 0 0 nil 0 2))
(defconst *hlt-bogus* '(:send 9 9 9 (0 0 0 1)))

(defun hlt-invp (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (and (fn-hll-invp (fn-rtc-x-state fn-rtc-st)) t))

(defun hlt-boot (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (mv-let (fn-rtc-st okp left) (fn-hld-init *fn-bs-profile-development* *hlt-cfg* *hlt-q* fn-rtc-st)
    (declare (ignore okp left))
    fn-rtc-st))

; a use no slot holds: the state is no longer invariant
(defun hlt-corrupt (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (fn-rtc-st-set-uses (cons *hlt-bogus* (fn-rtc-st-uses fn-rtc-st)) fn-rtc-st))

(defun hlt-boot-corrupt (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (let ((fn-rtc-st (hlt-boot fn-rtc-st))) (hlt-corrupt fn-rtc-st)))

; begin for resource R and the instance's workspace: (mv st id inc h), H nil while the request waits
(defun hlt-begin (r fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (mv-let (fn-rtc-st id inc left) (fn-hld-begin r fn-rtc-st)
    (declare (ignore left))
    (mv fn-rtc-st id inc (and id (fn-hld-workspace 0 id inc fn-rtc-st)))))

; the quantum of the window XS: (mv st out op n)
(defun hlt-quantum (xs h id inc fn-rtc-st fn-dss-out)
  (declare (xargs :stobjs (fn-rtc-st fn-dss-out) :mode :program))
  (let ((fn-dss-out (fn-dss-out-from-list xs fn-dss-out)))
    (mv-let (fn-rtc-st op n) (fn-hld-quantum h id inc fn-dss-out fn-rtc-st)
      (mv fn-rtc-st fn-dss-out op n))))

; ---------------------------------------------------------------------------
; The mutants: the book's drivers with one fault each.

; K2: an init that builds the fresh state and forgets to arm the listener's :accept (the raw fn-rtc-st-init
; instead of the layer's x-init).
(defun hlt-m-init-unarmed (profile cfg q fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (let ((c (fn-hl-rtc-config profile cfg q 1 0 0 0 0)))
    (if (fn-rtc-st-cfg-okp c)
        (let ((fn-rtc-st (fn-rtc-st-init c fn-rtc-st))) (mv fn-rtc-st t nil))
      (mv fn-rtc-st nil nil))))

; K3: a begin that gives the instance a machine state past the leased machine's bound (size 1).
(defun hlt-m-begin-bigstate (r fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (mv-let (fn-rtc-st id inc left) (fn-hld-begin r fn-rtc-st)
    (declare (ignore left))
    (let ((fn-rtc-st (if id (fn-rtc-st-set-mstate id '(1 2 3) fn-rtc-st) fn-rtc-st)))
      (mv fn-rtc-st id inc))))

; K3 / K4 setup: a begin that leaves its actions unsettled (so settle has work).
(defun hlt-begin-unsettled (r fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (let ((uses (fn-rtc-st-uses fn-rtc-st)) (j (fn-rtc-st-free-slot fn-rtc-st)))
    (if (and (natp r) (natp j) (fn-rtc-kind-out-p :accept 0 0 uses))
        (let ((op (fn-rtc-kind-op :accept 0 0 uses)))
          (mv-let (fn-rtc-st acts refused cost) (fn-hll-x-step* (list :accept 0 0 op (list :done r)) 1 fn-rtc-st)
            (declare (ignore acts refused cost))
            fn-rtc-st))
      fn-rtc-st)))

; K4: a settle that hands a waiting request its buffer by writing the owner itself (set-meta), leaving the
; :pool use outstanding, instead of completing the :pool action.
(defun hlt-m-settle-direct (work fuel fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (if (or (zp fuel) (atom work))
      (mv fn-rtc-st (if (atom work) nil work))
    (let ((a (car work)))
      (cond ((eq (fn-rtc-get 0 a) :pool)
             (let* ((h (fn-rtc-get 0 (fn-rtc-get 4 a)))
                    (fn-rtc-st (fn-rtc-st-set-meta h (fn-rtc-st-gen h fn-rtc-st)
                                                   (list :workspace (fn-rtc-get 1 a) (fn-rtc-get 2 a)) fn-rtc-st)))
               (hlt-m-settle-direct (cdr work) (- fuel 1) fn-rtc-st)))
            ((member-eq (fn-rtc-get 0 a) '(:grant :close :opened))
             (mv-let (fn-rtc-st acts refused cost)
               (fn-hll-x-step* (list (fn-rtc-get 0 a) (fn-rtc-get 1 a) (fn-rtc-get 2 a) (fn-rtc-get 3 a) '(:done 0)) 1 fn-rtc-st)
               (declare (ignore refused cost))
               (hlt-m-settle-direct (append (cdr work) (true-list-fix acts)) (- fuel 1) fn-rtc-st)))
            (t (hlt-m-settle-direct (cdr work) (- fuel 1) fn-rtc-st))))))

; K5: a sent that completes the send and then leaves H leased out, as if the socket still held it.
(defun hlt-m-sent-leased (h id inc op outcome fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (mv-let (fn-rtc-st left) (fn-hld-sent id inc op outcome fn-rtc-st)
    (let ((fn-rtc-st (fn-rtc-st-set-meta h (fn-rtc-st-gen h fn-rtc-st) (list :leased id inc :out) fn-rtc-st)))
      (mv fn-rtc-st left))))

; K6: an end that closes the instance and then frees its workspace itself (set-meta), instead of the close
; completion that releases it to the pool and grants the next waiter: the waiter is never granted.
(defun hlt-m-end-free (h id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (mv-let (fn-rtc-st acts refused cost) (fn-rtc-x-request '(:close) id inc fn-rtc-st)
    (declare (ignore acts refused cost))
    (let ((fn-rtc-st (fn-rtc-st-set-meta h (fn-rtc-st-gen h fn-rtc-st) '(:free) fn-rtc-st)))
      (mv fn-rtc-st nil))))

; K7: a quantum that marks H leased out to the send without submitting it.
(defun hlt-m-quantum-unsent (h id inc fn-dss-out fn-rtc-st)
  (declare (xargs :stobjs (fn-dss-out fn-rtc-st) :mode :program))
  (let ((fn-rtc-st (fn-rtc-st-set-meta h (fn-rtc-st-gen h fn-rtc-st) (list :leased id inc :out) fn-rtc-st)))
    (mv fn-rtc-st (fn-rtc-st-next-op fn-rtc-st) (fn-dss-out-len fn-dss-out))))

; K1: a quantum whose copy loop reads the render's window one octet late (wrapping), an off-by-one in the read
; index: every put succeeds and the send is accepted, but each cell holds its neighbour's octet.
(defun hlt-m-copy-late (i n h fn-dss-out fn-rtc-st)
  (declare (xargs :stobjs (fn-dss-out fn-rtc-st) :mode :program))
  (if (and (< i n) (< i (fn-dss-out-len fn-dss-out)))
      (let ((fn-rtc-st (fn-rtc-st-put h i (fn-dss-out-get (mod (+ i 1) n) fn-dss-out) fn-rtc-st)))
        (hlt-m-copy-late (+ 1 i) n h fn-dss-out fn-rtc-st))
    fn-rtc-st))
(defun hlt-m-quantum-late (h id inc fn-dss-out fn-rtc-st)
  (declare (xargs :stobjs (fn-dss-out fn-rtc-st) :mode :program))
  (let ((n (fn-dss-out-len fn-dss-out)) (cfg (fn-rtc-st-config fn-rtc-st)))
    (if (and (natp h) (< h (fn-rtc-nbufs cfg))
             (equal (fn-rtc-st-owner h fn-rtc-st) (list :workspace id inc))
             (fn-rtc-x-live-p id inc fn-rtc-st)
             (not (fn-rtc-kind-out-p :send id inc (fn-rtc-st-uses fn-rtc-st)))
             (< 0 n) (<= n (fn-rtc-buf-cap h cfg)))
        (let* ((g (fn-rtc-st-gen h fn-rtc-st)) (op (fn-rtc-st-next-op fn-rtc-st))
               (fn-rtc-st (hlt-m-copy-late 0 n h fn-dss-out fn-rtc-st)))
          (mv-let (fn-rtc-st acts refused cost)
            (fn-rtc-x-request (list :submit :send (list h g 0 n) nil) id inc fn-rtc-st)
            (declare (ignore acts cost))
            (mv fn-rtc-st (if refused nil op) n)))
      (mv fn-rtc-st nil 0))))

; ---------------------------------------------------------------------------
; K2: fn-hld-init-establishes-invp.  Result: (okp invp-after).
(defun hlt-k2 (cfg dirtyp mutp)
  (declare (xargs :mode :program))
  (hlt-scene
   (let ((fn-rtc-st (if dirtyp (hlt-boot-corrupt fn-rtc-st) fn-rtc-st)))
     (mv-let (fn-rtc-st okp left)
       (if mutp
           (hlt-m-init-unarmed *fn-bs-profile-development* cfg *hlt-q* fn-rtc-st)
         (fn-hld-init *fn-bs-profile-development* cfg *hlt-q* fn-rtc-st))
       (declare (ignore left))
       (mv (list okp (hlt-invp fn-rtc-st)) fn-rtc-st fn-dss-out)))))

; positive: the hypothesis (okp) and the conclusion, on a fresh stobj and on a dirty one (no hypothesis on the prior state)
(assert! (equal (hlt-k2 *hlt-cfg* nil nil) '(t t)))
(assert! (equal (hlt-k2 *hlt-cfg* t nil) '(t t)))
; okp removed: a configuration past the stobj's limits is refused, the state untouched; the untouched
; stobj, fresh or dirty, is not fn-hll-invp (the fresh state has no listener armed)
(assert! (equal (hlt-k2 *hlt-big* nil nil) '(nil nil)))
(assert! (equal (hlt-k2 *hlt-big* t nil) '(nil nil)))
; mutation (a driver fault): an init that forgets to arm the listener returns okp and a non-invariant state
(assert! (equal (hlt-k2 *hlt-cfg* nil t) '(t nil)))

; ---------------------------------------------------------------------------
; K3: fn-hld-begin-keeps-invp.  Result per begin: (hyp id inc workspace invp-after).
(defun hlt-k3-tuple (r fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (let ((hyp (hlt-invp fn-rtc-st)))
    (mv-let (fn-rtc-st id inc h) (hlt-begin r fn-rtc-st)
      (mv fn-rtc-st (list hyp id inc h (hlt-invp fn-rtc-st))))))

(defun hlt-k3-run (r fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :mode :program))
  (let ((fn-rtc-st (hlt-boot fn-rtc-st)))
    (mv-let (fn-rtc-st a) (hlt-k3-tuple r fn-rtc-st)
      (mv-let (fn-rtc-st b) (hlt-k3-tuple (+ r 1) fn-rtc-st)
        (mv-let (fn-rtc-st c) (hlt-k3-tuple (+ r 2) fn-rtc-st)
          (mv-let (fn-rtc-st d) (hlt-k3-tuple (+ r 3) fn-rtc-st)
            (mv fn-rtc-st (list a b c d))))))))
(defun hlt-k3-pos ()
  (declare (xargs :mode :program))
  (hlt-scene (mv-let (fn-rtc-st r) (hlt-k3-run 7 fn-rtc-st) (mv r fn-rtc-st fn-dss-out))))
(defun hlt-k3-removal ()
  (declare (xargs :mode :program))
  (hlt-scene (let ((fn-rtc-st (hlt-boot-corrupt fn-rtc-st)))
               (mv-let (fn-rtc-st a) (hlt-k3-tuple 7 fn-rtc-st) (mv a fn-rtc-st fn-dss-out)))))
(defun hlt-k3-mut ()
  (declare (xargs :mode :program))
  (hlt-scene (let* ((fn-rtc-st (hlt-boot fn-rtc-st)) (hyp (hlt-invp fn-rtc-st)))
               (mv-let (fn-rtc-st id inc) (hlt-m-begin-bigstate 7 fn-rtc-st)
                 (mv (list hyp id inc (hlt-invp fn-rtc-st)) fn-rtc-st fn-dss-out)))))

; positive (route b): three begins (the first two are granted a buffer at once; the third waits for one: no
; workspace yet) and a fourth with no free slot (a refused no-op); the hypothesis holds before each, the
; conclusion after
(assert! (equal (hlt-k3-pos)
                '((t 2 1 0 t) (t 3 1 1 t) (t 4 1 nil t) (t nil nil nil t))))
; invp removed: a state holding a use no slot holds; begin runs (it returns the instance) and the result is
; not invariant either
(assert! (equal (hlt-k3-removal) '(nil 2 1 0 nil)))
; mutation (a driver fault): a begin that gives the instance a machine state past the leased machine's bound
(assert! (equal (hlt-k3-mut) '(t 2 1 nil)))
; mutation (an edited conclusion): "begin always leaves the instance its workspace" is refuted by the
; third begin of the positive witness (it waits for a pool buffer)
(assert! (let ((third (third (hlt-k3-pos)))) (and (nth 4 third) (not (nth 3 third)))))

; ---------------------------------------------------------------------------
; K4: fn-hld-settle-keeps-invp.  The state after an unsettled begin holds :grant and :pool actions.
; Result: (hyp invp-after left workspace-of-instance-2).
(defun hlt-k4 (corruptp work-kind fuel mutp)
  (declare (xargs :mode :program))
  (hlt-scene
   (let* ((fn-rtc-st (hlt-boot fn-rtc-st))
          (fn-rtc-st (hlt-begin-unsettled 7 fn-rtc-st))
          (fn-rtc-st (if corruptp (hlt-corrupt fn-rtc-st) fn-rtc-st))
          (hyp (hlt-invp fn-rtc-st))
          (work (case work-kind
                  (:uses (fn-rtc-st-uses fn-rtc-st))
                  (:junk (list '(:grant 9 9 9 nil) 5 '(:pool 9 9 9 (9 9 9 9)) nil))
                  (t nil)))
          (fuel (if (eq fuel :full) (fn-hld-fuel fn-rtc-st) fuel)))
     (mv-let (fn-rtc-st left)
       (if mutp (hlt-m-settle-direct work fuel fn-rtc-st) (fn-hld-settle work fuel fn-rtc-st))
       (mv (list hyp (hlt-invp fn-rtc-st) left (fn-hld-workspace 0 2 1 fn-rtc-st)) fn-rtc-st fn-dss-out)))))

; positive (route b): the pending :grant, :pool and :accept actions of an unsettled begin completed to fixpoint
; (instance 2 holds buffer 0; the :accept stays outstanding); the same with fuel 1 (a prefix, actions left);
; with nothing to do; and junk work naming no use (every completion refused)
(assert! (equal (hlt-k4 nil :uses :full nil) '(t t nil 0)))
(assert! (let ((r (hlt-k4 nil :uses 1 nil))) (and (nth 0 r) (nth 1 r) (nth 2 r))))
(assert! (equal (hlt-k4 nil :none :full nil) '(t t nil nil)))
(assert! (equal (hlt-k4 nil :junk :full nil) '(t t nil nil)))
; invp removed: a state holding a use no slot holds; settle runs (it completes the instance's grant) and the
; result is not invariant either
(assert! (equal (hlt-k4 t :uses :full nil) '(nil nil nil 0)))
; mutation (a driver fault): a settle that writes the waiting request's buffer owner itself and leaves the
; :pool use outstanding
(assert! (equal (hlt-k4 nil :uses :full t) '(t nil nil 0)))
; mutation (an edited conclusion): "settle leaves no action unsettled" is refuted by the fuel-1 run
(assert! (and (nth 2 (hlt-k4 nil :uses 1 nil)) t))

; ---------------------------------------------------------------------------
; K5: fn-hld-sent-keeps-invp.  Instance 2 begins, renders "ABC", and the socket completes the send.
; Result: (hyp invp-after workspace-of-instance-2).
(defun hlt-k5 (outcome corruptp mutp)
  (declare (xargs :mode :program))
  (hlt-scene
   (let ((fn-rtc-st (hlt-boot fn-rtc-st)))
     (mv-let (fn-rtc-st id inc h) (hlt-begin 7 fn-rtc-st)
       (mv-let (fn-rtc-st fn-dss-out op n) (hlt-quantum '(65 66 67) h id inc fn-rtc-st fn-dss-out)
         (declare (ignore n))
         (let* ((fn-rtc-st (if corruptp (hlt-corrupt fn-rtc-st) fn-rtc-st))
                (hyp (hlt-invp fn-rtc-st)))
           (mv-let (fn-rtc-st left)
             (if mutp
                 (hlt-m-sent-leased h id inc op outcome fn-rtc-st)
               (fn-hld-sent id inc op outcome fn-rtc-st))
             (declare (ignore left))
             (mv (list hyp (hlt-invp fn-rtc-st) (fn-hld-workspace 0 id inc fn-rtc-st))
                 fn-rtc-st fn-dss-out))))))))

; positive (route b): the socket took all three octets, took one, or failed; the instance's workspace is its
; workspace again (buffer 0)
(assert! (equal (hlt-k5 '(:done 3) nil nil) '(t t 0)))
(assert! (equal (hlt-k5 '(:done 1) nil nil) '(t t 0)))
(assert! (equal (hlt-k5 '(:failed 5) nil nil) '(t t 0)))
; invp removed: a state holding a use no slot holds, then the same completion: the result is not invariant
(assert! (equal (hlt-k5 '(:done 3) t nil) '(nil nil 0)))
; mutation (a driver fault): a sent that leaves the buffer leased out to a send that has completed
(assert! (equal (hlt-k5 '(:done 3) nil t) '(t nil nil)))

; ---------------------------------------------------------------------------
; K6: fn-hld-end-keeps-invp.  Three instances begin (the third waits for a buffer), the first renders and
; sends, then the first ends.  Result: (hyp invp-after workspace-of-instance-4-after-end).
(defun hlt-k6 (corruptp mutp unknownp)
  (declare (xargs :mode :program))
  (hlt-scene
   (let ((fn-rtc-st (hlt-boot fn-rtc-st)))
     (mv-let (fn-rtc-st id inc h) (hlt-begin 7 fn-rtc-st)
       (mv-let (fn-rtc-st id2 inc2 h2) (hlt-begin 8 fn-rtc-st)
         (declare (ignore id2 inc2 h2))
         (mv-let (fn-rtc-st id3 inc3 h3) (hlt-begin 9 fn-rtc-st)
           (declare (ignore h3))
           (mv-let (fn-rtc-st fn-dss-out op n) (hlt-quantum '(65 66 67) h id inc fn-rtc-st fn-dss-out)
             (declare (ignore n))
             (mv-let (fn-rtc-st left) (fn-hld-sent id inc op '(:done 3) fn-rtc-st)
               (declare (ignore left))
               (let* ((fn-rtc-st (if corruptp (hlt-corrupt fn-rtc-st) fn-rtc-st))
                      (hyp (hlt-invp fn-rtc-st))
                      (eid (if unknownp 99 id)))
                 (mv-let (fn-rtc-st left)
                   (if mutp (hlt-m-end-free h eid inc fn-rtc-st) (fn-hld-end eid inc fn-rtc-st))
                   (declare (ignore left))
                   (mv (list hyp (hlt-invp fn-rtc-st) (fn-hld-workspace 0 id3 inc3 fn-rtc-st))
                       fn-rtc-st fn-dss-out)))))))))))

; positive (route b): ending the first instance releases its buffer and the waiting third instance is granted
; it (buffer 0); ending an instance that does not exist is a refused no-op and the waiter still waits
(assert! (equal (hlt-k6 nil nil nil) '(t t 0)))
(assert! (equal (hlt-k6 nil nil t) '(t t nil)))
; invp removed: a state holding a use no slot holds; end runs and the result is not invariant either
(assert! (equal (hlt-k6 t nil nil) '(nil nil 0)))
; mutation (a driver fault): an end that frees the buffer itself; the waiter is never granted
(assert! (equal (hlt-k6 nil t nil) '(t nil nil)))

; ---------------------------------------------------------------------------
; K7: fn-hld-quantum-keeps-invp.  Instance 2 begins and its quantum is run with the window XS (from the
; render's fn-dss-out, always an octet list).  Result: (hyp invp-after op n).
(defun hlt-k7 (xs corruptp mode)
  (declare (xargs :mode :program))
  (hlt-scene
   (let ((fn-rtc-st (hlt-boot fn-rtc-st)))
     (mv-let (fn-rtc-st id inc h) (hlt-begin 7 fn-rtc-st)
       (let* ((fn-rtc-st (if corruptp (hlt-corrupt fn-rtc-st) fn-rtc-st))
              (hyp (hlt-invp fn-rtc-st))
              (h (if (eq mode :wrong-buffer) (+ 1 h) h))
              (fn-dss-out (fn-dss-out-from-list xs fn-dss-out)))
         (mv-let (fn-rtc-st op n)
           (if (eq mode :mut)
               (hlt-m-quantum-unsent h id inc fn-dss-out fn-rtc-st)
             (fn-hld-quantum h id inc fn-dss-out fn-rtc-st))
           (mv (list hyp (hlt-invp fn-rtc-st) op n) fn-rtc-st fn-dss-out)))))))

; positive (route b): a window of three octets is sent (op 5, the contract's next operation)
(assert! (equal (hlt-k7 '(65 66 67) nil :real) '(t t 5 3)))
; ... and the quantum's refusals keep the state: an empty window, a window past the lease's capacity (1032),
; a buffer that is not the instance's workspace
(assert! (equal (hlt-k7 nil nil :real) '(t t nil 0)))
(assert! (equal (hlt-k7 (make-list 1033 :initial-element 7) nil :real) '(t t nil 0)))
(assert! (equal (hlt-k7 '(65 66 67) nil :wrong-buffer) '(t t nil 0)))
; invp removed: a state holding a use no slot holds; the quantum runs and the result is not invariant either
(assert! (equal (hlt-k7 '(65 66 67) t :real) '(nil nil 5 3)))
; mutation (a driver fault): a quantum that leases the buffer out without submitting the send
(assert! (equal (hlt-k7 '(65 66 67) nil :mut) '(t nil 5 3)))

; out-p removed (route a): a window that is not an octet list (no live fn-dss-out holds one).  Here the
; conclusion does NOT fail: the twin of the driver's state on the list a live run reads back stays invariant,
; because the contract's put refuses the non-octet (the octets before it land, the rest do not).  The
; hypothesis is carried by the proof (the puts' shape lemma needs it), and no scene in the seeded search
; (search.lsp, windows with non-octets) breaks the conclusion without it.  The witness: out-p false, invp
; true before, the twin's result invariant.
(defun hlt-k7-nonoctet ()
  (declare (xargs :mode :program))
  (hlt-scene
   (let ((fn-rtc-st (hlt-boot fn-rtc-st)))
     (mv-let (fn-rtc-st id inc h) (hlt-begin 7 fn-rtc-st)
       (let ((s (fn-rtc-x-state fn-rtc-st)) (out '(65 300 67)))
         (mv (list (fn-hll-invp s) (and (fn-cbor-octet-listp out) t)
                   (fn-hll-invp (fn-hl-quantum-state h out id inc s))
                   (fn-hll-invp (fn-hl-quantum-state h '(65 66 67) id inc s)))
             fn-rtc-st fn-dss-out))))))
(assert! (equal (hlt-k7-nonoctet) '(t nil t t)))

; ---------------------------------------------------------------------------
; K1: fn-hld-quantum-sends-the-window.  The concrete object (the stobj's foundation) that a list state stands
; for: configuration, slots, machine states, meta cells (gen owner fill), the one octet array (each buffer's
; octets then zeros to its capacity), uses, next operation.
(defun hlt-pad (l n)
  (declare (xargs :mode :program))
  (if (zp n) nil (cons (if (consp l) (car l) 0) (hlt-pad (if (consp l) (cdr l) nil) (- n 1)))))
(defun hlt-c-bytes (h n pool cfg)
  (declare (xargs :mode :program))
  (if (< h n)
      (append (hlt-pad (fn-rtc-get 2 (car pool)) (fn-rtc-buf-cap h cfg)) (hlt-c-bytes (+ 1 h) n (cdr pool) cfg))
    nil))
(defun hlt-c-meta (pool)
  (declare (xargs :mode :program))
  (if (consp pool)
      (cons (list (fn-rtc-get 0 (car pool)) (fn-rtc-get 1 (car pool)) (len (fn-rtc-get 2 (car pool))))
            (hlt-c-meta (cdr pool)))
    nil))
(defun hlt-c-of (s)
  (declare (xargs :mode :program))
  (list (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-mstates s) (hlt-c-meta (fn-rtc-pool s))
        (hlt-c-bytes 0 (fn-rtc-nbufs (fn-rtc-config s)) (fn-rtc-pool s) (fn-rtc-config s))
        (fn-rtc-uses s) (fn-rtc-next-op s)))

; The run: (before after h id inc op n live-st-p).  MUTP selects the late-read quantum.
(defun hlt-k1-run (xs mutp)
  (declare (xargs :mode :program))
  (hlt-scene
   (let ((fn-rtc-st (hlt-boot fn-rtc-st)))
     (mv-let (fn-rtc-st id inc h) (hlt-begin 7 fn-rtc-st)
       (let* ((before (fn-rtc-x-state fn-rtc-st)) (stp (and (fn-rtc-st-p fn-rtc-st) t))
              (fn-dss-out (fn-dss-out-from-list xs fn-dss-out)))
         (mv-let (fn-rtc-st op n)
           (if mutp
               (hlt-m-quantum-late h id inc fn-dss-out fn-rtc-st)
             (fn-hld-quantum h id inc fn-dss-out fn-rtc-st))
           (mv (list before (fn-rtc-x-state fn-rtc-st) h id inc op n stp) fn-rtc-st fn-dss-out)))))))

; The keystone's hypotheses, in order: st-p, out-p, the quantum's op, corr; and its conclusion.
(defun hlt-k1-hyps (r out c)
  (declare (xargs :mode :program))
  (let ((before (nth 0 r)) (after (nth 1 r)) (op (nth 5 r)))
    (list (and (fn-rtc-st$ap before) t) (and (fn-cbor-octet-listp out) t) (and op t)
          (and (fn-rtc-st$corr c after) t))))
(defun hlt-k1-concl (r out c)
  (declare (xargs :mode :program))
  (let ((before (nth 0 r)) (after (nth 1 r)) (h (nth 2 r)) (id (nth 3 r)) (inc (nth 4 r)) (op (nth 5 r)))
    (and (member-equal (list :send id inc op (list h (fn-rtc-get 0 (fn-rtc-buffer h before)) 0 (len out)))
                       (fn-rtc-uses after))
         (equal (fn-rtc-c-octets (fn-rtc-buf-base h (fn-rtc-config before)) (len out) (nth *fn-rtc-c-bytesi* c)) out)
         t)))
(defconst *hlt-win* '(65 66 67))

; positive (route b, the live run): every hypothesis, the conclusion, and the stobj's own recognizer
(assert! (let* ((r (hlt-k1-run *hlt-win* nil)) (c (hlt-c-of (nth 1 r))))
           (and (equal (hlt-k1-hyps r *hlt-win* c) '(t t t t))
                (hlt-k1-concl r *hlt-win* c)
                (nth 7 r)
                (equal (nth 5 r) 5)
                (equal (fn-rtc-c-octets (fn-rtc-buf-base (nth 2 r) (fn-rtc-config (nth 0 r))) 3 (nth *fn-rtc-c-bytesi* c))
                       '(65 66 67)))))
; the op removed: a window past the lease's capacity is refused (op nil, state unchanged, so the unchanged
; state and its concrete object still correspond); no send is outstanding
(assert! (let* ((xs (make-list 1033 :initial-element 7)) (r (hlt-k1-run xs nil)) (c (hlt-c-of (nth 1 r))))
           (and (equal (hlt-k1-hyps r xs c) '(t t nil t))
                (not (hlt-k1-concl r xs c)))))
; ... and the empty window
(assert! (let* ((r (hlt-k1-run nil nil)) (c (hlt-c-of (nth 1 r))))
           (and (equal (hlt-k1-hyps r nil c) '(t t nil t))
                (not (hlt-k1-concl r nil c)))))
; corr removed: a concrete array whose octet at the buffer's base is not the window's
(assert! (let* ((r (hlt-k1-run *hlt-win* nil))
                (c0 (hlt-c-of (nth 1 r)))
                (base (fn-rtc-buf-base (nth 2 r) (fn-rtc-config (nth 0 r))))
                (c (update-nth *fn-rtc-c-bytesi* (update-nth base 0 (nth *fn-rtc-c-bytesi* c0)) c0)))
           (and (equal (hlt-k1-hyps r *hlt-win* c) '(t t t nil))
                (not (hlt-k1-concl r *hlt-win* c)))))
; out-p removed (route a): the twin of the driver's state for a window with a non-octet, on the list a live run
; reads back, with the op the book proves the driver returns when it does not refuse (the contract's next
; operation, supplied here).  The contract's puts refuse the non-octet, so the fill falls short of the window,
; the send is refused, and the conclusion fails with the other three hypotheses true.  The driver itself would
; return op nil there (no :send in the twin's uses), so out-p is not removable alone from a driver run that
; sends; the witness shows the conclusion needs out-p when op is taken as given.
(assert! (let* ((r (hlt-k1-run *hlt-win* nil))
                (out '(65 300 67))
                (after (fn-hl-quantum-state (nth 2 r) out (nth 3 r) (nth 4 r) (nth 0 r)))
                (r2 (list (nth 0 r) after (nth 2 r) (nth 3 r) (nth 4 r) (fn-rtc-next-op (nth 0 r))))
                (c (hlt-c-of after)))
           (and (equal (hlt-k1-hyps r2 out c) '(t nil t t))
                (not (hlt-k1-concl r2 out c))
                (not (fn-rtc-kind-out-p :send (nth 3 r) (nth 4 r) (fn-rtc-uses after))))))
; st-p removed (route a): shape faults put into the list a live run reads back (fn-rtc-st$ap false), the twin of
; the driver's state, the op taken as the contract's next operation.  A buffer record with a stray field at H
; is rebuilt by the quantum, so corr, out-p and op hold and so does the conclusion: that fault does not refute
; the keystone.  A buffer generation that is no natural survives into the after state, so corr fails and the
; conclusion fails with st-p and corr false.  No
; shape fault in the seeded scan (sonnet-teeth/stp.lsp: ten faults) leaves corr true and the conclusion false, so st-p is
; carried by the proof, not independently refutable on these scenes.
(assert! (let* ((r (hlt-k1-run *hlt-win* nil)) (h (nth 2 r)) (id (nth 3 r)) (inc (nth 4 r))
                (before (fn-rtc-with-buffer h (append (fn-rtc-buffer h (nth 0 r)) '(:extra)) (nth 0 r)))
                (after (fn-hl-quantum-state h *hlt-win* id inc before))
                (r2 (list before after h id inc (fn-rtc-next-op before))) (c (hlt-c-of after)))
           (and (equal (hlt-k1-hyps r2 *hlt-win* c) '(nil t t t))
                (hlt-k1-concl r2 *hlt-win* c))))
(assert! (let* ((r (hlt-k1-run *hlt-win* nil)) (h (nth 2 r)) (id (nth 3 r)) (inc (nth 4 r))
                (b (fn-rtc-buffer h (nth 0 r)))
                (before (fn-rtc-with-buffer h (list :x (fn-rtc-get 1 b) (fn-rtc-get 2 b)) (nth 0 r)))
                (after (fn-hl-quantum-state h *hlt-win* id inc before))
                (r2 (list before after h id inc (fn-rtc-next-op before))) (c (hlt-c-of after)))
           (and (equal (hlt-k1-hyps r2 *hlt-win* c) '(nil t t nil))
                (not (hlt-k1-concl r2 *hlt-win* c)))))
; mutation (a driver fault): a copy loop reading the window one octet late; every hypothesis holds, the conclusion fails
(assert! (let* ((r (hlt-k1-run *hlt-win* t)) (c (hlt-c-of (nth 1 r))))
           (and (equal (hlt-k1-hyps r *hlt-win* c) '(t t t t))
                (not (hlt-k1-concl r *hlt-win* c)))))
; mutation (an edited conclusion): the range one past the buffer's base is not the window
(assert! (let* ((r (hlt-k1-run *hlt-win* nil)) (c (hlt-c-of (nth 1 r))))
           (not (equal (fn-rtc-c-octets (+ 1 (fn-rtc-buf-base (nth 2 r) (fn-rtc-config (nth 0 r)))) 3
                                        (nth *fn-rtc-c-bytesi* c))
                       *hlt-win*))))

; RTC-U64: high-incarnation transient controls, with all C6 hypotheses true.

; Entire antecedent of protected C6, not a failed search.
(defthm fn-a24-c6-sent-completion-control
  (let ((id 1) (inc 18446744073709551616) (op 0) (outcome '(:done 0)))
    (and (natp id) (natp inc) (natp op) (fn-rtc-outcomep outcome)
         (equal (fn-hld-sent-event id inc op outcome)
                '(:send 1 18446744073709551616 0 (:done 0)))
         (fn-rtc-get 0 (fn-hld-sent-event id inc op outcome))
         (fn-rtc-completionp (fn-hld-sent-event id inc op outcome))
         (not (fn-rtc-slotp (list inc :live 7)))
         (not (fn-rtc-ownerp (list :workspace id inc)))
         (not (fn-rtc-usep (list :send id inc op '(0 0 0 0))))
         (fn-rtc-usep (list :send id 18446744073709551615 op '(0 0 0 0)))))
  :rule-classes nil)

; Entire antecedent of the separately protected HL run helper.
(defthm fn-a24-hlr-completionp-send-control
  (let ((id 1) (inc 18446744073709551616) (op 0) (n 0))
    (and (natp id) (natp inc) (natp op) (natp n)
         (fn-rtc-completionp (list :send id inc op (list :done n)))
         (not (fn-rtc-slotp (list inc :free nil)))))
  :rule-classes nil)

; Fixture calls are logic-mode, guard-free only inside the evaluation event.
(defun fn-a24-host-u64-scene (mode fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil))
  (mv-let (fn-rtc-st okp left)
    (fn-hld-init *fn-bs-profile-development*
      (if (eq mode :drain) '(1 nil 0 0 nil 0 0 0 nil 0 2)
        '(3 nil 0 0 nil 0 0 0 nil 0 2)) 4 fn-rtc-st)
    (declare (ignore left))
    (cond
     ((eq mode :drain)
      (let* ((op (fn-rtc-st-next-op fn-rtc-st))
             (u (list :timer 2 0 op nil))
             (e (list :timer 2 0 op '(:done 0)))
             (fn-rtc-st (fn-rtc-st-set-slot 2 '(0 :draining 7) fn-rtc-st))
             (fn-rtc-st (fn-rtc-st-set-uses nil fn-rtc-st))
             (fn-rtc-st (fn-rtc-st-issue u fn-rtc-st))
             (before (fn-rtc-x-state fn-rtc-st)))
        (mv-let (fn-rtc-st acts refused cost) (fn-hll-x-step* e 1 fn-rtc-st)
          (declare (ignore acts refused cost))
          (mv (list okp before (fn-rtc-x-state fn-rtc-st) u e) fn-rtc-st))))
     ((member-eq mode '(:skip :last-valid))
      (let* ((slot (if (eq mode :last-valid) '(18446744073709551614 :free nil)
                    '(18446744073709551615 :free nil)))
             (fn-rtc-st (fn-rtc-st-set-slot 2 slot fn-rtc-st))
             (before (fn-rtc-x-state fn-rtc-st)))
        (mv-let (fn-rtc-st id inc left) (fn-hld-begin 7 fn-rtc-st)
          (mv (list okp before (fn-rtc-x-state fn-rtc-st) id inc left) fn-rtc-st))))
     (t
      (let* ((slot (if (eq mode :exhausted) '(18446744073709551615 :free nil) '(0 :live 7)))
             (fn-rtc-st (fn-rtc-st-set-slot 2 slot fn-rtc-st))
             (fn-rtc-st (fn-rtc-st-set-slot 3 slot fn-rtc-st))
             (fn-rtc-st (fn-rtc-st-set-slot 4 slot fn-rtc-st))
             (fn-rtc-st (fn-rtc-st-set-uses nil fn-rtc-st))
             (before (fn-rtc-x-state fn-rtc-st)))
        (mv-let (fn-rtc-st id inc left) (fn-hld-begin 7 fn-rtc-st)
          (mv (list okp before (fn-rtc-x-state fn-rtc-st) id inc left) fn-rtc-st)))))))
(defun fn-a24-host-u64-fixture (mode)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-rtc-st
    (mv-let (result fn-rtc-st) (fn-a24-host-u64-scene mode fn-rtc-st) result)))
(with-guard-checking-event nil
 (make-event
  (let ((drain (fn-a24-host-u64-fixture :drain))
        (skip (fn-a24-host-u64-fixture :skip))
        (last-valid (fn-a24-host-u64-fixture :last-valid))
        (exh (fn-a24-host-u64-fixture :exhausted))
        (wait (fn-a24-host-u64-fixture :wait)))
    `(progn
      (defconst *fn-a24-host-u64-drain* ',drain)
      (defconst *fn-a24-host-u64-skip* ',skip)
      (defconst *fn-a24-host-u64-last-valid* ',last-valid)
      (defconst *fn-a24-host-u64-exhausted* ',exh)
      (defconst *fn-a24-host-u64-wait* ',wait)))))
(with-guard-checking-event nil
 (assert-event
  (let* ((r *fn-a24-host-u64-drain*) (s (nth 1 r)) (s2 (nth 2 r))
         (u (nth 3 r)) (e (nth 4 r)))
    (and (nth 0 r) (fn-hll-invp s) (fn-hll-invp s2)
         (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)))
         (equal (fn-rtc-config s)
                (fn-hl-rtc-config *fn-bs-profile-development* '(1 nil 0 0 nil 0 0 0 nil 0 2) 4 1 0 0))
         (equal (fn-rtc-s-status (fn-rtc-slot 2 s)) :draining)
         (member-equal u (fn-rtc-uses s))
         (equal (fn-rtc-get 1 u) 2)
         (fn-rtc-ends-use-p e u)
         (not (fn-rtc-uses-of-slot-p 2 0 (fn-rtc-remove-use (fn-rtc-key u) (fn-rtc-uses s))))
         (equal (fn-rtc-s-status (fn-rtc-slot 2 s2)) :free)
         (fn-rtc-inc-roomp (fn-rtc-slot 2 s2))
         (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2))
         (iff (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2)) (fn-rtc-free-slot 0 (fn-rtc-slots s2)))))))
(with-guard-checking-event nil
 (assert-event
  (let* ((r *fn-a24-host-u64-skip*) (s (nth 1 r)) (s2 (nth 2 r)))
    (and (nth 0 r) (fn-hll-invp s) (fn-hll-invp s2)
         (equal (fn-rtc-free-slot 0 (fn-rtc-slots s)) 3)
         (equal (nth 3 r) 3) (equal (nth 4 r) 1)
         (equal (fn-rtc-slot 2 s2) '(18446744073709551615 :free nil))
         (equal (fn-rtc-s-status (fn-rtc-slot 3 s2)) :live)))))
(with-guard-checking-event nil
 (assert-event
  (let* ((r *fn-a24-host-u64-exhausted*) (s (nth 1 r)) (s2 (nth 2 r)))
    (and (nth 0 r) (fn-hll-invp s) (fn-hll-invp s2)
         (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
         (not (fn-rtc-free-slot 0 (fn-rtc-slots s)))
         (equal s2 s) (equal (nth 3 r) nil)
         (equal (nth 4 r) :rtc-slots-exhausted) (equal (nth 5 r) nil)))))
(with-guard-checking-event nil
 (assert-event
  (let* ((r *fn-a24-host-u64-last-valid*) (s (nth 1 r)) (s2 (nth 2 r)))
    (and (nth 0 r) (fn-hll-invp s) (fn-hll-invp s2)
         (fn-rtc-inc-roomp (fn-rtc-slot 2 s))
         (equal (nth 3 r) 2)
         (equal (nth 4 r) 18446744073709551615)
         (equal (fn-rtc-s-inc (fn-rtc-slot 2 s2)) 18446744073709551615)
         (equal (fn-rtc-s-status (fn-rtc-slot 2 s2)) :live)
         (not (fn-rtc-inc-roomp (fn-rtc-slot 2 s2)))))))
(with-guard-checking-event nil
 (assert-event
  (let* ((r *fn-a24-host-u64-wait*) (s (nth 1 r)))
    (and (nth 0 r) (fn-hll-invp s)
         (not (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s)))
         (equal (nth 2 r) s) (equal (nth 3 r) nil)
         (equal (nth 4 r) nil) (equal (nth 5 r) nil)))))

(local (defthm fn-a24-host-generic-max-state-positive
  (<= 1 (fn-rtc-m-max-state))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-m-init-is-bounded
           :in-theory (disable fn-rtc-m-init-is-bounded)))))
; The host-built drain supplies the full generic T13 antecedent as well as (c).
(defthm fn-a24-host-built-t13-room-witness
  (let* ((r *fn-a24-host-u64-drain*) (s (nth 1 r)) (s2 (nth 2 r))
         (u (nth 3 r)) (e (nth 4 r)) (j 2))
    (and (fn-rtc-invp s)
         (equal (fn-rtc-s-status (fn-rtc-slot j s)) :draining)
         (member-equal u (fn-rtc-uses s))
         (equal (fn-rtc-get 1 u) j)
         (fn-rtc-ends-use-p e u)
         (not (fn-rtc-uses-of-slot-p j (fn-rtc-s-inc (fn-rtc-slot j s))
                (fn-rtc-remove-use (fn-rtc-key u) (fn-rtc-uses s))))
         (equal s2 (mv-nth 0 (fn-rtc-step s e 1)))
         (equal (fn-rtc-s-status (fn-rtc-slot j s2)) :free)
         (iff (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2))
              (fn-rtc-free-slot 0 (fn-rtc-slots s2)))
         (fn-rtc-inc-roomp (fn-rtc-slot j s2))
         (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-invp fn-rtc-core-invp fn-rtc-mstates-okp fn-rtc-step
                 fn-rtc-step* fn-rtc-acts-on-p fn-rtc-end-use fn-rtc-end-lease
                 fn-rtc-retire-drained fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant)
                ((:executable-counterpart fn-rtc-invp)
                 (:executable-counterpart fn-rtc-core-invp)
                 (:executable-counterpart fn-rtc-mstates-okp))))))
(defthm fn-a24-host-built-terminal-iff-witness
  (let* ((r *fn-a24-host-u64-exhausted*) (s (nth 1 r)))
    (and (fn-rtc-st-p s) (fn-rtc-invp s)
         (equal (nth 3 r) nil) (equal (nth 4 r) :rtc-slots-exhausted)
         (equal (nth 5 r) nil)
         (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-invp fn-rtc-core-invp fn-rtc-mstates-okp
                 fn-rtc-st-p fn-rtc-st$ap fn-rtc-shapep)
                ((:executable-counterpart fn-rtc-invp)
                 (:executable-counterpart fn-rtc-core-invp)
                 (:executable-counterpart fn-rtc-mstates-okp))))))

(defthm fn-a24-host-built-slot-id-u64-witness
  (let ((s (nth 1 *fn-a24-host-u64-drain*)) (j 2))
    (and (fn-rtc-invp s) (fn-rtc-st-cfg-okp (fn-rtc-config s))
         (natp j) (< j (fn-rtc-nslots (fn-rtc-config s)))
         (fn-rtc-u64p j) (fn-rtc-u64p (fn-rtc-s-inc (fn-rtc-slot j s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-invp fn-rtc-core-invp fn-rtc-mstates-okp)
                ((:executable-counterpart fn-rtc-invp)
                 (:executable-counterpart fn-rtc-core-invp)
                 (:executable-counterpart fn-rtc-mstates-okp))))))
(defthm fn-a24-slot-id-range-hypothesis-tooth
  (let ((s (nth 1 *fn-a24-host-u64-drain*)) (j 18446744073709551616))
    (and (fn-rtc-invp s) (fn-rtc-st-cfg-okp (fn-rtc-config s)) (natp j)
         (not (< j (fn-rtc-nslots (fn-rtc-config s))))
         (not (fn-rtc-u64p j))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-invp fn-rtc-core-invp fn-rtc-mstates-okp)
                ((:executable-counterpart fn-rtc-invp)
                 (:executable-counterpart fn-rtc-core-invp)
                 (:executable-counterpart fn-rtc-mstates-okp))))))
(defthm fn-a24-slot-id-natural-hypothesis-tooth
  (let ((s (nth 1 *fn-a24-host-u64-drain*)) (j -1))
    (and (fn-rtc-invp s) (fn-rtc-st-cfg-okp (fn-rtc-config s))
         (< j (fn-rtc-nslots (fn-rtc-config s))) (not (natp j))
         (not (fn-rtc-u64p j))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-invp fn-rtc-core-invp fn-rtc-mstates-okp)
                ((:executable-counterpart fn-rtc-invp)
                 (:executable-counterpart fn-rtc-core-invp)
                 (:executable-counterpart fn-rtc-mstates-okp))))))

(defthm fn-a24-exhaustion-step-witness
  (let* ((s (nth 1 *fn-a24-host-u64-exhausted*))
         (e '(:accept 0 0 99 (:done 7)))
         (s2 (mv-nth 0 (fn-rtc-step* s e 1))))
    (and (fn-rtc-invp s)
         (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
         (fn-rtc-inc-roomp (fn-rtc-slot 0 s))
         (fn-rtc-inc-roomp (fn-rtc-slot 1 s))
         (equal s2 s)
         (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s2))
         (not (fn-rtc-free-slot 0 (fn-rtc-slots s2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-invp fn-rtc-core-invp fn-rtc-mstates-okp
                 fn-rtc-step*-state-is-step-state fn-rtc-step-state fn-rtc-acts-on-p
                 fn-rtc-end-use fn-rtc-retire-drained fn-rtc-end-lease
                 fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant)
                ((:executable-counterpart fn-rtc-invp)
                 (:executable-counterpart fn-rtc-core-invp)
                 (:executable-counterpart fn-rtc-mstates-okp)
                 (:executable-counterpart fn-rtc-step*))))))
(defthm fn-a24-exhaustion-invariant-hypothesis-tooth
  (let* ((s (fn-rtc-with-slot 1 '(1 :free nil)
              (nth 1 *fn-a24-host-u64-exhausted*))))
    (and (not (fn-rtc-invp s))
         (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
         (fn-rtc-free-slot 0 (fn-rtc-slots s))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-invp fn-rtc-core-invp fn-rtc-mstates-okp)
                ((:executable-counterpart fn-rtc-invp)
                 (:executable-counterpart fn-rtc-core-invp)
                 (:executable-counterpart fn-rtc-mstates-okp))))))

; The concrete layer's logical machine copy is intentionally non-executable.
; Prove the whole ground control by its definition instead of evaluating it.
(defthm fn-a24-after-deliver-retired-record-tooth
  (let ((s '((2 0 0 0 0 0 0)
              ((0 :live nil) (18446744073709551615 :free nil))
              nil nil (nil nil) 1)))
    (mv-let (sd acts refused cost) (fn-hll-deliver s 1 18446744073709551615 nil 1)
      (declare (ignore acts refused cost))
      (mv-let (s2 acts2) (fn-rtc-rearm sd)
        (declare (ignore acts2))
        (and (posp 1) (equal (fn-rtc-s-status (fn-rtc-slot 1 s)) :free)
             (not (fn-rtc-inc-roomp (fn-rtc-slot 1 s)))
             (equal (fn-rtc-slot 1 sd) (fn-rtc-slot 1 s))
             (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hll-deliver fn-hll-m-step fn-hlm-step))))

; A live instance can already have spent the slot's final incarnation.
(defun fn-a27-host-live-max-scene (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil))
  (mv-let (fn-rtc-st okp left)
    (fn-hld-init *fn-bs-profile-development* '(1 nil 0 0 nil 0 0 0 nil 0 2) 4 fn-rtc-st)
    (declare (ignore left))
    (let* ((fn-rtc-st (fn-rtc-st-set-slot 2 '(18446744073709551615 :live 7) fn-rtc-st))
           (fn-rtc-st (fn-rtc-st-set-uses nil fn-rtc-st))
           (before (fn-rtc-x-state fn-rtc-st)))
      (mv-let (fn-rtc-st id inc left) (fn-hld-begin 7 fn-rtc-st)
        (mv (list okp before (fn-rtc-x-state fn-rtc-st) id inc left) fn-rtc-st)))))
(defun fn-a27-host-live-max-fixture ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-rtc-st
    (mv-let (result fn-rtc-st) (fn-a27-host-live-max-scene fn-rtc-st) result)))
(with-guard-checking-event nil
 (make-event
  `(defconst *fn-a27-host-live-max* ',(fn-a27-host-live-max-fixture))))
(with-guard-checking-event nil
 (assert-event
  (let* ((r *fn-a27-host-live-max*) (s (nth 1 r)) (s2 (nth 2 r)))
    (and (nth 0 r) (fn-hll-invp s) (fn-hll-invp s2)
         (equal (fn-rtc-nslots (fn-rtc-config s)) 3)
         (equal (fn-rtc-nstatic (fn-rtc-config s)) 1)
         (equal (fn-rtc-s-status (fn-rtc-slot 2 s)) :live)
         (equal (fn-rtc-s-inc (fn-rtc-slot 2 s)) 18446744073709551615)
         (not (fn-rtc-inc-roomp (fn-rtc-slot 2 s)))
         (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
         (equal s2 s) (equal (nth 3 r) nil)
         (equal (nth 4 r) :rtc-slots-exhausted) (equal (nth 5 r) nil)))))
