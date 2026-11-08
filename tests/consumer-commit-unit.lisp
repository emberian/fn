; A consumer's durable mutations survive the process's death (NEXT-ASTRA
; lane 13, consumer-commit). Register and an advancing ack are B members
; (cns.lisp's :commit arm through the :commit word, machine-arms.lisp): a
; control connection registers consumer 1 and acks it forward; after each
; accepted result the process dies (the core is dropped, the device the
; adapter wrote is kept) and a fresh core runs B5's recovery row over the
; device; then a new control connection asks consumer 1's position, which is
; the position the last accepted result answered. Each mutation is its own
; commit position: the register's batch makes the frontier 1, the ack to 1
; makes it 2, so the ack to 2 advances too.
; The tooth: the same session with its last ack published around B (C's
; bind and publish of a predicted batch, the bypass cns.lisp used to take)
; answers the advanced position live and the register's after recovery, and
; the judge refuses it.
; Run: sh tools/certify.sh tests/consumer-commit-unit.lisp
(in-package "ACL2")
(include-book "../books/cns")
(include-book "../books/owed-conn")
(include-book "../books/owed-cursor")
(include-book "../books/assembly-attach")
(include-book "fnct-client")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-ccu-profile*
  (put-assoc-equal :cns 2
    (put-assoc-equal :control-connections 2
      (put-assoc-equal :identity-overlays 32
        (put-assoc-equal :identity-arena-bytes 4096
          (put-assoc-equal :pool-classes '((8 . 1024) (64 . 4096) (16 . 65536)) *fn2-conn-wire-profile*))))))

(defun fn2-ccu-cat (frames)
  (declare (xargs :verify-guards nil))
  (if (atom frames) nil (append (car frames) (fn2-ccu-cat (cdr frames)))))
(defun fn2-ccu-lens (frames)
  (declare (xargs :verify-guards nil))
  (if (atom frames) nil (cons (len (car frames)) (fn2-ccu-lens (cdr frames)))))
(defun fn2-ccu-client (frames)
  (declare (xargs :verify-guards nil))
  (list (fn2-ccu-cat frames) (fn2-ccu-lens frames) nil nil))

; A control connection admitted at capability CAP, then FRAMES on it, each
; its own receive, the last a stop: (mv status wire fn2-core). The clients
; before CAP are done (no input).
(defun fn2-ccu-done-clients (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil (cons (list nil nil nil nil) (fn2-ccu-done-clients (- n 1)))))
(defun fn2-ccu-session (cap frames fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
       ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl cap (+ 77 cap) 3 0 fn2-core))
       ((unless (eq acode :ok)) (mv (list :admit acode) nil nil fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
       (fn2-core (fn2-exec-wake wake fn2-core))
       (clients (append (fn2-ccu-done-clients cap) (list (fn2-ccu-client frames))))
       ((mv status clients store fn2-core) (fn2-cw-loop 40000 0 (+ 1 cap) clients nil fn2-core)))
    (mv status (car (nth cap (fn2-cw-results clients))) store fn2-core)))

; The cursor register issues consumer 1 (version 1, epoch 1, at 0), and the
; mutations of a prefix: the register, then acks to 1 and to 2.
(defconst *fn2-ccu-cursor* (fnc-issued 1 0 1 1 0))
(defconst *fn2-ccu-mutations*
  (list (list 'register (fnc-register 1 1) 0)
        (list 'ack (fnc-ack *fn2-ccu-cursor* 1) 1)
        (list 'ack (fnc-ack *fn2-ccu-cursor* 2) 2)))
(defun fn2-ccu-frames (ms)
  (declare (xargs :verify-guards nil))
  (if (atom ms) nil (cons (nth 1 (car ms)) (fn2-ccu-frames (cdr ms)))))
(defun fn2-ccu-verbs (ms)
  (declare (xargs :verify-guards nil))
  (if (atom ms) nil (cons (nth 0 (car ms)) (fn2-ccu-verbs (cdr ms)))))
(defun fn2-ccu-expected (ms)
  (declare (xargs :verify-guards nil))
  (if (atom ms) nil (cons (list :accepted "" (nth 2 (car ms))) (fn2-ccu-expected (cdr ms)))))

; The bypass (the mutant): consumer 1's ack to TO declared on the row's
; successor (row 0: this profile serves no posting or authority), staged,
; bound to the predicted batch one past the published frontier and published
; by C, never admitted to B.
(defun fn2-ccu-bypass-ack (to fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv & fn2-core) (fn2-successor-release 0 fn2-core))
       ((mv c0 fn2-core) (fn2-consumer-cursor-ack 0 0 (consumer 1) (epoch 1) (to to) fn2-core))
       ((unless (eq c0 :ok)) (mv (list :put c0) fn2-core))
       ((mv rc fn2-core) (fn2-cns-resolve-loop 32 0 fn2-core))
       ((unless (eq rc :ok)) (mv (list :resolve rc) fn2-core))
       ((mv sc & fn2-core) (fn2-successor-stage 0 fn2-core))
       ((unless (eq sc :ok)) (mv (list :stage sc) fn2-core))
       ((mv & pf) (fn2-successor-published fn2-core))
       ((mv bc fn2-core) (fn2-successor-bind 0 (+ 1 (nfix pf)) (+ 1 (nfix pf)) fn2-core))
       ((unless (eq bc :ok)) (mv (list :bind bc) fn2-core))
       ((mv pc fn2-core) (fn2-succ-core-publish (+ 1 (nfix pf)) fn2-core))
       ((unless (eq pc :ok)) (mv (list :publish pc) fn2-core))
       ((mv & fn2-core) (fn2-successor-release 0 fn2-core)))
    (mv :ok fn2-core)))

; Live: the mutations MS on one connection, then (BYPASS) the bypass ack to
; the published frontier, then consumer 1's position on a second one:
; (mutation-replies position-reply store stop-reason).
(defun fn2-ccu-live (ms bypass)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (r fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-ccu-profile* :echo nil fn2-core))
           ((mv & fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv s1 w1 store fn2-core) (fn2-ccu-session 0 (append (fn2-ccu-frames ms) (list (fnc-control 5))) fn2-core))
           ((mv bcode fn2-core)
            (if bypass
                (mv-let (fc pf) (fn2-successor-published fn2-core)
                  (declare (ignore fc))
                  (fn2-ccu-bypass-ack (nfix pf) fn2-core))
              (mv :ok fn2-core)))
           ((mv s2 w2 store2 fn2-core) (fn2-ccu-session 1 (list (fnc-position 1) (fnc-control 5)) fn2-core)))
        (mv (list (fnc-replies (fn2-ccu-verbs ms) w1) (car (fnc-replies '(position) w2))
                  (append store store2) (fn2-core-stop-reason fn2-core) (list s1 s2 bcode))
            fn2-core))
      r)))

; After death: a fresh core over STORE runs recovery (A-PERSISTENCE-FENCE,
; assume 2), then consumer 1's position on a new connection:
; (recovered-done position-reply stop-reason).
(defun fn2-ccu-recover (store)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (r fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-ccu-profile* :echo nil fn2-core))
           (id (fn2-machine-global-id *fn2-recovery-machine-kind* 0 *fn2-ccu-profile*))
           ((mv & fn2-core) (fn2-recovery-start id 2 0 fn2-core))
           ((mv & & & fn2-core) (fn2-cw-loop 400000 0 0 nil store fn2-core))
           (done (equal (fn2-machine-phase id fn2-core) *fn2-recovery-machine-state-done*))
           ((mv & w & fn2-core) (fn2-ccu-session 0 (list (fnc-position 1) (fnc-control 5)) fn2-core)))
        (mv (list done (car (fnc-replies '(position) w)) (fn2-core-stop-reason fn2-core)) fn2-core))
      r)))

; The judge: every mutation accepted with its position, the live position
; the last one's, and after death and recovery the same position.
(defun fn2-ccu-judge (ms live post)
  (declare (xargs :verify-guards nil))
  (let ((last (nth 2 (car (last ms)))))
    (and (equal (nth 0 live) (fn2-ccu-expected ms))
         (equal (nth 3 live) 0)
         (equal (nth 0 post) t)
         (equal (nth 2 post) 0)
         (equal (nth 1 post) (nth 1 live))
         (equal (nth 1 post) (list :accepted "" last)))))

(defun fn2-ccu-crash-after (k)
  ; the first K mutations, then death
  (declare (xargs :verify-guards nil))
  (let* ((ms (take k *fn2-ccu-mutations*))
         (live (fn2-ccu-live ms nil))
         (post (fn2-ccu-recover (nth 2 live))))
    (or (fn2-ccu-judge ms live post)
        (cw "consumer-commit crash after ~x0~%live ~x1~%post ~x2~%" k
            (list (nth 0 live) (nth 1 live) (nth 3 live) (nth 4 live)) post))))

; The bypass mutant: the register through B, then an ack published around
; it. Live, the position moves; after death it is the register's: caught.
(defun fn2-ccu-bypass-caught ()
  (declare (xargs :verify-guards nil))
  (let* ((ms (take 1 *fn2-ccu-mutations*))
         (live (fn2-ccu-live ms t))
         (post (fn2-ccu-recover (nth 2 live))))
    (or (and (equal (nth 4 live) (list :quiet :quiet :ok))
             (not (equal (nth 1 live) (list :accepted "" 0)))
             (equal (nth 1 post) (list :accepted "" 0))
             (not (equal (nth 1 post) (nth 1 live))))
        (cw "consumer-commit bypass: live ~x0~%post ~x1~%" (list (nth 1 live) (nth 4 live)) post))))

(defun fn2-ccu-teeth-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-ccu-crash-after 1) (fn2-ccu-crash-after 2) (fn2-ccu-crash-after 3)))
(defun fn2-ccu-teeth-negative ()
  (declare (xargs :verify-guards nil))
  (fn2-ccu-bypass-caught))

; The statement this fixture is a tested instance of (owed): over this
; profile, for every list of consumer request frames on one control
; connection, the process dying once they are answered, the consumer's
; position a fresh core recovers from the device is the one the live core
; answered: what B encoded as the members, what C published live and what
; recovery replayed are the same delta.
(defun fn2-ccu-replays-p (ms)
  (declare (xargs :verify-guards nil))
  (let* ((live (fn2-ccu-live ms nil))
         (post (fn2-ccu-recover (nth 2 live))))
    (implies (equal (nth 3 live) 0)
             (and (equal (nth 0 post) t) (equal (nth 1 post) (nth 1 live))))))
(defthm-owed fn2-cns-commit-replays-published (ms)
  (fn2-ccu-replays-p ms)
  :teeth (fn2-ccu-teeth-positive fn2-ccu-teeth-negative)
  :layer :e
  :doc "Every consumer mutation is a B member: after any request script on one control connection of the consumer-commit profile and the process's death, B5 recovery over the device reproduces the consumer position the live core answered (the encoded member, the published delta and the replayed delta agree). Tested instance: tests/consumer-commit-unit.lisp, crash after each accepted register/ack; tooth: an ack published around B is caught.")

(assert-event (fn2-ccu-teeth-positive))
(assert-event (fn2-ccu-teeth-negative))
