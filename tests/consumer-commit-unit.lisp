; A consumer's durable mutations survive the process's death (NEXT-ASTRA
; lane 13, consumer-commit). Register and an advancing ack are B members
; (cns.lisp's :commit arm through the :commit word, machine-arms.lisp): a
; control connection registers consumer 1, appends an article (a POST: its
; addr entry of the principal at its commit position) and acks consumer 1
; to that position; after each accepted result the process dies (the core
; is dropped, the device the adapter wrote is kept) and a fresh core runs
; B5's recovery row over the device; then a new control connection asks
; consumer 1's position and status, which are the ones the live core
; answered. Positions are the principal's stream positions (e-surface.md
; 3.2): the register is B's commit 1, the append 2 and the principal's only
; addr entry, the ack 3; the ack proposes 2, the stream frontier.
; The stream frontier (fn2-ccu-frontier-ok): after the ack, status reports
; nothing unread (2 2 0, where B's global frontier would answer 2 3 1); an
; ack to 3, one past the stream frontier and at B's global one, is refused
; beyond-frontier; another principal's addr entry published after it moves
; that principal's frontier and not this one's.
; The tooth: the same session with an ack published around B (C's bind and
; publish of a predicted batch, the bypass cns.lisp used to take) answers
; the advanced position live and the register's after recovery, and the
; judge refuses it.
; Run: sh tools/certify.sh tests/consumer-commit-unit.lisp
(in-package "ACL2")
(include-book "../books/cns")
(include-book "../books/owed-conn")
(include-book "../books/owed-cursor")
(include-book "../books/assembly-attach")
(include-book "fnct-client")
(include-book "std/util/bstar" :dir :system)

; The posting profile (owed-cursor.lisp's, local.test is group 1, T 2) with
; two control connections: one consumer request (fn2-txn's share 1), and two
; consumer requests with T 3 (fn2-txn's share 1 again). Two consumer requests
; under T 2 leave fn2-txn no row: posting is not served and an append is
; refused with D's word refused (fn2-ccu-unposting-answered), where it used to park
; on a transaction row that never exists, its request never answered.
(defconst *fn2-ccu-profile*
  (put-assoc-equal :cns 1
    (put-assoc-equal :control-connections 2
      (put-assoc-equal :extent-slots 128 *fn2-cursor-profile*))))
(defconst *fn2-ccu-profile-2*
  (put-assoc-equal :cns 2 (put-assoc-equal :t 3 *fn2-ccu-profile*)))
(defconst *fn2-ccu-profile-2-unposting*
  (put-assoc-equal :cns 2 *fn2-ccu-profile*))

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
; mutations of a prefix, each (verb frame reply position): the register at
; 0, the append (operation 9) at commit position 2, then the ack to 2.
(defconst *fn2-ccu-cursor* (fnc-issued 1 0 1 1 0))
(defconst *fn2-ccu-article*
  '("From: mini@example.invalid" "Subject: r1" "Newsgroups: local.test" "" "report r1"))
(defconst *fn2-ccu-mutations*
  (list (list 'register (fnc-register 1 1) '(:accepted "" 0) 0)
        (list 'append (fnc-append 9 (fn2-cw-crlf-octets *fn2-ccu-article*)) '(:accepted "" (2 1)) 0)
        (list 'ack (fnc-ack *fn2-ccu-cursor* 2) '(:accepted "" 2) 2)))
(defun fn2-ccu-frames (ms)
  (declare (xargs :verify-guards nil))
  (if (atom ms) nil (cons (nth 1 (car ms)) (fn2-ccu-frames (cdr ms)))))
(defun fn2-ccu-verbs (ms)
  (declare (xargs :verify-guards nil))
  (if (atom ms) nil (cons (nth 0 (car ms)) (fn2-ccu-verbs (cdr ms)))))
(defun fn2-ccu-expected (ms)
  (declare (xargs :verify-guards nil))
  (if (atom ms) nil (cons (nth 2 (car ms)) (fn2-ccu-expected (cdr ms)))))

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
(defun fn2-ccu-live (prof ms bypass)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (r fn2-core)
      (b* ((fn2-core (fn2-init-executor prof :echo nil fn2-core))
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
           ((mv s2 w2 store2 fn2-core)
            (fn2-ccu-session 1 (list (fnc-position 1) (fnc-status 1) (fnc-control 5)) fn2-core)))
        (mv (list (fnc-replies (fn2-ccu-verbs ms) w1) (fnc-replies '(position status) w2)
                  (append store store2) (fn2-core-stop-reason fn2-core) (list s1 s2 bcode))
            fn2-core))
      r)))

; After death: a fresh core over STORE runs recovery (A-PERSISTENCE-FENCE,
; assume 2), then consumer 1's position on a new connection:
; (recovered-done position-reply stop-reason).
(defun fn2-ccu-recover (prof store)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (r fn2-core)
      (b* ((fn2-core (fn2-init-executor prof :echo nil fn2-core))
           (id (fn2-machine-global-id *fn2-recovery-machine-kind* 0 prof))
           ((mv & fn2-core) (fn2-recovery-start id 2 0 fn2-core))
           ((mv & & & fn2-core) (fn2-cw-loop 400000 0 0 nil store fn2-core))
           (done (equal (fn2-machine-phase id fn2-core) *fn2-recovery-machine-state-done*))
           ((mv & w & fn2-core) (fn2-ccu-session 0 (list (fnc-position 1) (fnc-status 1) (fnc-control 5)) fn2-core)))
        (mv (list done (fnc-replies '(position status) w) (fn2-core-stop-reason fn2-core)) fn2-core))
      r)))

; The judge: every mutation answered as expected, the live position the
; last one's, and after death and recovery the same position and status
; (the stream frontier is read from the replayed addr run, no other state).
(defun fn2-ccu-judge (ms live post)
  (declare (xargs :verify-guards nil))
  (let ((last (nth 3 (car (last ms)))))
    (and (equal (nth 0 live) (fn2-ccu-expected ms))
         (equal (nth 3 live) 0)
         (equal (nth 0 post) t)
         (equal (nth 2 post) 0)
         (equal (nth 1 post) (nth 1 live))
         (equal (car (nth 1 post)) (list :accepted "" last)))))

(defun fn2-ccu-crash-after (prof k)
  ; the first K mutations, then death
  (declare (xargs :verify-guards nil))
  (let* ((ms (take k *fn2-ccu-mutations*))
         (live (fn2-ccu-live prof ms nil))
         (post (fn2-ccu-recover prof (nth 2 live))))
    (or (fn2-ccu-judge ms live post)
        (cw "consumer-commit ~x3 crash after ~x0~%live ~x1~%post ~x2~%" k
            (list (nth 0 live) (nth 1 live) (nth 3 live) (nth 4 live)) post (fn2-profile-get :cns prof)))))

; The bypass mutant: the register through B, then an ack published around
; it. Live, the position moves; after death it is the register's: caught.
(defun fn2-ccu-bypass-caught ()
  (declare (xargs :verify-guards nil))
  (let* ((ms (take 1 *fn2-ccu-mutations*))
         (live (fn2-ccu-live *fn2-ccu-profile* ms t))
         (post (fn2-ccu-recover *fn2-ccu-profile* (nth 2 live))))
    (or (and (equal (nth 4 live) (list :quiet :quiet :ok))
             (not (equal (car (nth 1 live)) (list :accepted "" 0)))
             (equal (car (nth 1 post)) (list :accepted "" 0))
             (not (equal (nth 1 post) (nth 1 live))))
        (cw "consumer-commit bypass: live ~x0~%post ~x1~%" (list (nth 1 live) (nth 4 live)) post))))

;; An addr entry of PRINCIPAL at POSITION (stream 1, article 7: no article
;; row behind it), bound and published by C past B's last commit, with B's
;; stream-wake hook run after it.
(defun fn2-ccu-seed-addr (principal pos fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv & fn2-core) (fn2-successor-release 0 fn2-core))
       ((mv c0 fn2-core)
        (fn2-addr-put 0 0 (principal principal) (position pos) (article 7) (stream 1) (reasons 1) fn2-core))
       ((unless (eq c0 :ok)) (mv (list :put c0) fn2-core))
       ((mv rc fn2-core) (fn2-cns-resolve-loop 32 0 fn2-core))
       ((unless (eq rc :ok)) (mv (list :resolve rc) fn2-core))
       ((mv sc & fn2-core) (fn2-successor-stage 0 fn2-core))
       ((unless (eq sc :ok)) (mv (list :stage sc) fn2-core))
       ((mv bc fn2-core) (fn2-successor-bind 0 pos pos fn2-core))
       ((unless (eq bc :ok)) (mv (list :bind bc) fn2-core))
       ((mv pc fn2-core) (fn2-succ-core-publish pos fn2-core))
       ((unless (eq pc :ok)) (mv (list :publish pc) fn2-core))
       ((mv & fn2-core) (fn2-cns-core-stream-wake pos fn2-core))
       ((mv & fn2-core) (fn2-successor-release 0 fn2-core)))
    (mv :ok fn2-core)))

;; The stream frontier (e-surface.md 3.2) on the served path: register,
;; append (the principal's addr entry at 2), ack to 2 (B's commit 3), then
;; status and an ack to 3 on the same connection; then principal 1's addr
;; entry at 4 and status on a second connection, and the frontiers the
;; host's fn2-cns-stream-frontier answers for both principals over read row 0.
(defun fn2-ccu-frontier-run (prof)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (r fn2-core)
      (b* ((fn2-core (fn2-init-executor prof :echo nil fn2-core))
           ((mv & fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv s1 w1 & fn2-core)
            (fn2-ccu-session 0 (append (fn2-ccu-frames *fn2-ccu-mutations*)
                                       (list (fnc-status 1) (fnc-ack *fn2-ccu-cursor* 3) (fnc-control 5)))
                             fn2-core))
           ((mv & pub1) (fn2-successor-published fn2-core))
           ((mv sd fn2-core) (fn2-ccu-seed-addr 1 4 fn2-core))
           ((mv s2 w2 & fn2-core) (fn2-ccu-session 1 (list (fnc-status 1) (fnc-control 5)) fn2-core))
           ((mv & pub2) (fn2-successor-published fn2-core))
           ((mv c0 f0 fn2-core) (fn2-cns-stream-frontier 0 0 fn2-core))
           ((mv c1 f1 fn2-core) (fn2-cns-stream-frontier 1 0 fn2-core)))
        (mv (list (fnc-replies (append (fn2-ccu-verbs *fn2-ccu-mutations*) '(status ack)) w1)
                  (fnc-replies '(status) w2)
                  (list pub1 pub2) (list c0 f0 c1 f1)
                  (list s1 sd s2 (fn2-core-stop-reason fn2-core)))
            fn2-core))
      r)))
(defun fn2-ccu-frontier-ok (prof)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-ccu-frontier-run prof)))
    (or (and (equal (nth 0 r)
                    (append (fn2-ccu-expected *fn2-ccu-mutations*)
                            ;; nothing unread after the reader's own ack (B's
                            ;; global frontier is 3: the ack's own commit)
                            '((:accepted "" (2 2 0))
                              ;; one past the stream frontier, at B's global one
                              (:refused "beyond-frontier" nil))))
             ;; another principal's entry at 4 moves B's frontier and its own,
             ;; not this principal's
             (equal (nth 1 r) '((:accepted "" (2 2 0))))
             (equal (nth 2 r) '(3 4))
             (equal (nth 3 r) '(:ok 2 :ok 4))
             (equal (nth 4 r) '(:quiet :ok :quiet 0)))
        (cw "consumer-commit frontier: ~x0~%" r))))

;; Two consumer requests under T 2: fn2-txn has no row, posting is not
;; served, and the append is answered refused, D's word refused (no publish).
(defun fn2-ccu-unposting-answered ()
  (declare (xargs :verify-guards nil))
  (let ((r (with-local-stobj fn2-core
             (mv-let (r fn2-core)
               (b* ((fn2-core (fn2-init-executor *fn2-ccu-profile-2-unposting* :echo nil fn2-core))
                    ((mv & fn2-core)
                     (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
                       (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
                    ((mv s1 w1 & fn2-core)
                     (fn2-ccu-session 0 (list (fnc-register 1 1) (nth 1 (nth 1 *fn2-ccu-mutations*)) (fnc-control 5))
                                      fn2-core))
                    ((mv & pub) (fn2-successor-published fn2-core)))
                 (mv (list s1 (fnc-replies '(register append) w1) pub (fn2-core-stop-reason fn2-core)) fn2-core))
               r))))
    (or (equal r '(:quiet ((:accepted "" 0) (:refused "refused" nil)) 1 0))
        (cw "consumer-commit unposting: ~x0~%" r))))

(defun fn2-ccu-teeth-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-ccu-crash-after *fn2-ccu-profile* 1) (fn2-ccu-crash-after *fn2-ccu-profile* 2)
       (fn2-ccu-crash-after *fn2-ccu-profile* 3) (fn2-ccu-frontier-ok *fn2-ccu-profile*)
       (fn2-ccu-crash-after *fn2-ccu-profile-2* 3) (fn2-ccu-frontier-ok *fn2-ccu-profile-2*)
       (fn2-ccu-unposting-answered)))
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
  (let* ((live (fn2-ccu-live *fn2-ccu-profile* ms nil))
         (post (fn2-ccu-recover *fn2-ccu-profile* (nth 2 live))))
    (implies (equal (nth 3 live) 0)
             (and (equal (nth 0 post) t) (equal (nth 1 post) (nth 1 live))))))
(defthm-owed fn2-cns-commit-replays-published (ms)
  (fn2-ccu-replays-p ms)
  :teeth (fn2-ccu-teeth-positive fn2-ccu-teeth-negative)
  :layer :e
  :doc "Every consumer mutation is a B member: after any request script on one control connection of the consumer-commit profile and the process's death, B5 recovery over the device reproduces the consumer position the live core answered (the encoded member, the published delta and the replayed delta agree). Tested instance: tests/consumer-commit-unit.lisp, crash after each accepted register/append/ack, positions the principal's stream positions; tooth: an ack published around B is caught.")

(assert-event (fn2-ccu-teeth-positive))
(assert-event (fn2-ccu-teeth-negative))
