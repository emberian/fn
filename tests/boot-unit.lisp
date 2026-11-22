; The native image machine through the same turn and storage adapter as
; recovery-article-unit. The held fence is a negative listener-release control.
(in-package "ACL2")
(include-book "../books/node-profile")
(include-book "../books/owed-conn")

(defun fn2-bu-accept-count (n i fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
 (if (zp n) 0
  (+ (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (yes)
      (if (and (< (nfix i) (fn2-ops-rows fn2-ops))
               (equal (fn2-ops-kind (nfix i) fn2-ops) *fn2-action-accept*)
               (not (equal (fn2-ops-phase (nfix i) fn2-ops) *fn2-op-phase-free*))) 1 0) yes)
     (fn2-bu-accept-count (- n 1) (+ 1 (nfix i)) fn2-core))))

(defun fn2-bu-to-fence (fuel store fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel store fn2-core)
  (b* (((mv & & & & fn2-core) (fn2-turn fn2-core))
       (fence (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (yes)
               (mv-let (code op gen) (fn2-outbox-peek 0 fn2-ops)
                (declare (ignore gen))
                (and (eq code :ok) (equal (fn2-ops-kind op fn2-ops) *fn2-action-fence*))) yes))
       ((when fence) (mv :held store fn2-core))
       ((when (not (equal (fn2-core-stop-reason fn2-core) 0))) (mv :failed store fn2-core))
       ((mv & & & store fn2-core) (fn2-cw-adapter-one 0 nil store fn2-core)))
   (fn2-bu-to-fence (- fuel 1) store fn2-core))))

(defun fn2-bu-start (create store)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (result fn2-core)
   (b* ((fn2-core (fn2-init-executor (fn2-image-profile *fn2-node-profile*) :echo nil fn2-core))
        ((mv start fn2-core) (fn2-boot-start create 33554432 fn2-core))
        ((mv held store fn2-core) (fn2-bu-to-fence 100000 store fn2-core))
        (pre (list start held (fn2-boot-status fn2-core) (fn2-bu-accept-count 32 0 fn2-core)))
        ((mv & & & store fn2-core) (if (eq held :held) (fn2-cw-adapter-one 0 nil store fn2-core)
                                   (mv nil 0 nil store fn2-core)))
        ((mv quiet & store fn2-core) (fn2-cw-loop 100000 0 0 nil store fn2-core))
        (epoch (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (e)
                 (fn2-alloc-current-epoch fn2-extents) e)))
    (mv (list pre quiet (fn2-boot-status fn2-core) epoch store (fn2-core-stop-reason fn2-core) (fn2-bu-accept-count 32 0 fn2-core)) fn2-core))
   result)))

(assert-event (eq (fn2-image-create-request 1 *fn2-node-profile*) :geometry))
(assert-event (eq (fn2-image-create-request 33554432 *fn2-node-profile*) :ok))

; The served image profile deliberately leaves room after its committed
; arena. Probe both geometry boundaries through the actual host-facing API.
(assert-event
 (let* ((n (fn2-b-capacity :extent-slots 16 *fn2-node-profile*))
        (g (len (fn2-profile-get :groups *fn2-node-profile*)))
        (old (+ (* 12288 n) (* 4096 (+ g 3))))
        (minimum (+ (* 65536 n) (* 4096 (+ g 8)))))
  (and (eq (fn2-image-create-request old *fn2-node-profile*) :geometry)
       (eq (fn2-image-create-request (- minimum 4096) *fn2-node-profile*) :geometry)
       (eq (fn2-image-create-request minimum *fn2-node-profile*) :ok))))

(defun fn2-bu-genesis-addressesp (at groups store)
 (declare (xargs :verify-guards nil :measure (nfix (1+ groups))))
 (and (assoc-equal at store)
      (or (zp groups)
          (fn2-bu-genesis-addressesp (+ at 4096) (1- groups) store))))

(defun fn2-bu-addresses-outside-arenap (arena store)
 (declare (xargs :verify-guards nil))
 (if (atom store) t
  (and (<= arena (caar store))
       (fn2-bu-addresses-outside-arenap arena (cdr store)))))

(defun fn2-bu-image-layoutp (size profile store)
 (declare (xargs :verify-guards nil))
 (let* ((extents (fn2-b-capacity :extent-slots 16 profile))
        (groups (len (fn2-profile-get :groups profile)))
        (arena (* 65536 extents)))
  (and (fn2-bu-genesis-addressesp arena groups store)
       (fn2-bu-addresses-outside-arenap arena store)
       ; Check both epoch offsets and the gap reserved for checkpoint blocks.
       (assoc-equal (- size 8192) store)
       (assoc-equal (- size 4096) store)
       (<= (+ arena (* 4096 (+ groups 6))) (- size 8192)))))

; Attachments are executable observations, not logical DEFCONST values.
(assert-event
 (let* ((created (fn2-bu-start t nil))
        (opened (fn2-bu-start nil (nth 4 created)))
        (reopened (fn2-bu-start nil (nth 4 opened)))
        (empty (fn2-bu-start nil nil))
        (bad-anchor (fn2-bu-start nil (cons (cons (- 33554432 8192) :corrupt) (nth 4 created)))))
  (or (and (fn2-bu-image-layoutp 33554432 *fn2-node-profile* (nth 4 created))
           (equal (take 4 created) '((:ok :held :booting 0) :quiet :ready 1))
           (equal (take 4 opened) '((:ok :held :booting 0) :quiet :ready 2))
           (equal (take 4 reopened) '((:ok :held :booting 0) :quiet :ready 3))
           (posp (nth 6 created)) (posp (nth 6 opened)) (posp (nth 6 reopened))
           (equal (nth 2 empty) :failed) (equal (nth 3 (car empty)) 0)
           (equal (nth 2 bad-anchor) :failed) (equal (nth 3 (car bad-anchor)) 0))
      (cw "boot-unit created/opened/reopened/empty/bad-anchor ~x0~%"
          (list (append (take 4 created) (nthcdr 5 created))
                (append (take 4 opened) (nthcdr 5 opened))
                (append (take 4 reopened) (nthcdr 5 reopened))
                (append (take 4 empty) (nthcdr 5 empty))
                (append (take 4 bad-anchor) (nthcdr 5 bad-anchor)))))))
