; A2, the borrow count: every pool row's out-count is the number of live
; send/write operations on that row that have not released their borrow.
; The accounting and the per-operation lemmas are borrow-accounting.lisp;
; this book lifts them to every core-level step and states the keystone.
(in-package "ACL2")
(include-book "borrow-accounting")
(include-book "executor-wake")
(include-book "host-ops")
(include-book "assembly-core")

;; The core faces of the accounting's children lemmas.
(defthm fn2-core-stop-children
  (and (equal (fn2-core-ops (fn2-core-stop reason core)) (fn2-core-ops core))
       (equal (fn2-core-pool (fn2-core-stop reason core)) (fn2-core-pool core)))
  :hints (("Goal" :in-theory (enable fn2-core-stop))))
(defthm fn2-harvest-one-children
  (and (equal (fn2-core-pool (mv-nth 10 (fn2-harvest-one core)))
              (mv-nth 1 (fn2-bc-harvest-pool-step (fn2-core-pool core) (fn2-core-ops core))))
       (equal (fn2-core-ops (mv-nth 10 (fn2-harvest-one core)))
              (fn2-bc-harvest-ops (fn2-core-pool core) (fn2-core-ops core))))
  :hints (("Goal" :in-theory (e/d (fn2-harvest-one fn2-bc-harvest-pool-step fn2-bc-harvest-ops
                                   fn2-bc-input-condp fn2-bc-release-condp)
                                  (fn2-harvest-next fn2-op-finish fn2-pool-release-out fn2-pool-complete-in
                                   fn2-core-stop fn2-op-cell fn2-op-range fn2-op-slotp fn2-op-phase
                                   fn2-bc-release-condp-by-vals fn2-op-borrowp-by-vals)))))
(defun-nx fn2-core-borrows-accountedp (core)
  (fn2-borrows-accountedp (fn2-core-pool core) (fn2-core-ops core)))
(defthm fn2-harvest-one-borrows-accounted
  (implies (and (fn2-ops-semanticp (fn2-core-ops core))
                (fn2-core-borrows-accountedp core))
           (fn2-core-borrows-accountedp (mv-nth 10 (fn2-harvest-one core))))
  :hints (("Goal" :in-theory (e/d (fn2-core-borrows-accountedp)
                                  (fn2-harvest-one fn2-borrows-accountedp fn2-ops-semanticp
                                   fn2-bc-harvest-pool-step fn2-bc-harvest-ops))
           :use ((:instance fn2-bc-harvest-borrows (pool (fn2-core-pool core)) (ops (fn2-core-ops core)))))))
(defmacro fn2-bc-issue-borrows (name args)
  (let ((call `(,name ,@args okind oslot ogen principal core))
        (children (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-CHILDREN") name)))
    `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BORROWS-ACCOUNTED") name)
       (implies (and (fn2-corep core) (fn2-core-wfp core) (fn2-core-borrows-accountedp core))
                (fn2-core-borrows-accountedp (mv-nth 3 ,call)))
       :hints (("Goal" :in-theory (e/d (,name ,children fn2-core-borrows-accountedp)
                                       (fn2-issue-children fn2-borrows-accountedp fn2-core-wfp)))))))
(fn2-bc-issue-borrows fn2-issue-receive (cap-index cap-nonce slot gen len))
(fn2-bc-issue-borrows fn2-issue-send (cap-index cap-nonce slot gen off len may-release))
(fn2-bc-issue-borrows fn2-issue-read (offset slot gen len))
(fn2-bc-issue-borrows fn2-issue-write (offset slot gen off len fua))
(fn2-bc-issue-borrows fn2-issue-fence ())
(fn2-bc-issue-borrows fn2-issue-accept (cap-index cap-nonce))
(fn2-bc-issue-borrows fn2-issue-close (cap-index cap-nonce))
(fn2-bc-issue-borrows fn2-issue-cancel (target-slot target-gen))
(fn2-bc-issue-borrows fn2-issue-entropy (slot gen len))
(defthm fn2-issue-arm-wake-borrow-row
  (and (equal (fn2-core-pool (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen core))) (fn2-core-pool core))
       (fn2-ops-keys-except (mv-nth 1 (fn2-op-reserve *fn2-action-arm-wake* 0 0 0 0 0 (fn2-core-ops core))) (fn2-core-ops core) (fn2-core-ops (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen core))))
       (equal (fn2-ops-rows (fn2-core-ops (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen core)))) (fn2-ops-rows (fn2-core-ops core)))
       (implies (not (and (unsigned-byte-p 60 deadline) (unsigned-byte-p 60 observation-gen) (fn2-core-outbox-ready (fn2-core-ops core)) (equal (mv-nth 0 (fn2-op-reserve *fn2-action-arm-wake* 0 0 0 0 0 (fn2-core-ops core))) :ok)))
                (equal (fn2-core-ops (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen core))) (fn2-core-ops core)))
       (implies (and (unsigned-byte-p 60 deadline) (unsigned-byte-p 60 observation-gen) (fn2-core-outbox-ready (fn2-core-ops core)) (equal (mv-nth 0 (fn2-op-reserve *fn2-action-arm-wake* 0 0 0 0 0 (fn2-core-ops core))) :ok))
                (and (not (fn2-op-borrowp (mv-nth 1 (fn2-op-reserve *fn2-action-arm-wake* 0 0 0 0 0 (fn2-core-ops core))) (fn2-core-ops (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen core)))))
                     (not (equal (fn2-ops-may-release (mv-nth 1 (fn2-op-reserve *fn2-action-arm-wake* 0 0 0 0 0 (fn2-core-ops core))) (fn2-core-ops (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen core)))) 1)))))
  :hints (("Goal" :in-theory (e/d (fn2-issue-arm-wake fn2-bc-vals-borrowp fn2-borrow-valsp)
                                  (fn2-op-reserve fn2-op-set-wake fn2-op-enqueue fn2-core-stop fn2-op-borrowp fn2-ops-keys-except
                                   fn2-op-phase-code fn2-ops-gen mv-nth fn2-core-outbox-ready)))))
(defthm fn2-issue-arm-wake-borrows-accounted
  (implies (and (fn2-corep core) (fn2-core-wfp core) (fn2-core-borrows-accountedp core))
           (fn2-core-borrows-accountedp (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen core))))
  :hints (("Goal" :cases ((and (unsigned-byte-p 60 deadline) (unsigned-byte-p 60 observation-gen) (fn2-core-outbox-ready (fn2-core-ops core)) (equal (mv-nth 0 (fn2-op-reserve *fn2-action-arm-wake* 0 0 0 0 0 (fn2-core-ops core))) :ok)))
           :in-theory (e/d (fn2-core-borrows-accountedp)
                           (fn2-issue-arm-wake fn2-op-reserve fn2-borrows-accountedp fn2-op-borrowp-by-vals
                            fn2-ops-keys-except fn2-borrows-accountedp-ops-transfer
                            fn2-issue-arm-wake-borrow-row fn2-core-wfp))
           :use ((:instance fn2-borrows-accountedp-ops-transfer (pool (fn2-core-pool core)) (ops (fn2-core-ops core))
                            (ops2 (fn2-core-ops (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen core)))) (j (mv-nth 1 (fn2-op-reserve *fn2-action-arm-wake* 0 0 0 0 0 (fn2-core-ops core)))))
                 (:instance fn2-op-reserve-borrow-row (kind *fn2-action-arm-wake*) (okind 0) (oslot 0) (ogen 0)
                            (principal 0) (may 0) (ops (fn2-core-ops core)))
                 (:instance fn2-op-borrowp-when-free (j (mv-nth 1 (fn2-op-reserve *fn2-action-arm-wake* 0 0 0 0 0 (fn2-core-ops core)))) (x (fn2-core-ops core)))
                 fn2-issue-arm-wake-borrow-row))))
(defun fn2-core-borrows-accounted-check (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)) (fn2-ops (fn2-core-ops fn2-core)))
    (ok) (fn2-borrows-accounted-check fn2-pool fn2-ops) ok))
(defthm fn2-core-rows-natp
  (implies (fn2-core-wfp core)
           (and (natp (fn2-pool-rows (fn2-core-pool core)))
                (natp (fn2-ops-rows (fn2-core-ops core)))))
  :hints (("Goal" :in-theory (e/d (fn2-pool-wfp fn2-ops-wfp) (fn2-core-wfp))
           :use (fn2-pool-wfp-of-fn2-core-pool fn2-ops-wfp-of-fn2-core-ops))))
(defthm fn2-core-borrows-accounted-check-equiv
  (implies (fn2-core-wfp core)
           (equal (fn2-core-borrows-accounted-check core) (fn2-core-borrows-accountedp core)))
  :hints (("Goal" :in-theory (e/d (fn2-core-borrows-accountedp) (fn2-borrows-accounted-check fn2-core-wfp)))))
;; ---------------------------------------------------------------------------
;; The other pool writers. Every pool primitive outside the borrow (lease-out,
;; release-out) writes at most one row S, and either keeps S's borrow key
;; (out-count, state, gen) or finds S not leased out (so, by the invariant,
;; holding no borrow) and leaves it holding none. One transfer covers them.
(defmacro fn2-bc-core-pool (name formals position)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BORROWS-ACCOUNTED") name)
     (implies (and (fn2-core-borrows-accountedp core) (natp (fn2-ops-rows (fn2-core-ops core))))
              (fn2-core-borrows-accountedp (mv-nth ,position (,name ,@formals core))))
     :hints (("Goal" :in-theory (e/d (,name fn2-core-borrows-accountedp)
                                     (fn2-borrows-accountedp fn2-pool-reserve fn2-pool-reset fn2-pool-write
                                      fn2-pool-copy-range fn2-pool-hand fn2-pool-accept-own fn2-pool-drop-prefix
                                      fn2-pool-truncate fn2-core-release-children))))))
(fn2-bc-core-pool fn2-core-reserve (class okind oslot ogen) 3)
(fn2-bc-core-pool fn2-core-release (slot gen okind oslot ogen) 1)
(fn2-bc-core-pool fn2-core-reset (slot gen okind oslot ogen) 1)
(fn2-bc-core-pool fn2-core-write (slot gen idx byte okind oslot ogen) 1)
(fn2-bc-core-pool fn2-core-copy-range (src sgen soff dst dgen doff len okind oslot ogen) 1)
(fn2-bc-core-pool fn2-core-hand (slot gen okind oslot ogen tkind tslot tgen) 1)
(fn2-bc-core-pool fn2-core-accept-hand (slot gen okind oslot ogen) 1)
(fn2-bc-core-pool fn2-core-drop-prefix (slot gen k cursor limit okind oslot ogen) 2)
(fn2-bc-core-pool fn2-core-truncate (slot gen n okind oslot ogen) 1)
;; ---------------------------------------------------------------------------
;; The ops-only steps: none moves a borrow. Each keeps every row's borrow key
;; (post-result, post-accept-result, ack, request-cancel and the scalars), or
;; touches only a row that holds no borrow before or after (finish).
(defthm fn2-core-loan-write-borrows-accounted
  (implies (and (fn2-core-borrows-accountedp core) (natp (fn2-ops-rows (fn2-core-ops core))))
           (fn2-core-borrows-accountedp
            (update-fn2-core-pool (mv-nth 1 (fn2-pool-adapter-write slot gen opslot opgen idx byte (fn2-core-pool core)))
                                  core)))
  :hints (("Goal" :in-theory (e/d (fn2-core-borrows-accountedp) (fn2-borrows-accountedp fn2-pool-adapter-write)))))
(defthm fn2-core-borrows-accounted-check-equiv-rows
  (implies (and (natp (fn2-pool-rows (fn2-core-pool core))) (natp (fn2-ops-rows (fn2-core-ops core))))
           (equal (fn2-core-borrows-accounted-check core) (fn2-core-borrows-accountedp core)))
  :hints (("Goal" :in-theory (e/d (fn2-core-borrows-accountedp) (fn2-borrows-accounted-check)))))

;; The host boundary's ops entries and the executor's mailbox, on the core.
(defmacro fn2-bc-core-ops-only (name formals target position)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BORROWS-ACCOUNTED") name)
     (implies (and (fn2-core-borrows-accountedp core) (fn2-ops-semanticp (fn2-core-ops core))
                   (natp (fn2-ops-rows (fn2-core-ops core))))
              (fn2-core-borrows-accountedp ,(if position `(mv-nth ,position (,name ,@formals core)) `(,name ,@formals core))))
     :hints (("Goal" :in-theory (e/d (,name fn2-core-borrows-accountedp)
                                     (fn2-borrows-accountedp fn2-ops-semanticp ,target))))))
(fn2-bc-core-ops-only fn2-host-post-result (cell slot gen evkind outcome reason count aux0 aux1) fn2-post-result nil)
(fn2-bc-core-ops-only fn2-host-post-accept-result (slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3)
  fn2-post-accept-result nil)
(fn2-bc-core-ops-only fn2-host-post-clock (mono real flags) fn2-post-clock nil)
(fn2-bc-core-ops-only fn2-host-post-signal (bits) fn2-post-signal nil)
(fn2-bc-core-ops-only fn2-host-count-stray () fn2-count-stray nil)
(fn2-bc-core-ops-only fn2-host-outbox-ack (n) fn2-outbox-ack 1)
(fn2-bc-core-ops-only fn2-host-op-finish (slot gen) fn2-op-finish 1)
(defthm fn2-exec-mailbox-borrows-accounted
  (implies (fn2-core-borrows-accountedp core)
           (fn2-core-borrows-accountedp (mv-nth 5 (fn2-exec-mailbox core))))
  :hints (("Goal" :in-theory (e/d (fn2-exec-mailbox fn2-core-borrows-accountedp)
                                  (fn2-borrows-accountedp fn2-take-clock fn2-take-signal fn2-exec-clock
                                   fn2-exec-record fn2-core-stop)))))
(defmacro fn2-bc-host-rows (name formals position)
  (let ((q (if position `(mv-nth ,position (,name ,@formals core)) `(,name ,@formals core))))
    `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BC-ROWS") name)
       (and (equal (fn2-core-pool ,q) (fn2-core-pool core))
            (equal (fn2-ops-rows (fn2-core-ops ,q)) (fn2-ops-rows (fn2-core-ops core))))
       :hints (("Goal" :in-theory (enable ,name))))))
(fn2-bc-host-rows fn2-host-post-result (cell slot gen evkind outcome reason count aux0 aux1) nil)
(fn2-bc-host-rows fn2-host-post-accept-result (slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3) nil)
(fn2-bc-host-rows fn2-host-post-clock (mono real flags) nil)
(fn2-bc-host-rows fn2-host-post-signal (bits) nil)
(fn2-bc-host-rows fn2-host-count-stray () nil)
(fn2-bc-host-rows fn2-host-outbox-ack (n) 1)
(fn2-bc-host-rows fn2-host-op-finish (slot gen) 1)
;; ---------------------------------------------------------------------------
;; FN2-CORE-BORROW-CONSERVATION (A2): over every step that leases or releases
;; a borrow (each action's issue, the arm-wake issue, and one harvest), each
;; pool row's out-count stays the number of live send/write operations on
;; that row that have not released, every live borrow names its row's current
;; generation, and only a send may release early. So the release a harvested
;; operation triggers always spends a borrow that operation itself counted.
(defconst *fn2-core-borrow-steps*
  '(:harvest :receive :send :read :write :fence :accept :close :cancel :entropy :arm-wake
    :reserve :release :reset :pool-write :copy-range :hand :accept-hand :drop-prefix :truncate :loan-write
    :post-result :post-accept-result :post-clock :post-signal :count-stray :outbox-ack :finish :mailbox))
(defun fn2-core-borrow-step (op a fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (case op
    (:harvest (mv-let (found opslot opgen cell evkind outcome reason count aux0 aux1 fn2-core)
                (fn2-harvest-one fn2-core)
                (declare (ignore found opslot opgen cell evkind outcome reason count aux0 aux1))
                fn2-core))
    (:receive (mv-let (code slot gen fn2-core)
                (fn2-issue-receive (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a)
                                   (nth 5 a) (nth 6 a) (nth 7 a) (nth 8 a) fn2-core)
                (declare (ignore code slot gen)) fn2-core))
    (:send (mv-let (code slot gen fn2-core)
             (fn2-issue-send (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) (nth 6 a)
                             (nth 7 a) (nth 8 a) (nth 9 a) (nth 10 a) fn2-core)
             (declare (ignore code slot gen)) fn2-core))
    (:read (mv-let (code slot gen fn2-core)
             (fn2-issue-read (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                             (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a) fn2-core)
             (declare (ignore code slot gen)) fn2-core))
    (:write (mv-let (code slot gen fn2-core)
              (fn2-issue-write (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a)
                               (nth 6 a) (nth 7 a) (nth 8 a) (nth 9 a) fn2-core)
              (declare (ignore code slot gen)) fn2-core))
    (:fence (mv-let (code slot gen fn2-core)
              (fn2-issue-fence (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) fn2-core)
              (declare (ignore code slot gen)) fn2-core))
    (:accept (mv-let (code slot gen fn2-core)
               (fn2-issue-accept (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) fn2-core)
               (declare (ignore code slot gen)) fn2-core))
    (:close (mv-let (code slot gen fn2-core)
              (fn2-issue-close (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) fn2-core)
              (declare (ignore code slot gen)) fn2-core))
    (:cancel (mv-let (code slot gen fn2-core)
               (fn2-issue-cancel (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) fn2-core)
               (declare (ignore code slot gen)) fn2-core))
    (:entropy (mv-let (code slot gen fn2-core)
                (fn2-issue-entropy (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) (nth 6 a)
                                   fn2-core)
                (declare (ignore code slot gen)) fn2-core))
    (:arm-wake (mv-let (code slot gen fn2-core)
                 (fn2-issue-arm-wake (nth 0 a) (nth 1 a) fn2-core)
                 (declare (ignore code slot gen)) fn2-core))
    (:reserve (mv-let (code slot gen fn2-core)
                (fn2-core-reserve (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) fn2-core)
                (declare (ignore code slot gen)) fn2-core))
    (:release (mv-let (code fn2-core)
                (fn2-core-release (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) fn2-core)
                (declare (ignore code)) fn2-core))
    (:reset (mv-let (code fn2-core)
              (fn2-core-reset (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) fn2-core)
              (declare (ignore code)) fn2-core))
    (:pool-write (mv-let (code fn2-core)
                   (fn2-core-write (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) (nth 6 a) fn2-core)
                   (declare (ignore code)) fn2-core))
    (:copy-range (mv-let (code fn2-core)
                   (fn2-core-copy-range (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a)
                                        (nth 6 a) (nth 7 a) (nth 8 a) (nth 9 a) fn2-core)
                   (declare (ignore code)) fn2-core))
    (:hand (mv-let (code fn2-core)
             (fn2-core-hand (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a)
                            fn2-core)
             (declare (ignore code)) fn2-core))
    (:accept-hand (mv-let (code fn2-core)
                    (fn2-core-accept-hand (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) fn2-core)
                    (declare (ignore code)) fn2-core))
    (:drop-prefix (mv-let (code next fn2-core)
                    (fn2-core-drop-prefix (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a)
                                          (nth 6 a) (nth 7 a) fn2-core)
                    (declare (ignore code next)) fn2-core))
    (:truncate (mv-let (code fn2-core)
                 (fn2-core-truncate (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) fn2-core)
                 (declare (ignore code)) fn2-core))
    (:loan-write (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
                   (code fn2-pool)
                   (fn2-pool-adapter-write (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) fn2-pool)
                   (let ((ignored code)) (declare (ignore ignored)) fn2-core)))
    (:post-result (fn2-host-post-result (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a)
                                        (nth 6 a) (nth 7 a) (nth 8 a) fn2-core))
    (:post-accept-result (fn2-host-post-accept-result (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a)
                                                      (nth 6 a) (nth 7 a) (nth 8 a) (nth 9 a) (nth 10 a)
                                                      (nth 11 a) fn2-core))
    (:post-clock (fn2-host-post-clock (nth 0 a) (nth 1 a) (nth 2 a) fn2-core))
    (:post-signal (fn2-host-post-signal (nth 0 a) fn2-core))
    (:count-stray (fn2-host-count-stray fn2-core))
    (:outbox-ack (mv-let (code fn2-core) (fn2-host-outbox-ack (nth 0 a) fn2-core)
                   (declare (ignore code)) fn2-core))
    (:finish (mv-let (code fn2-core) (fn2-host-op-finish (nth 0 a) (nth 1 a) fn2-core)
               (declare (ignore code)) fn2-core))
    (:mailbox (mv-let (o v n b s fn2-core) (fn2-exec-mailbox fn2-core)
                (declare (ignore o v n b s)) fn2-core))
    (otherwise fn2-core)))
(defun fn2-core-borrow-hyps (op fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (member-eq op *fn2-core-borrow-steps*)
       (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (ok) (fn2-ops-semanticp fn2-ops) ok)
       (fn2-core-borrows-accounted-check fn2-core)))
(defun-nx fn2-core-borrow-conclusion (op a core)
  (fn2-core-borrows-accounted-check (fn2-core-borrow-step op a core)))
(defthm-owed fn2-core-borrow-conservation (op a core)
  (implies (fn2-core-borrow-hyps op core)
           (fn2-core-borrow-conclusion op a core))
  :schema :invariant :from (:columns fn2-pool)
  :teeth (fn2-core-borrow-teeth)
  :doc "A2: every issue (each action kind and arm-wake), every harvest, every core pool writer (reserve, release, reset, write, copy-range, hand, accept-hand, drop-prefix, truncate) and the host's loan write, the host boundary's ops entries (post-result, post-accept-result, post-clock, post-signal, count-stray, outbox-ack, op-finish) and the executor's mailbox keep each pool row's out-count equal to the number of live send/write operations on that row that have not released their borrow, with every live borrow naming its row's current generation and may-release only on a send; so the release a harvested operation triggers spends that operation's own counted borrow.")
(defthm fn2-core-borrow-conservation-proved
  (implies (fn2-core-borrow-hyps op core)
           (fn2-core-borrow-conclusion op a core))
  :hints (("Goal" :in-theory (e/d (fn2-core-borrow-hyps fn2-core-borrow-conclusion fn2-core-borrow-step)
                                  (fn2-harvest-one fn2-issue-receive fn2-issue-send fn2-issue-read
                                   fn2-issue-write fn2-issue-fence fn2-issue-accept fn2-issue-close
                                   fn2-issue-cancel fn2-issue-entropy fn2-issue-arm-wake fn2-core-wfp
                                   fn2-core-reserve fn2-core-release fn2-core-reset fn2-core-write
                                   fn2-core-copy-range fn2-core-hand fn2-core-accept-hand fn2-core-drop-prefix
                                   fn2-core-truncate fn2-pool-adapter-write fn2-host-post-result
                                   fn2-host-post-accept-result fn2-host-post-clock fn2-host-post-signal
                                   fn2-host-count-stray fn2-host-outbox-ack fn2-host-op-finish fn2-exec-mailbox
                                   fn2-ops-semanticp fn2-core-borrows-accountedp
                                   fn2-core-borrows-accounted-check fn2-core-rows-natp))
           :use ((:instance fn2-core-rows-natp)))))
(defthm fn2-core-borrow-conservation-statement
  (fn2-core-borrow-conservation$owed op a core)
  :hints (("Goal" :in-theory '(fn2-core-borrow-conservation$owed) :use fn2-core-borrow-conservation-proved)))
(fn2-owed-discharge fn2-core-borrow-conservation fn2-core-borrow-conservation-statement)
