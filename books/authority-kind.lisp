;; Schema and partition registration for fn2-auth (layer E): one served
;; authority request (docs/design/AUTHORITY-20261105.md section 3), taken by
;; an owner control connection (fn2-ctl, cns-kind.lisp) for a kind-29 frame.
;; Arm bodies and helper operations live in books/authority.lisp (a leaf
;; book). A durable verb is a real transaction: its own successor write
;; transaction (fn2-txn-authority-share, txn-kind.lisp), its records emitted
;; into its own workspace range, admitted to B's commit batch, bound, and
;; answered from the batch's settled outcome.
(in-package "ACL2")
(include-book "txn-kind")
(include-book "authority-codec")
(include-book "machine-arms")
(fn2-book-layer :e)

(defun fn2-auth-capacity (profile)
  (declare (xargs :guard t))
  (fn2-txn-authority-share profile))
(defthm fn2-auth-capacity-natp (natp (fn2-auth-capacity profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-auth-capacity))

(defmachine fn2-auth
 :phases (:free :decode :lookup :allocate :bhead :outcome :head :get :ready :batched :draining :retired)
 :fields ((ctl :link) (ctl-gen :u60) (request :u32) (fpos :u32) (flen :u32) (rx-slot :link) (rx-gen :u60)
          (admin :bool) (worked :bool) (principal :u60)
          (ws-slot :link) (ws-gen :u60) (ks-slot :link) (ks-gen :u60) (sx :u32)
          (opcode :u8) (noff :u32) (nlen :u32) (aslot :u32) (pid :u60)
          (outcome (:enum fn2-auth-outcome (:none :accepted :refused :uncertain :fault))) (reason :u8)
          ;; grant-set's and grant-get's request (op the operation identity), the
          ;; row's read row, the heads and the grant read or written
          (grantee :u60) (gright :u8) (gscope :u8) (gtarget :u60) (enabled :bool) (ehead :u60) (gop :u60)
          (xrow :u32) (ahead :u60) (grant :u60) (grantor :u60) (genabled :bool) (previous :u60) (gfound :bool)
          (gstep :u8) (cut :u60)
          ;; :ready's write: 0 to declare, 1 declared and resolving, 2 resolved
          (wstep :u8)
          (stopped :bool) (next-free :link))
 :holds ((:decode :tx-range :transaction-row) (:lookup :tx-range :transaction-row)
         (:allocate :tx-range :transaction-row) (:bhead :tx-range :transaction-row)
         (:outcome :tx-range :transaction-row) (:head :tx-range :transaction-row) (:get :tx-range :transaction-row)
         (:ready :tx-range :transaction-row)
         (:batched :tx-range :transaction-row :batch-membership)
         (:draining :tx-range :transaction-row))
 ;; :ready's one run puts, stages, emits, admits and binds (28,672 bytes, as fn2-txn's :ready)
 :budget (:bytes 32768 :steps 32 :descriptors 4)
 :capacity (fn2-auth-capacity profile)
 ;; the row's workspace (WS): B's transaction records are emitted into it
 ;; and admitted from it, so the frame in the connection's range stays
 ;; intact; its key range (KS): the octets a write names (principal-create's
 ;; name), copied from the frame so the records encode under the row's own
 ;; ownership (pool writes are contiguous, so they cannot share WS)
 :taken (:phase :decode :rows :transaction-row
         :ranges ((:tx-range :slot ws-slot :gen ws-gen :class 0) (:tx-range :slot ks-slot :gen ks-gen :class 0))
         :copy (ctl ctl-gen request fpos flen rx-slot rx-gen admin worked principal)
         :clear (sx opcode noff nlen aslot pid outcome reason grantee gright gscope gtarget enabled ehead gop
                 xrow ahead grant grantor genabled previous gfound gstep cut wstep stopped))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (ctl *fn2-none*) (rx-slot *fn2-none*) (ws-slot *fn2-none*) (ks-slot *fn2-none*) (account-ref *fn2-none*)
           (next-free fn2-machine-initial-next-free))
 :arms ((:free) (:decode) (:lookup) (:allocate) (:bhead) (:outcome) (:head) (:get) (:ready) (:batched) (:draining) (:retired))
 :observes ())

(defmachine-registry fn2-auth)
