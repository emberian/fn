; Layer E: served authority's request kind, fn2-auth (docs/design/
; AUTHORITY-20261105.md sections 1 and 3). An owner control connection
; (fn2-ctl, cns.lisp) takes one row per kind-29 frame; the row decodes the
; frame with the generated request codec (authority-codec.lisp), runs its
; verb, encodes the kind-30 reply with the generated reply codec into the
; connection's range and wakes it.
;
; principal-create NAME (an administrator connection only): the exact lookup
; in fn2-principals answers a recorded name's identity (a repeat creates
; nothing); else the row claims a :free account slot (a fresh incarnation,
; D7's fn2-account-principal-id), writes (NAME -> id) as a real durable
; transaction (its own successor write transaction, the records emitted into
; its own workspace range, admitted to B's commit batch, bound, and answered
; from the batch's settled outcome: accepted only once recoverably published,
; uncertain on an ambiguous write), and answers the id. A lost race to the
; same name (stage :duplicate) returns the claimed slot and answers the
; winner's identity.
;
; principal-bind NAME (an administrator connection that has done no consumer
; work, once): the exact lookup; the connection then acts as that principal
; and administers nothing. Binding is connection state, not a mutation.
;
; grant-set and grant-get (opcodes 2 and 3) answer fault until the grants
; land (schemas 17-19); any other opcode, or a frame that is not exactly its
; layout, answers refused frame and never another verb.
(in-package "ACL2")
(include-book "cns")
(fn2-book-layer :e)

(defconst *fn2-auth-op-create* 0)
(defconst *fn2-auth-op-bind* 1)
(defconst *fn2-auth-op-set* 2)
(defconst *fn2-auth-op-get* 3)
(defconst *fn2-auth-op-stream* 4)
(assert-event (equal (fn2-authority-local-binding 'stream-resolve) (list *fn2-authority-request-kind* *fn2-auth-op-stream*)))
(assert-event (and (equal (fn2-authority-local-binding 'principal-create) (list *fn2-authority-request-kind* *fn2-auth-op-create*))
                   (equal (fn2-authority-local-binding 'principal-bind) (list *fn2-authority-request-kind* *fn2-auth-op-bind*))
                   (equal (fn2-authority-local-binding 'grant-set) (list *fn2-authority-request-kind* *fn2-auth-op-set*))
                   (equal (fn2-authority-local-binding 'grant-get) (list *fn2-authority-request-kind* *fn2-auth-op-get*))))

;; Reason words: 0 is the empty word (acceptance); K > 0 is the Kth of the
;; port's reasons followed by uncertain's persistence. The octets are the
;; word's lowercase name.
(defconst *fn2-auth-reason-words* (append *fn2-authority-reasons* '(persistence)))
(defun fn2-auth-word-octets-of (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (atom cs) nil (cons (char-code (char-downcase (car cs))) (fn2-auth-word-octets-of (cdr cs)))))
(defun fn2-auth-words-octets (ws)
  (declare (xargs :guard (symbol-listp ws)))
  (if (atom ws) nil (cons (fn2-auth-word-octets-of (coerce (symbol-name (car ws)) 'list)) (fn2-auth-words-octets (cdr ws)))))
(defconst *fn2-auth-reason-octets* (fn2-auth-words-octets *fn2-auth-reason-words*))
(defmacro fn2-auth-reason-code (word)
  (let ((p (position-eq word *fn2-auth-reason-words*)))
    (if p (+ 1 p) (er hard 'fn2-auth-reason-code "~x0 is not a reason of fn2-authority." word))))
(defconst *fn2-auth-reason-unknown-stream* (fn2-auth-reason-code unknown-stream))
(defconst *fn2-auth-reason-access* (fn2-auth-reason-code access))
(defconst *fn2-auth-reason-meter* (fn2-auth-reason-code meter))
(defconst *fn2-auth-reason-frame* (fn2-auth-reason-code frame))
(defconst *fn2-auth-reason-unknown-principal* (fn2-auth-reason-code unknown-principal))
(defconst *fn2-auth-reason-persistence* (fn2-auth-reason-code persistence))
(defconst *fn2-auth-reason-scope* (fn2-auth-reason-code scope))
(defconst *fn2-auth-reason-stale-revision* (fn2-auth-reason-code stale-revision))
(defconst *fn2-auth-reason-operation-reused* (fn2-auth-reason-code operation-reused))
;; The grant schemas (authority-schema.lisp) and the port's right and scope
;; codes (their enums' order; fn2-grant-current keys them as octets).
(defconst *fn2-grants-sid* 17)
;; fn2-outcome's accepted code, as D's transaction writes it (txn.lisp's
;; *fn2-txn-outcome-accepted*, a later book)
(defconst *fn2-auth-outcome-code-accepted* 1)
(defconst *fn2-grant-current-sid* 18)
(defconst *fn2-authority-head-sid* 19)
(defconst *fn2-authority-right-consume* 0)
(defconst *fn2-authority-right-read* 1)
(defconst *fn2-authority-scope-own-consumers* 0)
(defconst *fn2-authority-scope-stream* 1)
(assert-event (and (equal (caddr *fn2-authority-right-layout*) '(:consume :read :append))
                   (equal (caddr *fn2-authority-scope-layout*) '(:own-consumers :stream))
                   (equal *fn2-authority-right-append* 2)))
(defun fn2-auth-octet-listp (x)
  (declare (xargs :guard t))
  (if (atom x) (null x) (and (unsigned-byte-p 8 (car x)) (fn2-auth-octet-listp (cdr x)))))
(defun fn2-auth-octet-lists-p (x)
  (declare (xargs :guard t))
  (if (atom x) (null x) (and (fn2-auth-octet-listp (car x)) (<= (len (car x)) 64) (fn2-auth-octet-lists-p (cdr x)))))
(assert-event (fn2-auth-octet-lists-p *fn2-auth-reason-octets*))
(defun fn2-auth-word (reason)
  (declare (xargs :guard t))
  (let ((w (and (posp reason) (<= reason (len *fn2-auth-reason-octets*)) (nth (- reason 1) *fn2-auth-reason-octets*))))
    (if (and (fn2-auth-octet-listp w) (<= (len w) 64)) w nil)))
(defthm fn2-auth-word-octets
  (and (fn2-auth-octet-listp (fn2-auth-word reason)) (<= (len (fn2-auth-word reason)) 64)))
(in-theory (disable fn2-auth-word))

;; The codec's fields: the row's successor stripe (fn2-idc-stripe) past what
;; the successor's own resolve and lookup use, so a decoded request and an
;; encoded reply never touch the successor's rows.
(defconst *fn2-auth-codec-at* 1536)
(defconst *fn2-auth-request-at* *fn2-auth-codec-at*)
(defconst *fn2-auth-reply-at* (+ *fn2-auth-codec-at* 16))
(defconst *fn2-auth-result-at* (+ *fn2-auth-codec-at* 32))
(assert-event (and (<= (+ *fn2-idc-rb* *fn2-run-reader-fields*) *fn2-auth-codec-at*)
                   (<= (+ *fn2-auth-result-at* 16) *fn2-idc-stride*)
                   (<= *fn2-authority-req-principal-create-num-fields* 16)
                   (<= *fn2-authority-req-principal-bind-num-fields* 16)
                   (<= *fn2-authority-reply-num-fields* 16)
                   (<= *fn2-authority-res-principal-bind-num-fields* 16)))

;; The class octet of an outcome (fn2-auth-outcome's order is the port's
;; class enum's, :none aside).
(defun fn2-auth-class (outcome)
  (declare (xargs :guard t))
  (let ((o (nfix outcome)))
    (cond ((equal o *fn2-auth-outcome-accepted*) 0) ((equal o *fn2-auth-outcome-refused*) 1)
          ((equal o *fn2-auth-outcome-uncertain*) 2) (t 3))))

;; The reply into a range: the reason word at [0, W), the kind-30 reply at
;; [W, END), its fields at HB (header), HB + 16 (result) and HB + 24
;; (grant-get's found tail); (mv code w end fn2-fields fn2-pool). The
;; accepted result per verb: principal-create (P); principal-bind (P HEAD);
;; grant-set (GRANT HEAD receipt), the receipt empty (no receipt is defined
;; for a grant yet); grant-get (FOUND HEAD) and, iff FOUND = 1, (GRANT
;; GRANTOR ENABLED PREVIOUS).
(defun fn2-auth-write-word (ws i slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp i))))
  (if (atom ws) (mv :ok fn2-pool)
    (mv-let (c fn2-pool) (fn2-pool-write slot gen i (car ws) okind oslot ogen fn2-pool)
      (if (eq c :ok) (fn2-auth-write-word (cdr ws) (+ 1 (nfix i)) slot gen okind oslot ogen fn2-pool)
        (mv c fn2-pool)))))
(fn2-pool-preserves fn2-auth-write-word (ws i slot gen okind oslot ogen fn2-pool) :position 1)
(in-theory (disable fn2-auth-write-word))
(defun fn2-auth-encode-result (op p head grant grantor enabled previous found rb slot gen hend okind oslot ogen fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp rb)
                              (<= (+ rb 16) (fn2-fields-rows fn2-fields)))
                  :guard-hints (("Goal" :in-theory (disable fn2-fields-rows)))))
  (b* (((unless (and (unsigned-byte-p 60 p) (unsigned-byte-p 60 head) (unsigned-byte-p 60 grant)
                     (unsigned-byte-p 60 grantor) (unsigned-byte-p 60 previous)
                     (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (natp hend)))
        (mv :state 0 fn2-fields fn2-pool))
       (en (if (equal enabled 1) 1 0)) (fd (if (equal found 1) 1 0)))
    (cond ((equal op *fn2-auth-op-stream*)
           (let ((fn2-fields (fn2-layout-store rb p 0 0 0 0 0 fn2-fields)))
             (mv-let (c e fn2-pool) (fn2-authority-res-stream-resolve-encode rb slot gen hend okind oslot ogen fn2-fields fn2-pool) (mv c e fn2-fields fn2-pool))))
          ((equal op *fn2-auth-op-create*)
           (let ((fn2-fields (fn2-layout-store rb p 0 0 0 0 0 fn2-fields)))
             (mv-let (c e fn2-pool) (fn2-authority-res-principal-create-encode rb slot gen hend okind oslot ogen fn2-fields fn2-pool) (mv c e fn2-fields fn2-pool))))
          ((equal op *fn2-auth-op-bind*)
           (let* ((fn2-fields (fn2-layout-store rb p 0 0 0 0 0 fn2-fields))
                  (fn2-fields (fn2-layout-store (+ 1 rb) head 0 0 0 0 0 fn2-fields)))
             (mv-let (c e fn2-pool) (fn2-authority-res-principal-bind-encode rb slot gen hend okind oslot ogen fn2-fields fn2-pool) (mv c e fn2-fields fn2-pool))))
          ((equal op *fn2-auth-op-set*)
           (let* ((fn2-fields (fn2-layout-store rb grant 0 0 0 0 0 fn2-fields))
                  (fn2-fields (fn2-layout-store (+ 1 rb) head 0 0 0 0 0 fn2-fields))
                  (fn2-fields (fn2-layout-store (+ 2 rb) 0 slot gen 0 0 0 fn2-fields)))
             (mv-let (c e fn2-pool) (fn2-authority-res-grant-set-encode rb slot gen hend okind oslot ogen fn2-fields fn2-pool) (mv c e fn2-fields fn2-pool))))
          (t
           (b* ((fn2-fields (fn2-layout-store rb fd 0 0 0 0 0 fn2-fields))
                (fn2-fields (fn2-layout-store (+ 1 rb) head 0 0 0 0 0 fn2-fields))
                ((mv c e fn2-pool) (fn2-authority-res-grant-get-encode rb slot gen hend okind oslot ogen fn2-fields fn2-pool))
                ((unless (and (eq c :ok) (equal fd 1) (natp e))) (mv c e fn2-fields fn2-pool))
                (tb (+ rb 8))
                (fn2-fields (fn2-layout-store tb grant 0 0 0 0 0 fn2-fields))
                (fn2-fields (fn2-layout-store (+ 1 tb) grantor 0 0 0 0 0 fn2-fields))
                (fn2-fields (fn2-layout-store (+ 2 tb) en 0 0 0 0 0 fn2-fields))
                (fn2-fields (fn2-layout-store (+ 3 tb) previous 0 0 0 0 0 fn2-fields)))
             (mv-let (c e2 fn2-pool) (fn2-authority-res-grant-get-found-encode tb slot gen e okind oslot ogen fn2-fields fn2-pool) (mv c e2 fn2-fields fn2-pool)))))))

;; The kind 30 reply, sealed, at the range's fill (after the request, as
;; fn2-cns-post-reply's kind 28): the reason word at [ROFF, ROFF+W) as
;; scratch, then the frame at [K, K+TOTAL): ten reserved header octets, the
;; reply layout (header fields at HB, result at HB + 16, grant-get's found
;; tail at HB + 24), then fn2-fnct-seal-pool's header (fields at HB + 40)
;; and BLAKE3 trailer in hasher ROW (the control connection's format row).
;; (mv code k total fn2-fields fn2-digests fn2-b3 fn2-pool).
(fn2-pool-block-shape fn2-auth-encode-result-shape
  (fn2-auth-encode-result op p head grant grantor enabled previous found rb slot gen hend okind oslot ogen fn2-fields fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 2) (fn2-pool 3))
  (("Goal" :in-theory (e/d (fn2-auth-encode-result) (fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-fields-rows fn2-pool-rows)))))
(in-theory (disable fn2-auth-encode-result))
(defun fn2-auth-seal-reply-pool (op outcome reason p head grant grantor enabled previous found hb row slot gen okind oslot ogen
                                    fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
                  :guard-hints (("Goal" :in-theory (disable fn2-fields-rows)))))
  (b* (((unless (and (natp hb) (<= (+ hb 64) (fn2-fields-rows fn2-fields))
                     (unsigned-byte-p 8 op) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)))
        (mv :bounds 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       (rb (+ hb 16))
       (roff (fn2-pool-fill-value slot fn2-pool))
       ((unless (unsigned-byte-p 32 roff)) (mv :bounds 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       (word (fn2-auth-word reason))
       ((mv wc fn2-pool) (fn2-auth-write-word word roff slot gen okind oslot ogen fn2-pool))
       ((unless (eq wc :ok)) (mv :size 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       (w (len word))
       (k (fn2-pool-fill-value slot fn2-pool))
       ((unless (unsigned-byte-p 32 (+ k *fn2-fnct-header-octets*))) (mv :bounds 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv hc fn2-pool) (fn2-fnct-put-be 0 0 *fn2-fnct-header-octets* slot gen okind oslot ogen fn2-pool))
       ((unless (eq hc :ok)) (mv :size 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       (fn2-fields (fn2-layout-store hb op 0 0 0 0 0 fn2-fields))
       (fn2-fields (fn2-layout-store (+ 1 hb) (fn2-auth-class outcome) 0 0 0 0 0 fn2-fields))
       (fn2-fields (fn2-layout-store (+ 2 hb) 0 slot gen roff w 0 fn2-fields))
       ((mv ec hend fn2-pool)
        (fn2-authority-reply-encode hb slot gen (+ k *fn2-fnct-header-octets*) okind oslot ogen fn2-fields fn2-pool))
       ((unless (and (eq ec :ok) (natp hend))) (mv :size 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv xc & fn2-fields fn2-pool)
        (if (equal (nfix outcome) *fn2-auth-outcome-accepted*)
            (fn2-auth-encode-result op p head grant grantor enabled previous found rb slot gen hend okind oslot ogen fn2-fields fn2-pool)
          (mv :ok hend fn2-fields fn2-pool)))
       ((unless (eq xc :ok)) (mv :size 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv code total fn2-fields fn2-digests fn2-b3 fn2-pool)
        (fn2-fnct-seal-pool (+ hb 40) row k *fn2-authority-reply-kind* slot gen okind oslot ogen
                            fn2-fields fn2-digests fn2-b3 fn2-pool)))
    (mv code k (nfix total) fn2-fields fn2-digests fn2-b3 fn2-pool)))
(fn2-pool-block-shape fn2-auth-seal-reply-pool-shape
  (fn2-auth-seal-reply-pool op outcome reason p head grant grantor enabled previous found hb row slot gen okind oslot ogen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 3) (fn2-digests 4) (fn2-b3 5) (fn2-pool 6))
  (("Goal" :in-theory (e/d (fn2-auth-seal-reply-pool) (fn2-fieldsp fn2-fields-wfp fn2-digestsp fn2-digests-wfp fn2-b3p fn2-b3-wfp fn2-poolp fn2-pool-wfp fn2-digests-rows fn2-b3-rows fn2-fields-rows fn2-pool-rows)))))
(defthm fn2-auth-seal-reply-pool-natp
  (and (natp (mv-nth 1 (fn2-auth-seal-reply-pool op outcome reason p head grant grantor enabled previous found hb row slot gen okind oslot ogen fn2-fields fn2-digests fn2-b3 fn2-pool)))
       (natp (mv-nth 2 (fn2-auth-seal-reply-pool op outcome reason p head grant grantor enabled previous found hb row slot gen okind oslot ogen fn2-fields fn2-digests fn2-b3 fn2-pool))))
  :hints (("Goal" :in-theory (enable fn2-auth-seal-reply-pool))))
(in-theory (disable fn2-auth-seal-reply-pool))

;; ---------------------------------------------------------------------------
;; The operations the arms call.
(defcost fn2-auth-successor :answers (:ok :bounds)
 :doc "The row's successor write transaction: fn2-txn's capacity plus the row's slot (fn2-txn-authority-share).")
(defcost fn2-auth-decode :answers (:ok :frame) :bytes 4096 :tables (fn2-core-fields)
 :doc "Decode a kind-29 payload with its opcode's generated layout: (mv code opcode name-offset name-length); a payload that is not exactly its layout is :frame.")
(defcost fn2-auth-claim :answers (:ok :exhausted) :tables (fn2-core-accounts)
 :doc "Claim a :free account slot for a new principal (fn2-account-claim): (mv code slot id).")
(defcost fn2-auth-unclaim :tables (fn2-core-accounts)
 :doc "Return a claimed slot whose principal was not created.")
(defcost fn2-auth-put-create :answers (:ok :state) :bytes 4096
 :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields fn2-core-run-cursors fn2-core-run-paths fn2-core-id-decides)
 :doc "Declare principal-create's write, (NAME -> id) in fn2-principals, in the row's successor transaction and resolve its key.")
(defcost fn2-auth-bind-ctl :tables (fn2-ctl-table)
 :doc "An accepted principal-bind binds the connection: it acts as the principal and administers nothing.")
(defcost fn2-auth-post-reply :answers (:ok :dropped :fault) :bytes 4096
 :tables (fn2-ctl-table fn2-core-machines fn2-core-pool fn2-core-fields fn2-core-digests fn2-core-b3)
 :doc "Encode the kind-30 reply into the control connection's range, bind its principal on an accepted principal-bind, and post the reply's extent.")

;; the key range's release (the workspace's is fn2-core-release with its
;; :tx-range effect; one effect per release site, as upload's two windows)
(defcost fn2-auth-release-ks :answers t :tables (fn2-core-pool)
  :doc "Release a draining authority row's key range.")

(defcost fn2-auth-read-row :answers (:ok :bounds) :doc "The row's read row, in the authority block (the last A read rows).")
(defcost fn2-auth-decode-grant :answers (:ok :frame) :bytes 4096 :tables (fn2-core-fields)
 :doc "Decode grant-set's or grant-get's fields with the generated layout: (mv code grantee right scope target enabled expected-head op).")
(defcost fn2-auth-known :answers (:ok :absent) :doc "Whether a durable principal id names a live account incarnation.")
(defcost fn2-auth-identity :answers (:ok :bounds :owner :state) :bytes 64 :tables (fn2-core-pool)
 :doc "Write grant-set's 32-octet request identity at the key range's start.")
(defcost fn2-auth-find-outcome :answers (:ok :absent :more :state) :bytes 4096
 :tables (fn2-core-reads fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths fn2-core-fields fn2-core-pool)
 :doc "One step of the retry lookup in fn2-outcome: (mv code event same-request).")
(defcost fn2-auth-find-head :answers (:ok :more :state) :bytes 4096
 :tables (fn2-core-reads fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
 :doc "One step of a principal's authority-head lookup (0 when none): (mv code head).")
(defcost fn2-auth-find-current :answers (:ok :more :state) :bytes 4096
 :tables (fn2-core-reads fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
 :doc "One step of a current-grant lookup (0 when none): (mv code grant).")
(defcost fn2-auth-find-grant :answers (:ok :more :state) :bytes 4096
 :tables (fn2-core-reads fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
 :doc "One step of the immutable grant row's lookup: (mv code grantor enabled previous).")
(defcost fn2-auth-put-write :answers (:ok :state) :bytes 4096
 :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields fn2-core-run-cursors fn2-core-run-paths fn2-core-id-decides fn2-core-pool)
 :doc ":ready's write: grant-set's four (fn2-auth-put-grant) or principal-create's one (fn2-auth-put-create).")
(defcost fn2-auth-put-grant :answers (:ok :state) :bytes 4096
 :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields fn2-core-run-cursors fn2-core-run-paths fn2-core-id-decides)
 :doc "Declare grant-set's four writes (grant row, current pointer, head, outcome) in the row's successor transaction and resolve them.")

;; ---------------------------------------------------------------------------
;; The exact reads of the published grants on a read row, and the consumer
;; surface's check over them (step 3c), expanded in assembly-callbacks-e-cns
;; before the consumer request's continuations (fn2-cns-events), which call
;; fn2-cns-authority-allows at :check; the authority rows' continuations
;; (fn2-auth-events, after) use the same reads.
(assert-event (and (equal *fn2-cns-right-consume* *fn2-authority-right-consume*)
                   (equal *fn2-cns-scope-own-consumers* *fn2-authority-scope-own-consumers*)))
(defmacro fn2-auth-read-events ()
 '(progn
   ;; Whether the core serves authority (the profile gives fn2-auth rows):
   ;; a profile serving none has no principals directory and no grants, and
   ;; its appends are not governed by them (as its genesis names none).
   (defun fn2-auth-served (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (posp (fn2-machine-connection-count *fn2-auth-admission-ordinal* fn2-core)))
   ;; The row's read row: the authority block is the last A read rows
   ;; (machines-b's fn2-b-read-rows counts :authority), A the kind's capacity.
   (defun fn2-auth-read-row (slot fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (let ((a (fn2-machine-connection-count *fn2-auth-admission-ordinal* fn2-core))
           (r (stobj-let ((fn2-reads (fn2-core-reads fn2-core))) (r) (fn2-reads-rows fn2-reads) r)))
       (if (and (natp slot) (natp a) (natp r) (< slot a) (<= a r))
           (mv :ok (+ (- r a) slot))
         (mv :bounds 0))))
   (in-theory (disable fn2-auth-read-row))
   ;; whether read row X holds a lookup of SID in progress: its keys are then
   ;; written already, and writing a key would end it (fn2-rd-key)
   (defun fn2-auth-lookup-live (x sid fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (stobj-let ((fn2-reads (fn2-core-reads fn2-core))) (live)
       (and (fn2-reads-wfp fn2-reads) (natp x) (natp (fn2-reads-rows fn2-reads)) (< x (fn2-reads-rows fn2-reads))
            (equal (fn2-reads-op x fn2-reads) *fn2-read-op-lookup*) (equal (fn2-reads-sid x fn2-reads) sid))
       live))
   (in-theory (disable fn2-auth-lookup-live))
   ;; One step of an exact lookup on read row X whose keys are set: :more
   ;; continues; a final answer releases the row. (mv code) with the entry
   ;; still delivered on :ok (the caller reads it, then releases).
   (defun fn2-auth-lookup-step (x sid budget fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (mv-let (lc fn2-core) (fn2-read-lookup x sid budget fn2-core)
       (if (member-eq lc '(:more :ok))
           (mv lc fn2-core)
         (mv-let (rc fn2-core) (fn2-read-release x fn2-core)
           (declare (ignore rc))
           (mv (if (eq lc :absent) :absent :state) fn2-core)))))
   (fn2-core-preserves fn2-auth-lookup-step (x sid budget fn2-core) :position 1 :rows nil)
   (in-theory (disable fn2-auth-lookup-step))
   ;; The delivered entry's integer fields F1 F2 F3 (0 for a field index of
   ;; 0 when fewer are wanted), then the row released: (mv code v1 v2 v3).
   (defun fn2-auth-take-values (x f1 f2 f3 fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (mv-let (c1 v1) (fn2-read-value x f1 fn2-core)
       (mv-let (c2 v2) (if (natp f2) (fn2-read-value x f2 fn2-core) (mv :ok 0))
         (mv-let (c3 v3) (if (natp f3) (fn2-read-value x f3 fn2-core) (mv :ok 0))
           (mv-let (rc fn2-core) (fn2-read-release x fn2-core)
             (declare (ignore rc))
             (if (and (eq c1 :ok) (eq c2 :ok) (eq c3 :ok))
                 (mv :ok (nfix v1) (nfix v2) (nfix v3) fn2-core)
               (mv :state 0 0 0 fn2-core)))))))
   (fn2-core-preserves fn2-auth-take-values (x f1 f2 f3 fn2-core) :position 4 :rows nil)
   (in-theory (disable fn2-auth-take-values))
   ;; principal's authority head (0: none yet): (mv code head), :more to continue
   (defun fn2-auth-find-head (x principal budget fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (mv-let (kc fn2-core) (if (fn2-auth-lookup-live x *fn2-authority-head-sid* fn2-core) (mv :ok fn2-core)
                             (fn2-read-key x :lo *fn2-authority-head-entry-field-principal* (nfix principal) fn2-core))
       (if (not (eq kc :ok)) (mv :state 0 fn2-core)
         (mv-let (lc fn2-core) (fn2-auth-lookup-step x *fn2-authority-head-sid* budget fn2-core)
           (cond ((eq lc :ok)
                  (mv-let (c v a b fn2-core) (fn2-auth-take-values x *fn2-authority-head-entry-field-grant* nil nil fn2-core)
                    (declare (ignore a b)) (mv c v fn2-core)))
                 ((eq lc :absent) (mv :ok 0 fn2-core))
                 (t (mv lc 0 fn2-core)))))))
   (fn2-core-preserves fn2-auth-find-head (x principal budget fn2-core) :position 2 :rows nil)
   (in-theory (disable fn2-auth-find-head))
   ;; the current grant of (grantee right scope target), 0 when none: (mv code grant)
   (defun fn2-auth-find-current (x grantee right scope target budget fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (mv-let (k0 k1 k2 k3 fn2-core)
       (if (fn2-auth-lookup-live x *fn2-grant-current-sid* fn2-core) (mv :ok :ok :ok :ok fn2-core)
         (mv-let (k0 fn2-core) (fn2-read-key x :lo *fn2-grant-current-entry-field-grantee* (nfix grantee) fn2-core)
           (mv-let (k1 fn2-core) (fn2-read-key x :lo *fn2-grant-current-entry-field-right* (nfix right) fn2-core)
             (mv-let (k2 fn2-core) (fn2-read-key x :lo *fn2-grant-current-entry-field-scope* (nfix scope) fn2-core)
               (mv-let (k3 fn2-core) (fn2-read-key x :lo *fn2-grant-current-entry-field-target* (nfix target) fn2-core)
                 (mv k0 k1 k2 k3 fn2-core))))))
             (if (not (and (eq k0 :ok) (eq k1 :ok) (eq k2 :ok) (eq k3 :ok))) (mv :state 0 fn2-core)
               (mv-let (lc fn2-core) (fn2-auth-lookup-step x *fn2-grant-current-sid* budget fn2-core)
                 (cond ((eq lc :ok)
                        (mv-let (c v a b fn2-core) (fn2-auth-take-values x *fn2-grant-current-entry-field-grant* nil nil fn2-core)
                          (declare (ignore a b)) (mv c v fn2-core)))
                       ((eq lc :absent) (mv :ok 0 fn2-core))
                       (t (mv lc 0 fn2-core)))))))
   (fn2-core-preserves fn2-auth-find-current (x grantee right scope target budget fn2-core) :position 2 :rows nil)
   (in-theory (disable fn2-auth-find-current))
   ;; the immutable grant row GRANT: (mv code grantor enabled previous)
   (defun fn2-auth-find-grant (x grant budget fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (mv-let (kc fn2-core) (if (fn2-auth-lookup-live x *fn2-grants-sid* fn2-core) (mv :ok fn2-core)
                             (fn2-read-key x :lo *fn2-grants-entry-field-grant* (nfix grant) fn2-core))
       (if (not (eq kc :ok)) (mv :state 0 0 0 fn2-core)
         (mv-let (lc fn2-core) (fn2-auth-lookup-step x *fn2-grants-sid* budget fn2-core)
           (if (eq lc :ok)
               (fn2-auth-take-values x *fn2-grants-entry-field-grantor* *fn2-grants-entry-field-enabled*
                                     *fn2-grants-entry-field-previous* fn2-core)
             (mv (if (eq lc :absent) :state lc) 0 0 0 fn2-core))))))
   (fn2-core-preserves fn2-auth-find-grant (x grant budget fn2-core) :position 4 :rows nil)
   (in-theory (disable fn2-auth-find-grant))
   ;; ---- the consumer surface's check (step 3c; AUTHORITY-20261105 section 4) ----
   ;; A consumer request's read row: the cns block, the C read rows below the
   ;; authority block (machines-b's fn2-b-read-rows: 2X cursor rows, then C,
   ;; then A), row R - A - C + S for request slot S.
   (defun fn2-cns-read-row (cns fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (if (not (eq (fn2-cns-snapshot-read-code cns fn2-core) :ok)) (mv :bounds 0)
       (let ((s (fn2-machine-slot cns fn2-core))
             (a (fn2-machine-connection-count *fn2-auth-admission-ordinal* fn2-core))
             (c (fn2-machine-connection-count *fn2-cns-admission-ordinal* fn2-core))
             (r (stobj-let ((fn2-reads (fn2-core-reads fn2-core))) (r) (fn2-reads-rows fn2-reads) r)))
         (if (and (natp s) (natp a) (natp c) (natp r) (< s c) (<= (+ a c) r))
             (mv :ok (+ (- r (+ a c)) s))
           (mv :bounds 0)))))
   (in-theory (disable fn2-cns-read-row))
   ;; The effective durable principal of consumer request CNS of generation
   ;; GEN (section 1): its control connection's, the owner's or the one it
   ;; bound (0 when the profile has no owner principal); :state when the
   ;; request or its connection has moved on.
   (defun fn2-cns-principal (cns gen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (if (not (and (eq (fn2-cns-snapshot-read-code cns fn2-core) :ok)
                   (equal (fn2-machine-generation cns fn2-core) gen)))
         (mv :state 0)
       (let ((ctl (fn2-cns-row-ctl cns fn2-core)))
         (if (and (eq (fn2-ctl-snapshot-read-code ctl fn2-core) :ok)
                  (equal (fn2-machine-generation ctl fn2-core) (fn2-cns-row-ctl-gen cns fn2-core)))
             (mv :ok (nfix (fn2-ctl-row-principal ctl fn2-core)))
           (mv :state 0)))))
   (defthm fn2-cns-principal-natp (natp (mv-nth 1 (fn2-cns-principal cns gen fn2-core))) :rule-classes :type-prescription)
   (in-theory (disable fn2-cns-principal))
   ;; Whether CNS's control connection administers (an owner connection not
   ;; yet bound acts under the owner's bootstrap authority, section 1).
   (defun fn2-cns-admin-p (cns fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (and (eq (fn2-cns-snapshot-read-code cns fn2-core) :ok)
          (let ((ctl (fn2-cns-row-ctl cns fn2-core)))
            (and (eq (fn2-ctl-snapshot-read-code ctl fn2-core) :ok)
                 (equal (fn2-ctl-row-admin ctl fn2-core) 1)))))
   (in-theory (disable fn2-cns-admin-p))
   ;; (fn2-cns-authority-allows cns gen right scope target xstep head grant budget):
   ;; whether consumer request CNS's durable principal holds (RIGHT SCOPE
   ;; TARGET) now, in bounded steps on the request's own read row, each a
   ;; resumable exact lookup of the published grants. XSTEP 0 is a fresh
   ;; decision (the row's lookup a previous request left is released first);
   ;; XSTEP K > 0 runs step K - 1: 0 reads the principal's authority head, 1
   ;; its current grant, 2 that grant's immutable row, 3 the head again.
   ;; :more carries (xstep head grant) to the next call. :ok when the grant
   ;; is enabled and the head did not move across the decision (a moved head
   ;; decides again from step 0: the answer is linearized at the final read
   ;; of the head), with GRANT 0 when no grant governs (an administering
   ;; connection: the owner's bootstrap authority; or a core serving none); :access when no current
   ;; grant, or a disabled one, allows it; :state when the request moved on.
   (defun fn2-cns-authority-allows (cns gen right scope target xstep head grant budget fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (b* (((unless (fn2-auth-served fn2-core)) (mv :ok 0 0 0 fn2-core))
          ((mv pc pid) (fn2-cns-principal cns gen fn2-core))
          ((unless (eq pc :ok)) (mv :state 0 0 0 fn2-core))
          ((when (fn2-cns-admin-p cns fn2-core)) (mv :ok 0 0 0 fn2-core))
          ((unless (posp pid)) (mv :access 0 0 0 fn2-core))
          ((unless (and (unsigned-byte-p 60 pid) (unsigned-byte-p 60 right) (unsigned-byte-p 60 scope)
                        (unsigned-byte-p 60 target) (unsigned-byte-p 60 head) (unsigned-byte-p 60 grant)))
           (mv :state 0 0 0 fn2-core))
          ((mv xc x) (fn2-cns-read-row cns fn2-core))
          ((unless (eq xc :ok)) (mv :state 0 0 0 fn2-core))
          ((mv & fn2-core) (if (posp xstep) (mv :ok fn2-core) (fn2-read-release x fn2-core)))
          (step (if (posp xstep) (- xstep 1) 0)))
       (cond
        ((equal step 0)
         (mv-let (c h fn2-core) (fn2-auth-find-head x pid budget fn2-core)
           (cond ((not (eq c :ok)) (mv (if (eq c :more) :more :state) 1 0 0 fn2-core))
                 ((and (posp h) (unsigned-byte-p 60 h)) (mv :more 2 h 0 fn2-core))
                 (t (mv :access 1 0 0 fn2-core)))))
        ((equal step 1)
         (mv-let (c g fn2-core) (fn2-auth-find-current x pid right scope target budget fn2-core)
           (cond ((not (eq c :ok)) (mv (if (eq c :more) :more :state) 2 head 0 fn2-core))
                 ((and (posp g) (unsigned-byte-p 60 g)) (mv :more 3 head g fn2-core))
                 (t (mv :access 2 head 0 fn2-core)))))
        ((equal step 2)
         (mv-let (c grantor en prev fn2-core) (fn2-auth-find-grant x grant budget fn2-core)
           (declare (ignore grantor prev))
           (cond ((not (eq c :ok)) (mv (if (eq c :more) :more :state) 3 head grant fn2-core))
                 ((equal en 1) (mv :more 4 head grant fn2-core))
                 (t (mv :access 3 head grant fn2-core)))))
        (t
         (mv-let (c h fn2-core) (fn2-auth-find-head x pid budget fn2-core)
           (cond ((not (eq c :ok)) (mv (if (eq c :more) :more :state) 4 head grant fn2-core))
                 ((equal h head) (mv :ok 4 head grant fn2-core))
                 (t (mv :more 1 0 0 fn2-core))))))))
   (fn2-core-preserves fn2-cns-authority-allows (cns gen right scope target xstep head grant budget fn2-core) :position 4 :rows nil)
   (defthm fn2-cns-authority-allows-types
     (and (natp (mv-nth 1 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core)))
          (< (mv-nth 1 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core)) 5)
          (unsigned-byte-p 60 (mv-nth 2 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core)))
          (unsigned-byte-p 60 (mv-nth 3 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core))))
     :hints (("Goal" :in-theory (enable fn2-cns-authority-allows))))
   (defthm fn2-cns-authority-allows-natps
     (and (natp (mv-nth 1 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core))) (natp (mv-nth 2 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core))) (natp (mv-nth 3 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core))))
     :rule-classes ((:type-prescription :corollary (natp (mv-nth 1 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core))))
                    (:type-prescription :corollary (natp (mv-nth 2 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core))))
                    (:type-prescription :corollary (natp (mv-nth 3 (fn2-cns-authority-allows cns gen right scope target xstep head grant budget fn2-core)))))
     :hints (("Goal" :in-theory (disable fn2-cns-authority-allows-types) :use fn2-cns-authority-allows-types)))
   (in-theory (disable fn2-cns-authority-allows))
   ))

(defmacro fn2-auth-op-events ()
 '(progn
   (defun fn2-auth-release-ks (slot gen okind oslot ogen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (fn2-core-release slot gen okind oslot ogen fn2-core))
   (fn2-core-preserves fn2-auth-release-ks (slot gen okind oslot ogen fn2-core) :position 1 :rows nil)
   (in-theory (disable fn2-auth-release-ks))
   (defun fn2-auth-successor (slot fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (let ((c (fn2-machine-connection-count *fn2-txn-admission-ordinal* fn2-core)))
       (if (and (natp slot) (natp c) (unsigned-byte-p 32 (+ c slot)))
           (mv :ok (+ c slot))
         (mv :bounds 0))))
   (in-theory (disable fn2-auth-successor))
   ;; the payload [FPOS + 2, FPOS + FLEN) after the carrier's command and kind octets
   (defun fn2-auth-decode-name (op sx slot gen off end okind oslot ogen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-fc (fn2-core-fc fn2-core))
                 (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
       (code noff nlen fn2-fields)
       (mv-let (c b0) (fn2-idc-stripe sx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
         (let ((base (+ b0 *fn2-auth-request-at*)))
           (if (not (and (eq c :ok) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
                         (<= (+ base 16) (fn2-fields-rows fn2-fields))))
               (mv :frame 0 0 fn2-fields)
             (mv-let (dc next fn2-fields)
               (if (equal op *fn2-auth-op-create*)
                   (fn2-authority-req-principal-create-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool)
                 (if (equal op *fn2-auth-op-stream*)
                     (fn2-authority-req-stream-resolve-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool)
                   (fn2-authority-req-principal-bind-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
               (if (not (and (fn2-fields-wfp fn2-fields) (natp (fn2-fields-rows fn2-fields)) (< (+ base 1) (fn2-fields-rows fn2-fields))))
                   (mv :frame 0 0 fn2-fields)
                 (let ((len (fn2-fields-ref-len (+ base 1) fn2-fields)) (noff (fn2-fields-ref-off (+ base 1) fn2-fields)))
                   (if (and (eq dc :ok) (equal next end) (equal (fn2-fields-ref-slot (+ base 1) fn2-fields) slot)
                            (posp len) (<= len (if (equal op *fn2-auth-op-stream*) *fn2-groups-name-max* 64)) (unsigned-byte-p 32 noff))
                       (mv :ok noff len fn2-fields)
                     (mv :frame 0 0 fn2-fields))))))))
       (mv code (nfix noff) (nfix nlen) fn2-core)))
   (fn2-core-preserves fn2-auth-decode-name (op sx slot gen off end okind oslot ogen fn2-core)
     :position 3 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-auth-decode-name))
   (defun fn2-auth-decode (fpos flen sx slot gen okind oslot ogen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (if (not (and (natp fpos) (natp flen) (< 0 flen) (unsigned-byte-p 32 (+ fpos flen))))
         (mv :frame 0 0 0 fn2-core)
       (mv-let (rc op)
         (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (rc op)
           (fn2-pool-read slot gen fpos okind oslot ogen fn2-pool) (mv rc op))
         (cond ((not (and (eq rc :ok) (natp op))) (mv :frame 0 0 0 fn2-core))
               ((or (equal op *fn2-auth-op-create*) (equal op *fn2-auth-op-bind*) (equal op *fn2-auth-op-stream*))
                (mv-let (code noff nlen fn2-core)
                  (fn2-auth-decode-name op sx slot gen fpos (+ fpos flen) okind oslot ogen fn2-core)
                  (mv code op noff nlen fn2-core)))
               ((or (equal op *fn2-auth-op-set*) (equal op *fn2-auth-op-get*)) (mv :ok op 0 0 fn2-core))
               (t (mv :frame 0 0 0 fn2-core))))))
   (fn2-core-preserves fn2-auth-decode (fpos flen sx slot gen okind oslot ogen fn2-core)
     :position 4 :rows nil)
   (in-theory (disable fn2-auth-decode))
   (defun fn2-auth-claim (fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (let ((skip (stobj-let ((fn2-control (fn2-core-control fn2-core))) (o) (fn2-control-owner-account fn2-control) o)))
       (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
         (code slot id fn2-accounts)
         (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts))
             (mv-let (code slot fn2-accounts) (fn2-account-claim skip fn2-accounts)
               (mv code slot (if (eq code :ok) (fn2-account-principal-id slot fn2-accounts) 0) fn2-accounts))
           (mv :exhausted 0 0 fn2-accounts))
         (mv code (nfix slot) (nfix id) fn2-core))))
   (fn2-core-preserves fn2-auth-claim (fn2-core) :position 3 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-auth-claim))
   (defun fn2-auth-unclaim (slot fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (let ((skip (stobj-let ((fn2-control (fn2-core-control fn2-core))) (o) (fn2-control-owner-account fn2-control) o)))
       (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
         (fn2-accounts)
         (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts))
             (fn2-account-unclaim slot skip fn2-accounts)
           fn2-accounts)
         fn2-core)))
   (fn2-core-preserves fn2-auth-unclaim (slot fn2-core) :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-auth-unclaim))
   ;; ---- grants (step 2) ----
   ;; grant-set's and grant-get's fields: (mv code grantee right scope target enabled ehead op);
   ;; OP is the operation identity, 1 to 8 octets big-endian below 2^60 (as an append's).
   (defun fn2-auth-decode-grant (op sx slot gen off end okind oslot ogen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-fc (fn2-core-fc fn2-core))
                 (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
       (code ge rt sc tg en eh opid fn2-fields)
       (mv-let (c b0) (fn2-idc-stripe sx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
         (let ((base (+ b0 *fn2-auth-request-at*)))
           (if (not (and (eq c :ok) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
                         (<= (+ base 16) (fn2-fields-rows fn2-fields))))
               (mv :frame 0 0 0 0 0 0 0 fn2-fields)
             (mv-let (dc next fn2-fields)
               (if (equal op *fn2-auth-op-set*)
                   (fn2-authority-req-grant-set-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool)
                 (fn2-authority-req-grant-get-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
               (if (not (and (eq dc :ok) (equal next end) (fn2-fields-wfp fn2-fields)
                             (natp (fn2-fields-rows fn2-fields)) (<= (+ base 16) (fn2-fields-rows fn2-fields))))
                   (mv :frame 0 0 0 0 0 0 0 fn2-fields)
                 (let ((ge (fn2-fields-value (+ base 1) fn2-fields)) (rt (fn2-fields-value (+ base 2) fn2-fields))
                       (sc (fn2-fields-value (+ base 3) fn2-fields)) (tg (fn2-fields-value (+ base 4) fn2-fields)))
                   (if (not (equal op *fn2-auth-op-set*))
                       (mv :ok ge rt sc tg 0 0 0 fn2-fields)
                     (let ((en (fn2-fields-value (+ base 5) fn2-fields)) (eh (fn2-fields-value (+ base 6) fn2-fields))
                           (ooff (fn2-fields-ref-off (+ base 7) fn2-fields)) (olen (fn2-fields-ref-len (+ base 7) fn2-fields)))
                       (if (not (and (equal (fn2-fields-ref-slot (+ base 7) fn2-fields) slot)
                                     (posp olen) (<= olen 8) (natp ooff)))
                           (mv :frame 0 0 0 0 0 0 0 fn2-fields)
                         (mv-let (ok v) (fn2-cns-read-be 0 olen ooff 0 slot gen okind oslot ogen fn2-pool)
                           (if (and ok (posp v) (unsigned-byte-p 60 v))
                               (mv :ok ge rt sc tg en eh v fn2-fields)
                             (mv :frame 0 0 0 0 0 0 0 fn2-fields))))))))))))
       (mv code (nfix ge) (nfix rt) (nfix sc) (nfix tg) (nfix en) (nfix eh) (nfix opid) fn2-core)))
   (fn2-core-preserves fn2-auth-decode-grant (op sx slot gen off end okind oslot ogen fn2-core)
     :position 8 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-auth-decode-grant))
   ;; operation OP's recorded outcome for PRINCIPAL: (mv code event same),
   ;; SAME whether its request identity equals the one at the key range's
   ;; [0, 32) (the recorded one is copied to [32, 64) and compared).
   (defun fn2-auth-same-octets (n i j slot gen okind oslot ogen fn2-pool)
     (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp i) (natp j)) :measure (nfix n)))
     (if (zp n) t
       (mv-let (c1 a) (fn2-pool-read slot gen i okind oslot ogen fn2-pool)
         (mv-let (c2 b) (fn2-pool-read slot gen j okind oslot ogen fn2-pool)
           (and (eq c1 :ok) (eq c2 :ok) (equal a b)
                (fn2-auth-same-octets (- n 1) (+ 1 (nfix i)) (+ 1 (nfix j)) slot gen okind oslot ogen fn2-pool))))))
   (defun fn2-auth-find-outcome (x principal op kslot kgen budget okind oslot ogen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (mv-let (k0 k1 fn2-core)
       (if (fn2-auth-lookup-live x *fn2-txn-outcome-sid* fn2-core) (mv :ok :ok fn2-core)
         (mv-let (k0 fn2-core) (fn2-read-key x :lo *fn2-outcome-entry-field-principal* (nfix principal) fn2-core)
           (mv-let (k1 fn2-core) (fn2-read-key x :lo *fn2-outcome-entry-field-operation* (nfix op) fn2-core)
             (mv k0 k1 fn2-core))))
         (if (not (and (eq k0 :ok) (eq k1 :ok))) (mv :state 0 nil fn2-core)
           (mv-let (lc fn2-core) (fn2-auth-lookup-step x *fn2-txn-outcome-sid* budget fn2-core)
             (if (not (eq lc :ok))
                 (mv lc 0 nil fn2-core)
               (mv-let (oc copied left fn2-core)
                 (fn2-read-octets x *fn2-outcome-entry-field-request* 0 32 kslot kgen 32 okind oslot ogen fn2-core)
                 (declare (ignore left))
                 (mv-let (vc ev a b fn2-core) (fn2-auth-take-values x *fn2-outcome-entry-field-event* nil nil fn2-core)
                   (declare (ignore a b))
                   (let ((same (and (eq oc :ok) (equal copied 32)
                                    (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (s)
                                      (and (fn2-pool-wfp fn2-pool) (fn2-auth-same-octets 32 0 32 kslot kgen okind oslot ogen fn2-pool)) s))))
                     (mv (if (eq vc :ok) :ok :state) ev same fn2-core)))))))))
   (fn2-core-preserves fn2-auth-find-outcome (x principal op kslot kgen budget okind oslot ogen fn2-core) :position 3 :rows nil)
   (in-theory (disable fn2-auth-find-outcome))
   ;; grant-set's request identity: 32 octets at the key range's [0, 32), the
   ;; verb then grantee, right, scope, target, enabled and expected-head (the
   ;; ids 8 octets big-endian), zero-padded: injective in the request (an
   ;; exact identity where the outcome schema has room for a digest).
   (defun fn2-auth-put-be (k v i slot gen okind oslot ogen fn2-pool)
     (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp k) (natp i)) :measure (nfix k)))
     (if (zp k) (mv :ok fn2-pool)
       (mv-let (c fn2-pool)
         (fn2-pool-write slot gen i (mod (ash (nfix v) (- (* 8 (- (nfix k) 1)))) 256) okind oslot ogen fn2-pool)
         (if (eq c :ok) (fn2-auth-put-be (- k 1) v (+ 1 (nfix i)) slot gen okind oslot ogen fn2-pool) (mv c fn2-pool)))))
   (fn2-pool-preserves fn2-auth-put-be (k v i slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
   (in-theory (disable fn2-auth-put-be))
   (defun fn2-auth-put-identity (ge rt sc tg en eh slot gen okind oslot ogen fn2-pool)
     (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
     (b* (((mv c fn2-pool) (fn2-pool-reset slot gen okind oslot ogen fn2-pool))
          ((unless (eq c :ok)) (mv c fn2-pool))
          ((mv c fn2-pool) (fn2-auth-put-be 1 *fn2-auth-op-set* 0 slot gen okind oslot ogen fn2-pool))
          ((unless (eq c :ok)) (mv c fn2-pool))
          ((mv c fn2-pool) (fn2-auth-put-be 8 ge 1 slot gen okind oslot ogen fn2-pool))
          ((unless (eq c :ok)) (mv c fn2-pool))
          ((mv c fn2-pool) (fn2-auth-put-be 1 rt 9 slot gen okind oslot ogen fn2-pool))
          ((unless (eq c :ok)) (mv c fn2-pool))
          ((mv c fn2-pool) (fn2-auth-put-be 1 sc 10 slot gen okind oslot ogen fn2-pool))
          ((unless (eq c :ok)) (mv c fn2-pool))
          ((mv c fn2-pool) (fn2-auth-put-be 8 tg 11 slot gen okind oslot ogen fn2-pool))
          ((unless (eq c :ok)) (mv c fn2-pool))
          ((mv c fn2-pool) (fn2-auth-put-be 1 en 19 slot gen okind oslot ogen fn2-pool))
          ((unless (eq c :ok)) (mv c fn2-pool))
          ((mv c fn2-pool) (fn2-auth-put-be 8 eh 20 slot gen okind oslot ogen fn2-pool))
          ((unless (eq c :ok)) (mv c fn2-pool)))
       (fn2-auth-put-be 4 0 28 slot gen okind oslot ogen fn2-pool)))
   (fn2-pool-preserves fn2-auth-put-identity (ge rt sc tg en eh slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
   (in-theory (disable fn2-auth-put-identity))
   (defun fn2-auth-identity (ge rt sc tg en eh kslot kgen okind oslot ogen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (c fn2-pool)
       (if (fn2-pool-wfp fn2-pool)
           (fn2-auth-put-identity ge rt sc tg en eh kslot kgen okind oslot ogen fn2-pool)
         (mv :state fn2-pool))
       (mv c fn2-core)))
   (fn2-core-preserves fn2-auth-identity (ge rt sc tg en eh kslot kgen okind oslot ogen fn2-core) :position 1 :rows nil
     :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-auth-identity))
   ;; grant-set's four writes declared in one transaction (:ready resolves
   ;; them a bounded step at a time): the immutable grant row,
   ;; the current pointer's and the grantee's head's fold events (each
   ;; carrying the member's own event)
   ;; and the operation outcome naming the request identity in the key range.
   (defun fn2-auth-put-grant (sx grantor ge rt sc tg en prev op kslot kgen okind oslot ogen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (b* (((mv & fn2-core) (fn2-successor-release sx fn2-core))
          ((mv c fn2-core)
           (fn2-grants-put sx 0 (grant :event 0) (grantor grantor) (grantee ge) (right rt) (scope sc)
                           (target tg) (enabled en) (previous prev) fn2-core))
          ((unless (eq c :ok)) (mv :state fn2-core))
          ((mv c fn2-core)
           (fn2-grant-current-grant sx 1 (grantee ge) (right rt) (scope sc) (target tg) (g :event 0) fn2-core))
          ((unless (eq c :ok)) (mv :state fn2-core))
          ((mv c fn2-core) (fn2-authority-head-grant sx 2 (principal ge) (g :event 0) fn2-core))
          ((unless (eq c :ok)) (mv :state fn2-core))
          ((mv c fn2-core)
           (fn2-outcome-put sx 3 (principal grantor) (operation op) (request kslot kgen 0)
                            (outcome *fn2-auth-outcome-code-accepted*) (event :event 0)
                            :owner (okind oslot ogen) fn2-core))
          ((unless (eq c :ok)) (mv :state fn2-core)))
       (mv :ok fn2-core)))
   (fn2-core-preserves fn2-auth-put-grant (sx grantor ge rt sc tg en prev op kslot kgen okind oslot ogen fn2-core)
     :position 1 :rows nil)
   (in-theory (disable fn2-auth-put-grant))
   ;; a durable principal id names a live account incarnation (created or genesis'):
   (defun fn2-auth-known (p fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (let ((slot (floor (nfix p) 4294967296)))
       (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core))) (k)
         (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts)
              (posp p) (< slot (fn2-accounts-rows fn2-accounts))
              (equal (fn2-account-principal-id slot fn2-accounts) p)
              (not (equal (fn2-accounts-state slot fn2-accounts) *fn2-account-state-free*)))
         (if k :ok :absent))))
   (in-theory (disable fn2-auth-known))
   ;; principal-create's one write. The name is copied from the connection's
   ;; frame (owner OKIND OSLOT OGEN) to the start of the row's key range
   ;; KSLOT/KGEN (owner DK DS DG, the row), and the write names it there.
   (defun fn2-auth-put-create (sx pid slot gen noff nlen kslot kgen dk ds dg okind oslot ogen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (mv-let (cc fn2-core)
       (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (cc fn2-pool)
         (if (and (fn2-pool-wfp fn2-pool) (natp nlen) (<= nlen 64) (natp noff))
             (fn2-rd-copy nlen slot gen noff okind oslot ogen kslot kgen 0 dk ds dg fn2-pool)
           (mv :bounds fn2-pool))
         (mv cc fn2-core))
       (if (not (eq cc :ok))
           (mv :state fn2-core)
         (mv-let (rc0 fn2-core) (fn2-successor-release sx fn2-core)
           (declare (ignore rc0))
           (mv-let (c0 fn2-core)
             (fn2-principals-put-row sx 0 kslot kgen 0 nlen :value pid dk ds dg fn2-core)
             (if (not (eq c0 :ok))
                 (mv :state fn2-core)
               (mv :ok fn2-core)))))))
   (fn2-core-preserves fn2-auth-put-create (sx pid slot gen noff nlen kslot kgen dk ds dg okind oslot ogen fn2-core)
     :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-auth-put-create))
   ;; :ready's one write, per verb (grant-set's names the key range under the
   ;; row's ownership DK DS DG; principal-create's copies the name from the
   ;; frame, owner OKIND OSLOT OGEN)
   (defun fn2-auth-put-write (op sx pid slot gen noff nlen kslot kgen dk ds dg grantor ge rt sc tg en prev gop
                                 okind oslot ogen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (if (equal op *fn2-auth-op-set*)
         (fn2-auth-put-grant sx grantor ge rt sc tg en prev gop kslot kgen dk ds dg fn2-core)
       (fn2-auth-put-create sx pid slot gen noff nlen kslot kgen dk ds dg okind oslot ogen fn2-core)))
   (fn2-core-preserves fn2-auth-put-write (op sx pid slot gen noff nlen kslot kgen dk ds dg grantor ge rt sc tg en prev gop
                                           okind oslot ogen fn2-core) :position 1 :rows nil)
   (in-theory (disable fn2-auth-put-write))
   ;; an accepted principal-bind: the connection acts as P and administers nothing
   (defun fn2-auth-bind-ctl (ctl ctl-gen op outcome p fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (if (and (equal op *fn2-auth-op-bind*) (equal (nfix outcome) *fn2-auth-outcome-accepted*) (unsigned-byte-p 60 p)
              (eq (fn2-ctl-snapshot-read-code ctl fn2-core) :ok)
              (equal (fn2-machine-generation ctl fn2-core) ctl-gen))
         (fn2-ctl-put-core ctl (principal p) (admin 0))
       fn2-core))
   (fn2-core-preserves fn2-auth-bind-ctl (ctl ctl-gen op outcome p fn2-core) :rows nil)
   (in-theory (disable fn2-auth-bind-ctl))
   ;; the sealed kind 30 reply after the request in CTL's range, its fields
   ;; the connection's format stripe and its hasher the connection's row
   ;; (as fn2-cns-post-reply's kind 28); the connection sends [K, K+TOTAL)
   (defun fn2-auth-post-reply (ctl ctl-gen request op outcome reason p head grant grantor enabled previous found slot gen fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                     :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
     (if (not (and (eq (fn2-ctl-snapshot-read-code ctl fn2-core) :ok)
                   (equal (fn2-machine-generation ctl fn2-core) ctl-gen)
                   (equal (fn2-ctl-row-request ctl fn2-core) request)
                   (equal (fn2-ctl-row-phase ctl fn2-core) *fn2-ctl-state-waiting*)))
         (mv :dropped fn2-core)
       (mv-let (rc row) (fn2-ctl-fc-row ctl fn2-core)
         (if (not (eq rc :ok)) (mv :fault fn2-core)
           (mv-let (code k total fn2-core)
             (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-digests (fn2-core-digests fn2-core))
                         (fn2-b3 (fn2-core-b3 fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
               (code k total fn2-fields fn2-digests fn2-b3 fn2-pool)
               (fn2-auth-seal-reply-pool op outcome reason p head grant grantor enabled previous found (* 128 row) row slot gen
                                         *fn2-ctl-kind* ctl ctl-gen fn2-fields fn2-digests fn2-b3 fn2-pool)
               (mv code k total fn2-core))
             (if (not (and (eq code :ok) (unsigned-byte-p 32 k) (unsigned-byte-p 32 (+ k total)) (< 0 total)))
                 (mv :fault fn2-core)
               (let* ((fn2-core (fn2-machine-write-tx-off ctl k fn2-core))
                      (fn2-core (fn2-machine-write-tx-len ctl (+ k total) fn2-core)))
                 (mv :ok fn2-core))))))))
   (fn2-core-preserves fn2-auth-post-reply (ctl ctl-gen request op outcome reason p head grant grantor enabled previous found slot gen fn2-core)
     :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-auth-post-reply))))

;; ---------------------------------------------------------------------------
;; fn2-auth: one authority request.
(defmachine-arms fn2-auth :declare
 :subarms
 ((answer :on-refusal ((:stop :machine-phase))
   (:do (rcode) (fn2-successor-release row-sx)
    :accept (:ok :state) :why "a committed or bound transaction's successor is already closed")
   (:do (pcode) (fn2-auth-post-reply row-ctl row-ctl-gen row-request row-opcode row-outcome row-reason
                                     (if (equal row-opcode *fn2-auth-op-stream*) row-gtarget row-pid)
                                     row-ahead row-grant row-grantor row-genabled row-previous row-gfound
                                     row-rx-slot row-rx-gen)
    :accept (:ok :dropped) :why "the control connection may have closed while the request ran")
   (:do () (fn2-auth-bind-ctl row-ctl row-ctl-gen row-opcode row-outcome row-pid))
   (:wake-row row-ctl)
   (:next :draining) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
  ;; a claimed slot whose principal was not created goes back
  (unclaim
   (:if (equal row-aslot 0)
        ((:goto answer))
        ((:do () (fn2-auth-unclaim row-aslot)) (:set (aslot 0)) (:goto answer))))
  (refuse
   (:set (outcome *fn2-auth-outcome-refused*))
   (:goto unclaim))
  (fault
   (:set (outcome *fn2-auth-outcome-fault*) (reason 0))
   (:goto unclaim))
  ;; grant-set and grant-get (opcodes 2, 3): the fields, then the checks the
  ;; ruling orders (access, scope, the grantee's existence), then the reads
  (grant
   (:do (gcode ge rt sc tg en eh opid)
        (fn2-auth-decode-grant row-opcode row-sx row-rx-slot row-rx-gen row-fpos (+ row-fpos row-flen)
                               :okind *fn2-ctl-kind* :oslot row-ctl :ogen row-ctl-gen)
    :case (((:frame) (:set (reason *fn2-auth-reason-frame*)) (:goto refuse))))
   (:set (grantee ge) (gright rt) (gscope sc) (gtarget tg) (enabled en) (ehead eh) (gop opid))
   (:cond ((not (or (equal row-admin 1) (and (equal row-opcode *fn2-auth-op-get*) (equal row-principal ge))))
           (:set (reason *fn2-auth-reason-access*)) (:goto refuse))
          ((not (if (equal rt *fn2-authority-right-consume*)
                    (and (equal sc *fn2-authority-scope-own-consumers*) (equal tg 0))
                  (and (equal sc *fn2-authority-scope-stream*) (not (equal tg 0)))))
           (:set (reason *fn2-auth-reason-scope*)) (:goto refuse))
          (t (:do (kcode) (fn2-auth-known ge) :accept (:ok :absent) :why "an unknown grantee is a refusal")
             (:cond ((eq kcode :absent) (:set (reason *fn2-auth-reason-unknown-principal*)) (:goto refuse))
                    ((equal row-opcode *fn2-auth-op-get*)
                     (:do (fcode fr) (fn2-read-frontier) :case (((:state) (:goto fault))))
                     (:set (cut fr) (gstep 0))
                     (:next :get) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                    (t (:do (icode) (fn2-auth-identity ge rt sc tg en eh row-ks-slot row-ks-gen)
                        :case ((:otherwise (:goto fault))))
                       (:next :outcome) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))))
 :arms
 ((:free (:idle))
  (:decode :on-refusal ((:stop :machine-phase))
   (:do (xcode sx) (fn2-auth-successor row-slot) :case (((:bounds) (:stop :machine-phase))))
   (:do (rxcode x) (fn2-auth-read-row row-slot) :case (((:bounds) (:stop :machine-phase))))
   (:set (sx sx) (xrow x))
   (:do (dcode op noff nlen) (fn2-auth-decode row-fpos row-flen sx row-rx-slot row-rx-gen
                                              :okind *fn2-ctl-kind* :oslot row-ctl :ogen row-ctl-gen)
    :case (((:frame) (:set (reason *fn2-auth-reason-frame*)) (:goto refuse))))
   (:set (opcode op) (noff noff) (nlen nlen))
   (:cond ((or (equal op *fn2-auth-op-set*) (equal op *fn2-auth-op-get*)) (:goto grant))
          ((not (equal row-admin 1)) (:set (reason *fn2-auth-reason-access*)) (:goto refuse))
          ((and (equal op *fn2-auth-op-bind*) (equal row-worked 1)) (:set (reason *fn2-auth-reason-access*)) (:goto refuse))
          (t (:next :lookup) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))))
  ;; the exact name lookup, resumable (:more is one bounded source)
  (:lookup :on-refusal ((:stop :machine-phase))
   (:if (equal row-opcode *fn2-auth-op-stream*)
        ((:do (lcode target) (fn2-group-lookup row-sx row-rx-slot row-rx-gen row-noff row-nlen :budget 4096
                                              :okind *fn2-ctl-kind* :oslot row-ctl :ogen row-ctl-gen)
          :accept ()
          :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                 ((:ok) (:set (gtarget target) (outcome *fn2-auth-outcome-accepted*)) (:goto answer))
                 ((:absent) (:set (reason *fn2-auth-reason-unknown-stream*)) (:goto refuse))
                 (:otherwise (:goto fault)))))
        ((:do (lcode lpid) (fn2-principal-lookup row-sx row-rx-slot row-rx-gen row-noff row-nlen :budget 4096
                                           :okind *fn2-ctl-kind* :oslot row-ctl :ogen row-ctl-gen)
    :accept ()
    :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
           ((:ok) (:if (equal row-opcode *fn2-auth-op-bind*)
                       ((:set (pid lpid)) (:next :bhead) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                       ((:set (pid lpid) (outcome *fn2-auth-outcome-accepted*)) (:goto unclaim))))
           ((:absent)
            (:cond ((equal row-opcode *fn2-auth-op-bind*)
                    (:set (reason *fn2-auth-reason-unknown-principal*)) (:goto refuse))
                   ((equal row-aslot 0) (:next :allocate) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                   (t (:next :ready) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))))))
  (:allocate :on-refusal ((:stop :machine-phase))
   (:do (ccode cslot cpid) (fn2-auth-claim)
    :case (((:exhausted) (:set (reason *fn2-auth-reason-meter*)) (:goto refuse))))
   (:set (aslot cslot) (pid cpid))
   (:next :ready) (:charge :steps *fn2-work-transition* :runnable t))
  ;; grant-set: the retry lookup first (the ruling: before the expected head)
  (:outcome :on-refusal ((:stop :machine-phase))
   (:do (ocode oev same) (fn2-auth-find-outcome row-xrow row-principal row-gop row-ks-slot row-ks-gen 4096)
    :accept ()
    :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
           ((:absent) (:next :head) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
           ((:ok) (:if same
                       ((:set (grant oev) (ahead oev) (outcome *fn2-auth-outcome-accepted*)) (:goto answer))
                       ((:set (reason *fn2-auth-reason-operation-reused*)) (:goto refuse))))
           (:otherwise (:goto fault)))))
  ;; the grantee's head against the request's expected head
  (:head :on-refusal ((:stop :machine-phase))
   (:do (hcode h) (fn2-auth-find-head row-xrow row-grantee 4096)
    :accept ()
    :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
           ((:ok) (:if (equal h row-ehead)
                       ((:set (ahead h)) (:next :ready) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                       ((:set (reason *fn2-auth-reason-stale-revision*)) (:goto refuse))))
           (:otherwise (:goto fault)))))
  ;; principal-bind's answer carries the bound principal's head
  (:bhead :on-refusal ((:stop :machine-phase))
   (:do (hcode h) (fn2-auth-find-head row-xrow row-pid 4096)
    :accept ()
    :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
           ((:ok) (:set (ahead h) (outcome *fn2-auth-outcome-accepted*)) (:goto answer))
           (:otherwise (:goto fault)))))
  ;; grant-get: current pointer (GSTEP 0), head (1), the immutable row (2),
  ;; at one committed cut: the frontier at the start (CUT) and at the end
  ;; agree, else the reads start again
  (:get :on-refusal ((:stop :machine-phase))
   (:cond
    ((equal row-gstep 0)
     (:do (ccode g) (fn2-auth-find-current row-xrow row-grantee row-gright row-gscope row-gtarget 4096)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:ok) (:set (grant g) (gfound (if (equal g 0) 0 1)) (gstep 1))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             (:otherwise (:goto fault)))))
    ((equal row-gstep 1)
     (:do (hcode h) (fn2-auth-find-head row-xrow row-grantee 4096)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:ok) (:set (ahead h) (gstep (if (equal row-gfound 1) 2 3)))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             (:otherwise (:goto fault)))))
    ((equal row-gstep 2)
     (:do (rcode gr en pv) (fn2-auth-find-grant row-xrow row-grant 4096)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:ok) (:set (grantor gr) (genabled en) (previous pv) (gstep 3))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             (:otherwise (:goto fault)))))
    ;; the cut held (no publication between the first read and the last), or the reads start again
    (t
     (:do (fcode fr) (fn2-read-frontier) :case (((:state) (:goto fault))))
     (:if (equal fr row-cut)
          ((:set (outcome *fn2-auth-outcome-accepted*)) (:goto answer))
          ((:set (gstep 0) (cut fr)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))))))
  ;; declare and stage the write against the tip, emit it into the workspace,
  ;; admit it to B's batch, bind on :ok (fn2-txn's :ready, one transaction)
  (:ready :on-refusal ((:stop :machine-phase))
   (:if (eq (fn2-commit-posture) :draining)
        ((:goto fault))
        ((:if (not (eq (fn2-machine-pool-capacity-read-code row-ws-slot) :ok))
              ((:stop :machine-phase))
              ((:let cap (fn2-machine-pool-capacity row-ws-slot))
               (:cond
                ;; declare the write once (WSTEP 0), then resolve its
                ;; reads a bounded step per run (a fold's key row, read in
                ;; the installed runs), then stage
                ((equal row-wstep 0)
                 (:do (wcode) (fn2-auth-put-write row-opcode row-sx row-pid row-rx-slot row-rx-gen row-noff row-nlen
                                                  row-ks-slot row-ks-gen *fn2-auth-kind* id row-generation
                                                  row-principal row-grantee row-gright row-gscope row-gtarget
                                                  row-enabled row-ahead row-gop
                                                  :okind *fn2-ctl-kind* :oslot row-ctl :ogen row-ctl-gen)
                  :case (((:state) (:goto fault))))
                 (:set (wstep 1))
                 (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                ((equal row-wstep 1)
                 (:do (rvcode) (fn2-successor-resolve row-sx 4096)
                  :accept ()
                  :case (((:ok) (:set (wstep 2)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                         ((:more) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                         (:otherwise (:goto fault)))))
                (t
               (:do (scode i) (fn2-successor-stage row-sx)
                :accept ()
                :case (((:ok)
                        (:do (ecode elen) (fn2-successor-emit row-sx row-ws-slot row-ws-gen 0 cap)
                         :accept ()
                         :case (((:ok)
                                 (:do (acode b ev) (fn2-commit-admit-txn row-ws-slot row-ws-gen elen)
                                  :effects ((:acquire (:batch-membership)))
                                  :accept ()
                                  :case (((:ok)
                                          (:if (and (unsigned-byte-p 60 b) (unsigned-byte-p 60 ev))
                                               ((:do (bcode) (fn2-successor-bind row-sx b ev))
                                                (:next :batched) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                                               ((:stop :machine-phase))))
                                         ((:exhausted) (:park :batch-membership :steps *fn2-work-transition*))
                                         ((:admission) (:goto fault)))))
                                ((:room) (:goto fault)))))
                       ((:full) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                       ;; the tip moved, or another create of this name won: look again
                       ((:stale :duplicate)
                        (:do (rcode) (fn2-successor-release row-sx))
                        (:set (wstep 0))
                        (:next (:if (equal row-opcode *fn2-auth-op-set*) :outcome :lookup))
                        (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                       ((:refused :capacity) (:goto fault)))))))))))
  (:batched :on-refusal ((:stop :machine-phase))
   (:do (tcode tbatch tevent tout) (fn2-commit-take)
    :effects ((:release (:batch-membership)))
    :accept ()
    :case (((:pending) (:charge :steps *fn2-work-empty* :runnable t))
           ((:ok)
            (:cond ((equal tout *fn2-commit-outcome-accepted*)
                    (:set (outcome *fn2-auth-outcome-accepted*) (aslot 0)
                          (grant (if (equal row-opcode *fn2-auth-op-set*) tevent row-grant))
                          (ahead (if (equal row-opcode *fn2-auth-op-set*) tevent row-ahead)))
                    (:goto answer))
                   ((equal tout *fn2-commit-outcome-uncertain*)
                    (:set (outcome *fn2-auth-outcome-uncertain*) (reason *fn2-auth-reason-persistence*) (aslot 0))
                    (:goto answer))
                   (t (:goto fault)))))))
  (:draining
   (:do (rcode) (fn2-core-release row-ws-slot row-ws-gen) :effects ((:release (:tx-range)))
    :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)"
    :case ((:otherwise (:stop :pool-release :steps *fn2-work-state*))))
   (:do (kcode) (fn2-auth-release-ks row-ks-slot row-ks-gen)
    :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)"
    :case ((:otherwise (:stop :pool-release :steps *fn2-work-state*))))
   (:let next (fn2-machine-free-head *fn2-auth-admission-ordinal*))
   (:let retire (>= row-generation (fn2-machine-gen-limit)))
   (:set (generation (if retire row-generation (+ 1 row-generation)))
         (ctl *fn2-none*) (ctl-gen 0) (rx-slot *fn2-none*) (rx-gen 0) (ws-slot *fn2-none*) (ws-gen 0)
         (ks-slot *fn2-none*) (ks-gen 0)
         (next-free next) (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free))
   (:do () (fn2-machine-reclaim-fn2-auth id retire))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle)))
 :observes ())

;; ---------------------------------------------------------------------------
;; The append check (section 4; step 3b): a transaction asks it once per
;; destination group at :prepare, through its own exact lookup (fn2-xl-step
;; on its successor stripe: the published grants), and its answer's head is
;; the member's read dependency, which stage validates against the immediate
;; predecessor before commit eligibility (machines-c-stage's :depend slot).

;; One call of TX's exact lookup in SID of the integer key (K0..K3, the
;; first NK of them) at its stripe's query rows: (mv code value txns cursors
;; paths fields), :ok with integer field VFIELD of the entry found, :absent,
;; :more (call again with the same key), else a refusal. The key rows are
;; written on every call, so a continuation finds them.
(defun fn2-auth-xl (sid nk k0 k1 k2 k3 vfield tx budget b0
                    fn2-succ-txns fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                    fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-xl-step fn2-fields-rows)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-id-decides-wfp fn2-id-decides) (fn2-overlays-wfp fn2-overlays)
                    (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp fn2-run-installed)
                    (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache)
                    (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (< tx (fn2-id-decides-rows fn2-id-decides))
                    (natp b0) (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields)) (natp budget) (<= budget 4096)
                    (natp sid) (natp vfield) (< vfield *fn2-run-entry-rows*) (member nk '(1 4))
                    (unsigned-byte-p 60 k0) (unsigned-byte-p 60 k1) (unsigned-byte-p 60 k2) (unsigned-byte-p 60 k3)))
       (mv :bounds 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (member (fn2-id-decides-phase tx fn2-id-decides) (list *fn2-id-decide-phase-idle* *fn2-id-decide-phase-done*))
                    (not (equal (fn2-succ-txns-rstate tx fn2-succ-txns) *fn2-succ-resolve-look*))))
       (mv :state 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      (qb (+ b0 *fn2-idc-eb*)) (rb (+ b0 *fn2-idc-rb*))
      (fn2-fields (fn2-fields-put qb (value k0) (ref-len 0)))
      (fn2-fields (if (equal nk 4)
                      (let* ((fn2-fields (fn2-fields-put (+ qb 1) (value k1) (ref-len 0)))
                             (fn2-fields (fn2-fields-put (+ qb 2) (value k2) (ref-len 0))))
                        (fn2-fields-put (+ qb 3) (value k3) (ref-len 0)))
                    fn2-fields))
      ((mv code erow fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-xl-step tx sid budget qb rb *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen*
                    fn2-succ-txns fn2-overlays fn2-overlay-index
                    fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      (row (+ erow vfield))
      ((unless (< row (fn2-fields-rows fn2-fields))) (mv :bounds 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
  (mv :ok (nfix (fn2-fields-value row fn2-fields)) fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
(fn2-idc-fn-shape fn2-auth-xl (sid nk k0 k1 k2 k3 vfield tx budget b0
                               fn2-succ-txns fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                               fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-succ-txns 2) (fn2-run-cursors 3) (fn2-run-paths 4) (fn2-fields 5))
 (fn2-succ-txns fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) t
 (fn2-xl-step fn2-id-decides-phase fn2-succ-txns-rstate))

;; The transaction's slot for its read dependency (txn.lisp's
;; *fn2-txn-slot-depend*, asserted equal where both are included).
(defconst *fn2-auth-depend-slot* 20)

;; The definitions over the served core (expanded in assembly-callbacks-d-txn
;; before fn2-txn-events; txn.lisp holds their defcosts).
(defmacro fn2-authority-allows-events ()
 '(progn
   (defun fn2-auth-xl-core (tx sid nk k0 k1 k2 k3 vfield budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
                (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-run-cursors (fn2-core-run-cursors fn2-core))
                (fn2-run-paths (fn2-core-run-paths fn2-core)) (fn2-run-cache (fn2-core-run-cache fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code v fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)
     (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
      (if (eq c :ok)
          (fn2-auth-xl sid nk k0 k1 k2 k3 vfield tx budget b0 fn2-succ-txns fn2-id-decides fn2-overlays
                       fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
        (mv c 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
     (mv code (nfix v) fn2-core)))
   (fn2-core-preserves fn2-auth-xl-core (tx sid nk k0 k1 k2 k3 vfield budget fn2-core)
    :position 2 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-auth-xl-core))
   ;; The effective durable principal of a transaction (section 1): a
   ;; consumer request's (CONN a fn2-cns row of generation CONN-GEN) is its
   ;; control connection's, the owner's or the one it bound; a connection's
   ;; is its account slot PSLOT's (D7's id; an NNTP reader's the anonymous
   ;; principal). :state when the request or its connection has moved on.
   (defun fn2-txn-principal (conn conn-gen pslot fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (if (eq (fn2-cns-snapshot-read-code conn fn2-core) :ok)
        (mv-let (c pid) (fn2-cns-principal conn conn-gen fn2-core)
          (if (and (eq c :ok) (posp pid)) (mv :ok pid) (mv :state 0)))
      (fn2-principal-of-slot pslot fn2-core)))
   (defthm fn2-txn-principal-natp (natp (mv-nth 1 (fn2-txn-principal conn conn-gen pslot fn2-core)))
    :hints (("Goal" :in-theory (enable fn2-principal-of-slot))) :rule-classes :type-prescription)
   (in-theory (disable fn2-txn-principal))
   ;; (fn2-authority-allows tx pid right target step head grant budget):
   ;; whether durable principal PID holds RIGHT on stream TARGET
   ;; for transaction TX, in bounded steps: STEP 0 reads the principal's
   ;; authority head, 1 its current grant of (RIGHT :stream TARGET), 2 that
   ;; grant's immutable row; :more carries (step head grant) to the next
   ;; call. :ok (step head grant): GRANT is enabled under HEAD, or GRANT 0
   ;; when no grant governs (the owner's bootstrap authority, or a core
   ;; serving no authority); :access when no current grant, or a disabled
   ;; one, allows it. The head is read first, so a decision any later grant
   ;; event changes fails the dependency on HEAD at stage.
   (defun fn2-authority-allows (tx pid right target step head grant budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* (((unless (fn2-auth-served fn2-core)) (mv :ok 0 0 0 fn2-core))
         ((unless (and (posp pid) (unsigned-byte-p 60 pid) (unsigned-byte-p 60 target)
                       (unsigned-byte-p 60 right) (unsigned-byte-p 60 grant) (unsigned-byte-p 60 head)))
          (mv :state 0 0 0 fn2-core))
         ((mv oc owner) (fn2-ctl-owner-principal fn2-core))
         ((when (and (eq oc :ok) (equal pid owner))) (mv :ok 0 0 0 fn2-core)))
     (cond
      ((equal step 0)
       (mv-let (c h fn2-core)
         (fn2-auth-xl-core tx *fn2-authority-head-sid* 1 pid 0 0 0 *fn2-authority-head-entry-field-grant* budget fn2-core)
        (case c
         (:ok (if (and (posp h) (unsigned-byte-p 60 h)) (mv :more 1 h 0 fn2-core) (mv :access 0 0 0 fn2-core)))
         (:absent (mv :access 0 0 0 fn2-core))
         (:more (mv :more 0 0 0 fn2-core))
         (otherwise (mv :state 0 0 0 fn2-core)))))
      ((equal step 1)
       (mv-let (c g fn2-core)
         (fn2-auth-xl-core tx *fn2-grant-current-sid* 4 pid right *fn2-authority-scope-stream* target
                           *fn2-grant-current-entry-field-grant* budget fn2-core)
        (case c
         (:ok (if (and (posp g) (unsigned-byte-p 60 g)) (mv :more 2 head g fn2-core) (mv :access 1 head 0 fn2-core)))
         (:absent (mv :access 1 head 0 fn2-core))
         (:more (mv :more 1 head 0 fn2-core))
         (otherwise (mv :state 1 head 0 fn2-core)))))
      (t
       (mv-let (c en fn2-core)
         (fn2-auth-xl-core tx *fn2-grants-sid* 1 grant 0 0 0 *fn2-grants-entry-field-enabled* budget fn2-core)
        (case c
         (:ok (if (equal en 1) (mv :ok 2 head grant fn2-core) (mv :access 2 head grant fn2-core)))
         (:more (mv :more 2 head grant fn2-core))
         (otherwise (mv :state 2 head grant fn2-core))))))))
   (fn2-core-preserves fn2-authority-allows (tx pid right target step head grant budget fn2-core) :position 4 :rows nil)
   (defthm fn2-authority-allows-types
    (and (natp (mv-nth 1 (fn2-authority-allows tx pid right target step head grant budget fn2-core)))
         (< (mv-nth 1 (fn2-authority-allows tx pid right target step head grant budget fn2-core)) 3)
         (unsigned-byte-p 60 (mv-nth 2 (fn2-authority-allows tx pid right target step head grant budget fn2-core)))
         (unsigned-byte-p 60 (mv-nth 3 (fn2-authority-allows tx pid right target step head grant budget fn2-core))))
    :hints (("Goal" :in-theory (enable fn2-authority-allows))))
   (defthm fn2-authority-allows-natps
    (and (natp (mv-nth 1 (fn2-authority-allows tx pid right target step head grant budget fn2-core)))
         (natp (mv-nth 2 (fn2-authority-allows tx pid right target step head grant budget fn2-core)))
         (natp (mv-nth 3 (fn2-authority-allows tx pid right target step head grant budget fn2-core))))
    :rule-classes ((:type-prescription :corollary (natp (mv-nth 1 (fn2-authority-allows tx pid right target step head grant budget fn2-core))))
                   (:type-prescription :corollary (natp (mv-nth 2 (fn2-authority-allows tx pid right target step head grant budget fn2-core))))
                   (:type-prescription :corollary (natp (mv-nth 3 (fn2-authority-allows tx pid right target step head grant budget fn2-core)))))
    :hints (("Goal" :in-theory (disable fn2-authority-allows-types) :use fn2-authority-allows-types)))
   (in-theory (disable fn2-authority-allows))
   ;; The member's read dependency on the authority it decided under: when
   ;; GRANT governed the decision (nonzero) and none is declared yet, TX's
   ;; :depend slot on fn2-authority-head (PID -> HEAD). The first
   ;; decision's head is kept: a later group read under a newer head makes
   ;; the tip differ from it, so stage answers :changed.
   (defun fn2-authority-depend (tx pid grant head fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* (((unless (and (posp grant) (posp head) (unsigned-byte-p 60 head))) (mv :ok fn2-core))
         ((unless (and (posp pid) (unsigned-byte-p 60 pid))) (mv :state fn2-core))
         (declared (stobj-let ((fn2-succ-slots (fn2-core-succ-slots fn2-core))) (d)
                     (let ((s (+ (* (nfix tx) *fn2-succ-slots*) *fn2-auth-depend-slot*)))
                      (and (fn2-succ-slots-wfp fn2-succ-slots) (natp (fn2-succ-slots-rows fn2-succ-slots))
                           (< s (fn2-succ-slots-rows fn2-succ-slots))
                           (not (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*))))
                     d))
         ((when declared) (mv :ok fn2-core))
         ((mv c fn2-core) (fn2-successor-put tx *fn2-auth-depend-slot* *fn2-authority-head-sid* :depend fn2-core))
         ((unless (eq c :ok)) (mv :state fn2-core))
         ((mv c fn2-core) (fn2-successor-arg tx *fn2-auth-depend-slot* *fn2-authority-head-entry-field-principal* :value pid fn2-core))
         ((unless (eq c :ok)) (mv :state fn2-core))
         ((mv c fn2-core) (fn2-successor-arg tx *fn2-auth-depend-slot* *fn2-authority-head-entry-field-grant* :value head fn2-core)))
     (mv (if (eq c :ok) :ok :state) fn2-core)))
   (fn2-core-preserves fn2-authority-depend (tx pid grant head fn2-core) :position 1 :rows nil)
   (in-theory (disable fn2-authority-depend))))

(defmacro fn2-auth-events ()
 '(progn
   (fn2-auth-op-events)
   (defmachine-arms fn2-auth)
   (defmachine-run fn2-auth)))
