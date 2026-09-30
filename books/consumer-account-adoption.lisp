; Shared account authority interpreter for persisted Store rows. Stages do
; not authorize. The owner must fund each transition before allocation and
; install the fence's completed auth/index root atomically with its CP state.
; No host activation until those owner/context and restart joins are proved.
(in-package "ACL2")
(include-book "consumer-authority-codec")
(include-book "consumer-account-index")
(include-book "auth-credentials")

; Only already established <=64-octet login paths reach the actual producer.
; Ordered-map completeness/bounds are carried, not rechecked here.
(defun fn-caa-name-lessp (a b)
  (declare (xargs :guard t :measure (len a)))
  (if (consp a)
      (and (consp b)
           (or (< (nfix (car a)) (nfix (car b)))
               (and (equal (car a) (car b))
                    (fn-caa-name-lessp (cdr a) (cdr b)))))
    (consp b)))

(defun fn-caa-root (policy index credentials)
  (declare (xargs :guard t))
  (list :account-root policy index credentials))

(defun fn-caa-root-auth-config (root)
  (declare (xargs :guard t))
  (let ((policy (nfix (fn-cp-nth 1 root))))
    (fn-auth-make-config (logbitp 0 policy) (logbitp 1 policy)
                         (logbitp 2 policy) (fn-cp-nth 3 root))))

(defun fn-caa-row-credential (op)
  (declare (xargs :guard t))
  (fn-auth-make-cred
   (fn-cp-nth 3 op) (fn-cp-nth 5 op)
   (fn-authsec-verifier (fn-cp-nth 6 op) (fn-cp-nth 7 op)
                        (fn-cp-nth 8 op) (fn-cp-nth 9 op))
   (equal (fn-cp-nth 10 op) 1)))

; These octets record the exact adopted authentication descriptor. Encoding
; is bounded by the credential field grammar, not by total account count.
(defun fn-caa-row-descriptor (op)
  (declare (xargs :guard t))
  (fn-cac-fields-encode
   (list (fn-cp-nth 5 op) (fn-cp-nth 6 op) (fn-cp-nth 7 op)
         (fn-cp-nth 8 op) (fn-cp-nth 9 op) (fn-cp-nth 10 op))
   '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag)))

(defun fn-caa-preparation (phase old reversed forward root namespace watermark)
  (declare (xargs :guard t))
  (list :account-preparation phase old reversed forward root namespace watermark))

(defun fn-caa-pending (candidate base count watermark prep last digest ready)
  (declare (xargs :guard t))
  (list :adoption candidate base count watermark prep last digest ready))

(defun fn-caa-authority-pending (a pending)
  (declare (xargs :guard t))
  (list :authority (fn-cp-nth 1 a) (fn-cp-nth 2 a)
        (fn-cp-nth 3 a) (fn-cp-nth 4 a) pending))

(defun fn-caa-success (s a event root)
  (declare (xargs :guard t))
  (list :ok
        (fn-cp-state-carry (fn-cp-nth 1 s) (fn-cp-nth 2 s)
                           (1+ (nfix (fn-cp-nth 1 event)))
                           (fn-cp-nth 4 s) (fn-cp-nth 5 s) a)
        root))

; Restore/rollover keeps prior account tokens literal; a newly born account
; uses the current CP incarnation and this persisted begin coordinate.
; Prefix equality is not a nonreuse proof: actual lifecycle invariants are
; required before serving a newly installed authority namespace.
(defun fn-caa-namespace (s a event)
  (declare (xargs :guard t))
  (let ((old (fn-cp-nth 3 a)) (incarnation (fn-cp-nth 2 s)))
    (if (and (fn-cp-authority-namespacep old)
             (equal (ec-call (take 32 old)) incarnation))
        old
      (fn-cp-authority-namespace incarnation (fn-cp-nth 2 event)))))

(defun fn-caa-begin (s a event op)
  (declare (xargs :guard t))
  (let ((namespace (fn-caa-namespace s a event)))
    (if (or (fn-cp-nth 5 a)
            (not (equal (fn-cp-nth 2 op) (fn-cp-nth 1 a)))
            (not (equal (fn-cp-nth 3 op) (fn-cp-nth 2 a)))
            (not (fn-cp-authority-namespacep namespace)))
        (list :refused :authority-begin)
      (let ((pending
             (fn-caa-pending
              (fn-cp-nth 1 op) (fn-cp-nth 1 a) 0 (fn-cp-nth 2 a)
              (fn-caa-preparation :merge (fn-cp-nth 4 a) nil nil
                                  (fn-caa-root (fn-cp-nth 4 op) nil nil)
                                  namespace (fn-cp-nth 2 a))
              nil (fn-sha256 (fn-cac-encode event)) nil)))
        (fn-caa-success s (fn-caa-authority-pending a pending) event nil)))))

(defun fn-caa-matching-pendingp (a op)
  (declare (xargs :guard t))
  (let ((p (fn-cp-nth 5 a)))
    (and p (equal (fn-cp-nth 1 op) (fn-cp-nth 1 p))
         (equal (fn-cp-nth 2 op) (fn-cp-nth 2 p))
         (equal (fn-cp-nth 2 p) (fn-cp-nth 1 a)))))

; One selected row, one persistent bounded login-path update and one bounded
; hash-chain step. No traversal/copy of old or accumulated account tables.
(defun fn-caa-stage-indexed (s a event row index old-rest)
  (declare (xargs :guard t))
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (root (fn-cp-nth 5 prep))
         (watermark (max (nfix (fn-cp-nth 4 p))
                          (1+ (nfix (fn-cp-nth 2 event)))))
         (root1 (fn-caa-root
                 (fn-cp-nth 1 root)
                 index
                 (fn-cp-nth 3 root)))
         (prep1 (fn-caa-preparation
                 :merge old-rest (cons row (fn-cp-nth 3 prep)) nil root1
                 (fn-cp-nth 6 prep) watermark))
         (pending
          (fn-caa-pending
           (fn-cp-nth 1 p) (fn-cp-nth 2 p) (1+ (nfix (fn-cp-nth 3 p)))
           watermark prep1 (fn-cp-nth 1 row)
           (fn-sha256 (ec-call (binary-append (fn-cp-nth 7 p) (fn-cac-encode event)))) nil)))
    (fn-caa-success s (fn-caa-authority-pending a pending) event nil)))

(defun fn-caa-stage-selected (s a event row credential old-rest)
  (declare (xargs :guard t))
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (root (fn-cp-nth 5 prep)))
    (fn-caa-stage-indexed
     s a event row
     (fn-cai-put-octets (fn-cp-nth 1 row)
                        (list :account-binding row credential)
                        (fn-cp-nth 2 root))
     old-rest)))

(defun fn-caa-row-plan (a event op)
  (declare (xargs :guard t))
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
         (name (fn-cp-nth 3 op)) (last (fn-cp-nth 6 p))
         (same (and head (equal name (fn-cp-nth 1 head))))
         (retained (and same (fn-cp-nth 3 head)))
         (coordinate (if retained
                         (fn-cp-creation-coordinate (fn-cp-nth 2 head))
                       (fn-cp-nth 2 event)))
         (credential (fn-caa-row-credential op)))
    (if (or (not (eq (fn-cp-nth 1 prep) :merge))
            (and last (not (fn-caa-name-lessp last name)))
            (and head (fn-caa-name-lessp (fn-cp-nth 1 head) name))
            (not (equal (fn-cp-nth 4 op) coordinate))
            (not (fn-auth-credp credential))
            (>= (nfix (fn-cp-nth 3 p)) *fn-cbor-max-uint*))
        (list :refused :authority-row)
      (list :stage
       (list :account name
             (if retained (fn-cp-nth 2 head)
               (fn-cp-account-creation (fn-cp-nth 6 prep) (fn-cp-nth 2 event)))
             t (fn-caa-row-descriptor op))
       credential (if same (if (consp old) (cdr old) nil) old) same))))

(defun fn-caa-row (s a event op)
  (declare (xargs :guard t))
  (let ((plan (fn-caa-row-plan a event op)))
    (if (eq (fn-cp-nth 0 plan) :stage)
        (fn-caa-stage-selected s a event (fn-cp-nth 1 plan)
                               (fn-cp-nth 2 plan) (fn-cp-nth 3 plan))
      plan)))

(defun fn-caa-tombstone-plan (a event op)
  (declare (ignore event) (xargs :guard t))
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
         (name (fn-cp-nth 3 op)) (last (fn-cp-nth 6 p)))
    (if (or (not (eq (fn-cp-nth 1 prep) :merge)) (not head)
            (not (equal name (fn-cp-nth 1 head)))
            (not (equal (fn-cp-nth 4 op)
                         (fn-cp-creation-coordinate (fn-cp-nth 2 head))))
            (and last (not (fn-caa-name-lessp last name)))
            (>= (nfix (fn-cp-nth 3 p)) *fn-cbor-max-uint*))
        (list :refused :authority-tombstone)
      (list :stage (list :account name (fn-cp-nth 2 head) nil nil) nil
       (if (consp old) (cdr old) nil) t))))

(defun fn-caa-tombstone (s a event op)
  (declare (xargs :guard t))
  (let ((plan (fn-caa-tombstone-plan a event op)))
    (if (eq (fn-cp-nth 0 plan) :stage)
        (fn-caa-stage-selected s a event (fn-cp-nth 1 plan)
                               (fn-cp-nth 2 plan) (fn-cp-nth 3 plan))
      plan)))

(defun fn-caa-count-digest-matchp (p op)
  (declare (xargs :guard t))
  (and (equal (fn-cp-nth 3 op) (fn-cp-nth 3 p))
       (equal (fn-cp-nth 4 op) (fn-cp-nth 7 p))))

(defun fn-caa-seal (s a event op)
  (declare (xargs :guard t))
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (reversed (fn-cp-nth 3 prep)))
    (if (or (not (eq (fn-cp-nth 1 prep) :merge))
            (fn-cp-nth 2 prep) (not (fn-caa-count-digest-matchp p op)))
        (list :refused :authority-seal)
      (let* ((ready (not (consp reversed)))
             (prep1 (fn-caa-preparation
                     (if ready :ready :reverse) nil reversed nil
                     (fn-cp-nth 5 prep) (fn-cp-nth 6 prep) (fn-cp-nth 7 prep)))
             (pending (fn-caa-pending
                       (fn-cp-nth 1 p) (fn-cp-nth 2 p) (fn-cp-nth 3 p)
                       (fn-cp-nth 4 p) prep1 (fn-cp-nth 6 p) (fn-cp-nth 7 p) ready)))
        (fn-caa-success s (fn-caa-authority-pending a pending) event nil)))))

; Persisted reversal is a single-cell transition, never an unbounded reverse
; at the final fence. The exact row binding supplies its already-validated
; credential; tombstones contribute no credential to the installed config.
(defun fn-caa-prepare (s a event)
  (declare (xargs :guard t))
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (reversed (fn-cp-nth 3 prep)) (head (if (consp reversed) (car reversed) nil))
         (root (fn-cp-nth 5 prep))
         (binding (fn-cai-get-octets (fn-cp-nth 1 head) (fn-cp-nth 2 root))))
    (if (or (not (eq (fn-cp-nth 1 prep) :reverse)) (not head)
            (not (equal (fn-cp-nth 1 binding) head)))
        (list :refused :authority-prepare)
      (let* ((rest (if (consp reversed) (cdr reversed) nil))
             (ready (not (consp rest)))
             (root1 (fn-caa-root
                     (fn-cp-nth 1 root) (fn-cp-nth 2 root)
                     (if (fn-cp-nth 3 head)
                         (cons (fn-cp-nth 2 binding) (fn-cp-nth 3 root))
                       (fn-cp-nth 3 root))))
             (prep1 (fn-caa-preparation
                     (if ready :ready :reverse) nil rest
                     (cons head (fn-cp-nth 4 prep)) root1
                     (fn-cp-nth 6 prep) (fn-cp-nth 7 prep)))
             (pending (fn-caa-pending
                       (fn-cp-nth 1 p) (fn-cp-nth 2 p) (fn-cp-nth 3 p)
                       (fn-cp-nth 4 p) prep1 (fn-cp-nth 6 p) (fn-cp-nth 7 p) ready)))
        (fn-caa-success s (fn-caa-authority-pending a pending) event nil)))))

(defun fn-caa-fence (s a event op)
  (declare (xargs :guard t))
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (revision (fn-cp-nth 1 a)))
    (if (or (not (fn-cp-nth 8 p))
            (not (eq (fn-cp-nth 1 prep) :ready))
            (not (fn-caa-count-digest-matchp p op))
            (not (fn-cp-uintp revision)) (>= revision *fn-cbor-max-uint*))
        (list :refused :authority-fence)
      (fn-caa-success
       s (list :authority (1+ revision) (fn-cp-nth 4 p)
               (fn-cp-nth 6 prep) (fn-cp-nth 4 prep) nil)
       event (fn-cp-nth 5 prep)))))

; On the served path s carries its established invariant. Only the external
; bounded event is recognized. The event's txid is its persisted coordinate,
; not an allocator expectation. A proposal invoking this interpreter is not
; authority until the prepared journal/frame is durably installed.
(defun fn-caa-step (s event)
  (declare (xargs :guard t))
  (let* ((a (fn-cp-nth 6 s)) (op (fn-cp-nth 4 event))
         (kind (fn-cp-nth 0 op)))
    (cond
     ((or (null s) (not (fn-cac-eventp event))
          (not (equal (fn-cp-nth 1 event) (fn-cp-nth 3 s)))
          (not (fn-cp-uintp (fn-cp-nth 1 event)))
          (>= (nfix (fn-cp-nth 1 event)) *fn-cbor-max-uint*)
          (not (fn-cp-uintp (fn-cp-nth 2 event)))
          (not (posp (fn-cp-nth 2 event)))
          (>= (nfix (fn-cp-nth 2 event)) *fn-cbor-max-uint*))
      (list :refused :authority-coordinate))
     ((eq kind :authority-begin) (fn-caa-begin s a event op))
     ((not (fn-caa-matching-pendingp a op)) (list :refused :authority-base))
     ((eq kind :authority-row) (fn-caa-row s a event op))
     ((eq kind :authority-tombstone) (fn-caa-tombstone s a event op))
     ((eq kind :authority-seal) (fn-caa-seal s a event op))
     ((eq kind :authority-prepare) (fn-caa-prepare s a event))
     ((eq kind :authority-fence) (fn-caa-fence s a event op))
     ((eq kind :authority-discard)
      (fn-caa-success s (fn-caa-authority-pending a nil) event nil))
     (t (list :refused :authority-operation)))))

(defun fn-caa-root-index (root)
  (declare (xargs :guard t))
  (fn-cp-nth 2 root))

(defun fn-caa-current-binding (login root)
  (declare (xargs :guard t))
  (let ((binding (fn-cai-lookup login *fn-auth-max-name-octets*
                               (fn-caa-root-index root))))
    (and (fn-cp-nth 3 (fn-cp-nth 1 binding)) binding)))

; This fold is for the authority substream only. The Store's cfg-first
; ordered fold must dispatch all other records/config changes and retain its
; latest installed root too. A dropped sequence is refused by fn-caa-step.
(defun fn-caa-replay (s root events)
  (declare (xargs :guard t :measure (len events)))
  (if (consp events)
      (let ((one (fn-caa-step s (car events))))
        (if (eq (car one) :ok)
            (fn-caa-replay (fn-cp-nth 1 one)
                           (if (fn-cp-nth 2 one) (fn-cp-nth 2 one) root)
                           (cdr events))
          one))
    (if (null events) (list :ok s root) (list :refused :authority-events))))

(defthm fn-caa-account-creation-is-48-octets
  (implies (and (fn-cp-authority-namespacep namespace) (fn-cp-uintp txid))
           (and (fn-cbor-octet-listp (fn-cp-account-creation namespace txid))
                (equal (len (fn-cp-account-creation namespace txid)) 48)))
  :hints (("Goal" :in-theory
           (e/d (fn-cp-account-creation fn-cp-authority-namespacep fn-cp-uintp)
                (fn-cbor-u64-bytes fn-cbor-octet-listp)))))

(defthm fn-caa-account-creation-records-stage-coordinate
  (implies (and (fn-cp-authority-namespacep namespace) (fn-cp-uintp txid))
           (equal (fn-cp-creation-coordinate (fn-cp-account-creation namespace txid))
                  txid))
  :hints (("Goal" :use ((:instance fn-cp-nthcdr-append-prefix
                                   (x namespace) (y (fn-cbor-u64-bytes txid)))
                        (:instance fn-cbor-u64-from-u64-bytes (n txid) (rest nil)))
           :in-theory
           (e/d (fn-cp-account-creation fn-cp-authority-namespacep
                  fn-cp-creation-coordinate fn-cp-uintp)
                (nthcdr fn-cbor-u64-bytes fn-cbor-u64-from
                 fn-cp-nthcdr-append-prefix fn-cbor-u64-from-u64-bytes)))))

(defun fn-caa-preserves-adoptedp (a one)
  (declare (xargs :guard t))
  (if (eq (fn-cp-nth 0 one) :ok)
      (let ((after (fn-cp-nth 6 (fn-cp-nth 1 one))))
        (and (equal (fn-cp-nth 1 after) (fn-cp-nth 1 a))
             (equal (fn-cp-nth 2 after) (fn-cp-nth 2 a))
             (equal (fn-cp-nth 3 after) (fn-cp-nth 3 a))
             (equal (fn-cp-nth 4 after) (fn-cp-nth 4 a))
             (null (fn-cp-nth 2 one))))
    t))

(local
 (defthm fn-caa-refusal-preserves-adopted
   (fn-caa-preserves-adoptedp a (list :refused reason))
   :hints (("Goal" :in-theory (enable fn-caa-preserves-adoptedp fn-cp-nth)))))

(local
 (defthm fn-caa-begin-preserves-adopted
   (fn-caa-preserves-adoptedp a (fn-caa-begin s a event op))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-begin fn-caa-preserves-adoptedp fn-caa-success
                   fn-caa-authority-pending fn-cp-state-carry fn-cp-nth)
                 (fn-cac-eventp fn-caa-namespace fn-caa-name-lessp fn-caa-row-credential fn-caa-row-descriptor fn-caa-preparation fn-caa-pending fn-caa-root fn-caa-matching-pendingp fn-caa-count-digest-matchp fn-cai-get-octets fn-cai-put-octets fn-sha256 fn-cp-account-creation fn-cp-uintp fn-auth-credp fn-cp-authority-namespacep fn-cp-creation-coordinate))))))

(local
 (defthm fn-caa-stage-selected-preserves-adopted
   (fn-caa-preserves-adoptedp a (fn-caa-stage-selected s a event row credential old-rest))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-stage-selected fn-caa-stage-indexed fn-caa-preserves-adoptedp fn-caa-success
                   fn-caa-authority-pending fn-cp-state-carry fn-cp-nth)
                 (fn-cac-eventp fn-caa-namespace fn-caa-name-lessp fn-caa-row-credential fn-caa-row-descriptor fn-caa-preparation fn-caa-pending fn-caa-root fn-caa-matching-pendingp fn-caa-count-digest-matchp fn-cai-get-octets fn-cai-put-octets fn-sha256 fn-cp-account-creation fn-cp-uintp fn-auth-credp fn-cp-authority-namespacep fn-cp-creation-coordinate))))))

(local
 (defthm fn-caa-seal-preserves-adopted
   (fn-caa-preserves-adoptedp a (fn-caa-seal s a event op))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-seal fn-caa-preserves-adoptedp fn-caa-success
                   fn-caa-authority-pending fn-cp-state-carry fn-cp-nth)
                 (fn-cac-eventp fn-caa-namespace fn-caa-name-lessp fn-caa-row-credential fn-caa-row-descriptor fn-caa-preparation fn-caa-pending fn-caa-root fn-caa-matching-pendingp fn-caa-count-digest-matchp fn-cai-get-octets fn-cai-put-octets fn-sha256 fn-cp-account-creation fn-cp-uintp fn-auth-credp fn-cp-authority-namespacep fn-cp-creation-coordinate))))))

(local
 (defthm fn-caa-prepare-preserves-adopted
   (fn-caa-preserves-adoptedp a (fn-caa-prepare s a event))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-prepare fn-caa-preserves-adoptedp fn-caa-success
                   fn-caa-authority-pending fn-cp-state-carry fn-cp-nth)
                 (fn-cac-eventp fn-caa-namespace fn-caa-name-lessp fn-caa-row-credential fn-caa-row-descriptor fn-caa-preparation fn-caa-pending fn-caa-root fn-caa-matching-pendingp fn-caa-count-digest-matchp fn-cai-get-octets fn-cai-put-octets fn-sha256 fn-cp-account-creation fn-cp-uintp fn-auth-credp fn-cp-authority-namespacep fn-cp-creation-coordinate))))))

(local
 (defthm fn-caa-row-preserves-adopted
   (fn-caa-preserves-adoptedp a (fn-caa-row s a event op))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-row fn-caa-row-plan fn-cp-nth)
                 (fn-caa-preserves-adoptedp fn-caa-stage-selected fn-cac-eventp fn-caa-namespace fn-caa-name-lessp fn-caa-row-credential fn-caa-row-descriptor fn-caa-preparation fn-caa-pending fn-caa-root fn-caa-matching-pendingp fn-caa-count-digest-matchp fn-cai-get-octets fn-cai-put-octets fn-sha256 fn-cp-account-creation fn-cp-uintp fn-auth-credp fn-cp-authority-namespacep fn-cp-creation-coordinate))))))

(local
 (defthm fn-caa-tombstone-preserves-adopted
   (fn-caa-preserves-adoptedp a (fn-caa-tombstone s a event op))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-tombstone fn-caa-tombstone-plan fn-cp-nth)
                 (fn-caa-preserves-adoptedp fn-caa-stage-selected fn-cac-eventp fn-caa-namespace fn-caa-name-lessp fn-caa-row-credential fn-caa-row-descriptor fn-caa-preparation fn-caa-pending fn-caa-root fn-caa-matching-pendingp fn-caa-count-digest-matchp fn-cai-get-octets fn-cai-put-octets fn-sha256 fn-cp-account-creation fn-cp-uintp fn-auth-credp fn-cp-authority-namespacep fn-cp-creation-coordinate))))))

; No pending root or provisional creation becomes adopted before the
; scalar fence. Local frame lemmas keep the full interpreter proof focused.
(defthm fn-caa-stages-preserve-current-authority
  (implies (and (eq (car (fn-caa-step s event)) :ok)
                (not (eq (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-fence)))
           (let ((before (fn-cp-nth 6 s))
                 (after (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-step s event)))))
             (and (equal (fn-cp-nth 1 after) (fn-cp-nth 1 before))
                  (equal (fn-cp-nth 2 after) (fn-cp-nth 2 before))
                  (equal (fn-cp-nth 3 after) (fn-cp-nth 3 before))
                  (equal (fn-cp-nth 4 after) (fn-cp-nth 4 before))
                  (null (fn-cp-nth 2 (fn-caa-step s event))))))
  :hints (("Goal"
           :use ((:instance fn-caa-begin-preserves-adopted (a (fn-cp-nth 6 s)) (op (fn-cp-nth 4 event)))
                 (:instance fn-caa-row-preserves-adopted (a (fn-cp-nth 6 s)) (op (fn-cp-nth 4 event)))
                 (:instance fn-caa-tombstone-preserves-adopted (a (fn-cp-nth 6 s)) (op (fn-cp-nth 4 event)))
                 (:instance fn-caa-seal-preserves-adopted (a (fn-cp-nth 6 s)) (op (fn-cp-nth 4 event)))
                 (:instance fn-caa-prepare-preserves-adopted (a (fn-cp-nth 6 s))))
           :in-theory (e/d (fn-caa-step fn-caa-preserves-adoptedp
                             fn-caa-success fn-caa-authority-pending fn-cp-state-carry fn-cp-nth)
                            (fn-caa-begin-preserves-adopted fn-caa-row-preserves-adopted
                             fn-caa-tombstone-preserves-adopted fn-caa-seal-preserves-adopted
                             fn-caa-prepare-preserves-adopted
                             fn-caa-begin fn-caa-row fn-caa-tombstone fn-caa-seal fn-caa-prepare
                             fn-cac-eventp fn-caa-namespace fn-caa-name-lessp fn-caa-row-credential fn-caa-row-descriptor fn-caa-preparation fn-caa-pending fn-caa-root fn-caa-matching-pendingp fn-caa-count-digest-matchp fn-cai-get-octets fn-cai-put-octets fn-sha256 fn-cp-account-creation fn-cp-uintp fn-auth-credp fn-cp-authority-namespacep fn-cp-creation-coordinate)))))

(in-theory (disable fn-caa-name-lessp fn-caa-root fn-caa-root-auth-config
                    fn-caa-row-credential fn-caa-row-descriptor fn-caa-preparation
                    fn-caa-pending fn-caa-authority-pending fn-caa-success
                    fn-caa-namespace fn-caa-begin fn-caa-matching-pendingp
                    fn-caa-stage-selected fn-caa-row fn-caa-tombstone
                    fn-caa-count-digest-matchp fn-caa-seal fn-caa-prepare
                    fn-caa-fence fn-caa-step fn-caa-root-index
                    fn-caa-current-binding fn-caa-replay fn-caa-preserves-adoptedp))
