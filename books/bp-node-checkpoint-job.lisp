; Actual BP checkpoint continuation under one charged source-action token.
; The captured CURRENT state stays frozen until source return and definite
; stage settlement. Its existing graph charge remains owned; this root borrows
; resident held/handoff lists, never an arena payload view or encoded copy.
; The shared-pool adapter must admit the actual runtime envelope BEFORE begin.
; A token's shape alone is not funding or authority.
(in-package "ACL2")
(include-book "bp-node-rotation-cursor")
(set-verify-guards-eagerness 0)

; Fixed fields: tag/token/epoch/generation/depth/capture/phase/tasks/count/
; frame-bound/offset/stage. COUNT is payload octets, never a whole encoding.
(defun fn-bpck-make
  (token epoch generation depth capture phase tasks count bound offset stage)
  (declare (xargs :guard t))
  (list :bp-checkpoint-job token epoch generation depth capture phase tasks
        count bound offset stage))

(defun fn-bpck-begin
  (token epoch generation depth held handoffs next-arrival covered bound)
  (declare (xargs :guard t))
  (let ((capture (fn-bpnr-checkpoint generation held handoffs (cons epoch 0)
                                    next-arrival covered)))
    (fn-bpck-make token epoch generation depth capture :census
                  (fn-bpnrc-begin capture depth) 0 bound 0 :none)))

; Only this scheduler budget is consumed. Exhaustion returns :census with
; the exact residual and accumulated count, never a truncated checkpoint.
(defun fn-bpck-census-step (job quantum)
  (declare (xargs :guard t))
  (if (not (equal (fn-bpn-nth 6 job) :census)) job
    (let* ((answer (fn-bpnrc-census-run (fn-bpn-nth 7 job) quantum
                                        (fn-bpn-nth 8 job)))
           (word (fn-bpn-nth 0 answer))
           (count (fn-bpn-nth 1 answer))
           (bound (fn-bpn-nth 9 job))
           (phase (cond ((equal word :yield) :census)
                        ((and (equal word :done) (posp count)
                              (<= count *fn-bpc-max-uint*)
                              (natp bound) (<= (+ 46 count) bound))
                         :stage-demand)
                        (t :refused))))
      (fn-bpck-make (fn-bpn-nth 1 job) (fn-bpn-nth 2 job)
                    (fn-bpn-nth 3 job) (fn-bpn-nth 4 job)
                    (fn-bpn-nth 5 job) phase (fn-bpn-nth 2 answer) count
                    bound (fn-bpn-nth 10 job) (fn-bpn-nth 11 job)))))

; Vector order is resident/disk/FD/worker/ID. The initial grant owns worker
; and ID through cleanup; grow reserves this exact staging demand before I/O.
; Frame = six magic/version/kind bytes + u64 length + payload + digest32.
(defun fn-bpck-stage-demand (job)
  (declare (xargs :guard t))
  (and (equal (fn-bpn-nth 6 job) :stage-demand)
       (natp (fn-bpn-nth 8 job))
       (list 0 (+ 46 (fn-bpn-nth 8 job)) 1 0 0)))

(defun fn-bpck-prefix (count)
  (declare (xargs :guard t))
  (append *fn-bpnr-head* (fn-bpc-u64-bytes (nfix count))))

; This observation is produced only by the live ledger grow adapter. It
; names this same token; another grant cannot open this job's stage.
(defun fn-bpck-stage-granted (job result)
  (declare (xargs :guard t))
  (if (not (and (equal (fn-bpn-nth 6 job) :stage-demand)
                (equal (fn-bpn-nth 0 result) :grown)
                (equal (fn-bpn-nth 1 result) (fn-bpn-nth 1 job)))) job
    (fn-bpck-make
     (fn-bpn-nth 1 job) (fn-bpn-nth 2 job) (fn-bpn-nth 3 job)
     (fn-bpn-nth 4 job) (fn-bpn-nth 5 job) :emit
     (cons (list :octets (fn-bpck-prefix (fn-bpn-nth 8 job)))
           (fn-bpnrc-begin (fn-bpn-nth 5 job) (fn-bpn-nth 4 job)))
     (fn-bpn-nth 8 job) (fn-bpn-nth 9 job) 0 :none)))

; One encoder turn returns at most nine prefix/payload octets. The native
; writer feeds these exact octets to both its bounded write buffer and the
; exact-byte digest cursor, whose final output supplies the trailer.
; Answer = (new-job emitted-octets). No digest or receipt is guessed here.
(defun fn-bpck-emit-step (job)
  (declare (xargs :guard t))
  (if (not (equal (fn-bpn-nth 6 job) :emit)) (list job nil)
    (let* ((answer (fn-bpnrc-step (fn-bpn-nth 7 job)))
           (word (fn-bpn-nth 0 answer))
           (bytes (fn-bpn-nth 1 answer))
           (offset (+ (nfix (fn-bpn-nth 10 job)) (len bytes)))
           (phase (cond ((equal word :continue) :emit)
                        ((and (equal word :done)
                              (equal offset (+ 14 (nfix (fn-bpn-nth 8 job)))))
                         :digest-finish)
                        (t :uncertain))))
      (list
       (fn-bpck-make (fn-bpn-nth 1 job) (fn-bpn-nth 2 job)
                     (fn-bpn-nth 3 job) (fn-bpn-nth 4 job)
                     (fn-bpn-nth 5 job) phase (fn-bpn-nth 2 answer)
                     (fn-bpn-nth 8 job) (fn-bpn-nth 9 job) offset
                     (fn-bpn-nth 11 job)) bytes))))

(defun fn-bpck-write-action (job)
  (declare (xargs :guard t))
  (cond ((equal (fn-bpn-nth 6 job) :emit) :emit)
        ((equal (fn-bpn-nth 6 job) :digest-finish) :digest)
        (t :uncertain)))

(defun fn-bpck-prefix-end (job)
  (declare (xargs :guard t))
  (nfix (fn-bpn-nth 10 job)))

; One native turn observes at most one bounded encoder/digest action or one
; filesystem primitive. CONTROL is separate from the captured semantic job.
(defun fn-bpck-io-begin (job)
  (declare (xargs :guard t))
  (if (and (equal (fn-bpn-nth 6 job) :emit)
           (equal (fn-bpn-nth 11 job) :none))
      '(:open :pending)
    '(:done :uncertain)))

(defun fn-bpck-io-action (control job)
  (declare (xargs :guard t))
  (case (fn-cbor-ag-car control)
    (:open :open)
    (:prefix (if (equal (fn-bpck-write-action job) :emit) :emit :prefix-end))
    (:digest-start :digest-start)
    (:digest :digest)
    (:trailer :trailer)
    (:barrier :barrier)
    (:close :close)
    (otherwise :done)))

(defun fn-bpck-io-step (control observation)
  (declare (xargs :guard t))
  (let ((phase (fn-cbor-ag-car control)) (outcome (fn-bpn-nth 1 control)))
    (cond
     ((member-equal phase '(:done :fenced)) control)
     ((equal phase :close)
      (if (equal observation :ok) (list :done outcome) '(:fenced :uncertain)))
     ((equal observation :cancel) '(:close :cancelled))
     ((equal observation :error) '(:close :uncertain))
     ((equal phase :open)
      (if (equal observation :ok) '(:prefix :pending) control))
     ((equal phase :prefix)
      (if (equal observation :prefix-end) '(:digest-start :pending) control))
     ((equal phase :digest-start)
      (if (equal observation :ok) '(:digest :pending) control))
     ((equal phase :digest)
      (if (equal observation :trailer-ready) '(:trailer :pending) control))
     ((equal phase :trailer)
      (if (equal observation :ok) '(:barrier :pending) control))
     ((equal phase :barrier)
      (if (equal observation :ok) '(:close :written) control))
     (t '(:close :uncertain)))))

; The buffer is at most one digest block plus the tail of one encoder turn.
; This bounded shape check is for the concrete boundary, not a full source
; revalidation. It stops at LIMIT even for a malformed externally supplied list.
(defun fn-bpck-small-octet-listp (xs limit)
  (declare (xargs :guard t :measure (nfix limit)))
  (if (atom xs) (null xs)
    (and (not (zp (nfix limit))) (fn-cbor-octetp (car xs))
         (fn-bpck-small-octet-listp (cdr xs) (1- (nfix limit))))))

(defthm fn-bpck-small-octet-list-is-proper
  (implies (fn-bpck-small-octet-listp xs limit) (true-listp xs))
  :hints (("Goal" :induct (fn-bpck-small-octet-listp xs limit)
           :in-theory (enable fn-bpck-small-octet-listp))))

; Answer = (word job block remainder). WANTED is the digest cursor's actual
; demand, at most64. A block is written and digested exactly once; at most8
; octets remain from the final9-octet encoder turn. A scan-only quantum yields
; with its exact source/task cursor and bounded buffer.
(defun fn-bpck-fill (job buffer wanted quantum)
  (declare (xargs :guard t :measure (nfix quantum) :verify-guards nil))
  (cond
   ((not (and (posp wanted) (<= wanted 64)
               (fn-bpck-small-octet-listp buffer 72)))
    (list :uncertain job nil buffer))
   ((<= wanted (len buffer))
    (list :block job (fn-bpnrc-prefix wanted buffer)
          (fn-bpnrc-suffix wanted buffer)))
   ((zp (nfix quantum)) (list :yield job nil buffer))
   ((not (equal (fn-bpn-nth 6 job) :emit))
    (list :uncertain job nil buffer))
   (t
    (let* ((answer (fn-bpck-emit-step job))
           (next (fn-bpn-nth 0 answer))
           (bytes (fn-bpn-nth 1 answer)))
      (fn-bpck-fill next (append buffer bytes) wanted
                    (1- (nfix quantum)))))))

; Definite primitive observations, not timeout or requested cancellation.
; Private or uncertain staging keeps its charge until deletion/publication
; is actually observed; the source action must have returned as well.
(defun fn-bpck-stage-observation (job observation)
  (declare (xargs :guard t))
  (let* ((stage (fn-bpn-nth 11 job))
         (next (cond ((and (equal stage :none) (equal observation :created))
                      :private)
                     ((and (member-equal stage '(:private :uncertain))
                           (equal observation :deleted)) :deleted)
                     ((and (equal stage :private) (equal observation :published))
                      :published)
                     ((and (member-equal stage '(:none :private))
                           (equal observation :ambiguous))
                      :uncertain)
                     (t stage))))
    (fn-bpck-make (fn-bpn-nth 1 job) (fn-bpn-nth 2 job)
                  (fn-bpn-nth 3 job) (fn-bpn-nth 4 job)
                  (fn-bpn-nth 5 job) (fn-bpn-nth 6 job)
                  (fn-bpn-nth 7 job) (fn-bpn-nth 8 job)
                  (fn-bpn-nth 9 job) (fn-bpn-nth 10 job) next)))

(defun fn-bpck-cleanup-word (job source-result aliases-result fd-result baseline-result)
  (declare (xargs :guard t))
  (cond ((not (and (equal source-result :returned)
                   (equal aliases-result :relinquished)
                   (equal fd-result :closed))) :pending)
        ((not (member-equal (fn-bpn-nth 11 job) '(:none :deleted :published)))
         :uncertain)
        ((and (equal (fn-bpn-nth 11 job) :published)
              (not (equal baseline-result :transferred))) :pending)
        (t :release)))

(verify-guards fn-bpck-make)
(verify-guards fn-bpck-begin)
(verify-guards fn-bpck-census-step)
(verify-guards fn-bpck-stage-demand)
(verify-guards fn-bpck-prefix)
(verify-guards fn-bpck-stage-granted)
(verify-guards fn-bpck-emit-step)
(verify-guards fn-bpck-write-action)
(verify-guards fn-bpck-prefix-end)
(verify-guards fn-bpck-io-begin)
(verify-guards fn-bpck-io-action)
(verify-guards fn-bpck-io-step)
(verify-guards fn-bpck-small-octet-listp)
(verify-guards fn-bpck-fill)
(verify-guards fn-bpck-stage-observation)
(verify-guards fn-bpck-cleanup-word)

; Ghost abstraction only: served turns use TASKS and COUNT, never this full
; encoder or residual. The capture's exact payload length is carried across
; every census yield; completion determines staging demand without encoding.
(defun fn-bpck-census-invariantp (job)
  (declare (xargs :guard t :verify-guards nil))
  (and (natp (fn-bpn-nth 8 job))
       (fn-bpnrc-tasks-validp (fn-bpn-nth 7 job))
       (equal (+ (fn-bpn-nth 8 job)
                 (len (fn-bpnrc-residual (fn-bpn-nth 7 job))))
              (len (fn-bpnr-enc (fn-bpn-nth 5 job)
                                (fn-bpn-nth 4 job))))))

(local
 (defthm fn-bpck-census-count-is-natural
   (natp (fn-bpn-nth 1 (fn-bpnrc-census-run tasks quantum count)))
   :hints (("Goal" :induct (fn-bpnrc-census-run tasks quantum count)
            :in-theory (enable fn-bpnrc-census-run fn-bpn-nth
                               fn-cbor-ag-car fn-cbor-ag-cdr)))))

(defthm fn-bpck-census-step-preserves-exact-capture-length
  (implies (and (equal (fn-bpn-nth 6 job) :census)
                (fn-bpck-census-invariantp job))
           (fn-bpck-census-invariantp (fn-bpck-census-step job quantum)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnrc-census-preserves-exact-length
                            (tasks (fn-bpn-nth 7 job))
                            (count (fn-bpn-nth 8 job))))
           :in-theory (union-theories
                        '(fn-bpck-census-invariantp fn-bpck-census-step
                          fn-bpck-make fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr
                          fn-bpck-census-count-is-natural nfix natp car-cons cdr-cons
                          (:e zp) (:e natp) (:e equal) (:e binary-+)
                          (:type-prescription len))
                        (theory 'minimal-theory)))))

(defthm fn-bpck-emit-step-is-bounded
  (<= (len (fn-bpn-nth 1 (fn-bpck-emit-step job))) 9)
  :hints (("Goal" :use ((:instance fn-bpnrc-step-emits-at-most-nine-bytes
                                    (tasks (fn-bpn-nth 7 job))))
           :in-theory (enable fn-bpck-emit-step fn-bpn-nth))))

(defthm fn-bpck-cleanup-needs-actual-return-and-settlement
  (iff (equal (fn-bpck-cleanup-word job source aliases fd baseline) :release)
       (and (equal source :returned) (equal aliases :relinquished)
            (equal fd :closed)
            (member-equal (fn-bpn-nth 11 job) '(:none :deleted :published))
            (or (not (equal (fn-bpn-nth 11 job) :published))
                (equal baseline :transferred))))
  :hints (("Goal" :in-theory (enable fn-bpck-cleanup-word))))

(in-theory (disable fn-bpck-make fn-bpck-begin fn-bpck-census-step
                    fn-bpck-stage-demand fn-bpck-prefix fn-bpck-stage-granted
                    fn-bpck-emit-step fn-bpck-write-action fn-bpck-prefix-end
                    fn-bpck-io-begin fn-bpck-io-action fn-bpck-io-step
                    fn-bpck-small-octet-listp fn-bpck-fill fn-bpck-stage-observation
                    fn-bpck-cleanup-word))
