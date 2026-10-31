; Layer A machine declarations. The directory carries only (kind, slot);
; every machine field lives in its kind's own struct of arrays.
(in-package "ACL2")
(include-book "machines")
(include-book "profile")

(in-theory (disable fn2-profile-generation-start fn2-profile-generation-limit
                    fn2-profile-accept-credits fn2-profile-c))

(defun fn2-machine-initial-generation (slot base n gen)
  (declare (xargs :guard t) (ignore slot base n)) gen)
(defun fn2-machine-initial-next-free (slot base n gen)
  (declare (xargs :guard t) (ignore gen))
  (if (< (+ (nfix slot) 1) (nfix n)) (+ (nfix base) (nfix slot) 1) *fn2-none*))

;; The three layer-A probes in the machine form (MACHINE-FORM-20261030 6.2):
;; each arm is steps in the arm language; machine-arms.lisp derives its
;; contract (cost, writes, tables, next, uses) and emits its function in the
;; kind's callbacks section. :holds gives each phase's resources in D0's
;; order (fn2/books/resources.lisp).
(defmachine fn2-listener
 :phases (:accepting :admitting :closing)
 :fields ((cap-index :u32) (cap-nonce :u32) (pending :u32) (stopped :bool) (event-ready :bool) (mode :bool)
          ; the admitted kind's ordinal (D 4.5): echo unless :listener-targets names another
          (target :u8)
          ; the last Accept's peer record (layer doc 4.1.1), for an admitted kind's :copy
          (peer-family :u8) (peer-port :u16) (peer-w0 :u32) (peer-w1 :u32) (peer-w2 :u32) (peer-w3 :u32))
 :holds ((:accepting :accept-credit) (:admitting :accept-credit :connection-row) (:closing :accept-credit))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-accept-credits profile)
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (phase *fn2-listener-state-accepting*) (mode 1))
 :subarms
 ;; the admission of an accepted connection into the target kind; a refused
 ;; admission returns the row credit and the booking and closes the capability
 ((admit
   (:do (code) (fn2-machine-admit row-target row-cap-index row-cap-nonce row-mode row-principal-slot row-account-ref
                                  row-peer-family row-peer-port row-peer-w0 row-peer-w1 row-peer-w2 row-peer-w3)
    :case ((:otherwise
            (:do () (fn2-listener-return-credit row-target))
            (:do (ucode) (fn2-account-unbook-ref row-account-ref) :case ((:otherwise (:stop :account))))
            (:set (account-ref *fn2-none*))
            (:next :closing)
            (:charge :steps (if (eq code :no-row) *fn2-work-state* *fn2-work-refusal*) :runnable t))))
   (:set (event-ready 0) (account-ref *fn2-none*))
   (:next :accepting)
   (:charge :steps *fn2-work-transition* :runnable t)))
 :arms
 ;; :accepting holds only the accept credit. A successful Accept issue takes
 ;; one row credit and moves to :admitting; without a credit the listener
 ;; parks on the admission FIFO. D7's S1: for a target that carries a
 ;; booking, the principal's :connection-row is booked before the issue; a
 ;; refused booking (:limit, :shared) admits the connection unbooked.
 ((:accepting
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (< row-target *fn2-machine-admitted-max*)) (:stop :machine-phase))
          ((zp (fn2-machine-admission-credits row-target)) (:park :admission row-target))
          ((not (and (natp budget) (< 0 budget))) (:yield))
          (t
           (:do (bcode) (fn2-account-book row-principal-slot)
            :when (fn2-machine-admission-books-p row-target) :else (:limit)
            :accept (:ok :limit :shared)
            :why "a refused booking admits the connection unbooked: its greeting is the capacity 400"
            :case ((:otherwise (:stop :account :steps *fn2-work-mailbox*))))
           (:let ref (if (eq bcode :ok) row-principal-slot *fn2-none*))
           (:issue (fn2-issue-accept 0 0 :principal 0)
            :ok ((:do () (fn2-listener-take-credit row-target))
                 (:set (account-ref ref))
                 (:next :admitting)
                 (:wait :completion :bytes 0))
            :refused ((:do (ucode) (fn2-account-unbook-ref ref) :case ((:otherwise (:stop :account)))))))))
  ;; :admitting holds the accept credit and one reserved row credit, with the
  ;; Accept pending or its capability ready; reached without either, it stops.
  (:admitting
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((equal row-event-ready 1) (:goto admit))
          (t (:stop :machine-phase))))
  ;; :closing closes a capability whose admission was refused.
  (:closing
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (and (natp budget) (< 0 budget))) (:yield))
          (t (:issue (fn2-issue-close row-cap-index row-cap-nonce :principal 0)
              :ok ((:wait :completion :bytes 0)))))))
 :observes
 ;; a failed Accept returns the row credit and releases the booking (D7's S1)
 ((:accept-result :from (:admitting)
   (:if (equal outcome *fn2-outcome-done*)
        ((:do (family port w0 w1 w2 w3) (fn2-core-observed-peer))
         (:set (cap-index aux0) (cap-nonce aux1) (peer-family family) (peer-port port) (peer-w0 w0)
               (peer-w1 w1) (peer-w2 w2) (peer-w3 w3) (event-ready 1))
         (:wake))
        ((:do () (fn2-listener-return-credit row-target))
         (:do (ucode) (fn2-account-unbook-ref row-account-ref) :case ((:otherwise (:stop :account))))
         (:set (event-ready 0) (account-ref *fn2-none*))
         (:next :accepting)
         (:wake))))
  (:close-result :from (:closing)
   (:set (event-ready 0)) (:next :accepting) (:wake))))

;; echo lends the exact RX bytes and waits for every borrow before resetting
;; its window.
(defmachine fn2-echo
 :phases (:free :command :reply :closing :draining :retired)
 :fields ((cap-index :u32) (cap-nonce :u32) (pool-slot :link) (pool-gen :u60)
          (off :u32) (length :u32) (pending :u32) (borrows :u32)
          (next-free :link) (stopped :bool) (mode :bool))
 :holds ((:command :connection-row :rx-range) (:reply :connection-row :rx-range)
         (:closing :connection-row :rx-range) (:draining :connection-row :rx-range))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-c profile)
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (pool-slot *fn2-none*) (next-free fn2-machine-initial-next-free))
 :admission (:phase :command :ranges ((:rx-range :slot pool-slot :gen pool-gen :class 0))
             :copy (mode) :clear (off length pending borrows))
 :arms
 ((:free (:idle))
  (:command
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (and (natp budget) (< 0 budget))) (:charge :steps *fn2-work-poll* :runnable t))
          ((not (eq (fn2-machine-pool-capacity-read-code row-pool-slot) :ok)) (:stop :machine-phase))
          (t (:let capacity (min *fn2-echo-run-bytes* (fn2-machine-pool-capacity row-pool-slot)))
             (:issue (fn2-issue-receive row-cap-index row-cap-nonce row-pool-slot row-pool-gen capacity
                                        :principal row-principal-slot)
              :ok ((:wait :completion :bytes capacity))))))
  (:reply
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (equal row-borrows 0)) (:charge :steps *fn2-work-poll*))
          ((or (equal row-mode 0) (>= row-off row-length))
           (:do (code) (fn2-core-reset row-pool-slot row-pool-gen)
            :case (((:ok) (:set (off 0) (length 0)) (:next :command) (:charge :steps *fn2-work-mailbox* :runnable t))
                   (:otherwise (:set (off 0) (length 0)) (:next :closing)
                               (:charge :steps *fn2-work-mailbox* :runnable t)))))
          ((not (and (natp budget) (< 0 budget))) (:charge :steps *fn2-work-poll* :runnable t))
          (t (:let len (min *fn2-echo-run-bytes* (nfix (- row-length row-off))))
             (:issue (fn2-issue-send row-cap-index row-cap-nonce row-pool-slot row-pool-gen row-off len 1
                                     :principal row-principal-slot)
              :ok ((:set (borrows 1)) (:wait :completion :bytes len))))))
  (:closing
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (and (natp budget) (< 0 budget))) (:charge :steps *fn2-work-poll* :runnable t))
          (t (:issue (fn2-issue-close row-cap-index row-cap-nonce :principal row-principal-slot)
              :ok ((:wait :completion :bytes 0))))))
  ;; a drained row returns its window and its partition row (retiring at the
  ;; generation limit)
  (:draining
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (equal row-borrows 0)) (:charge :steps *fn2-work-poll*))
          (t (:do (code) (fn2-core-release row-pool-slot row-pool-gen) :effects ((:release (:rx-range)))
              :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)"
              :case ((:otherwise (:stop :pool-release :steps *fn2-work-state*))))
             (:let next (fn2-machine-free-head *fn2-echo-admission-ordinal*))
             (:let retire (>= row-generation (fn2-machine-gen-limit)))
             (:set (generation (if retire row-generation (+ 1 row-generation)))
                   (pool-slot *fn2-none*) (pool-gen 0) (cap-index 0) (cap-nonce 0) (off 0) (length 0)
                   (next-free next) (wait-reason *fn2-wait-none*))
             (:next (:if retire :retired :free))
             (:do () (fn2-machine-reclaim-fn2-echo id retire))
             (:charge :steps *fn2-work-release*))))
  (:retired (:idle)))
 :observes
 ((:receive-result
   (:if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
             (unsigned-byte-p 32 count) (< 0 count))
        ((:set (length count) (off 0)) (:next :reply) (:wake))
        ((:next :closing) (:wake))))
  (:send-result
   (:if (not (eq (fn2-machine-pool-borrows-read-code row-pool-slot) :ok))
        ((:stop :machine-observation))
        ((:let off row-off) (:let len row-length)
         (:set (borrows (fn2-machine-pool-borrows row-pool-slot)))
         (:if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
                   (natp count) (<= (+ off count) len))
              ((:set (off (+ off count))) (:wake))
              ((:next :closing) (:wake))))))
  (:borrow-released
   (:if (not (eq (fn2-machine-pool-borrows-read-code row-pool-slot) :ok))
        ((:stop :machine-observation))
        ((:set (borrows (fn2-machine-pool-borrows row-pool-slot))) (:wake))))
  (:close-result (:next :draining) (:wake))))

;; scribe is the layer-A storage probe, not a persistence implementation. Its
;; only acknowledgement point is its own successful FenceResult; a failed
;; write/fence result never retries I/O.
(defmachine fn2-scribe
 :phases (:free :reserve :fill :patch :write :write-result :fence :fence-result :reset :read :read-result :verify :next :stopped)
 :fields ((pool-slot :link) (pool-gen :u60) (pending :u32) (borrows :u32)
          (sequence :u32) (cursor :u32) (checksum :u32) (completed :u32)
          (verified :u32) (stopped :bool) (event :u8) (outcome :u8)
          (count :u32) (aux0 :u32) (aux1 :u32) (event-ready :bool))
 :holds ((:reserve :storage-job) (:fill :storage-job :storage-window) (:patch :storage-job :storage-window)
         (:write :storage-job :storage-window) (:write-result :storage-job :storage-window)
         (:fence :storage-job :storage-window) (:fence-result :storage-job :storage-window)
         (:reset :storage-job :storage-window) (:read :storage-job :storage-window)
         (:read-result :storage-job :storage-window) (:verify :storage-job :storage-window)
         (:next :storage-job :storage-window) (:stopped :storage-job :storage-window))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (pool-slot *fn2-none*) (sequence 1))
 :subarms
 ((stop (:set (stopped 1) (event-ready 0)) (:next :stopped) (:charge :steps *fn2-work-state*))
  ;; a result row: the event its handler recorded decides the next phase
  (result
   (:cond ((equal row-event-ready 0) (:charge :steps *fn2-work-poll*))
          ((not (or (equal row-outcome *fn2-outcome-done*)
                    (and (equal row-phase *fn2-scribe-state-read-result*) (equal row-outcome *fn2-outcome-short*))))
           (:goto stop))
          ((and (equal row-phase *fn2-scribe-state-write-result*) (equal row-event *fn2-event-write-result*)
                (equal row-count *fn2-format-sector-bytes*))
           (:set (event-ready 0)) (:next :fence) (:charge :steps *fn2-work-refusal* :runnable t))
          ((and (equal row-phase *fn2-scribe-state-fence-result*) (equal row-event *fn2-event-fence-result*))
           (:set (completed row-sequence) (event-ready 0)) (:next :reset) (:charge :steps *fn2-work-mailbox* :runnable t))
          ((and (equal row-phase *fn2-scribe-state-read-result*) (equal row-event *fn2-event-read-result*)
                (< 0 row-count) (<= (+ row-cursor row-count) *fn2-format-sector-bytes*))
           (:let full (equal (+ row-cursor row-count) *fn2-format-sector-bytes*))
           (:set (cursor (if full 0 (+ row-cursor row-count))) (event-ready 0))
           (:next (:if full :verify :read))
           (:charge :steps *fn2-work-mailbox* :runnable t))
          (t (:goto stop)))))
 :arms
 ((:free (:idle))
  (:reserve
   (:let class (fn2-scribe-window-class))
   (:if (null class)
        ((:set (stopped 1)) (:next :stopped) (:charge :steps *fn2-work-release*))
        ((:do (code slot gen) (fn2-core-reserve class) :effects ((:acquire (:storage-window)))
          :case (((:exhausted) (:park :pool class :steps *fn2-work-transition*))
                 (:otherwise (:set (stopped 1) (event-ready 0)) (:next :stopped) (:charge :steps *fn2-work-transition*))))
         (:set (pool-slot slot) (pool-gen gen) (cursor 0) (checksum *fn2-fnv-offset-basis*))
         (:next :fill)
         (:charge :steps *fn2-work-transition* :runnable t))))
  ;; each byte loop yields after a chunk; conservative byte work includes an
  ;; attempted access on refusal
  (:fill
   (:do (code cursor hash) (fn2-scribe-fill *fn2-scribe-chunk-bytes* row-cursor row-sequence row-checksum
                                            row-pool-slot row-pool-gen id row-generation)
    :case (((:ok) (:set (cursor cursor) (checksum hash) (stopped 0))
                  (:next (:if (equal cursor *fn2-format-sector-bytes*) :patch :fill))
                  (:charge :bytes *fn2-scribe-chunk-bytes* :steps *fn2-work-transition* :runnable t))
           (:otherwise (:set (cursor cursor) (checksum hash) (stopped 1)) (:next :stopped)
                       (:charge :bytes *fn2-scribe-chunk-bytes* :steps *fn2-work-transition*)))))
  (:patch
   (:do (code) (fn2-scribe-patch-loop 4 0 row-checksum row-pool-slot row-pool-gen id row-generation)
    :case (((:ok) (:set (stopped 0)) (:next :write)
                  (:charge :bytes *fn2-format-word-bytes* :steps *fn2-work-small* :runnable t))
           (:otherwise (:set (stopped 1)) (:next :stopped)
                       (:charge :bytes *fn2-format-word-bytes* :steps *fn2-work-small*)))))
  (:write :on-refusal ((:goto stop))
   (:if (not (and (natp budget) (< 0 budget))) ((:yield))
        ((:issue (fn2-issue-write (* *fn2-format-sector-bytes* (nfix (- row-sequence 1))) row-pool-slot row-pool-gen
                                  0 *fn2-format-sector-bytes* 0 :principal row-principal-slot)
          :ok ((:set (pending 1) (event-ready 0)) (:next :write-result)
               (:charge :bytes *fn2-format-sector-bytes* :steps *fn2-work-small* :descriptors 1))))))
  (:write-result (:goto result))
  (:fence :on-refusal ((:goto stop))
   (:if (not (and (natp budget) (< 0 budget))) ((:yield))
        ((:issue (fn2-issue-fence :principal row-principal-slot)
          :ok ((:set (pending 1) (event-ready 0)) (:next :fence-result)
               (:charge :steps *fn2-work-small* :descriptors 1))))))
  (:fence-result (:goto result))
  (:reset
   (:do (code) (fn2-core-reset row-pool-slot row-pool-gen)
    :case (((:ok) (:set (cursor 0) (stopped 0)) (:next :read) (:charge :steps *fn2-work-mailbox* :runnable t))
           (:otherwise (:set (cursor 0) (stopped 1)) (:next :stopped) (:charge :steps *fn2-work-mailbox*)))))
  (:read :on-refusal ((:goto stop))
   (:cond ((not (and (natp budget) (< 0 budget))) (:yield))
          ((>= row-cursor *fn2-format-sector-bytes*) (:goto stop))
          (t (:issue (fn2-issue-read (+ (* *fn2-format-sector-bytes* (nfix (- row-sequence 1))) row-cursor)
                                     row-pool-slot row-pool-gen (- *fn2-format-sector-bytes* row-cursor)
                                     :principal row-principal-slot)
              :ok ((:set (pending 1) (event-ready 0)) (:next :read-result)
                   (:charge :bytes (- *fn2-format-sector-bytes* row-cursor) :steps *fn2-work-small* :descriptors 1))))))
  (:read-result (:goto result))
  (:verify
   (:do (ok cursor) (fn2-scribe-verify *fn2-scribe-chunk-bytes* row-cursor row-sequence row-checksum
                                       row-pool-slot row-pool-gen id row-generation))
   (:set (cursor cursor) (stopped (if ok 0 1)))
   (:next (:if ok (:if (equal cursor *fn2-format-sector-bytes*) :next :verify) :stopped))
   (:charge :bytes *fn2-scribe-chunk-bytes* :steps *fn2-work-transition* :runnable ok))
  (:next
   (:if (>= row-sequence *fn2-none*) ((:goto stop))
        ((:do (code) (fn2-core-reset row-pool-slot row-pool-gen)
          :case (((:ok) (:set (verified row-sequence) (sequence (+ 1 row-sequence)) (cursor 0)
                              (checksum *fn2-fnv-offset-basis*) (stopped 0))
                        (:next :fill) (:charge :steps *fn2-work-small* :runnable t))
                 (:otherwise (:set (verified row-sequence) (sequence (+ 1 row-sequence)) (cursor 0)
                                   (checksum *fn2-fnv-offset-basis*) (stopped 1))
                             (:next :stopped) (:charge :steps *fn2-work-small*)))))))
  (:stopped (:idle)))
 :observes
 ((:write-result (:set (event event) (outcome outcome) (count count) (aux0 aux0) (aux1 aux1) (event-ready 1)) (:wake))
  (:fence-result (:set (event event) (outcome outcome) (count count) (aux0 aux0) (aux1 aux1) (event-ready 1)) (:wake))
  (:read-result (:set (event event) (outcome outcome) (count count) (aux0 aux0) (aux1 aux1) (event-ready 1)) (:wake))))
