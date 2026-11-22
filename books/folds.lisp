; Layer C4: the folds the clients read (STORAGE-DESIGN §4 decision 1;
; INBOX-DELIVERY §4.3; docs/c-ordered-runs.md §4). Each is a run schema
; with :merge :latest whose declaration carries its fold (runs-schema.lisp):
; the interpretation per event kind, the initialization and coverage, and the
; observation a summary must keep answering. Declared before a world's run
; assembly (runs-served.lisp includes this book).
(in-package "ACL2")
(include-book "runs-schema")
(fn2-book-layer :c)

; Group counts and watermarks: GROUP's COUNT LOW HIGH (RFC 3977 §6.1.1). An
; accepted article is numbered by the group; a withdrawal lowers the count and
; leaves the watermarks (the reply's low and high are bounds, not exact).
; D5's transaction writes the accept in the article's own batch through the
; private successor (C-S3), which assigns the number, high + 1, from the
; group's newest row when the transaction is staged, so numbers follow commit
; order; D6's GROUP and LIST ACTIVE read it.
(defrunschema fn2-group-counts :id 5
 :key ((group (:id group)))
 :value ((count :u60) (low :u60) (high :u60))
 :merge :latest
 :fold (:events ((:accept (group number) :assign ((number (+ high 1))) :when (< high number)
                  :set ((count (+ count 1)) (low (if (= count 0) number (min low number))) (high number)))
                 (:withdraw (group number) :when (and (< 0 count) (<= number high))
                  :set ((count (- count 1)))))
        :init :empty :coverage :history-start
        :observe (count low high)))

;; The active consumer row, keyed by durable principal and consumer.
;; Epoch 0 is the empty fold. An inactive row retains its epoch with
;; version 0. Registration from a tombstone advances that epoch.
(defrunschema fn2-consumer-cursor :id 6
 :key ((principal (:id principal)) (consumer (:id consumer)))
 :value ((position (:id position)) (version (:id version)) (view (:id version)) (epoch :u32)
         (peer-stream (:id stream))
         (pull-mode :bool) (pull-stream (:id stream)) (pull-domain (:id domain)) (pull-incarnation (:id incarnation))
         (pull-revision :u60) (pull-view (:id stream)) (pull-view-version (:id version))
         (pull-interpretation :u16)
         (pull-chain-a :u60) (pull-chain-b :u60) (pull-chain-c :u60) (pull-chain-d :u60) (pull-chain-e :u60))
 :merge :latest
 :fold (:events
        ((:ack (principal consumer expected-epoch to)
          :when (and (= pull-mode 0) (and (= peer-stream 0) (and (< 0 version) (and (= epoch expected-epoch) (< position to)))))
          :unless-when :unchanged :set ((position to)))
         (:register (principal consumer expected-epoch next-epoch query start new-view)
          :when (and (= pull-mode 0) (and (= peer-stream 0) (and (= version 0) (and (= epoch expected-epoch)
                                       (and (= next-epoch (+ 1 epoch)) (< 0 query))))))
          :unless-when :unchanged
          :set ((epoch next-epoch) (version query) (position start) (view new-view)))
         (:register-peer (principal consumer expected-epoch next-epoch new-stream new-view)
          :when (and (= pull-mode 0) (and (= version 0) (and (= peer-stream 0) (and (= epoch expected-epoch)
                                      (and (= next-epoch (+ 1 epoch)) (< 0 new-stream))))))
          :unless-when :unchanged
          :set ((epoch next-epoch) (version 1) (position 0) (view new-view) (peer-stream new-stream)))
         (:rebase (principal consumer expected-epoch expected-position next-epoch query start new-view)
          :when (and (= pull-mode 0) (and (= peer-stream 0) (and (or (< 0 version) (= 0 epoch))
                     (and (= epoch expected-epoch)
                          (and (= position expected-position)
                               (and (= next-epoch (+ 1 epoch)) (< 0 query)))))))
          :unless-when :unchanged
          :set ((epoch next-epoch) (version query) (position start) (view new-view)))
         (:unregister (principal consumer expected-epoch)
          :when (and (= pull-mode 0) (and (= peer-stream 0) (and (< 0 version) (= epoch expected-epoch))))
          :unless-when :unchanged
          :set ((version 0) (position 0) (view 0)))
         ;; Receiver-side progress has a disjoint mode and a strict CAS.
         ;; A stale CAS refuses the containing transaction, including any
         ;; evidence or receipt the caller declared in its other slots.
         (:pull-advance (principal consumer target-stream source-domain source-incarnation source-revision source-view
                         source-view-version interpretation from to expect-absent
                         old-a old-b old-c old-d old-e new-a new-b new-c new-d new-e)
          :when (and (and (< from to) (= position from))
                     (or (and (and (= expect-absent 1) (= pull-mode 0))
                              (and (= from 0) (and (= epoch 0) (and (= version 0) (= peer-stream 0)))))
                         (and (and (= expect-absent 0) (= pull-mode 1))
                              (and (and (and (= pull-chain-a old-a) (= pull-chain-b old-b))
                                        (and (= pull-chain-c old-c) (and (= pull-chain-d old-d) (= pull-chain-e old-e))))
                                   (and (and (= pull-stream target-stream) (= pull-domain source-domain))
                                        (and (and (= pull-incarnation source-incarnation) (= pull-revision source-revision))
                                             (and (and (= pull-view source-view) (= pull-view-version source-view-version))
                                                  (= pull-interpretation interpretation))))))))
          :set ((pull-mode 1) (position to) (pull-stream target-stream) (pull-domain source-domain) (pull-incarnation source-incarnation)
                (pull-revision source-revision) (pull-view source-view) (pull-view-version source-view-version)
                (pull-interpretation interpretation) (pull-chain-a new-a) (pull-chain-b new-b)
                (pull-chain-c new-c) (pull-chain-d new-d) (pull-chain-e new-e))))
        :init :empty :coverage :history-start
 :observe (position version view epoch peer-stream)))

; Principal accounts, the durable half: what each principal has been charged
; per dimension (D0's accounting holds the resident half: reservations in
; flight). A refund returns at most what was charged.
(defrunschema fn2-principal-charges :id 7
 :key ((principal (:id principal)) (dimension :u8))
 :value ((charged :u60))
 :merge :latest
 :fold (:events ((:charge (principal dimension amount) :when (< 0 amount) :set ((charged (+ charged amount))))
                 (:refund (principal dimension amount) :when (and (< 0 amount) (<= amount charged))
                  :set ((charged (- charged amount)))))
        :init :empty :coverage :history-start
        :observe (charged)))
