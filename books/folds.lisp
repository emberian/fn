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
 :value ((position (:id position)) (version (:id version)) (view (:id version)) (epoch :u32))
 :merge :latest
 :fold (:events
        ((:ack (principal consumer expected-epoch to)
          :when (and (< 0 version) (and (= epoch expected-epoch) (< position to)))
          :unless-when :unchanged :set ((position to)))
         (:register (principal consumer expected-epoch next-epoch query start new-view)
          :when (and (= version 0) (and (= epoch expected-epoch)
                                       (and (= next-epoch (+ 1 epoch)) (< 0 query))))
          :unless-when :unchanged
          :set ((epoch next-epoch) (version query) (position start) (view new-view)))
         (:rebase (principal consumer expected-epoch expected-position next-epoch query start new-view)
          :when (and (or (< 0 version) (= 0 epoch))
                     (and (= epoch expected-epoch)
                          (and (= position expected-position)
                               (and (= next-epoch (+ 1 epoch)) (< 0 query)))))
          :unless-when :unchanged
          :set ((epoch next-epoch) (version query) (position start) (view new-view)))
         (:unregister (principal consumer expected-epoch)
          :when (and (< 0 version) (= epoch expected-epoch))
          :unless-when :unchanged
          :set ((version 0) (position 0) (view 0))))
        :init :empty :coverage :history-start
        :observe (position version view epoch)))

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
