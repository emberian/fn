; Layer C4: the folds the clients read (STORAGE-DESIGN §4 decision 1;
; INBOX-DELIVERY §4.3; fn2/docs/c-ordered-runs.md §4). Each is a run schema
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
; D5's transaction writes the accept in the article's own batch; D6's GROUP
; and LIST ACTIVE read it; high + 1 is the next number.
(defrunschema fn2-group-counts :id 5
 :key ((group (:id group)))
 :value ((count :u60) (low :u60) (high :u60))
 :merge :latest
 :fold (:events ((:accept (group number) :when (< high number)
                  :set ((count (+ count 1)) (low (if (= count 0) number (min low number))) (high number)))
                 (:withdraw (group number) :when (and (< 0 count) (<= number high))
                  :set ((count (- count 1)))))
        :init :empty :coverage :history-start
        :observe (count low high)))

; The consumer cursor, per (consumer, registration epoch): the acknowledged
; commit position and the registration's query version (INBOX §4.3, §4.8).
; An ack moves the position forward only (an ack behind it is refused, the
; wire's "behind" outcome); a rebase installs a new query version and its
; start position. D8's wait machine reads it; E3's ack writes it.
(defrunschema fn2-consumer-cursor :id 6
 :key ((consumer (:id consumer)) (epoch :u32))
 :value ((position (:id position)) (version (:id version)))
 :merge :latest
 :fold (:events ((:ack (consumer epoch to) :when (< position to) :set ((position to)))
                 (:rebase (consumer epoch query start) :when (< version query)
                  :set ((version query) (position start))))
        :init :empty :coverage :history-start
        :observe (position version)))

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
