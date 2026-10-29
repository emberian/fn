; The resource acquisition and release protocol (EXECUTION-MODEL section 7a
; item 2; layer-D brief contract item 0) as data with certification-time
; checks. This book is a library: it includes only the declaration machinery,
; so machines.lisp can include it for each defmachine's :holds. Its printed
; form is fn2/docs/d-machines-nntp.md section 3; this book is authoritative.
(in-package "ACL2")
(include-book "owed")
(fn2-book-layer :d)

; Every resource kind a transition can hold, in the one acquisition order.
; A resource is ranked by how long it is held: what a machine keeps across
; many runs and external waits comes first, what it holds only for one issue
; comes last. Every bundle acquires in ascending rank, and a holder waits only
; for a kind ranked above every kind it holds (rule (c)), so no wait-for path
; returns to its start (argument (g), fn2-resource-ranked-no-cycle below).
; :bound names the profile key (or ROUND2 section B.1 capacity) that bounds it.
(defconst *fn2-resource-order*
  '((:service-work :rank 1 :unit :visit :bound (:calendar) :reserve :service-classes
     :why "One bounded run of a scheduled service; a visit is the frame in which a service acquires and is never awaited.")
    (:accept-credit :rank 2 :unit :credit :bound (:profile :accept-credits) :reserve nil
     :why "A listener row: at most one pending Accept each, held for the listener's lifetime.")
    (:connection-row :rank 3 :unit :row :bound (:profile :c) :reserve nil
     :why "Reserved as an admission credit at Accept issue, held for the connection's lifetime.")
    (:rx-range :rank 4 :unit :pool-slot :bound (:profile :pool-classes) :reserve nil
     :why "The connection's receive window, held for its lifetime.")
    (:tx-range :rank 5 :unit :pool-slot :bound (:profile :pool-classes) :reserve nil
     :why "The connection's reply window, held for its lifetime.")
    (:principal-reservation :rank 6 :unit :quantity :bound (:profile :p) :reserve :system
     :why "One request's charge on its principal account, held from request admission to its reply; a machine holds at most one.")
    (:tls-slot :rank 7 :unit :slot :bound (:round2 :ltls 16) :reserve nil
     :why "A handshake job, held for the handshake only.")
    (:upload-row :rank 8 :unit :row :bound (:profile :u) :reserve nil
     :why "An article input in progress, held while its bytes arrive.")
    (:chunk-window :rank 9 :unit :window :bound (:round2 :large-upload-windows 16) :reserve nil
     :why "Two 256 KiB chunk ranges of a large upload, held while it streams.")
    (:transaction-row :rank 10 :unit :row :bound (:profile :t) :reserve nil
     :why "A posting transaction from admission to its outcome.")
    (:identity-reservation :rank 11 :unit :reservation :bound (:profile :t) :reserve nil
     :why "The Message-ID and operation identity claim of one transaction.")
    (:cursor-row :rank 12 :unit :row :bound (:profile :x) :reserve nil
     :why "A query cursor from its command to its last reply byte.")
    (:wait-row :rank 13 :unit :row :bound (:profile :w) :reserve nil
     :why "A parked consumer wait from registration to its reply or cancellation.")
    (:subscription-edge :rank 14 :unit :edge :bound (:round2 :esub 4096) :reserve nil
     :why "One wait row's edge to a stream, reserved at registration.")
    (:control-output :rank 15 :unit :bytes :bound (:profile :w) :reserve nil
     :why "The reply window a wake or control reply needs, reserved at registration so delivery never waits.")
    (:cache-pin :rank 16 :unit :pin :bound (:round2 :cache-profile) :reserve :recovery
     :why "An object lease under a pinned view, held while a reply streams it.")
    (:batch-membership :rank 17 :unit :records-and-bytes :bound (:round2 :batch 1024 4194304) :reserve nil
     :why "A transaction's records in a commit batch until publish.")
    (:storage-job :rank 18 :unit :job :bound (:profile :jread :jwrite) :reserve :recovery
     :why "A read or write slot: a storage job row, held across its issue, completion and verification.")
    (:storage-window :rank 19 :unit :pool-slot :bound (:profile :pool-classes) :reserve :recovery
     :why "The pool range a storage job reads into or writes from.")
    (:fence-slot :rank 20 :unit :slot :bound (:profile :fence-slots) :reserve :fence
     :why "One fence in flight per storage domain.")
    (:cancel-credit :rank 21 :unit :credit :bound (:profile :ncancel) :reserve :cancel
     :why "One outstanding cancellation request.")
    (:operation :rank 22 :unit :op :bound (:profile :o :qa) :reserve (:close :cancel :arm-wake :fence)
     :why "One op row with its outbox descriptor and two result cells, reserved together (fn2-op-reserve); held for one issue.")))

; Protected reserves (e): units set aside at init and never lent to ordinary
; issue, so a table full of idle receives can still close, cancel, arm a wake
; and fence; recovery and control draw the system reserve.
(defconst *fn2-resource-reserves*
  '((:close :covers (:operation) :issue t
     :why "Close always issues: a connection or listener full of idle receives can still time out and close.")
    (:cancel :covers (:cancel-credit :operation) :issue t
     :why "Cancellation of an outstanding operation never waits for the operations it cancels.")
    (:arm-wake :covers (:operation) :issue t
     :why "The timer service can always arm the earliest deadline.")
    (:fence :covers (:fence-slot :operation) :issue t
     :why "A batch or probe holding its writes can always fence them.")
    (:recovery :covers (:cache-pin :storage-job :storage-window :operation) :issue nil
     :why "Recovery acquires its whole bundle from this reserve at start and never waits for ordinary holders.")
    (:system :covers (:principal-reservation) :issue nil
     :why "Recovery and control are charged to the system reserve of every account dimension.")
    (:service-classes :covers (:service-work) :issue nil
     :why "The four protected service classes of the calendar (ROUND2 section C.2).")))

; Admission bundles (b) with the held-while-waiting set (c). A transition
; acquires :acquires whole or nothing; on refusal it keeps its continuation
; with a wait reason naming the first exhausted kind. :holds is everything
; its holder may hold while it waits for this bundle. :status :exists marks a
; transition layer A has today; (:planned QUEST) one a later quest adds.
; :owed-by names the quest that makes A's code atomic for the bundle: the
; acquisition driver runs its scenario anyway, and fails if it passes.
(defconst *fn2-resource-bundles*
  '(((fn2-listener :accept) :acquires (:connection-row :rx-range :operation)
     :holds (:accept-credit) :reserve nil :status :exists :owed-by :r6b
     :why "A takes the row credit and op at issue and the RX slot only at admission; an accepted capability without an RX slot is closed.")
    ((fn2-listener :close) :acquires (:operation)
     :holds (:accept-credit) :reserve :close :status :exists :owed-by :r6b
     :why "A has no close reserve: the Close draws an ordinary op reservation.")
    ((fn2-echo :receive) :acquires (:operation)
     :holds (:connection-row :rx-range) :reserve nil :status :exists :owed-by nil
     :why "Receive into the RX slot the connection already holds.")
    ((fn2-echo :send) :acquires (:operation)
     :holds (:connection-row :rx-range) :reserve nil :status :exists :owed-by nil
     :why "Echo sends from its RX slot; D3's connection adds its TX range.")
    ((fn2-echo :close) :acquires (:operation)
     :holds (:connection-row :rx-range) :reserve :close :status :exists :owed-by :r6b
     :why "A has no close reserve: the Close draws an ordinary op reservation.")
    ((fn2-scribe :reserve) :acquires (:storage-window)
     :holds (:storage-job) :reserve nil :status :exists :owed-by nil
     :why "The probe's row is its storage job; it reserves its 4 KiB window.")
    ((fn2-scribe :write) :acquires (:operation)
     :holds (:storage-job :storage-window) :reserve nil :status :exists :owed-by nil
     :why "Write from the held window.")
    ((fn2-scribe :fence) :acquires (:fence-slot :operation)
     :holds (:storage-job :storage-window) :reserve :fence :status :exists :owed-by :r6b
     :why "A takes the fence slot adapter-side at take, after the op, and has no fence reserve.")
    ((fn2-scribe :read) :acquires (:operation)
     :holds (:storage-job :storage-window) :reserve nil :status :exists :owed-by nil
     :why "Read back into the held window.")
    ((:timer :arm-wake) :acquires (:operation)
     :holds (:service-work) :reserve :arm-wake :status :exists :owed-by :r6b
     :why "A has no ArmWake reserve: the wake draws an ordinary op reservation.")
    ((:connection :accept) :acquires (:connection-row :rx-range :tx-range :operation)
     :holds (:accept-credit) :reserve nil :status (:planned :d3) :owed-by nil
     :why "The connection machine's admission, whole at Accept issue.")
    ((:connection :receive) :acquires (:operation)
     :holds (:connection-row :rx-range :tx-range) :reserve nil :status (:planned :d3) :owed-by nil
     :why "Single-shot receive into the held RX range.")
    ((:connection :send) :acquires (:operation)
     :holds (:connection-row :rx-range :tx-range) :reserve nil :status (:planned :d3) :owed-by nil
     :why "Single-shot send from the held TX range.")
    ((:connection :close) :acquires (:operation)
     :holds (:connection-row :rx-range :tx-range) :reserve :close :status (:planned :d3) :owed-by nil
     :why "Close from the close reserve.")
    ((:connection :request) :acquires (:principal-reservation)
     :holds (:connection-row :rx-range :tx-range) :reserve nil :status (:planned :d7) :owed-by nil
     :why "A command's charge on its principal, before any request row.")
    ((:tls-admission :start) :acquires (:tls-slot :operation)
     :holds (:connection-row :rx-range :tx-range :principal-reservation) :reserve nil
     :status (:planned :d7) :owed-by nil
     :why "STARTTLS: a handshake slot and the TlsStart op.")
    ((:upload :admit) :acquires (:upload-row :chunk-window)
     :holds (:connection-row :rx-range :tx-range :principal-reservation) :reserve nil
     :status (:planned :d4) :owed-by nil
     :why "POST/IHAVE/TAKETHIS article input.")
    ((:transaction :admit) :acquires (:transaction-row :identity-reservation)
     :holds (:connection-row :rx-range :tx-range :principal-reservation :upload-row :chunk-window)
     :reserve nil :status (:planned :d5) :owed-by nil
     :why "The transaction and its identity claim.")
    ((:transaction :batch) :acquires (:batch-membership)
     :holds (:connection-row :rx-range :tx-range :principal-reservation :upload-row :chunk-window
             :transaction-row :identity-reservation)
     :reserve nil :status (:planned :d5) :owed-by nil
     :why "Joining a commit batch.")
    ((:cursor :select) :acquires (:cursor-row :cache-pin)
     :holds (:connection-row :rx-range :tx-range :principal-reservation) :reserve nil
     :status (:planned :d6) :owed-by nil
     :why "ARTICLE/BODY and the other queries pin their view before the success line.")
    ((:storage-job :read) :acquires (:storage-job :storage-window :operation)
     :holds (:connection-row :rx-range :tx-range :principal-reservation :cursor-row :cache-pin)
     :reserve nil :status (:planned :d6) :owed-by nil
     :why "A cursor's page read.")
    ((:storage-job :write) :acquires (:storage-job :storage-window :operation)
     :holds (:connection-row :rx-range :tx-range :principal-reservation :upload-row :chunk-window)
     :reserve nil :status (:planned :d4) :owed-by nil
     :why "An upload's extent write.")
    ((:wait :register) :acquires (:wait-row :subscription-edge :control-output)
     :holds (:connection-row :rx-range :tx-range :principal-reservation) :reserve nil
     :status (:planned :d8) :owed-by nil
     :why "A consumer wait reserves its edges and its wake reply before it parks.")
    ((:any :cancel) :acquires (:cancel-credit :operation)
     :holds (:connection-row :rx-range :tx-range) :reserve :cancel :status (:planned :d7) :owed-by nil
     :why "Cancel from the cancel reserve.")
    ((:commit-batch :log-write) :acquires (:storage-job :storage-window :operation)
     :holds (:batch-membership) :reserve nil :status (:planned :b) :owed-by nil
     :why "B's batch writes its packed records.")
    ((:commit-batch :fence) :acquires (:fence-slot :operation)
     :holds (:batch-membership :storage-job :storage-window) :reserve :fence :status (:planned :b) :owed-by nil
     :why "B's batch fences from the fence reserve.")
    ((:recovery :start) :acquires (:cache-pin :storage-job :storage-window :operation)
     :holds nil :reserve :recovery :status (:planned :b) :owed-by nil
     :why "Recovery takes its whole bundle from the recovery reserve.")))

; Release and rollback (d), per holder and cause, in descending rank. A
; refusal acquired nothing, so it releases nothing. The op reservation goes
; after its terminal and any release result; a range still externally
; borrowed goes only on BorrowReleased; a principal reservation is settled,
; never refunded past what was charged (rule 5).
(defconst *fn2-resource-releases*
  '(((fn2-listener :refusal) :releases nil)
    ((fn2-listener :failed-result) :releases (:operation :connection-row))
    ((fn2-listener :close) :releases (:operation :connection-row))
    ((fn2-echo :refusal) :releases nil)
    ((fn2-echo :failed-result) :releases (:operation))
    ((fn2-echo :close) :releases (:operation :rx-range :connection-row))
    ((fn2-scribe :refusal) :releases nil)
    ((fn2-scribe :failed-result) :releases (:operation))
    ((fn2-scribe :cancellation) :releases (:operation :storage-window))
    ((:connection :refusal) :releases nil)
    ((:connection :close)
     :releases (:operation :control-output :subscription-edge :wait-row :cursor-row
                :principal-reservation :tx-range :rx-range :connection-row))
    ((:request :cancellation)
     :releases (:operation :storage-window :storage-job :cache-pin :cursor-row :identity-reservation
                :transaction-row :chunk-window :upload-row :principal-reservation))
    ((:request :failed-result)
     :releases (:operation :storage-window :storage-job :cache-pin :cursor-row :chunk-window
                :upload-row :principal-reservation))
    ((:wait :cancellation) :releases (:operation :control-output :subscription-edge :wait-row))
    ((:commit-batch :publish) :releases (:batch-membership))
    ((:commit-batch :failed-result) :releases (:operation :fence-slot :storage-window :storage-job))))

; Notification debt (f): what each commit-batch phase may hold. From publish
; on, a batch owes nothing per recipient: each outcome is a state bit on its
; own transaction row, each affected subscription is reached by the wake
; service's dirty-subscription cursor over the published frontier, and a late
; registrant compares its cursor with the frontier. Two slow recipients hold
; their own rows and windows, never a batch slot.
(defconst *fn2-resource-batch-phases*
  '((:collect :holds (:batch-membership) :after-publish nil)
    (:seal :holds (:batch-membership) :after-publish nil)
    (:dependencies :holds (:batch-membership) :after-publish nil)
    (:log-write :holds (:batch-membership :storage-job :storage-window) :after-publish nil)
    (:fence :holds (:batch-membership :storage-job :storage-window :fence-slot) :after-publish nil)
    (:durable :holds (:batch-membership :storage-job :storage-window) :after-publish nil)
    (:install :holds (:batch-membership :storage-window) :after-publish nil)
    (:publish :holds (:storage-window) :after-publish t)
    (:notify :holds nil :after-publish t)
    (:uncertain :holds (:batch-membership :storage-window) :after-publish nil)
    (:draining :holds nil :after-publish t)))
(defconst *fn2-resource-per-recipient*
  '(:connection-row :rx-range :tx-range :principal-reservation :transaction-row :wait-row
    :subscription-edge :control-output :batch-membership))

; Interim, A's three kinds only: the kinds a machine of each phase may hold
; (pending operations are the outstanding table's and are not listed: a
; completion wait is not a resource wait), and A's wait reasons by the kind
; they await. R7 moves the holds into each defmachine's :holds and deletes
; this table; the wait-reason enum then names D0's kinds directly.
(defconst *fn2-resource-a-holds*
  '((fn2-listener (:accepting :accept-credit) (:admitting :accept-credit :connection-row)
                 (:closing :accept-credit))
    (fn2-echo (:free) (:command :connection-row :rx-range) (:reply :connection-row :rx-range)
              (:closing :connection-row :rx-range) (:draining :connection-row :rx-range) (:retired))
    (fn2-scribe (:free) (:reserve :storage-job)
                (:fill :storage-job :storage-window) (:patch :storage-job :storage-window)
                (:write :storage-job :storage-window) (:write-result :storage-job :storage-window)
                (:fence :storage-job :storage-window) (:fence-result :storage-job :storage-window)
                (:reset :storage-job :storage-window) (:read :storage-job :storage-window)
                (:read-result :storage-job :storage-window) (:verify :storage-job :storage-window)
                (:next :storage-job :storage-window) (:stopped :storage-job :storage-window))))
; A's wait reasons are no longer integers mapped here: defmachine's common
; wait-reason enum is (:none :completion . the kinds of *fn2-resource-order*).

;; Declared resource effects of an operation that moves resources between
;; rows (the form both seats use; R7 declares these on its allocator
;; operations). Effect forms, applied in order within one run:
;;   (:acquire KINDS)               for the acting row
;;   (:acquire KINDS :for TARGET)   on behalf of a row of machine kind TARGET
;;   (:release KINDS)               from the acting row, descending rank
;;   (:transfer KINDS :to TARGET)   from the acting row to a TARGET row
;; :holds-before is what the acting row holds when the operation starts.
;; A transfer adds no wait-for edge: neither row waits during it, and the
;; target (a :free row) waits for nothing. An acquisition inside an operation
;; ranks above everything the acting row holds, so refusing it is a wait
;; that satisfies rule (c); a refused operation applies no effect at all.
;; A's listener today keeps one :accepting phase; R7 splits it into
;; :accepting (:accept-credit) and :admitting (:accept-credit :connection-row).
(defconst *fn2-resource-effects*
  '(((fn2-listener :accept-issue) :holds-before (:accept-credit)
     :effects ((:acquire (:connection-row :operation))))
    ((fn2-listener :admit) :holds-before (:accept-credit :connection-row)
     :effects ((:transfer (:connection-row) :to fn2-echo) (:acquire (:rx-range) :for fn2-echo)))
    ((fn2-listener :admit-refused) :holds-before (:accept-credit :connection-row)
     :effects ((:release (:connection-row))))
    ((fn2-echo :reclaim) :holds-before (:connection-row :rx-range)
     :effects ((:release (:rx-range :connection-row))))))

; ------------------------------------------------------------------------
; Guard-verified readers and predicates over the tables. Every function
; accepts any value, so a malformed table is rejected rather than erroring.

(defun fn2-resource-get (key plist)
  (declare (xargs :guard t))
  (cond ((atom plist) nil)
        ((atom (cdr plist)) nil)
        ((equal key (car plist)) (cadr plist))
        (t (fn2-resource-get key (cddr plist)))))

(defun fn2-resource-memberp (x l)
  (declare (xargs :guard t))
  (cond ((atom l) nil) ((equal x (car l)) t) (t (fn2-resource-memberp x (cdr l)))))
(defun fn2-resource-remove (l drop)
  (declare (xargs :guard t))
  (cond ((atom l) nil)
        ((fn2-resource-memberp (car l) drop) (fn2-resource-remove (cdr l) drop))
        (t (cons (car l) (fn2-resource-remove (cdr l) drop)))))

(defun fn2-resource-entry (key table)
  (declare (xargs :guard t))
  (cond ((atom table) nil)
        ((and (consp (car table)) (equal key (caar table))) (cdar table))
        (t (fn2-resource-entry key (cdr table)))))

(defun fn2-resource-rank (kind order)
  (declare (xargs :guard t))
  (nfix (fn2-resource-get :rank (fn2-resource-entry kind order))))

(defun fn2-resource-kindp (kind order)
  (declare (xargs :guard t))
  (and (keywordp kind) (posp (fn2-resource-rank kind order))))

(defun fn2-resource-kinds-known-p (kinds order)
  (declare (xargs :guard t))
  (if (atom kinds) (null kinds)
    (and (fn2-resource-kindp (car kinds) order)
         (fn2-resource-kinds-known-p (cdr kinds) order))))

; Ranks are exactly 1..n in listed order: one total order, no ties.
(defun fn2-resource-order-entries-p (order rank seen)
  (declare (xargs :guard t))
  (if (atom order) (null order)
    (let ((e (car order)))
      (and (consp e) (keywordp (car e)) (not (fn2-resource-memberp (car e) seen))
           (keyword-value-listp (cdr e))
           (equal (fn2-resource-get :rank (cdr e)) rank)
           (keywordp (fn2-resource-get :unit (cdr e)))
           (consp (fn2-resource-get :bound (cdr e)))
           (stringp (fn2-resource-get :why (cdr e)))
           (fn2-resource-order-entries-p (cdr order) (+ 1 (nfix rank)) (cons (car e) seen))))))
(defun fn2-resource-order-p (order)
  (declare (xargs :guard t))
  (and (consp order) (fn2-resource-order-entries-p order 1 nil)))

(defun fn2-resource-ascending-p (kinds order)
  (declare (xargs :guard t))
  (if (or (atom kinds) (atom (cdr kinds))) t
    (and (< (fn2-resource-rank (car kinds) order) (fn2-resource-rank (cadr kinds) order))
         (fn2-resource-ascending-p (cdr kinds) order))))
(defun fn2-resource-descending-p (kinds order)
  (declare (xargs :guard t))
  (if (or (atom kinds) (atom (cdr kinds))) t
    (and (> (fn2-resource-rank (car kinds) order) (fn2-resource-rank (cadr kinds) order))
         (fn2-resource-descending-p (cdr kinds) order))))
; Rule (c): every kind held while waiting for KIND ranks strictly below it.
(defun fn2-resource-below-p (held kind order)
  (declare (xargs :guard t))
  (if (atom held) t
    (and (< (fn2-resource-rank (car held) order) (fn2-resource-rank kind order))
         (fn2-resource-below-p (cdr held) kind order))))

(defun fn2-resource-reserve-covers (reserve reserves)
  (declare (xargs :guard t))
  (fn2-resource-get :covers (fn2-resource-entry reserve reserves)))
(defun fn2-resource-subsetp (a b)
  (declare (xargs :guard t))
  (if (atom a) t (and (fn2-resource-memberp (car a) b) (fn2-resource-subsetp (cdr a) b))))
(defun fn2-resource-disjointp (a b)
  (declare (xargs :guard t))
  (if (atom a) t (and (not (fn2-resource-memberp (car a) b)) (fn2-resource-disjointp (cdr a) b))))

(defun fn2-resource-reserves-p (reserves order)
  (declare (xargs :guard t))
  (if (atom reserves) (null reserves)
    (let ((e (car reserves)))
      (and (consp e) (keywordp (car e)) (keyword-value-listp (cdr e))
           (consp (fn2-resource-get :covers (cdr e)))
           (fn2-resource-kinds-known-p (fn2-resource-get :covers (cdr e)) order)
           (booleanp (fn2-resource-get :issue (cdr e)))
           (stringp (fn2-resource-get :why (cdr e)))
           (not (fn2-resource-entry (car e) (cdr reserves)))
           (fn2-resource-reserves-p (cdr reserves) order)))))

; Kinds covered by an issue reserve (close, cancel, arm-wake, fence).
(defun fn2-resource-issue-kinds (reserves)
  (declare (xargs :guard t))
  (if (atom reserves) nil
    (append (and (consp (car reserves)) (fn2-resource-get :issue (cdar reserves))
                 (true-listp (fn2-resource-get :covers (cdar reserves)))
                 (fn2-resource-get :covers (cdar reserves)))
            (fn2-resource-issue-kinds (cdr reserves)))))

(defconst *fn2-resource-protected-transitions* '(:close :cancel :fence :arm-wake))

(defun fn2-resource-statusp (status)
  (declare (xargs :guard t))
  (or (eq status :exists)
      (and (true-listp status) (equal (len status) 2)
           (eq (car status) :planned) (keywordp (cadr status)))))

; One bundle row: ascending acquisition, waits only below its first kind,
; every kind known; a protected transition draws a reserve that covers its
; whole bundle; no unit an issue reserve covers is ever held while waiting.
(defun fn2-resource-bundle-p (row order reserves)
  (declare (xargs :guard t))
  (and (consp row) (true-listp (car row)) (equal (len (car row)) 2)
       (symbolp (caar row)) (keywordp (cadar row))
       (keyword-value-listp (cdr row))
       (let* ((p (cdr row)) (acq (fn2-resource-get :acquires p))
              (held (fn2-resource-get :holds p)) (reserve (fn2-resource-get :reserve p)))
         (and (consp acq)
              (fn2-resource-kinds-known-p acq order)
              (fn2-resource-kinds-known-p held order)
              (fn2-resource-ascending-p acq order)
              (fn2-resource-below-p held (car acq) order)
              (fn2-resource-statusp (fn2-resource-get :status p))
              (member-eq (fn2-resource-get :owed-by p) '(nil :r6b))
              (stringp (fn2-resource-get :why p))
              (if (member-eq (cadar row) *fn2-resource-protected-transitions*)
                  (and reserve (fn2-resource-subsetp acq (fn2-resource-reserve-covers reserve reserves)))
                (or (null reserve)
                    (fn2-resource-subsetp acq (fn2-resource-reserve-covers reserve reserves))))
              (fn2-resource-disjointp held (fn2-resource-issue-kinds reserves))))))
(defun fn2-resource-bundles-p (rows order reserves)
  (declare (xargs :guard t))
  (if (atom rows) (null rows)
    (and (fn2-resource-bundle-p (car rows) order reserves)
         (not (fn2-resource-entry (caar rows) (cdr rows)))
         (fn2-resource-bundles-p (cdr rows) order reserves))))

(defun fn2-resource-releases-p (rows order)
  (declare (xargs :guard t))
  (if (atom rows) (null rows)
    (let ((row (car rows)))
      (and (consp row) (true-listp (car row)) (equal (len (car row)) 2)
           (keyword-value-listp (cdr row))
           (let ((rel (fn2-resource-get :releases (cdr row))))
             (and (fn2-resource-kinds-known-p rel order)
                  (fn2-resource-descending-p rel order)
                  (or (not (eq (cadar row) :refusal)) (null rel))))
           (not (fn2-resource-entry (car row) (cdr rows)))
           (fn2-resource-releases-p (cdr rows) order)))))

; (f): no batch phase holds a per-recipient kind, and from publish on it
; holds no batch membership either, so a new batch can form behind it.
(defun fn2-resource-batch-phases-p (rows order recipient)
  (declare (xargs :guard t))
  (if (atom rows) (null rows)
    (let ((row (car rows)))
      (and (consp row) (keywordp (car row)) (keyword-value-listp (cdr row))
           (let ((held (fn2-resource-get :holds (cdr row))))
             (and (fn2-resource-kinds-known-p held order)
                  (fn2-resource-disjointp
                   held (if (fn2-resource-get :after-publish (cdr row))
                            (cons :batch-membership recipient)
                          (fn2-resource-remove recipient '(:batch-membership))))))
           (fn2-resource-batch-phases-p (cdr rows) order recipient)))))

; The interim per-phase holds of A's kinds, and A's wait reasons by kind.
(defun fn2-resource-phase-holds-p (phases order)
  (declare (xargs :guard t))
  (if (atom phases) (null phases)
    (and (consp (car phases)) (keywordp (caar phases))
         (fn2-resource-kinds-known-p (cdar phases) order)
         (fn2-resource-ascending-p (cdar phases) order)
         (fn2-resource-phase-holds-p (cdr phases) order))))
(defun fn2-resource-machine-holds-p (rows order)
  (declare (xargs :guard t))
  (if (atom rows) (null rows)
    (and (consp (car rows)) (symbolp (caar rows))
         (fn2-resource-phase-holds-p (cdar rows) order)
         (fn2-resource-machine-holds-p (cdr rows) order))))
(defun fn2-resource-wait-reasons-p (rows order)
  (declare (xargs :guard t))
  (if (atom rows) (null rows)
    (and (consp (car rows)) (keywordp (caar rows))
         (or (null (cdar rows)) (fn2-resource-kindp (cdar rows) order))
         (fn2-resource-wait-reasons-p (cdr rows) order))))

;; One effect is well formed: known kinds, acquisitions ascending and above
;; everything held, releases descending, released or transferred kinds held.
(defun fn2-resource-effect-p (effect held order)
  (declare (xargs :guard t))
  (and (true-listp effect) (consp (cdr effect))
       (let ((op (car effect)) (kinds (cadr effect)) (rest (cddr effect)))
         (and (consp kinds) (fn2-resource-kinds-known-p kinds order)
              (case op
                (:acquire (and (fn2-resource-ascending-p kinds order)
                               (fn2-resource-below-p held (car kinds) order)
                               (or (null rest)
                                   (and (equal (len rest) 2) (eq (car rest) :for)
                                        (symbolp (cadr rest)) (cadr rest)))))
                (:release (and (fn2-resource-descending-p kinds order)
                               (fn2-resource-subsetp kinds held) (null rest)))
                (:transfer (and (fn2-resource-ascending-p kinds order)
                                (fn2-resource-subsetp kinds held)
                                (equal (len rest) 2) (eq (car rest) :to)
                                (symbolp (cadr rest)) (cadr rest)))
                (otherwise nil))))))
;; The acting row's holdings after an effect (acquisitions for a target and
;; transfers leave the acting row's set as the target's gain).
(defun fn2-resource-effect-after (effect held)
  (declare (xargs :guard t))
  (if (not (and (true-listp effect) (consp (cdr effect)) (true-listp (cadr effect)))) held
    (case (car effect)
      (:acquire (if (cddr effect) held (append (fn2-resource-remove held nil) (cadr effect))))
      ((:release :transfer) (fn2-resource-remove held (cadr effect)))
      (otherwise held))))
(defun fn2-resource-effect-list-p (effects held order)
  (declare (xargs :guard t))
  (if (atom effects) (null effects)
    (and (fn2-resource-effect-p (car effects) held order)
         (fn2-resource-effect-list-p (cdr effects) (fn2-resource-effect-after (car effects) held) order))))
(defun fn2-resource-effects-p (rows order)
  (declare (xargs :guard t))
  (if (atom rows) (null rows)
    (let ((row (car rows)))
      (and (consp row) (true-listp (car row)) (equal (len (car row)) 2)
           (keyword-value-listp (cdr row))
           (fn2-resource-kinds-known-p (fn2-resource-get :holds-before (cdr row)) order)
           (consp (fn2-resource-get :effects (cdr row)))
           (fn2-resource-effect-list-p (fn2-resource-get :effects (cdr row))
                                       (fn2-resource-get :holds-before (cdr row)) order)
           (not (fn2-resource-entry (car row) (cdr rows)))
           (fn2-resource-effects-p (cdr rows) order)))))

; Each table, checked over its own data at certification (negative fixtures
; for every predicate: tests/resources-unit.lisp).
(assert-event (fn2-resource-order-p *fn2-resource-order*))
(assert-event (equal (len *fn2-resource-order*) 22))
(assert-event (fn2-resource-reserves-p *fn2-resource-reserves* *fn2-resource-order*))
(assert-event (fn2-resource-bundles-p *fn2-resource-bundles* *fn2-resource-order* *fn2-resource-reserves*))
(assert-event (fn2-resource-releases-p *fn2-resource-releases* *fn2-resource-order*))
(assert-event (fn2-resource-batch-phases-p *fn2-resource-batch-phases* *fn2-resource-order*
                                           *fn2-resource-per-recipient*))
(assert-event (fn2-resource-kinds-known-p *fn2-resource-per-recipient* *fn2-resource-order*))
(assert-event (fn2-resource-machine-holds-p *fn2-resource-a-holds* *fn2-resource-order*))
(assert-event (fn2-resource-effects-p *fn2-resource-effects* *fn2-resource-order*))

; ------------------------------------------------------------------------
; (g) Why no cycle, proved over the abstract wait-for structure. A waiter is
; (held . awaited). A chain links waiter i to i+1 when i's awaited kind is one
; i+1 holds. If every waiter's held kinds rank below its awaited kind, ranks
; of awaited kinds strictly increase along a chain, so no chain closes.

(defun fn2-resource-waiters-ranked-p (waiters order)
  (declare (xargs :guard t))
  (if (atom waiters) t
    (and (consp (car waiters))
         (fn2-resource-below-p (caar waiters) (cdar waiters) order)
         (fn2-resource-waiters-ranked-p (cdr waiters) order))))

(defun fn2-resource-chainp (waiters)
  (declare (xargs :guard t))
  (if (or (atom waiters) (atom (cdr waiters))) t
    (and (consp (car waiters)) (consp (cadr waiters))
         (fn2-resource-memberp (cdar waiters) (caadr waiters))
         (fn2-resource-chainp (cdr waiters)))))

(defun fn2-resource-last-awaited (waiters)
  (declare (xargs :guard t))
  (if (atom waiters) nil
    (if (atom (cdr waiters)) (and (consp (car waiters)) (cdar waiters))
      (fn2-resource-last-awaited (cdr waiters)))))

; A cycle: a chain whose last awaited kind is held by its first waiter.
(defun fn2-resource-cyclep (waiters)
  (declare (xargs :guard t))
  (and (consp waiters) (consp (car waiters))
       (fn2-resource-chainp waiters)
       (fn2-resource-memberp (fn2-resource-last-awaited waiters) (caar waiters))))

(local
 (defthm fn2-resource-below-member
   (implies (and (fn2-resource-below-p held kind order) (fn2-resource-memberp k held))
            (< (fn2-resource-rank k order) (fn2-resource-rank kind order)))
   :rule-classes nil))

(local
 (defthm fn2-resource-chain-increases
   (implies (and (consp waiters) (fn2-resource-chainp waiters)
                 (fn2-resource-waiters-ranked-p waiters order))
            (<= (fn2-resource-rank (cdar waiters) order)
                (fn2-resource-rank (fn2-resource-last-awaited waiters) order)))
   :hints (("Subgoal *1/3" :use ((:instance fn2-resource-below-member
                                   (held (caadr waiters)) (kind (cdadr waiters))
                                   (k (cdar waiters))))))
   :rule-classes :linear))

(defthm fn2-resource-ranked-no-cycle
  (implies (fn2-resource-waiters-ranked-p waiters order)
           (not (fn2-resource-cyclep waiters)))
  :hints (("Goal" :in-theory (disable fn2-resource-chain-increases)
                  :use (fn2-resource-chain-increases
                        (:instance fn2-resource-below-member
                         (held (caar waiters)) (kind (cdar waiters))
                         (k (fn2-resource-last-awaited waiters)))))))
