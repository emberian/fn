; Recovery's payload pass (b-durability.md S9a): an article POSTed and
; committed survives the process's death. Two articles are POSTed on one
; connection, one whose stored octets fit one payload extent (its raw
; source) and one longer (its source manifest, three 4 KiB blocks to an
; extent); then the process dies (the core is dropped, the device is kept),
; and a fresh core runs the B5 recovery row over the device. Recovery walks
; each chained commit's record stream, claims every extent an article row
; names (following the manifest to the extent of each block at unit 0 of its
; extent) and adopts it with its recorded identity, so the classification is
; :intact under broad assumptions (no position beyond the chain is dirt),
; the allocator holds exactly the payload allocations the live path made,
; and each article's stored octets read back through B's block read (whose
; handle check refuses a moved allocation as :stale). Then recovery's M7
; replay (b-durability.md S9c) has rebuilt C's rows from the record stream:
; a new connection's GROUP, ARTICLE and HEAD answer with the posted octets.
; Run: sh tools/certify.sh tests/recovery-article-unit.lisp
(in-package "ACL2")
(include-book "../books/owed-txn")
(include-book "../sim/check-wire")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-ra-profile*
  (put-assoc-equal :pool-classes '((8 . 1024) (128 . 16384) (64 . 65536))
                   (put-assoc-equal :reading t (put-assoc-equal :x 2
                    ;; the test's reads hold their descriptors (no owner row consumes the completions)
                    (put-assoc-equal :o 32 (put-assoc-equal :qa 16 *fn2-txn-posting-profile*))))))
(defun fn2-ra-text (lines) (declare (xargs :verify-guards nil)) (fn2-cw-crlf-octets lines))
(defun fn2-ra-body (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil
    (cons (concatenate 'string (if (equal n 7) "." "") "line "
                       (coerce (explode-nonnegative-integer n 10 nil) 'string)
                       " 0123456789012345678901234567890123456789012345678901")
          (fn2-ra-body (- n 1)))))
(defun fn2-ra-stuff (lines)
  (declare (xargs :verify-guards nil))
  (if (atom lines) nil
    (cons (if (and (< 0 (length (car lines))) (equal (char (car lines) 0) #\.))
              (concatenate 'string "." (car lines)) (car lines))
          (fn2-ra-stuff (cdr lines)))))
(defun fn2-ra-article (mid n)
  (declare (xargs :verify-guards nil))
  (append (list "From: a@example.invalid" "Subject: hello" "Newsgroups: local.test"
                (concatenate 'string "Message-ID: " mid) "")
          (fn2-ra-body n)))
; 6,296 stored octets (one extent's raw source) and 15,746 (a manifest of
; four blocks over two block extents).
(defconst *fn2-ra-small* (fn2-ra-article "<small@example.invalid>" 100))
(defconst *fn2-ra-big* (fn2-ra-article "<big@example.invalid>" 250))
(defconst *fn2-ra-lines*
  (append '("POST") (fn2-ra-stuff *fn2-ra-small*) '(".") '("POST") (fn2-ra-stuff *fn2-ra-big*) '(".") '("QUIT")))
(defconst *fn2-ra-wire*
  (fn2-ra-text (list "200 fn-nntp experimental server ready" "340 send article to be posted" "240 article received OK"
                     "340 send article to be posted" "240 article received OK" "205 closing connection")))

;; After death and recovery, a new connection reads both articles through
;; the served cursor (M7's replay rebuilt C's rows): the group's counts, the
;; small article whole (its stored octets, dot-stuffed again) and the big
;; one's headers.
(defconst *fn2-ra-after-lines* '("GROUP local.test" "ARTICLE 1" "HEAD 2" "QUIT"))
(defun fn2-ra-head (lines)
  (declare (xargs :verify-guards nil))
  (if (or (atom lines) (equal (car lines) "")) nil (cons (car lines) (fn2-ra-head (cdr lines)))))
(defconst *fn2-ra-after-wire*
  (fn2-ra-text (append (list "200 fn-nntp experimental server ready" "211 2 1 2 local.test"
                             "220 1 <small@example.invalid> article follows" "Xref: fn2.invalid local.test:1")
                       (fn2-ra-stuff *fn2-ra-small*)
                       (list "." "221 2 <big@example.invalid> headers follow" "Xref: fn2.invalid local.test:2")
                       (fn2-ra-head *fn2-ra-big*)
                       (list "." "205 closing connection"))))

;; The listener's Accept, issued at boot and taken by the recovery run's
;; adapter (no client yet), stays submitted: the new connection completes it.
(defun fn2-ra-pending-accept (left i fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix left)))
  (cond ((or (zp left) (>= (nfix i) (fn2-ops-rows fn2-ops))) nil)
        ((and (equal (fn2-ops-kind (nfix i) fn2-ops) *fn2-action-accept*)
              (equal (fn2-ops-phase (nfix i) fn2-ops) *fn2-op-phase-submitted*))
         (list (nfix i) (fn2-ops-gen (nfix i) fn2-ops)))
        (t (fn2-ra-pending-accept (- left 1) (+ 1 (nfix i)) fn2-ops))))
(defun fn2-ra-serve (lines store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((octets (fn2-ra-text lines))
       (clients (fn2-cw-clients (list (list octets (list (len octets))))))
       (acc (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (acc) (fn2-ra-pending-accept (fn2-ops-rows fn2-ops) 0 fn2-ops) acc))
       ((unless acc) (mv (list :no-accept) fn2-core))
       (fn2-core (fn2-cw-post-accept (nth 0 acc) (nth 1 acc) 0 77 (nth 4 (car clients)) fn2-core))
       ((mv status clients & fn2-core) (fn2-cw-loop 400000 0 1 clients store fn2-core)))
    (mv (list status (car (car (fn2-cw-results clients))) (fn2-core-stop-reason fn2-core)) fn2-core)))

; The payload allocations: (extent epoch counter owner) of every extent
; allocated to the transaction kind (an article), in extent order.
(defun fn2-ra-allocs-from (left i fn2-extents)
  (declare (xargs :stobjs fn2-extents :verify-guards nil :measure (nfix left)))
  (if (or (zp left) (>= (nfix i) (fn2-extents-rows fn2-extents))) nil
    (let ((rest (fn2-ra-allocs-from (- left 1) (+ 1 (nfix i)) fn2-extents)))
      (if (and (equal (fn2-extents-state (nfix i) fn2-extents) *fn2-extent-state-allocated*)
               (equal (fn2-extents-owner-kind (nfix i) fn2-extents) *fn2-txn-kind*))
          (cons (list (nfix i) (fn2-extents-epoch (nfix i) fn2-extents) (fn2-extents-counter (nfix i) fn2-extents)
                      (fn2-extents-owner-id (nfix i) fn2-extents))
                rest)
        rest))))
(defun fn2-ra-allocs (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (l) (fn2-ra-allocs-from (fn2-extents-rows fn2-extents) 0 fn2-extents) l))

; Before death: the wire and the device, and the payload allocations.
(defun fn2-ra-post ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-ra-profile* :echo nil fn2-core))
           ((mv & fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           (octets (fn2-ra-text *fn2-ra-lines*))
           ((mv status clients store fn2-core)
            (fn2-cw-loop 20000 0 0 (fn2-cw-clients (list (list octets (list (len octets))))) nil fn2-core)))
        (mv (list status (car (car (fn2-cw-results clients))) store (fn2-ra-allocs fn2-core) (fn2-core-stop-reason fn2-core))
            fn2-core))
      result)))

; After death, through the recovered core: block read [0, LEN) of unit PU
; under handle EPOCH ALLOC into a fresh lease of the test's owner (kind 200),
; the adapter completing it from STORE: (mv code octets fn2-core).
(defun fn2-ra-read-unit (pu epoch alloc len store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv code lslot lgen fn2-core) (fn2-core-reserve 1 200 0 1 fn2-core))
       ((unless (eq code :ok)) (mv (list :lease code) nil fn2-core))
       ((mv code & & fn2-core) (fn2-block-read pu epoch alloc 0 len lslot lgen 200 0 1 0 fn2-core))
       ((unless (eq code :ok)) (mv code nil fn2-core))
       ((mv took & & & fn2-core) (fn2-cw-adapter-one 0 nil store fn2-core))
       ((unless took) (mv :not-taken nil fn2-core))
       (octets (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (octets)
                 (fn2-cw-read-range 0 len lslot fn2-pool) octets)))
    (mv :ok octets fn2-core)))
;; A read's lease stays the adapter's until its completion is delivered,
;; which no row of the test's owner consumes; the manifest unit read into it
;; is copied (as raw octets) into a workspace of the owner and decoded there.
(defun fn2-ra-put (i octets slot gen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (len octets)))
  (if (atom octets) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-core-write slot gen i (car octets) 200 0 1 fn2-core)
      (if (eq code :ok) (fn2-ra-put (+ 1 (nfix i)) (cdr octets) slot gen fn2-core) (mv code fn2-core)))))
(defun fn2-ra-stage (lslot fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((octets (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (octets)
                 (fn2-cw-read-range 0 4096 lslot fn2-pool) octets))
       ((mv code slot gen fn2-core) (fn2-core-reserve 1 200 0 1 fn2-core))
       ((unless (eq code :ok)) (mv code 0 0 fn2-core))
       ((mv code fn2-core) (fn2-ra-put 0 octets slot gen fn2-core)))
    (mv code slot gen fn2-core)))
(defun fn2-ra-read-units (n pu epoch alloc total store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
  (if (or (zp n) (zp total)) (mv :ok nil fn2-core)
    (b* (((mv code octets fn2-core) (fn2-ra-read-unit pu epoch alloc (min 4096 total) store fn2-core))
         ((unless (eq code :ok)) (mv code nil fn2-core))
         ((mv code rest fn2-core)
          (fn2-ra-read-units (- n 1) (+ 1 pu) epoch alloc (- total (min 4096 total)) store fn2-core)))
      (mv code (append octets rest) fn2-core))))
; The lease's manifest unit (just read into LSLOT LGEN) from in-unit OFF:
; every block it names read back, the cursor's walk: (mv code done octets fn2-core).
(defun fn2-ra-entries (fuel off total lslot lgen store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (let ((at (fn2-am-entry-at off)))
    (if (or (zp fuel) (<= 4096 at)) (mv :ok nil nil fn2-core)
      (b* (((mv code next lo len unit epoch alloc fn2-core)
            (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
              (code next lo len unit epoch alloc fn2-fields)
              (fn2-am-get-entry 256 lslot lgen at 4096 200 0 1 fn2-fields fn2-pool)
              (mv code next lo len unit epoch alloc fn2-core)))
           ((unless (eq code :ok)) (mv (list :entry code) nil nil fn2-core))
           ((mv code octets fn2-core) (fn2-ra-read-unit unit epoch alloc len store fn2-core))
           ((unless (eq code :ok)) (mv code nil nil fn2-core))
           ((when (<= total (+ lo len))) (mv :ok t octets fn2-core))
           ((mv code done rest fn2-core) (fn2-ra-entries (- fuel 1) next total lslot lgen store fn2-core)))
        (mv code done (append octets rest) fn2-core)))))
(defun fn2-ra-manifest-units (u n pu epoch alloc total store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix (- (nfix n) (nfix u)))))
  (if (>= (nfix u) (nfix n)) (mv :short nil fn2-core)
    (b* (((mv code lslot lgen fn2-core) (fn2-core-reserve 1 200 0 1 fn2-core))
         ((unless (eq code :ok)) (mv (list :lease code) nil fn2-core))
         ((mv code & & fn2-core) (fn2-block-read (+ pu (nfix u)) epoch alloc 0 4096 lslot lgen 200 0 1 0 fn2-core))
         ((unless (eq code :ok)) (mv code nil fn2-core))
         ((mv took & & & fn2-core) (fn2-cw-adapter-one 0 nil store fn2-core))
         ((unless took) (mv :not-taken nil fn2-core))
         ((mv code lslot lgen fn2-core) (fn2-ra-stage lslot fn2-core))
         ((unless (eq code :ok)) (mv (list :stage code) nil fn2-core))
         ((mv code off fn2-core)
          (if (zp u)
              (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
                (code next fn2-fields)
                (fn2-am-get-header 256 total lslot lgen 0 4096 200 0 1 fn2-fields fn2-pool)
                (mv code next fn2-core))
            (mv :ok 0 fn2-core)))
         ((unless (eq code :ok)) (mv (list :header code) nil fn2-core))
         ((mv code done octets fn2-core) (fn2-ra-entries 32 off total lslot lgen store fn2-core))
         ((unless (eq code :ok)) (mv code nil fn2-core))
         ((when done) (mv :ok octets fn2-core))
         ((mv code rest fn2-core) (fn2-ra-manifest-units (+ 1 (nfix u)) n pu epoch alloc total store fn2-core)))
      (mv code (append octets rest) fn2-core))))
; An article's stored octets of length TOTAL at its location (unit PU,
; handle EPOCH ALLOC): its raw source, or through its source manifest.
(defun fn2-ra-read-stored (pu epoch alloc total store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (fn2-am-manifestp total)
      (fn2-ra-manifest-units 0 (fn2-am-units total) pu epoch alloc total store fn2-core)
    (fn2-ra-read-units 3 pu epoch alloc total store fn2-core)))

; The owners' extents: OWNER's allocations, and the one that holds its location
; (the raw source's only extent, or the extent whose unit 0 is TOTAL's manifest
; header, found by reading it).
(defun fn2-ra-owned (owner allocs)
  (declare (xargs :verify-guards nil))
  (cond ((atom allocs) nil)
        ((equal (nth 3 (car allocs)) owner) (cons (car allocs) (fn2-ra-owned owner (cdr allocs))))
        (t (fn2-ra-owned owner (cdr allocs)))))
(defun fn2-ra-find-manifest (allocs total store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom allocs) (mv nil fn2-core)
    (b* ((a (car allocs))
         ((mv code lslot lgen fn2-core) (fn2-core-reserve 1 200 0 1 fn2-core))
         ((unless (eq code :ok)) (mv nil fn2-core))
         ((mv code & & fn2-core) (fn2-block-read (* 3 (nth 0 a)) (nth 1 a) (nth 2 a) 0 4096 lslot lgen 200 0 1 0 fn2-core))
         ((unless (eq code :ok)) (mv nil fn2-core))
         ((mv & & & & fn2-core) (fn2-cw-adapter-one 0 nil store fn2-core))
         ((mv code lslot lgen fn2-core) (fn2-ra-stage lslot fn2-core))
         ((unless (eq code :ok)) (mv nil fn2-core))
         ((mv code fn2-core)
          (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
            (code next fn2-fields)
            (fn2-am-get-header 256 total lslot lgen 0 4096 200 0 1 fn2-fields fn2-pool)
            (mv (and (natp next) code) fn2-core))))
      (if (eq code :ok) (mv a fn2-core) (fn2-ra-find-manifest (cdr allocs) total store fn2-core)))))
(defun fn2-ra-readback (owner total allocs store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((mine (fn2-ra-owned owner allocs))
       ((mv loc fn2-core)
        (if (fn2-am-manifestp total) (fn2-ra-find-manifest mine total store fn2-core) (mv (car mine) fn2-core)))
       ((unless loc) (mv (list :no-location owner) nil fn2-core)))
    (fn2-ra-read-stored (* 3 (nth 0 loc)) (nth 1 loc) (nth 2 loc) total store fn2-core)))

; After death: a fresh core over the device STORE runs recovery (ASSUME the
; profile's assumption bits, no witness) through the executor and the
; adapter; then the recovered row's phase, class and chain, the payload
; allocations, each article's stored octets read back, and a stale handle's
; answer (the small article's allocation counter moved by one).
(defun fn2-ra-recover (store assume owners)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-ra-profile* :echo nil fn2-core))
           (id (fn2-machine-global-id *fn2-recovery-machine-kind* 0 *fn2-ra-profile*))
           ((mv start fn2-core) (fn2-recovery-start id assume 0 fn2-core))
           ((mv status & & fn2-core) (fn2-cw-loop 400000 0 0 nil store fn2-core))
           (phase (fn2-machine-phase id fn2-core))
           ((mv served fn2-core) (fn2-ra-serve *fn2-ra-after-lines* store fn2-core))
           (class (nth (fn2-machine-rc-class id fn2-core) *fn2-rec-classes*))
           (chain (fn2-machine-rc-chain id fn2-core))
           (allocs (fn2-ra-allocs fn2-core))
           ((mv c1 small fn2-core) (fn2-ra-readback (car owners) (len (fn2-ra-text *fn2-ra-small*)) allocs store fn2-core))
           ((mv c2 big fn2-core) (fn2-ra-readback (cadr owners) (len (fn2-ra-text *fn2-ra-big*)) allocs store fn2-core))
           (a (car (fn2-ra-owned (car owners) allocs)))
           ((mv lc lslot lgen fn2-core) (fn2-core-reserve 1 200 0 1 fn2-core))
           ((mv stale & & fn2-core)
            (if (and a (eq lc :ok)) (fn2-block-read (* 3 (nth 0 a)) (nth 1 a) (+ 1 (nth 2 a)) 0 16 lslot lgen 200 0 1 0 fn2-core)
              (mv :no-allocation 0 0 fn2-core))))
        (mv (list start status (fn2-core-stop-reason fn2-core)
                  (equal phase *fn2-recovery-machine-state-done*) class chain allocs
                  c1 (equal small (fn2-ra-text *fn2-ra-small*)) c2 (equal big (fn2-ra-text *fn2-ra-big*)) stale
                  (if (equal served (list :quiet *fn2-ra-after-wire* 0)) :served served))
            fn2-core))
      result)))
(defun fn2-ra-owners (allocs acc)
  (declare (xargs :verify-guards nil))
  (cond ((atom allocs) (reverse acc))
        ((member-equal (nth 3 (car allocs)) acc) (fn2-ra-owners (cdr allocs) acc))
        (t (fn2-ra-owners (cdr allocs) (cons (nth 3 (car allocs)) acc)))))

; The fixture: both POSTs answered 240; the small article one extent, the big
; one its manifest's extent and two block extents; recovery :done and :intact
; under broad assumptions with A-PERSISTENCE-FENCE (assume 2) and crash-only
; too (assume 3), the same allocations, both articles read back whole, and a
; moved allocation refused :stale. One POST run (PRE) serves both
; assumptions: recovery reads only the device it left.
(defun fn2-ra-test (assume pre)
  (declare (xargs :verify-guards nil))
  (b* ((store (nth 2 pre)) (allocs (nth 3 pre))
       (owners (fn2-ra-owners allocs nil))
       (post (fn2-ra-recover store assume owners)))
    (or (and (equal (nth 0 pre) :quiet) (equal (nth 1 pre) *fn2-ra-wire*) (equal (nth 4 pre) 0)
             (< (len (fn2-ra-text *fn2-ra-small*)) *fn2-commit-extent-bytes*)
             (< *fn2-commit-extent-bytes* (len (fn2-ra-text *fn2-ra-big*)))
             (equal (len owners) 2)
             (equal (len (fn2-ra-owned (car owners) allocs)) 1)
             (equal (len (fn2-ra-owned (cadr owners) allocs)) 3)
             (equal post (list :ok :quiet 0 t :intact (nth 5 post) allocs :ok t :ok t :stale :served))
             (posp (nth 5 post)))
        (cw "recovery-article ~x0~%pre ~x1~%post ~x2~%" assume
            (list (nth 0 pre) (equal (nth 1 pre) *fn2-ra-wire*) (nth 4 pre) allocs owners)
            post))))
(assert-event (let ((pre (fn2-ra-post))) (and (fn2-ra-test 2 pre) (fn2-ra-test 3 pre))))
