; Witnesses and teeth for books/store-log-route.lisp (lane commit-onto-log,
; 2026-09-27).  The host's take into the open batch (fn-olr-take), the entry
; octets it accumulates, and the allocation catch-up.  Records are the log
; core's workload records (fn-lg-workload-record: a well-formed record of the
; codec at a given txid).
(in-package "ACL2")
(include-book "../../books/store-log-route")
(include-book "must-fail-checked")

; A recovered empty kernel at next txid 1, and records at txids 1 and 2.
(defconst *slrt-ks* (fn-lgk-make nil *fn-lg-genesis* 0 1 nil nil 0 :ready))
(defconst *slrt-r1* (fn-lg-workload-record 1 100))
(defconst *slrt-r2* (fn-lg-workload-record 2 100))

; The entry octets: what the host adds per record is its share of the
; packed chunk (PKT-749), its length field and its octets.
(assert-event (equal (fn-olr-entry-octets (len *slrt-r1*) 4096)
                     (fn-lg-pack-len (list *slrt-r1*))))
(assert-event (equal (fn-olr-entry-octets (len *slrt-r1*) 4096) (+ 4 (len *slrt-r1*))))
(assert-event (equal (fn-olr-entry-octets 5000 4096) 5004))

; The segment need (fn-olr-log-need-is-the-append-end), reachable: two
; records in the open batch are one packed entry of one unit; the need is
; the append's end and the fit agrees with it.
(assert-event
 (let* ((ks (fn-lgk-prepare (fn-lgk-prepare *slrt-ks* *slrt-r1*) *slrt-r2*)))
   (and (fn-frame-digestp (fn-lgk-last ks))
        (fn-lg-recordsp (fn-lgk-batch ks) 4096)
        (equal (fn-olr-log-need ks 4096) 4096)
        (equal (fn-olr-log-need ks 4096)
               (+ (fn-lgk-frontier ks) (len (fn-lgk-append-octets ks 4096))))
        (fn-lgk-fitsp ks 4096 4096)
        (not (fn-lgk-fitsp ks 4096 4095)))))

; The take: the record at the owner's txid, the kernel's next, joins the
; batch (:taken, the kernel's prepare); the next record then joins a batch of
; one.
(assert-event (equal (car (fn-olr-take *slrt-ks* *slrt-r1* 1 0 0 64 16777216 4096)) :taken))
(assert-event (equal (cadr (fn-olr-take *slrt-ks* *slrt-r1* 1 0 0 64 16777216 4096))
                     (fn-lgk-prepare *slrt-ks* *slrt-r1*)))
(assert-event (equal (fn-lgk-next-txid (cadr (fn-olr-take *slrt-ks* *slrt-r1* 1 0 0 64 16777216 4096)))
                     2))
(assert-event (equal (fn-lgk-batch (cadr (fn-olr-take *slrt-ks* *slrt-r1* 1 0 0 64 16777216 4096)))
                     (list *slrt-r1*)))
(assert-event
 (let ((ks1 (cadr (fn-olr-take *slrt-ks* *slrt-r1* 1 0 0 64 16777216 4096))))
   (and (equal (car (fn-olr-take ks1 *slrt-r2* 2 1 4096 64 16777216 4096)) :taken)
        (equal (fn-lgk-batch (cadr (fn-olr-take ks1 *slrt-r2* 2 1 4096 64 16777216 4096)))
               (list *slrt-r1* *slrt-r2*)))))
; A record the owner reserved at another txid is refused and the kernel is
; unchanged.
(assert-event (equal (fn-olr-take *slrt-ks* *slrt-r2* 2 0 0 64 16777216 4096)
                     (list :refused *slrt-ks* (+ 4 (len *slrt-r2*)))))
; The close rule: a batch at BMAX members, or an entry past OMAX, is :full
; and the kernel is unchanged.
(assert-event (equal (car (fn-olr-take *slrt-ks* *slrt-r1* 1 2 8192 2 16777216 4096)) :full))
(assert-event (equal (cadr (fn-olr-take *slrt-ks* *slrt-r1* 1 2 8192 2 16777216 4096)) *slrt-ks*))
(assert-event (equal (car (fn-olr-take *slrt-ks* *slrt-r1* 1 1 4096 64 4099 4096)) :full))
; Tooth for fn-olr-take-keeps-the-bounds' hypothesis (a NON-EMPTY batch): the
; first record of a batch is taken whatever OMAX says, so the octet bound's
; conclusion fails without it.
(assert-event (equal (car (fn-olr-take *slrt-ks* *slrt-r1* 1 0 0 64 100 4096)) :taken))
(must-fail-checked
 (assert-event
  (<= (+ 0 (fn-olr-entry-octets (len *slrt-r1*) 4096)) 100)))

; The catch-up: the next txid rises to the owner's, never falls.
(assert-event (equal (fn-lgk-next-txid (fn-olr-consume-to *slrt-ks* 5)) 5))
(assert-event (equal (fn-olr-consume-to *slrt-ks* 0) *slrt-ks*))
; After it the record at the old next txid is refused: nothing below the
; owner's allocation is handed out again.
(assert-event (equal (car (fn-olr-take (fn-olr-consume-to *slrt-ks* 5) *slrt-r1* 1 0 0 64 16777216 4096))
                     :refused))
; T5's invariant holds of the kernels here.
(assert-event (fn-lgt-okp *slrt-ks*))
(assert-event (fn-lgt-okp (cadr (fn-olr-take *slrt-ks* *slrt-r1* 1 0 0 64 16777216 4096))))
(assert-event (fn-lgt-okp (fn-olr-consume-to *slrt-ks* 5)))

; The extent's growth: doubling, and at least the need rounded to the unit.
(assert-event (equal (fn-olr-next-extent 1048576 10 4096) 2097152))
(assert-event (equal (fn-olr-next-extent 4096 1000000 4096) 1003520))
(assert-event (fn-lg-extent-okp (fn-olr-next-extent 1048576 5000000 4096) 4096))

; The link (fn-olr-linkp): the log kernel's committed ++ in flight ++ open
; batch is the store node's history.  A reachable chain from a recovered empty
; log: the take of r1 (history (r1)), the append (r1 in flight), the barrier
; (r1 committed), the acknowledgement, the take of r2 -- the link holds at
; every step.  The crash half of fn-olr-crash-reads-a-prefix-of-the-history is
; T2's (fn-lgk-crash-of-related-state-is-a-prefix; its witnesses are
; tests/acl2/store-log-kernel-tests.lisp and store-log-programs-tests.lisp).
(defun slrt-k1 () (declare (xargs :guard t :verify-guards nil)) (cadr (fn-olr-take *slrt-ks* *slrt-r1* 1 0 0 64 16777216 4096)))
(defun slrt-k2 () (declare (xargs :guard t :verify-guards nil)) (fn-lgk-append (slrt-k1) 4096 1048576))
(defun slrt-k3 () (declare (xargs :guard t :verify-guards nil)) (fn-lgk-fence (slrt-k2) 4096))
(defun slrt-k4 () (declare (xargs :guard t :verify-guards nil)) (fn-lgk-finish-one (slrt-k3)))
(defun slrt-k5 () (declare (xargs :guard t :verify-guards nil)) (cadr (fn-olr-take (slrt-k4) *slrt-r2* 2 0 0 64 16777216 4096)))
(assert-event (fn-olr-linkp nil *slrt-ks*))
(assert-event (fn-olr-linkp (list *slrt-r1*) (slrt-k1)))
(assert-event (and (equal (fn-lgk-inflight (slrt-k2)) (list *slrt-r1*))
                   (fn-olr-linkp (list *slrt-r1*) (slrt-k2))))
(assert-event (and (equal (fn-lgk-committed (slrt-k3)) (list *slrt-r1*))
                   (fn-olr-linkp (list *slrt-r1*) (slrt-k3))))
(assert-event (and (equal (fn-lgk-acked (slrt-k4)) 1)
                   (fn-olr-linkp (list *slrt-r1*) (slrt-k4))))
(assert-event (fn-olr-linkp (list *slrt-r1* *slrt-r2*) (slrt-k5)))
; Teeth: the link names ONE history; the store node's history without the
; batch's record (the file kernel not yet ordered it) is not linked, and a
; take that was not :taken (a refused record) does not extend it.
(assert-event (not (fn-olr-linkp nil (slrt-k1))))
(assert-event (not (fn-olr-linkp (list *slrt-r1* *slrt-r1*) (slrt-k5))))
(must-fail-checked
 (assert-event (fn-olr-linkp (list *slrt-r2*)
                             (cadr (fn-olr-take *slrt-ks* *slrt-r2* 2 0 0 64 16777216 4096)))))

; -----------------------------------------------------------------------------
; fn-olr-crash-reads-a-prefix-of-the-history (PRF-264; audit packet G4-3,
; lane audit-fixes): the route's own contribution, evaluated.  The state is
; store-log-kernel-tests' appended batch in flight (the recovered log r1 r2
; committed, r3 r4 r5 in flight, R asserted there); HISTORY is the store
; node's history the link names.  Each crash image is fn-bs-crash of the
; appended store under explicit admissible choices (fn-bs-crash-imagep's
; witness).
(include-book "store-log-kernel-tests")
(defun slrt-cx-history () (declare (xargs :guard t))
  (list (slk-r 1) (slk-r 2) (slk-r 3) (slk-r 4) (slk-r 5)))
(defun slrt-cx-concl (history choices)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((bs (slk-appended-bs)) (ks (slk-appended-ks))
         (content (fn-bs-durable-content (fn-bs-crash bs choices) 0))
         (scan (fn-lg-scan content (slk-genesis) (fn-bs-unit bs) (slk-max))))
    (or (and (fn-lg-prefixp (car scan) history)
             (fn-lg-prefixp (fn-lgk-committed ks) (car scan)))
        (fn-lg-forgery-in (nthcdr (fn-lgk-frontier ks) content)
                          (fn-lgk-inflight ks) (fn-lgk-last ks)
                          (fn-bs-unit bs) (slk-max)))))
(defun slrt-cx-units () (declare (xargs :guard t :verify-guards nil))
  (let ((ks (slk-appended-ks)))
    (floor (len (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (slk-unit))) (slk-unit))))
; Positive: the antecedent (R, a batch in flight, admissible choices, the
; link) and both conjuncts of the prefix disjunct, on two images: every
; unit landed (the scan is the whole history) and nothing landed (the scan
; is the committed prefix).
(assert-event
 (let* ((bs (slk-appended-bs)) (ks (slk-appended-ks))
        (all (list (slk-sels (slrt-cx-units) (slrt-cx-units) :new :new)))
        (none (list (slk-sels (slrt-cx-units) 0 :new :old))))
   (and (fn-lgk-relp bs ks 0 (slk-genesis) (slk-max))
        (consp (fn-lgk-inflight ks))
        (fn-olr-linkp (slrt-cx-history) ks)
        (fn-bs-crash-choicesp all (fn-bs-pending bs) (fn-bs-unit bs))
        (fn-bs-crash-choicesp none (fn-bs-pending bs) (fn-bs-unit bs))
        (equal (car (fn-lg-scan (fn-bs-durable-content (fn-bs-crash bs all) 0)
                                (slk-genesis) (fn-bs-unit bs) (slk-max)))
               (slrt-cx-history))
        (equal (car (fn-lg-scan (fn-bs-durable-content (fn-bs-crash bs none) 0)
                                (slk-genesis) (fn-bs-unit bs) (slk-max)))
               (list (slk-r 1) (slk-r 2)))
        (slrt-cx-concl (slrt-cx-history) all)
        (slrt-cx-concl (slrt-cx-history) none))))
; Removal of the link: a history without the committed record r1 (the store
; node's history is not the kernel's).  R, the batch in flight and the
; image are as above; the scan (r1 ... r5) is no prefix of it, and the
; damaged-entry disjunct is false (nothing is damaged).
(assert-event
 (let* ((ks (slk-appended-ks))
        (all (list (slk-sels (slrt-cx-units) (slrt-cx-units) :new :new)))
        (history (cdr (slrt-cx-history))))
   (and (not (fn-olr-linkp history ks))
        (consp (fn-lgk-inflight ks))
        (not (slrt-cx-concl history all)))))
