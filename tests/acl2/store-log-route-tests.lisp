; Witnesses and teeth for books/store-log-route.lisp (lane commit-onto-log,
; 2026-09-27).  The host's take into the open batch (fn-olr-take), the entry
; octets it accumulates, and the allocation catch-up.  Records are the log
; core's workload records (fn-lg-workload-record: a well-formed record of the
; codec at a given txid).
(in-package "ACL2")
(include-book "../../books/store-log-route")
(include-book "std/testing/must-fail" :dir :system)

; A recovered empty kernel at next txid 1, and records at txids 1 and 2.
(defconst *slrt-ks* (fn-lgk-make nil *fn-lg-genesis* 0 1 nil nil 0 :ready))
(defconst *slrt-r1* (fn-lg-workload-record 1 100))
(defconst *slrt-r2* (fn-lg-workload-record 2 100))

; The entry octets: what the host adds per record is the entry's length.
(assert-event (equal (fn-olr-entry-octets (len *slrt-r1*) 4096)
                     (len (fn-lg-entry *fn-lg-genesis* *slrt-r1* 4096))))
(assert-event (equal (fn-olr-entry-octets (len *slrt-r1*) 4096) 4096))
(assert-event (equal (fn-olr-entry-octets 5000 4096) 8192))

; The take: the record at the next txid joins the batch (:taken, the checked
; prepare); the next record then joins a batch of one.
(assert-event (equal (car (fn-olr-take *slrt-ks* *slrt-r1* 0 0 64 16777216 4096)) :taken))
(assert-event (equal (cadr (fn-olr-take *slrt-ks* *slrt-r1* 0 0 64 16777216 4096))
                     (fn-lgt-prepare *slrt-ks* *slrt-r1*)))
(assert-event (equal (fn-lgk-batch (cadr (fn-olr-take *slrt-ks* *slrt-r1* 0 0 64 16777216 4096)))
                     (list *slrt-r1*)))
(assert-event
 (let ((ks1 (cadr (fn-olr-take *slrt-ks* *slrt-r1* 0 0 64 16777216 4096))))
   (and (equal (car (fn-olr-take ks1 *slrt-r2* 1 4096 64 16777216 4096)) :taken)
        (equal (fn-lgk-batch (cadr (fn-olr-take ks1 *slrt-r2* 1 4096 64 16777216 4096)))
               (list *slrt-r1* *slrt-r2*)))))
; A record at another txid is refused and the kernel is unchanged.
(assert-event (equal (fn-olr-take *slrt-ks* *slrt-r2* 0 0 64 16777216 4096)
                     (list :refused *slrt-ks* 4096)))
; The close rule: a batch at BMAX members, or an entry past OMAX, is :full
; and the kernel is unchanged.
(assert-event (equal (car (fn-olr-take *slrt-ks* *slrt-r1* 2 8192 2 16777216 4096)) :full))
(assert-event (equal (cadr (fn-olr-take *slrt-ks* *slrt-r1* 2 8192 2 16777216 4096)) *slrt-ks*))
(assert-event (equal (car (fn-olr-take *slrt-ks* *slrt-r1* 1 4096 64 6000 4096)) :full))
; Tooth for fn-olr-take-keeps-the-bounds' hypothesis (a NON-EMPTY batch): the
; first record of a batch is taken whatever OMAX says, so the octet bound's
; conclusion fails without it.
(assert-event (equal (car (fn-olr-take *slrt-ks* *slrt-r1* 0 0 64 100 4096)) :taken))
(must-fail
 (assert-event
  (<= (+ 0 (fn-olr-entry-octets (len *slrt-r1*) 4096)) 100)))

; The catch-up: the next txid rises to the owner's, never falls.
(assert-event (equal (fn-lgk-next-txid (fn-olr-consume-to *slrt-ks* 5)) 5))
(assert-event (equal (fn-olr-consume-to *slrt-ks* 0) *slrt-ks*))
; After it the record at the old next txid is refused: nothing below the
; owner's allocation is handed out again.
(assert-event (equal (car (fn-olr-take (fn-olr-consume-to *slrt-ks* 5) *slrt-r1* 0 0 64 16777216 4096))
                     :refused))
; T5's invariant holds of the kernels here.
(assert-event (fn-lgt-okp *slrt-ks*))
(assert-event (fn-lgt-okp (cadr (fn-olr-take *slrt-ks* *slrt-r1* 0 0 64 16777216 4096))))
(assert-event (fn-lgt-okp (fn-olr-consume-to *slrt-ks* 5)))

; The extent's growth: doubling, and at least the need rounded to the unit.
(assert-event (equal (fn-olr-next-extent 1048576 10 4096) 2097152))
(assert-event (equal (fn-olr-next-extent 4096 1000000 4096) 1003520))
(assert-event (fn-lg-extent-okp (fn-olr-next-extent 1048576 5000000 4096) 4096))
