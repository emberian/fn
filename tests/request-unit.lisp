;; Teeth for D7 4/n-a (books/owed-accounts.lisp; layer doc 13.8): the
;; ledger's request operations and its grant source over the request FIFO,
;; driven on a served core with no machine run (no arm requests before
;; 4/n-b). Machine ids stand for parked rows (the FIFO links are the
;; directory's; the kind of the row is immaterial to the ledger).
(in-package "ACL2")
(include-book "../books/owed-accounts-proof")
(include-book "std/util/bstar" :dir :system)

;; Three principals and request capacity 8: slot 1 holds a request reserve
;; of 1, so the shared remainder is 7.
(defconst *fn2-rqu-profile*
  (put-assoc-equal :accounts
   '((0 :state :anonymous :limits ((:connection-row . 8) (:principal-reservation . 8)))
     (1 :state :configured :limits ((:principal-reservation . 1)) :reserves ((:principal-reservation . 1)))
     (2 :state :configured :limits ((:principal-reservation . 8))))
   (put-assoc-equal :p 3
    (put-assoc-equal :c 8
     (put-assoc-equal :pool-classes '((16 . 64) (8 . 256)) *fn2-profile-tiny*)))))

(defmacro fn2-rqu-d () '*fn2-account-request-dim*)

;; Park each id of IDS on principal P.
(defun fn2-rqu-park-all (p ids fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-account-request-park-on p (car ids) fn2-core)
      (if (eq code :ok) (fn2-rqu-park-all p (cdr ids) fn2-core) (mv code fn2-core)))))
(defun fn2-rqu-request-n (n p fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
  (if (zp n) (mv nil fn2-core)
    (mv-let (code fn2-core) (fn2-account-request-core p fn2-core)
      (mv-let (rest fn2-core) (fn2-rqu-request-n (- n 1) p fn2-core) (mv (cons code rest) fn2-core)))))

;; One grant checked against fn2-account-grant-exact's conclusion; MUTATE
;; returns the reservation after the grant (a grant that does not acquire).
(defun fn2-rqu-exact (mutate fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((in-domain (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-account-core-invariantp fn2-core)))
       (ready (fn2-account-grant-ready fn2-core))
       (p (fn2-account-core-grant-next fn2-core))
       ((mv & head &) (fn2-account-core-ends p fn2-core))
       (next (fn2-machine-ready-next head fn2-core))
       (h0 (fn2-account-core-hold p (fn2-rqu-d) fn2-core))
       ((mv id fn2-core) (fn2-account-grant-take fn2-core))
       ((mv & fn2-core) (if mutate (fn2-account-request-release p fn2-core) (mv :ok fn2-core)))
       ((mv & head2 &) (fn2-account-core-ends p fn2-core)))
    (mv (and in-domain ready
             (or (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-machine-write*)
                 (and (equal id head)
                      (equal (fn2-account-core-hold p (fn2-rqu-d) fn2-core) (+ 1 h0))
                      (equal head2 next)
                      (equal (fn2-machine-wait-reason id fn2-core) *fn2-wait-none*))))
        fn2-core)))

;; Astra's example (layer doc 13.4), scaled to capacity 8: B (slot 0)
;; holds 7, C (slot 1) keeps its reserve of 1, A (slot 2) is refused
;; :shared and parks; B's release makes the source ready and the grant
;; reaches A, not B.
(defun fn2-rqu-astra (mutate fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-rqu-profile* :null nil fn2-core))
       ((mv b fn2-core) (fn2-rqu-request-n 7 0 fn2-core))
       ((mv a fn2-core) (fn2-account-request-core 2 fn2-core))
       ((mv pk fn2-core) (fn2-account-request-park-on 2 5 fn2-core))
       ;; A queued: a second request of A answers :queued (no barging)
       ((mv a2 fn2-core) (fn2-account-request-core 2 fn2-core))
       (ready0 (fn2-account-grant-ready fn2-core))
       ((mv r fn2-core) (fn2-account-request-release 0 fn2-core))
       (ready1 (fn2-account-grant-ready fn2-core))
       ((mv exact fn2-core) (fn2-rqu-exact mutate fn2-core)))
    (mv (list :b b :a a :park pk :a2 a2 :ready (list ready0 ready1) :release r :exact exact
              :holds (list (fn2-account-core-hold 0 (fn2-rqu-d) fn2-core) (fn2-account-core-hold 2 (fn2-rqu-d) fn2-core))
              :stop (fn2-core-stop-reason fn2-core))
        fn2-core)))
(defun fn2-rqu-astra-result (mutate)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-rqu-astra mutate fn2-core) r)))
(make-event (value `(defconst *fn2-rqu-astra* ',(fn2-rqu-astra-result nil))))
(value-triple (cw "REQUEST-UNIT astra ~x0~%" *fn2-rqu-astra*))
(assert-event (equal *fn2-rqu-astra*
                     (list :b '(:ok :ok :ok :ok :ok :ok :ok) :a :shared :park :ok :a2 :queued
                           :ready '(nil t) :release :ok :exact t :holds '(6 1) :stop *fn2-stop-reason-none*)))
(defun fn2-account-test-grant-exact () (declare (xargs :verify-guards nil))
  (equal (cadr (member :exact (fn2-rqu-astra-result nil))) t))
(defun fn2-account-test-grant-exact-negative () (declare (xargs :verify-guards nil))
  (equal (cadr (member :exact (fn2-rqu-astra-result t))) nil))
(assert-event (fn2-account-test-grant-exact))
(assert-event (fn2-account-test-grant-exact-negative))

;; The bounded wait: five rows wait on slot 0, one (id 7) on slot 2; the
;; cursor at 0. The real grant reaches id 7 within the ledger's 4 rows
;; (slot 0's head, then slot 2's); a grant whose cursor restarts at 0
;; serves slot 0 four times and never reaches slot 2.
(defun fn2-rqu-restart-within (n p h fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
  (cond ((not (fn2-account-core-headed-fits p h fn2-core)) (mv t fn2-core))
        ((zp n) (mv nil fn2-core))
        (t (mv-let (id fn2-core) (fn2-account-grant-take fn2-core)
             (let ((fn2-core (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
                               (fn2-accounts)
                               (fn2-accounts-set-grant-at (- (fn2-accounts-rows fn2-accounts) 1) 0 fn2-accounts)
                               fn2-core)))
               (if (equal id h) (mv t fn2-core) (fn2-rqu-restart-within (- n 1) p h fn2-core)))))))
(defun fn2-rqu-wait (restart fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-rqu-profile* :null nil fn2-core))
       ((mv c0 fn2-core) (fn2-rqu-park-all 0 '(0 1 2 3 4) fn2-core))
       ((mv c2 fn2-core) (fn2-rqu-park-all 2 '(7) fn2-core))
       (in-domain (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-account-core-invariantp fn2-core)))
       (rows (fn2-account-core-rows fn2-core))
       ((mv ok fn2-core) (if restart (fn2-rqu-restart-within rows 2 7 fn2-core)
                           (fn2-account-granted-within rows 2 7 fn2-core))))
    (mv (list c0 c2 rows (and in-domain ok) (fn2-core-stop-reason fn2-core)) fn2-core)))
(defun fn2-rqu-wait-result (restart)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-rqu-wait restart fn2-core) r)))
(defun fn2-account-test-bounded-wait () (declare (xargs :verify-guards nil))
  (equal (fn2-rqu-wait-result nil) (list :ok :ok 4 t *fn2-stop-reason-none*)))
(defun fn2-account-test-bounded-wait-negative () (declare (xargs :verify-guards nil))
  (equal (fn2-rqu-wait-result t) (list :ok :ok 4 nil *fn2-stop-reason-none*)))
(value-triple (cw "REQUEST-UNIT wait ~x0 restart ~x1~%" (fn2-rqu-wait-result nil) (fn2-rqu-wait-result t)))
(assert-event (fn2-account-test-bounded-wait))
(assert-event (fn2-account-test-bounded-wait-negative))

;; Settled once: one waiter granted; the next grant returns none. The
;; negative re-parks the granted row, and the next grant returns it again,
;; so the check sees a second grant of one park.
(defun fn2-rqu-once (repark fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-rqu-profile* :null nil fn2-core))
       ((mv & fn2-core) (fn2-rqu-park-all 2 '(6) fn2-core))
       (in-domain (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-account-core-invariantp fn2-core)
                       (fn2-account-grant-ready fn2-core)))
       ((mv id fn2-core) (fn2-account-grant-take fn2-core))
       ((mv & fn2-core) (if repark (fn2-account-request-park-on 2 id fn2-core) (mv :ok fn2-core)))
       ((mv id2 fn2-core) (fn2-account-grant-take fn2-core)))
    (mv (and in-domain (list id id2)) fn2-core)))
(defun fn2-rqu-once-result (repark)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-rqu-once repark fn2-core) r)))
(defun fn2-account-test-once () (declare (xargs :verify-guards nil))
  (equal (fn2-rqu-once-result nil) (list 6 *fn2-none*)))
(defun fn2-account-test-once-negative () (declare (xargs :verify-guards nil))
  (equal (fn2-rqu-once-result t) (list 6 6)))
(assert-event (fn2-account-test-once))
(assert-event (fn2-account-test-once-negative))

; A stopped core retains its first reason and the queued request. Simulate
; the structurally valid inconsistent stop separately from a real kind stop.
(defun fn2-rqu-stopped (missing-reason fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-rqu-profile* :null nil fn2-core))
       ((mv parked fn2-core) (fn2-account-request-park-on 2 6 fn2-core))
       (ready (fn2-account-grant-ready fn2-core))
       (fn2-core
        (if missing-reason
            (stobj-let ((fn2-control (fn2-core-control fn2-core))) (fn2-control)
              (update-fn2-control-stop 1 fn2-control) fn2-core)
          (fn2-core-kind-stop 0 1 fn2-core)))
       (structural (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)))
       (invariant (fn2-account-core-invariantp fn2-core))
       (stopped-ready (fn2-account-grant-ready fn2-core))
       ((mv id fn2-core) (fn2-account-grant-take fn2-core))
       ((mv granted fn2-core)
        (fn2-account-granted-within (fn2-account-core-rows fn2-core) 2 6 fn2-core)))
    (mv (and (equal granted (not missing-reason)) (eq parked :ok) ready structural (equal invariant (not missing-reason)) (not stopped-ready)
             (equal id *fn2-none*) (fn2-core-stopped-p fn2-core)
             (equal (fn2-core-stop-reason fn2-core)
                    (if missing-reason *fn2-stop-reason-none* *fn2-stop-reason-kind*))
             (equal (fn2-account-core-hold 2 (fn2-rqu-d) fn2-core) 0)
             (fn2-account-core-headed-fits 2 6 fn2-core))
        fn2-core)))

(defun fn2-rqu-stopped-result (missing-reason)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core) (fn2-rqu-stopped missing-reason fn2-core) ok)))

(defun fn2-rqu-wait-without-stop-reason ()
  (declare (xargs :verify-guards nil))
  (fn2-rqu-stopped-result t))

(assert-event (and (fn2-rqu-stopped-result nil) (fn2-rqu-wait-without-stop-reason)))

; Drop readiness from exactness on a coherently stopped core. Principal 2
; still has a fitting head. Taking a grant leaves that head and its hold intact.
(defun fn2-rqu-exact-without-readiness ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-rqu-profile* :null nil fn2-core))
           ((mv pk fn2-core) (fn2-account-request-park-on 2 6 fn2-core))
           (fn2-core (fn2-core-kind-stop 0 1 fn2-core))
           (remaining (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                           (fn2-account-core-invariantp fn2-core) (not (fn2-account-grant-ready fn2-core))))
           (p (fn2-account-core-grant-next fn2-core))
           ((mv & head &) (fn2-account-core-ends p fn2-core))
           ((mv id fn2-core) (fn2-account-grant-take fn2-core)))
        (mv (and (eq pk :ok) remaining (equal p 2) (equal head 6)
                 (not (equal id head))
                 (not (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-machine-write*)))
            fn2-core))
      ok)))
(assert-event (fn2-rqu-exact-without-readiness))

; Drop readiness from the once claim. Both takes on an empty running core
; return the sentinel, with the same recorded stop reason.
(defun fn2-rqu-once-without-readiness ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-rqu-profile* :null nil fn2-core))
           (remaining (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                           (fn2-account-core-invariantp fn2-core) (not (fn2-account-grant-ready fn2-core))))
           ((mv first fn2-core) (fn2-account-grant-take fn2-core))
           (reason (fn2-core-stop-reason fn2-core))
           ((mv second fn2-core) (fn2-account-grant-take fn2-core)))
        (mv (and remaining (equal first *fn2-none*) (equal second first)
                 (equal reason *fn2-stop-reason-none*)) fn2-core))
      ok)))
(assert-event (fn2-rqu-once-without-readiness))

; A self-link in an otherwise fitting one-row FIFO is a pending refusal.
(defun fn2-rqu-self-link ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-rqu-profile* :null nil fn2-core))
           ((mv parked fn2-core) (fn2-account-request-park-on 2 6 fn2-core))
           (before (fn2-account-core-invariantp fn2-core))
           (fn2-core (fn2-machine-write-ready-next 6 6 fn2-core))
           (corrupt (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                         (not (fn2-account-core-invariantp fn2-core))
                         (fn2-account-grant-pending fn2-core)
                         (not (fn2-account-grant-ready fn2-core))))
           ((mv id fn2-core) (fn2-account-grant-take fn2-core)))
        (mv (and (eq parked :ok) before corrupt (equal id *fn2-none*)
                 (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-machine-write*)
                 (equal (fn2-account-core-hold 2 (fn2-rqu-d) fn2-core) 0))
            fn2-core))
      ok)))
(assert-event (fn2-rqu-self-link))

;; Refused by name: a principal with request limit 0 (slot 3 does not
;; exist; the system row's limit is its capacity), so a free slot's 0 limit
;; is shown on a profile whose slot 1 has no request limit.
(defconst *fn2-rqu-zero-profile*
  (put-assoc-equal :accounts '((0 :state :anonymous :limits ((:connection-row . 8)))) *fn2-rqu-profile*))
(defun fn2-rqu-zero ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (r fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-rqu-zero-profile* :null nil fn2-core))
           ((mv c fn2-core) (fn2-account-request-core 1 fn2-core)))
        (mv c fn2-core))
      r)))
(assert-event (equal (fn2-rqu-zero) :refused))
(value-triple (cw "REQUEST-UNIT PASS~%"))
