; Witnesses and teeth for PRF-180: the committed count read from the derived
; event index (books/store-budget.lisp fn-sbud-count-is-used), the committed
; record octets advanced through it (fn-sbud-bytes-carried-is-the-fold,
; fn-sbud-headroom-carried-is-headroom-at) and the owner's two other caches
; (books/store-carried-folds.lisp fn-scf-debt-carried-is-the-record-debt,
; fn-scf-usage-carried-is-the-projection).
;
; The Stores are the live owner's, built the way the host builds them
; (tests/acl2/owner-store-indexed-tests.lisp): *osi-before* is the owner
; opened over the enrolment after its recovery barriers; *osi-after* is the
; same owner after the host's own transitions commit the signed composite
; (reservation, carried identity prepare, record-file, record-link,
; record-directory, completion).  The cache is the one the host holds
; across that commit: (COUNT . VALUE) taken of *osi-before*.
(in-package "ACL2")
(include-book "owner-store-indexed-tests")
(include-book "peer-carriage-tests")
(include-book "store-capacity-vector-tests")
(include-book "../../books/store-carried-folds")
(include-book "std/testing/must-fail" :dir :system)

(defconst *scft-before-records* (fn-sf-records (fn-sn-files *osi-before*)))
(defconst *scft-after-records* (fn-sf-records (fn-sn-files *osi-after*)))
(assert-event (equal (len *scft-before-records*) 1))
(assert-event (equal (len *scft-after-records*) 2))
(assert-event (equal *scft-after-records*
                     (append *scft-before-records* (list *bsb-composite*))))

; -----------------------------------------------------------------------------
; fn-sbud-count-is-used: antecedent and conclusion, before and after.
(assert-event (fn-ceis-indexedp *osi-before*))
(assert-event (equal (fn-sbud-count *osi-before*) (fn-sbud-used *osi-before*)))
(assert-event (equal (fn-sbud-count *osi-before*) 1))
(assert-event (fn-ceis-indexedp *osi-after*))
(assert-event (equal (fn-sbud-count *osi-after*) (fn-sbud-used *osi-after*)))
(assert-event (equal (fn-sbud-count *osi-after*) 2))

; Without the relation: the kernel crash image (a model state the host never
; reaches: fn-osi-host-own-eventp excludes the crash) keeps its history and
; empties its index.  Not indexed; the count is 0 while 2 records stand.
(assert-event (not (fn-ceis-indexedp *osi-crashed*)))
(assert-event (equal (fn-sbud-used *osi-crashed*) 2))
(assert-event (not (equal (fn-sbud-count *osi-crashed*)
                          (fn-sbud-used *osi-crashed*))))
(must-fail
 (defthm scft-count-without-the-relation
   (equal (fn-sbud-count *osi-crashed*) (fn-sbud-used *osi-crashed*))))

; -----------------------------------------------------------------------------
; fn-sbud-bytes-carried-is-the-fold, across the commit: the cache taken
; before it is still valid after it, and the advance over the one new record
; (sequence 1, read through the index) gives the fold.
(defconst *scft-octets-cache*
  (cons (fn-sbud-count *osi-before*) (fn-sbud-bytes-used *osi-before*)))
(assert-event (< 0 (cdr *scft-octets-cache*)))
(assert-event (fn-sbud-octets-cache-validp *scft-octets-cache* *scft-after-records*))
(assert-event (equal (fn-sbud-bytes-carried *scft-octets-cache* *osi-after*)
                     (fn-sbud-bytes-used *osi-after*)))
(assert-event (< (cdr *scft-octets-cache*) (fn-sbud-bytes-used *osi-after*)))
; The fold at open (fn-owner-install-profile's) and the empty cache agree.
(assert-event (equal (fn-sbud-bytes-carried '(0 . 0) *osi-after*)
                     (fn-sbud-bytes-used *osi-after*)))

; (1) Without the relation: the crash image, with the empty cache (valid for
; any history).  The carried octets are 0; the fold is not.
(assert-event (fn-sbud-octets-cache-validp '(0 . 0)
                                           (fn-sf-records (fn-sn-files *osi-crashed*))))
(assert-event (not (equal (fn-sbud-bytes-carried '(0 . 0) *osi-crashed*)
                          (fn-sbud-bytes-used *osi-crashed*))))
(must-fail
 (defthm scft-octets-without-the-relation
   (implies (fn-sbud-octets-cache-validp '(0 . 0)
                                         (fn-sf-records (fn-sn-files *osi-crashed*)))
            (equal (fn-sbud-bytes-carried '(0 . 0) *osi-crashed*)
                   (fn-sbud-bytes-used *osi-crashed*)))))
; (2) Without a valid cache: a CORRUPTED cache (the right count, a wrong
; sum) over the live, indexed Store.
(assert-event (fn-ceis-indexedp *osi-after*))
(assert-event (not (fn-sbud-octets-cache-validp '(1 . 999) *scft-after-records*)))
(assert-event (not (equal (fn-sbud-bytes-carried '(1 . 999) *osi-after*)
                          (fn-sbud-bytes-used *osi-after*))))
(must-fail
 (defthm scft-octets-without-a-valid-cache
   (implies (fn-ceis-indexedp *osi-after*)
            (equal (fn-sbud-bytes-carried '(1 . 999) *osi-after*)
                   (fn-sbud-bytes-used *osi-after*)))))

; fn-sbud-headroom-carried-is-headroom-at, live and without the relation.
(defconst *scft-profile* (fn-bs-config-for-profile :development))
(assert-event (equal (fn-sbud-headroom-carried *scft-profile* *osi-after* 7)
                     (fn-sbud-headroom-at *scft-profile* *osi-after* 7)))
(assert-event (equal (car (fn-sbud-headroom-carried *scft-profile* *osi-after* 7)) 2))
(assert-event (not (equal (fn-sbud-headroom-carried *scft-profile* *osi-crashed* 7)
                          (fn-sbud-headroom-at *scft-profile* *osi-crashed* 7))))
(must-fail
 (defthm scft-headroom-without-the-relation
   (equal (fn-sbud-headroom-carried *scft-profile* *osi-crashed* 7)
          (fn-sbud-headroom-at *scft-profile* *osi-crashed* 7))))

; -----------------------------------------------------------------------------
; fn-scf-debt-carried-is-the-record-debt, across the same commit.  This
; history owes no completion debt (an enrolment and a signed composite), so
; the positive witness is the equality at 0; the corrupted cache shows the
; carried figure is the cache's, not a constant.
(defconst *scft-debt-cache*
  (cons 1 (fn-cvec-record-debt *scft-before-records*)))
(assert-event (fn-cvec-debt-cache-validp *scft-debt-cache* *scft-after-records*))
(assert-event (equal (fn-scf-debt-carried *scft-debt-cache* *osi-after*)
                     (fn-cvec-record-debt *scft-after-records*)))
(assert-event (fn-ceis-indexedp *osi-after*))
(assert-event (not (fn-cvec-debt-cache-validp '(1 . 7) *scft-after-records*)))
(assert-event (not (equal (fn-scf-debt-carried '(1 . 7) *osi-after*)
                          (fn-cvec-record-debt *scft-after-records*))))
(must-fail
 (defthm scft-debt-without-a-valid-cache
   (implies (fn-ceis-indexedp *osi-after*)
            (equal (fn-scf-debt-carried '(1 . 7) *osi-after*)
                   (fn-cvec-record-debt *scft-after-records*)))))
; Without the relation, over CONSTRUCTED Stores (a Store-shaped value whose
; file kernel holds RECORDS and whose derived index is INDEX; a stale index
; is a state no host transition reaches).  With an index built from the
; history the carried debt is the fold (a non-zero one: an open
; undertaking); with the empty index it is not.
(defun scft-store (records index)
  (declare (xargs :guard t))
  (list nil nil (list :store-files :ready 2 nil records nil nil nil 0)
        nil nil nil nil nil nil nil nil nil nil index))
(defconst *scft-debt-records* (list *cvt-undertake*))
(defconst *scft-debt-good* (scft-store *scft-debt-records*
                                       (fn-cei-build *scft-debt-records*)))
(defconst *scft-debt-stale* (scft-store *scft-debt-records* nil))
(assert-event (equal (fn-sf-records (fn-sn-files *scft-debt-good*)) *scft-debt-records*))
(assert-event (fn-ceis-indexedp *scft-debt-good*))
(assert-event (fn-cvec-debt-cache-validp '(0 . 0) *scft-debt-records*))
(assert-event (equal (fn-cvec-record-debt *scft-debt-records*) 1))
(assert-event (equal (fn-scf-debt-carried '(0 . 0) *scft-debt-good*) 1))
(assert-event (not (fn-ceis-indexedp *scft-debt-stale*)))
(assert-event (not (equal (fn-scf-debt-carried '(0 . 0) *scft-debt-stale*)
                          (fn-cvec-record-debt *scft-debt-records*))))
(must-fail
 (defthm scft-debt-without-the-relation
   (implies (fn-cvec-debt-cache-validp '(0 . 0) *scft-debt-records*)
            (equal (fn-scf-debt-carried '(0 . 0) *scft-debt-stale*)
                   (fn-cvec-record-debt *scft-debt-records*)))))

; -----------------------------------------------------------------------------
; fn-scf-usage-carried-is-the-projection, across the same commit, at the
; composite's own evidence string and at an absent one.
(defconst *scft-usage-cache*
  (cons 1 (fn-pcb-tally-records *scft-before-records* nil)))
(assert-event (fn-pcb-cache-validp *scft-usage-cache* *scft-after-records*))
(assert-event (equal (fn-pcb-tally-get "r" (fn-scf-usage-carried *scft-usage-cache*
                                                                  *osi-after*))
                     (fn-pcb-usage *scft-after-records* "r")))
(assert-event (equal (fn-scf-usage-carried *scft-usage-cache* *osi-after*)
                     (fn-pcb-usage-extend *scft-usage-cache* *scft-after-records*)))
; CORRUPTED cache: a tally the history never produced.
(defconst *scft-bad-tally* (cons 1 (list (cons "r" (cons 5 5)))))
(assert-event (not (fn-pcb-cache-validp *scft-bad-tally* *scft-after-records*)))
(assert-event (not (equal (fn-pcb-tally-get "r" (fn-scf-usage-carried *scft-bad-tally*
                                                                       *osi-after*))
                          (fn-pcb-usage *scft-after-records* "r"))))
; A non-zero usage over a CONSTRUCTED indexed Store holding the carried
; event of tests/acl2/peer-carriage-tests.lisp, the cache taken before it;
; and without the relation, the index of the first event only.
; (make-event: the index's Message-ID half decodes the composite, which
; defconst evaluation cannot run.)
(make-event
 `(defconst *scft-carried-good*
    ',(scft-store *pcb-records* (fn-cei-build *pcb-records*))))
(make-event
 `(defconst *scft-carried-stale*
    ',(scft-store *pcb-records* (fn-cei-build (list (car *pcb-records*))))))
(assert-event (fn-ceis-indexedp *scft-carried-good*))
(assert-event (fn-pcb-cache-validp *pcb-cache* *pcb-records*))
(assert-event (not (equal (fn-pcb-usage *pcb-records* *pcb-evidence*) '(0 . 0))))
(assert-event (equal (fn-pcb-tally-get *pcb-evidence*
                                       (fn-scf-usage-carried *pcb-cache* *scft-carried-good*))
                     (fn-pcb-usage *pcb-records* *pcb-evidence*)))
(assert-event (not (fn-ceis-indexedp *scft-carried-stale*)))
(assert-event (fn-pcb-cache-validp '(0 . nil) *pcb-records*))
(assert-event (not (equal (fn-pcb-tally-get *pcb-evidence*
                                            (fn-scf-usage-carried '(0 . nil)
                                                                  *scft-carried-stale*))
                          (fn-pcb-usage *pcb-records* *pcb-evidence*))))
(must-fail
 (defthm scft-usage-without-a-valid-cache
   (implies (fn-ceis-indexedp *osi-after*)
            (equal (fn-pcb-tally-get "r" (fn-scf-usage-carried *scft-bad-tally*
                                                                *osi-after*))
                   (fn-pcb-usage *scft-after-records* "r")))))
(must-fail
 (defthm scft-usage-without-the-relation
   (implies (fn-pcb-cache-validp '(0 . nil) *pcb-records*)
            (equal (fn-pcb-tally-get *pcb-evidence*
                                     (fn-scf-usage-carried '(0 . nil)
                                                           *scft-carried-stale*))
                   (fn-pcb-usage *pcb-records* *pcb-evidence*)))))
