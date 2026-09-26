; Teeth of books/store-record-tally.lisp (PRF-139 part 1).  Reachable Stores
; from the Store's own transitions: three consumer records reserved,
; published and finished one after another, then a crash and the recovery.
; One reachable witness per keystone and one hypothesis-removal witness per
; hypothesis; the corrupted-state witnesses are labelled.
(in-package "ACL2")
(include-book "../../books/store-record-tally")
(include-book "std/testing/must-fail" :dir :system)

(defun srtt-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun srtt-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))
(defun srtt-commit (s event)
  (fn-sn-finish (srtt-publish (fn-sn-prepare-consumer (srtt-reserve s) event))))

(defconst *srtt-boot* (fn-cpe-make 0 0 0 '(:bootstrap (1) (2))))
(defconst *srtt-reg* (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 1 1)))
(defconst *srtt-ack*
  (fn-cpe-make 2 2 2
               (list :ack (fn-cp-cursor '(1) '(2) '(3) '(4) '(5)
                                         1 1 1 2))))
(defconst *srtt-initial* (fn-sn-initial '("g") 32))
(defconst *srtt-1* (srtt-commit *srtt-initial* *srtt-boot*))
(defconst *srtt-2* (srtt-commit *srtt-1* *srtt-reg*))
(defconst *srtt-3* (srtt-commit *srtt-2* *srtt-ack*))
(defconst *srtt-records* (fn-sf-records (fn-sn-files *srtt-3*)))
(defconst *srtt-crashed* (fn-sn-crash *srtt-3* :old :absent))
(defconst *srtt-recovered* (fn-sn-recover *srtt-crashed*))

;; The trace is real: three records committed, each extended the tally.
(assert-event (and (equal (len *srtt-records*) 3)
                   (equal (fn-sf-phase (fn-sn-files *srtt-3*)) :ready)
                   (equal (fn-sn-tally-count (fn-sn-record-tally *srtt-3*)) 3)
                   (< 0 (fn-sn-tally-octets (fn-sn-record-tally *srtt-3*)))))
;; Established and preserved along it (fn-srt-initial-related, the io,
;; prepare and finish preservation, crash, recovery).
(assert-event (and (fn-srt-relatedp *srtt-initial*) (fn-srt-relatedp *srtt-1*)
                   (fn-srt-relatedp *srtt-2*) (fn-srt-relatedp *srtt-3*)
                   (fn-srt-relatedp *srtt-crashed*)
                   (fn-srt-relatedp *srtt-recovered*)
                   (not (member-eq (fn-sf-phase (fn-sn-files *srtt-recovered*))
                                   '(:replaying :fault)))))

;; KEYSTONE fn-srt-tally-is-the-fold (no hypothesis): the reachable history.
(assert-event
 (and (equal (fn-sn-tally-count (fn-sn-tally-of *srtt-records*)) (len *srtt-records*))
      (equal (fn-sn-tally-octets (fn-sn-tally-of *srtt-records*))
             (fn-sbud-record-octets *srtt-records*))
      (< 0 (fn-sbud-record-octets *srtt-records*))))

;; KEYSTONE fn-srt-carried-figures-are-the-kernel-figures.  Witness: the
;; Store after three commits and the recovered one; both hypotheses hold and
;; both figures agree, non-zero.
(assert-event
 (and (fn-srt-relatedp *srtt-3*)
      (not (member-eq (fn-sf-phase (fn-sn-files *srtt-3*)) '(:replaying :fault)))
      (equal (fn-sbud-carried-used *srtt-3*) (fn-sbud-used *srtt-3*))
      (equal (fn-sbud-carried-bytes *srtt-3*) (fn-sbud-bytes-used *srtt-3*))
      (equal (fn-sbud-carried-used *srtt-3*) 3)
      (equal (fn-sbud-carried-bytes *srtt-recovered*) (fn-sbud-bytes-used *srtt-recovered*))))
;; Without the relation (corrupted state: a stale tally on the ready Store):
;; the phase is served, the figures differ.
(defconst *srtt-stale* (fn-sn-with-record-tally *srtt-3* (cons 2 1)))
(assert-event
 (and (not (fn-srt-relatedp *srtt-stale*))
      (not (member-eq (fn-sf-phase (fn-sn-files *srtt-stale*)) '(:replaying :fault)))
      (not (equal (fn-sbud-carried-used *srtt-stale*) (fn-sbud-used *srtt-stale*)))
      (not (equal (fn-sbud-carried-bytes *srtt-stale*) (fn-sbud-bytes-used *srtt-stale*)))))
;; Without the phase condition (corrupted state: a replaying Store, which the
;; relation exempts, carrying a stale tally): related, figures differ.
(defconst *srtt-replaying-stale* (fn-sn-with-record-tally *srtt-crashed* nil))
(assert-event
 (and (fn-srt-relatedp *srtt-replaying-stale*)
      (equal (fn-sf-phase (fn-sn-files *srtt-replaying-stale*)) :replaying)
      (not (equal (fn-sbud-carried-used *srtt-replaying-stale*)
                  (fn-sbud-used *srtt-replaying-stale*)))))
(must-fail
 (defthm srtt-figures-without-the-relation
   (implies (not (member-eq (fn-sf-phase (fn-sn-files s)) '(:replaying :fault)))
            (equal (fn-sbud-carried-bytes s) (fn-sbud-bytes-used s)))))

;; fn-srt-carried-figures-are-a-valid-octet-cache.  Witness: the ready Store;
;; the status report's cache is the carried pair.
(assert-event
 (fn-sbud-octets-cache-validp
  (cons (fn-sbud-carried-used *srtt-3*) (fn-sbud-carried-bytes *srtt-3*))
  *srtt-records*))
;; Without the relation: the stale pair is not a valid cache.
(assert-event
 (not (fn-sbud-octets-cache-validp
       (cons (fn-sbud-carried-used *srtt-stale*) (fn-sbud-carried-bytes *srtt-stale*))
       *srtt-records*)))
;; Without the phase condition (corrupted state: a replaying Store with a
;; tally past its history): related, the pair is not a valid cache.
(defconst *srtt-replaying-long* (fn-sn-with-record-tally *srtt-crashed* (cons 5 0)))
(assert-event
 (and (fn-srt-relatedp *srtt-replaying-long*)
      (equal (fn-sf-phase (fn-sn-files *srtt-replaying-long*)) :replaying)
      (not (fn-sbud-octets-cache-validp
            (cons (fn-sbud-carried-used *srtt-replaying-long*)
                  (fn-sbud-carried-bytes *srtt-replaying-long*))
            (fn-sf-records (fn-sn-files *srtt-replaying-long*))))))
