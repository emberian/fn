; Witnesses and teeth for books/store-compact-window (PKT-686 item 2): each
; keystone's reachable witness over the five-event history
; store-compact-verb-tests uses, and per hypothesis a counterexample where
; the other holds and the conclusion fails, with the must-fail of the
; keystone without it.
(in-package "ACL2")
(include-book "../../books/store-compact-window")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

(defconst *cwt-a0*
  (fn-record-make 0 0 0 "<compact@example.invalid>" '(65 13 10)
                  '("fn.letters") "archive-0" "subject-0" "evidence-0" 3 841000000))
(defconst *cwt-e1*
  (fn-store-retention-event-make :undertake 1 1 1
                                 "forward-1" "subject-1" "evidence-1" 2))
(defconst *cwt-e2*
  (fn-store-retention-event-make :release 2 2 2
                                 "forward-1" "subject-1" "receipt-1" 0))
(defconst *cwt-i3*
  (fn-stxe-make 3 3 3 "<compact@example.invalid>" :unverified
                '(117 110 118 101 114 105 102 105 101 100) 7 '(116 101 115 116)))
(defconst *cwt-k4*
  (fn-stxk-make 4 4 4 7 '(116 101 115 116) '(1 2 3 4)))
(make-event `(defconst *cwt-records*
               ',(list (fn-store-event-encode *cwt-a0*)
                       (fn-store-event-encode *cwt-e1*)
                       (fn-store-event-encode *cwt-e2*)
                       (fn-store-event-encode *cwt-i3*)
                       (fn-store-event-encode *cwt-k4*))))
(make-event `(defconst *cwt-names*
               ',(list (fn-bs-txn-name 0) (fn-bs-txn-name 1) (fn-bs-txn-name 2)
                       (fn-bs-txn-name 3) (fn-bs-txn-name 4))))
(defconst *cwt-dev* *fn-bs-profile-development*)
(defconst *cwt-disk* 1000000)

; fn-scw-window-count-is-fit (no hypothesis): the count from the lengths is
; the fit, from the start and from the middle; the lengths are small
; naturals, one per record.
(assert-event (equal (fn-scw-lens *cwt-records*)
                     (list (len (nth 0 *cwt-records*)) (len (nth 1 *cwt-records*))
                           (len (nth 2 *cwt-records*)) (len (nth 3 *cwt-records*))
                           (len (nth 4 *cwt-records*)))))
(assert-event (equal (fn-scw-window-count (fn-scw-lens *cwt-records*) 0) 5))
(assert-event (equal (fn-scw-window-count (fn-scw-lens *cwt-records*) 0)
                     (fn-ccc-fit *cwt-records*)))
(assert-event (equal (fn-scw-window-count (fn-scw-lens *cwt-records*) 2)
                     (fn-ccc-fit (nthcdr 2 *cwt-records*))))
(assert-event (equal (fn-scw-window-count (fn-scw-lens *cwt-records*) 5) 0))
; The fit's event bound: 5,000 one-octet records take 4,096.
(assert-event (equal (fn-scw-window-count (make-list 5000 :initial-element 1) 0) 4096))
; The octet bound: two records of 3 MiB take one link each; one record over
; 4 MiB still takes one (the fit is at least 1).
(assert-event (equal (fn-scw-window-count (list 3145728 3145728) 0) 1))
(assert-event (equal (fn-scw-window-count (list 5242880 1) 0) 1))

; -----------------------------------------------------------------------------
; fn-cverb-decide-window-is-cverb-decide.  The witness: every hypothesis
; and the conclusion, a fresh store packing from 0 and one resuming from 2.
(assert-event (equal (fn-cverb-decide-window *cwt-dev* 5 0 (fn-scw-window *cwt-records* 0)
                                             *cwt-names* nil nil *cwt-disk*)
                     (list :compact *fn-cverb-pack-steps*)))
(assert-event (equal (fn-cverb-decide-window *cwt-dev* 5 0 (fn-scw-window *cwt-records* 0)
                                             *cwt-names* nil nil *cwt-disk*)
                     (fn-cverb-decide *cwt-dev* *cwt-records* 0 *cwt-names* nil nil
                                      *cwt-disk*)))
(assert-event (equal (fn-cverb-decide-window *cwt-dev* 5 2 (fn-scw-window *cwt-records* 2)
                                             *cwt-names* nil nil *cwt-disk*)
                     (fn-cverb-decide *cwt-dev* *cwt-records* 2 *cwt-names* nil nil
                                      *cwt-disk*)))

; Without USED = (len RECORDS): a length of 3 read at lower 3 is covered
; history (resume), where the five records still need a pack.
(assert-event (equal (fn-scw-window *cwt-records* 3) (nthcdr 3 *cwt-records*)))
(assert-event (not (equal (fn-cverb-decide-window *cwt-dev* 3 3 (fn-scw-window *cwt-records* 3)
                                                  *cwt-names* nil nil *cwt-disk*)
                          (fn-cverb-decide *cwt-dev* *cwt-records* 3 *cwt-names* nil nil
                                           *cwt-disk*))))
(must-fail
 (defthm cwt-decide-without-used
   (implies (equal window (fn-scw-window records lower))
            (equal (fn-cverb-decide-window profile used lower window names generations
                                           selected disk-free)
                   (fn-cverb-decide profile records lower names generations selected
                                    disk-free)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-cverb-decide fn-cverb-decide-window
                                         fn-cverb-link-octets-of-window)
                                       (theory 'minimal-theory))))))

; Without WINDOW = the fit: an empty window on a disk one octet short of
; the real link admits the link the real window refuses.
(defconst *cwt-short* (1- (fn-cverb-link-octets *cwt-records* 0)))
(assert-event (equal (fn-cverb-decide *cwt-dev* *cwt-records* 0 *cwt-names* nil nil
                                      *cwt-short*)
                     '(:refused :temporary-space)))
(assert-event (equal (fn-cverb-decide-window *cwt-dev* 5 0 nil *cwt-names* nil nil
                                             *cwt-short*)
                     (list :compact *fn-cverb-pack-steps*)))
(must-fail
 (defthm cwt-decide-without-window
   (implies (equal used (len records))
            (equal (fn-cverb-decide-window profile used lower window names generations
                                           selected disk-free)
                   (fn-cverb-decide profile records lower names generations selected
                                    disk-free)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-cverb-decide fn-cverb-decide-window
                                         fn-cverb-link-octets-of-window)
                                       (theory 'minimal-theory))))))

; -----------------------------------------------------------------------------
; fn-ccc-capture-link-window-is-capture-link.  The witness: the first link
; over the whole history, and a link from 2 with a predecessor.
(assert-event (equal (car (fn-ccc-capture-link-window 5 (fn-scw-window *cwt-records* 0)
                                                      0 0 0 nil))
                     :ok))
(assert-event (equal (fn-ccc-capture-link-window 5 (fn-scw-window *cwt-records* 0) 0 0 0 nil)
                     (fn-ccc-capture-link *cwt-records* 0 0 0 nil)))
(assert-event (equal (fn-ccc-capture-link-window 5 (fn-scw-window *cwt-records* 2) 2 3 0
                                                 '(1 2 3))
                     (fn-ccc-capture-link *cwt-records* 2 3 0 '(1 2 3))))
; The covered history is the named no-op on both.
(assert-event (equal (fn-ccc-capture-link-window 5 (fn-scw-window *cwt-records* 5) 5 6 0 nil)
                     '(:nothing-uncovered 5)))

; Without USED = (len RECORDS): at lower 5 a length of 10 is not the no-op.
(assert-event (not (equal (fn-ccc-capture-link-window 10 (fn-scw-window *cwt-records* 5)
                                                      5 6 0 nil)
                          (fn-ccc-capture-link *cwt-records* 5 6 0 nil))))
(must-fail
 (defthm cwt-capture-without-used
   (implies (equal window (fn-scw-window records lower))
            (equal (fn-ccc-capture-link-window used window lower lower-frontier
                                               pred-generation pred-digest)
                   (fn-ccc-capture-link records lower lower-frontier pred-generation
                                        pred-digest)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-ccc-capture-link fn-scw-window)
                            (fn-ccc-make fn-ccc-linkp fn-ccc-event-txid fn-ccc-fit))))))

; Without WINDOW = the fit: a window of the first record alone captures a
; link covering one event, where the fit covers five.
(assert-event (not (equal (fn-ccc-capture-link-window 5 (take 1 *cwt-records*) 0 0 0 nil)
                          (fn-ccc-capture-link *cwt-records* 0 0 0 nil))))
(must-fail
 (defthm cwt-capture-without-window
   (implies (equal used (len records))
            (equal (fn-ccc-capture-link-window used window lower lower-frontier
                                               pred-generation pred-digest)
                   (fn-ccc-capture-link records lower lower-frontier pred-generation
                                        pred-digest)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-ccc-capture-link fn-scw-window)
                            (fn-ccc-make fn-ccc-linkp fn-ccc-event-txid fn-ccc-fit))))))
