(in-package "ACL2")
(include-book "../../books/feed-journal")
(include-book "must-fail-checked")

(defconst *fj-peer* '(105 110 110))
(defconst *fj-values* '((105 110 110) (60 97 64 102 110 62) 7))
(defconst *fj-protected*
  (fn-frame-protected *fn-feed-magic* *fn-frame-version* 1
    (fn-frame-fields-octets '(:text :text :nat) *fj-values*)))
(defconst *fj-frame* (append *fj-protected* (fn-blake3 *fj-protected*)))
(defconst *fj-prefix* (fn-cbor-u32-bytes (len *fj-frame*)))
(defun fj-frame-of (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((zeroes '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
         (unsigned (fn-feed-encode kind values zeroes))
         (prefix (fn-frame-protected-prefix unsigned)))
    (fn-feed-encode kind values (fn-blake3 prefix))))
(defmacro fn-feed-journal-test-scan ()
  '(fn-feed-journal-scan *fj-peer* *fj-prefix* *fj-frame* 99))

(assert-event (equal (car (fn-feed-journal-test-scan)) :next))
(assert-event (equal (cadr (fn-feed-journal-test-scan)) (+ 99 4 (len *fj-frame*))))
(assert-event (equal (caddr (fn-feed-journal-test-scan)) (list :feed-enqueue *fj-values*)))
(assert-event (equal (fn-feed-journal-wrap *fj-frame*)
                     (append *fj-prefix* *fj-frame*)))
(assert-event (equal (fn-feed-journal-prefix '(255 255 255 255)) :invalid))
(assert-event (equal (fn-feed-journal-prefix '(0 0 0 0)) :invalid))
(assert-event (equal (fn-feed-journal-prefix '(0 0)) :repair))
(assert-event (equal (fn-feed-journal-prefix nil) :end))
(assert-event (equal (fn-feed-journal-scan *fj-peer* *fj-prefix* '(70 78) 99)
                     '(:repair 99 nil)))
(assert-event (equal (fn-feed-journal-scan *fj-peer* '(0 0) nil 99)
                     '(:repair 99 nil)))
; Complete bad trailer and complete frame from another peer are evidence,
; never truncation authority. The valid prefix before them stays at 99.
(assert-event (equal (fn-feed-journal-scan *fj-peer* *fj-prefix*
                       (update-nth 12 255 *fj-frame*) 99) '(:invalid 99 nil)))
(assert-event (equal (fn-feed-journal-scan '(98) *fj-prefix* *fj-frame* 99)
                     '(:invalid 99 nil)))
;; A final outcome is a record and the scan advances over it.  An outcome
;; frame with a retry or loss code (the pre-6.6.0 journal's shape; this
;; release writes :feed-retry / :feed-lost with the tick, books/feed-events
;; fn-feed-observe-records) is complete, correctly sealed, and not a record:
;; the scan reports it :invalid at the last safe offset, never a truncation
;; and never a replayed record (no migrations: fresh deploys at 6.6.0).
(defconst *fj-final-values* (list *fj-peer* '(60 97 64 102 110 62) 1 239))
(defconst *fj-final-frame* (fj-frame-of :feed-outcome *fj-final-values*))
(assert-event
 (equal (car (fn-feed-journal-scan
              *fj-peer* (fn-cbor-u32-bytes (len *fj-final-frame*))
              *fj-final-frame* 99))
        :next))
(defun fj-raw-frame-of (kind values)
  ;; Sealed like the writer's frames, without fn-feed-encode's record check.
  (declare (xargs :guard t :verify-guards nil))
  (let ((protected (fn-frame-protected
                    *fn-feed-magic* *fn-frame-version*
                    (fn-frame-enum-index kind *fn-feed-kinds*)
                    (fn-frame-fields-octets
                     (fn-frame-spec-for kind *fn-feed-specs*) values))))
    (append protected (fn-blake3 protected))))
(assert-event (equal (fj-raw-frame-of :feed-outcome *fj-final-values*)
                     *fj-final-frame*))
(defmacro fj-legacy-scan (code)
  `(let ((frame (fj-raw-frame-of :feed-outcome
                                 (list *fj-peer* '(60 97 64 102 110 62) 1 ,code))))
     (fn-feed-journal-scan *fj-peer* (fn-cbor-u32-bytes (len frame)) frame 99)))
(assert-event (equal (fj-legacy-scan 431) '(:invalid 99 nil)))
(assert-event (equal (fj-legacy-scan 436) '(:invalid 99 nil)))
(assert-event (equal (fj-legacy-scan 400) '(:invalid 99 nil)))
; Teeth: drop :next from bounded-progress, EOF has no strict progress.
(must-fail-checked
 (assert-event (< 99 (cadr (fn-feed-journal-scan *fj-peer* nil nil 99)))))
; Drop :repair from preserved-offset: the live valid frame advances it.
(must-fail-checked (assert-event (equal (cadr (fn-feed-journal-test-scan)) 99)))

(defconst *fj-open-events*
  '(:opened :repair :truncated :content-durable :directory-durable :parent-durable))
(assert-event (equal (fn-feed-journal-phase-run :closed *fj-open-events*) :ready))
(assert-event (equal (fn-feed-journal-phase-run :ready
                      '(:append :written :append-durable)) :ready))
; A non-degenerate failure after a write stays fenced through an entire
; attempted reopen and a subsequent successful-looking append observation.
(assert-event (equal (fn-feed-journal-phase-run :ready
  (append '(:append :written :failed) *fj-open-events*
          '(:append :written :append-durable))) :uncertain))
; Every process cut in the host is an event position in these traces.
(defun fn-feed-journal-test-crash-cuts (phase events)
  (declare (xargs :measure (acl2-count events)))
  (if (atom events) t
    (let ((next (fn-feed-journal-phase-step phase (car events))))
      (and (equal (fn-feed-journal-phase-run next
                   (cons :crash (cdr events))) :uncertain)
           (fn-feed-journal-test-crash-cuts next (cdr events))))))
(assert-event (fn-feed-journal-test-crash-cuts :closed *fj-open-events*))
(assert-event (fn-feed-journal-test-crash-cuts :closed
  '(:opened :end :content-durable :directory-durable :parent-durable)))
(assert-event (fn-feed-journal-test-crash-cuts :ready '(:append :written :append-durable)))

; PKT-825a: fn-feed-journal-batch-is-durable-only-at-its-one-barrier.
; Positive witness, K = 3: the complete antecedent (posp 3) and both conjuncts.
(assert-event (posp 3))
(assert-event (equal (fn-feed-journal-batch-writes 3)
                     '(:append :written :append :written :append :written)))
(assert-event (equal (fn-feed-journal-phase-run :ready (fn-feed-journal-batch-writes 3))
                     :sync))
(assert-event (equal (fn-feed-journal-phase-run
                      :ready (append (fn-feed-journal-batch-writes 3) '(:append-durable)))
                     :ready))
; Hypothesis removal (posp k): K = 0 fails the hypothesis and the first
; conjunct (no write, still :ready, not :sync).
(assert-event (not (posp 0)))
(must-fail-checked
 (assert-event (equal (fn-feed-journal-phase-run :ready (fn-feed-journal-batch-writes 0))
                      :sync)))
; The conclusion can fail: without its barrier the batch is not durable, and
; a failed write inside the batch fences the journal even after a barrier.
(assert-event (not (equal (fn-feed-journal-phase-run :ready (fn-feed-journal-batch-writes 3))
                          :ready)))
(assert-event (equal (fn-feed-journal-phase-run :ready
                      '(:append :written :append :failed :append-durable))
                     :uncertain))
; A barrier is still owed while :sync: a :sync journal is never :ready by
; any event but its barrier.
(must-fail-checked
 (assert-event (equal (fn-feed-journal-phase-step :sync :written) :ready)))
; Every cut inside a batch is a crash point: a crash there fences the journal.
(assert-event (fn-feed-journal-test-crash-cuts :ready
  (append (fn-feed-journal-batch-writes 3) '(:append-durable))))
