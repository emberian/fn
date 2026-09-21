(in-package "ACL2")
(include-book "../../books/feed-journal")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fj-peer* '(105 110 110))
(defconst *fj-values* '((105 110 110) (60 97 64 102 110 62) 7))
(defconst *fj-protected*
  (fn-frame-protected *fn-feed-magic* *fn-frame-version* 1
    (fn-frame-fields-octets '(:text :text :nat) *fj-values*)))
(defconst *fj-frame* (append *fj-protected* (fn-sha256 *fj-protected*)))
(defconst *fj-prefix* (fn-cbor-u32-bytes (len *fj-frame*)))
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
; Teeth: drop :next from bounded-progress, EOF has no strict progress.
(must-fail
 (assert-event (< 99 (cadr (fn-feed-journal-scan *fj-peer* nil nil 99)))))
; Drop :repair from preserved-offset: the live valid frame advances it.
(must-fail (assert-event (equal (cadr (fn-feed-journal-test-scan)) 99)))

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
