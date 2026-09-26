; fn: the cheaper committed-history marker programs PKT-079 and PKT-143
; allowed, each stated as a constructor beside fn-bs-marker-program's
; contract, and each REFUSED by the theorems that contract rests on (lane
; publish-program, planning/evidence/publish-program-2026-09-26.md).
;
; The frozen guarantee is D31's A <= M <= D at every cut: A the prefix
; covered by success answers, M the durable marker's count, D the durable
; reconstructable length.  A served commit makes seven barriers
; (host/native/io.lisp: the frontier's stage and root, the record's stage,
; transactions directory and staging directory, the marker's stage and root).
; The marker's two are its stage's fence (the content, fn-bs-fsync-file
; drains exactly that inode) and the root's (the entry, before the
; acknowledgement).  Three candidates take one of them away:
;
;   1. fn-bs-marker-unfenced-program: the stage's fence folded into the
;      record's staging barrier.  A fence drains ONE inode and the marker's
;      stage is not the record's, so "folded" means unfenced.  The model's
;      discipline D1 rejects the program (a rename of an unfenced source),
;      and a crash image after its root barrier may hold ANY octets in the
;      marker's place (a garbled unit, fn-bs-tear-write): the open refuses a
;      store that lost nothing, :marker-damaged or :history-short-of-marker
;      at whatever count the garble spells.  Keystone 1 (every crash image
;      admitted) fails; the tests hold the refuting images.
;   2. fn-bs-marker-in-place-program: one overwrite of committed-history.json
;      and one fsync of it (the marker-required design's option 3 with one
;      slot).  Discipline D2 rejects it (an overwrite under an authority
;      directory), and the garble at marker-written refutes keystone 1 the
;      same way.  A second slot does not help: the pending slot's garble may
;      spell a count above the history, and the model has no digest
;      assumption to exclude it.
;   3. The deferred marker: commit n's marker renamed under commit n+1's
;      reservation, one root barrier for both, the acknowledgement of n
;      before it.  Stated in the history model as fn-hmr-deferred-commit,
;      the step that answers success for record n while the marker still
;      counts n.  It leaves fn-hmr-invp (A <= M fails); the open at the old
;      count then ADMITS, although a client holds a 240 for a record above
;      it; and D31's catch-up writes nothing, since the marker already
;      covers the shortened history.  Keystone 2
;      (fn-hmr-open-refuses-below-every-answered-record) does not survive
;      the step, and case (2) of D31 does not cover it.
;
; What is left is a sharing that keeps every barrier's order: the NEXT
; reservation's frontier renamed under commit n's marker barrier, before
; the acknowledgement.  That moves the reservation into the completion
; window, which the file kernel's phases and the K0 relation
; (books/byte-store-scan.lisp fn-bs-store-relation: fn-sf-crash-imagep over
; the durable frontier, and fn-bs-pending-matches-phase over one root entry)
; do not admit today; it is a kernel and K0 change, named in the record as
; PKT-441, and not a program of this book.  fn-bs-marker-program stays the
; served program and the specification.
(in-package "ACL2")
(include-book "byte-store-marker-program")
(include-book "store-history-required")

; -----------------------------------------------------------------------------
; Candidate 1: the stage unfenced.  The cut names are the served program's
; without marker-staged-durable.

(defun fn-bs-marker-unfenced-program (stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)
        (list :cut "marker-created")
        (list :write-all :staging stage octets)
        (list :cut "marker-written")
        (list :rename :staging stage :root *fn-bs-history-marker-name*)
        (list :cut "marker-replaced")
        (list :fsync-dir :root)
        (list :cut "marker-durable")))

(defconst *fn-bs-p-marker-unfenced* (fn-bs-marker-unfenced-program ".stage-marker-1" '(1)))
(assert-event (fn-bs-step-listp *fn-bs-p-marker-unfenced*))
; D1 refuses it: the rename's source was written and never fenced.
(assert-event (not (fn-bs-links-only-fencedp *fn-bs-p-marker-unfenced*)))
(assert-event (fn-bs-never-overwrites-authorityp *fn-bs-p-marker-unfenced*))
(assert-event (fn-bs-fences-authority-dirsp *fn-bs-p-marker-unfenced*))

; -----------------------------------------------------------------------------
; Candidate 2: one in-place overwrite, one fence.

(defun fn-bs-marker-in-place-program (octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :write-all :root *fn-bs-history-marker-name* octets)
        (list :cut "marker-written")
        (list :fsync-file :root *fn-bs-history-marker-name*)
        (list :cut "marker-durable")))

(defconst *fn-bs-p-marker-in-place* (fn-bs-marker-in-place-program '(1)))
(assert-event (fn-bs-step-listp *fn-bs-p-marker-in-place*))
(assert-event (fn-bs-links-only-fencedp *fn-bs-p-marker-in-place*))
; D2 refuses it: a :write-all under an authority directory.
(assert-event (not (fn-bs-never-overwrites-authorityp *fn-bs-p-marker-in-place*)))
(assert-event (fn-bs-fences-authority-dirsp *fn-bs-p-marker-in-place*))

; The served program passes all three, as byte-store-marker-program asserts;
; restated here beside the refusals.
(assert-event (and (fn-bs-links-only-fencedp *fn-bs-p-marker*)
                   (fn-bs-never-overwrites-authorityp *fn-bs-p-marker*)
                   (fn-bs-fences-authority-dirsp *fn-bs-p-marker*)))

; -----------------------------------------------------------------------------
; Candidate 3: the deferred marker, in the history model of
; books/store-history-required.lisp.  In a live process, record COUNT is
; durable and the node answers success (A covers it) while the marker is
; left for the next reservation's barrier; the process stays live.  A
; process that is not live cannot answer.

(defun fn-hmr-deferred-commit (st)
  (declare (xargs :guard t :verify-guards nil))
  (let ((count (fn-hmr-count st)) (marker (nth 1 st))
        (acked (nfix (nth 2 st))) (profile (nth 3 st)) (live (nth 4 st)))
    (if (not live)
        st
      (fn-hmr-state (1+ count) marker (max acked (1+ count)) profile t))))

(local (in-theory (enable fn-hmr-invp fn-hmr-count fn-hmr-marker-count fn-hmr-state
                          fn-hmr-coveringp fn-hmr-open-verdict fn-hmr-catch-up
                          fn-hm-open-verdict)))
(local (in-theory (disable fn-hm-decode fn-hm-encode fn-bs-profile-marker-requiredp
                           fn-hm-after-commit (:e fn-hm-decode) (:e fn-hm-encode))))

; A covering marker is present and counts exactly the history.
(local
 (defthm fn-hmr-cand-covering-means
   (implies (fn-hmr-coveringp obs k)
            (and (natp k) (consp obs) (equal (car obs) :present)
                 (consp (cdr obs)) (null (cddr obs))
                 (equal (fn-hm-decode (cadr obs)) k)
                 (equal (fn-hmr-marker-count obs) k)))
   :rule-classes nil))

; The step leaves the invariant: after it, A = COUNT + 1 while M = COUNT.
(defthm fn-hmr-deferred-commit-leaves-the-invariant
  (implies (and (fn-hmr-invp st) (nth 4 st))
           (not (fn-hmr-invp (fn-hmr-deferred-commit st))))
  :hints (("Goal" :use ((:instance fn-hmr-cand-covering-means
                                   (obs (nth 1 st)) (k (fn-hmr-count st)))))))

; The open at the old count admits, although a client holds a success answer
; for the record above it: the negation of keystone 2's conclusion at K =
; COUNT, which is below A.
(defthm fn-hmr-deferred-commit-admits-a-lost-answered-record
  (implies (and (fn-hmr-invp st) (nth 4 st))
           (let ((end (fn-hmr-deferred-commit st)) (k (fn-hmr-count st)))
             (and (natp k)
                  (< k (nfix (nth 2 end)))
                  (equal (fn-hmr-open-verdict (nth 3 end) (nth 1 end) k)
                         (list :admitted :marked k)))))
  :hints (("Goal" :use ((:instance fn-hmr-cand-covering-means
                                   (obs (nth 1 st)) (k (fn-hmr-count st)))))))

; D31 case (2) does not cover it: the next open's catch-up, over the
; shortened history (the newest record lost, D back to COUNT), writes
; nothing, because the marker already covers COUNT.
(defthm fn-hmr-deferred-commit-is-not-caught-up
  (implies (and (fn-hmr-invp st) (nth 4 st))
           (let ((end (fn-hmr-deferred-commit st)))
             (equal (fn-hmr-catch-up (nth 3 end) (nth 1 end) (fn-hmr-count st))
                    nil)))
  :hints (("Goal" :use ((:instance fn-hmr-cand-covering-means
                                   (obs (nth 1 st)) (k (fn-hmr-count st)))))))

(in-theory (disable fn-bs-marker-unfenced-program fn-bs-marker-in-place-program
                    fn-hmr-deferred-commit))
