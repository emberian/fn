; Real syscall failures followed by the host's classified error observation.
; The concrete metadata seam supplies executable, nondegenerate witnesses.
(in-package "ACL2")
(include-book "byte-store-relation-tests")
(include-book "../../books/byte-store-program-invariants")
(include-book "../../books/codec-attach")

(defun fn-bs-test-failure-outcomes (index outcome)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp index) (list outcome)
    (cons :ok (fn-bs-test-failure-outcomes (1- index) outcome))))

(defun fn-bs-test-frontier-failure-run (index outcome)
  (fn-bs-run (fn-bs-initial-image 4 (fn-bs-test-config) (fn-bs-test-frontier))
             (fn-sf-initial-state)
             (fn-bs-frontier-program ".allocation-test" (fn-bs-test-next))
             (fn-bs-test-failure-outcomes index outcome) nil nil))

(defun fn-bs-test-observe (pair event)
  (mv-let (r bs ks)
    (fn-bs-step (car pair) (cdr pair) (list :observe event) :ok nil nil)
    (declare (ignore r))
    (cons bs ks)))

(assert-event
 (let ((bs (fn-bs-initial-image 4 (fn-bs-test-config) (fn-bs-test-frontier))))
   (and (fn-bs-store-relation bs (fn-sf-initial-state))
        (fn-bs-authority-knownp bs)
        (not (member-equal (fn-bs-next-ino bs) (fn-bs-authority-inode-list bs)))
        (equal (fn-bs-ops-for-dir (fn-bs-pending bs) :root) nil)
        (equal (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions) nil))))

; Pin the syscall positions used below to the transcribed program.
(assert-event
 (let ((program (fn-bs-frontier-program ".allocation-test" (fn-bs-test-next))))
   (and (equal (car (nth 3 program)) :write-all)
        (equal (car (nth 5 program)) :fsync-file)
        (equal (car (nth 8 program)) :rename)
        (equal (nth 12 program) '(:fsync-dir :root)))))

; One-octet short write then ENOSPC: no rename can have run. The runner
; stops at that write, and the host's known-fail observation returns ready.
(assert-event
 (let* ((run (fn-bs-test-frontier-failure-run 3 '(:enospc . 1)))
        (pair (car (last run)))
        (after (fn-bs-test-observe pair '(:frontier-file :known-fail))))
   (and (equal (len run) 4)
        (fn-bs-run-relatedp run)
        (equal (fn-sf-phase (cdr pair)) :frontier-staged)
        (equal (fn-sf-phase (cdr after)) :ready)
        (fn-bs-store-relation (car after) (cdr after))
        (equal (fn-bs-durable-frontier (car after)) 0))))

; fsync fails after a torn/zero unit. The failed inode is private staging;
; no retry or later rename is executed. The same known-fail arm applies.
(assert-event
 (let* ((run (fn-bs-test-frontier-failure-run 5 '(:eio (:zero))))
        (pair (car (last run)))
        (after (fn-bs-test-observe pair '(:frontier-file :known-fail))))
   (and (equal (len run) 6)
        (fn-bs-run-relatedp run)
        (not (equal (fn-bs-durable-content (car pair) 2) (fn-bs-test-next)))
        (equal (fn-sf-phase (cdr after)) :ready)
        (fn-bs-store-relation (car after) (cdr after)))))

; A rename can report EIO after issue. The callback fences the kernel;
; it cannot turn the visible replacement into a known refusal.
(assert-event
 (let* ((run (fn-bs-test-frontier-failure-run 8 '(:eio . :issued)))
        (pair (car (last run)))
        (after (fn-bs-test-observe pair '(:frontier-replace :error))))
   (and (equal (len run) 9)
        (fn-bs-run-relatedp run)
        (equal (fn-sf-phase (cdr after)) :fenced-frontier)
        (fn-bs-store-relation (car after) (cdr after))
        (equal (fn-bs-durable-frontier (car after)) 0)
        (equal (fn-bs-scan-frontier (fn-bs-scan-store (car after))) 1))))

; Both legal directory-fsync failure outcomes are live. The pending rename
; is drained/discarded, and the error callback fences the process in either
; case; the durable byte frontier is genuinely different between the cases.
(assert-event
 (let* ((old-run (fn-bs-test-frontier-failure-run 12 '(:eio :drop)))
        (new-run (fn-bs-test-frontier-failure-run 12 '(:eio :apply)))
        (old (fn-bs-test-observe (car (last old-run)) '(:frontier-dir :error)))
        (new (fn-bs-test-observe (car (last new-run)) '(:frontier-dir :error))))
   (and (equal (len old-run) 13) (equal (len new-run) 13)
        (fn-bs-run-relatedp old-run) (fn-bs-run-relatedp new-run)
        (fn-bs-store-relation (car old) (cdr old))
        (fn-bs-store-relation (car new) (cdr new))
        (equal (fn-sf-phase (cdr old)) :fenced-frontier)
        (equal (fn-sf-phase (cdr new)) :fenced-frontier)
        (equal (fn-bs-durable-frontier (car old)) 0)
        (equal (fn-bs-durable-frontier (car new)) 1))))

(assert-event (fn-bs-frontier-noncommit-observationp '(:frontier-dir :error)))
; The relation premise of the actual-step observation theorem is necessary.
(must-fail
 (assert-event
  (let* ((pair (cons (fn-bs-initial-image 4 nil (fn-bs-test-frontier))
                     (fn-sf-initial-state)))
         (after (fn-bs-test-observe pair '(:start-frontier))))
    (fn-bs-store-relation (car after) (cdr after)))))
; The event-domain premise is necessary: announcing directory success BEFORE
; the real fence lets the kernel reserve a frontier that can still disappear.
(must-fail
 (assert-event
  (let* ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                      ".allocation-test" (fn-bs-test-next)))
         (after (fn-bs-test-observe (nth 11 run) '(:frontier-dir :ok))))
    (fn-bs-store-relation (car after) (cdr after)))))

; After the actual successful root fence, the commit observation is valid.
(assert-event
 (let* ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                     ".allocation-test" (fn-bs-test-next)))
        (pair (nth 13 run))
        (after (fn-bs-test-observe pair '(:frontier-dir :ok))))
   (and (fn-bs-store-relation (car pair) (cdr pair))
        (equal (fn-sf-phase (cdr pair)) :frontier-attempted)
        (fn-bs-frontier-directory-committedp (car pair) (cdr pair))
        (fn-bs-store-relation (car after) (cdr after))
        (equal (fn-sf-phase (cdr after)) :reserved))))

; Fresh allocation needs the relation's allocation invariant. Reusing 0
; aliases the real config inode while keeping its nonempty metadata bytes.
(must-fail
 (assert-event
  (let* ((bs (fn-bs-initial-image 4 (fn-bs-test-config) (fn-bs-test-frontier)))
         (bad (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                          (fn-bs-pending bs) 0)))
    (not (member-equal (fn-bs-next-ino bad) (fn-bs-authority-inode-list bad))))))

; The :ready hypothesis of authority quietness is necessary at the real
; post-rename cut; dropping the relation permits that byte image to be
; paired incorrectly with a :ready kernel as well.
(must-fail
 (assert-event
  (let* ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                      ".allocation-test" (fn-bs-test-next)))
         (pair (nth 9 run)))
    (and (equal (fn-bs-ops-for-dir (fn-bs-pending (car pair)) :root) nil)
         (equal (fn-bs-ops-for-dir (fn-bs-pending (car pair)) :transactions) nil)))))
(must-fail
 (assert-event
  (let* ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                      ".allocation-test" (fn-bs-test-next)))
         (bs (car (nth 9 run))))
    (implies (equal (fn-sf-phase (fn-sf-initial-state)) :ready)
             (and (equal (fn-bs-ops-for-dir (fn-bs-pending bs) :root) nil)
                  (equal (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions) nil))))))

; Commit observation: one independent must-fail per hypothesis.
; No relation: malformed config, but the attempted phase and committed
; frontier (quiet root, candidate bytes durable) both hold.
(must-fail
 (assert-event
  (let* ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                      ".allocation-test" (fn-bs-test-next)))
         (ks (cdr (nth 13 run)))
         (bs (fn-bs-initial-image 4 nil (fn-bs-test-next)))
         (after (fn-sf-frontier-dir-result ks :ok)))
    (and (fn-bs-store-relation bs after) (equal (fn-sf-phase after) :reserved)))))
; No phase premise: a commit observation cannot skip the replace observation.
(must-fail
 (assert-event
  (let* ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                      ".allocation-test" (fn-bs-test-next)))
         (bs (car (nth 13 run)))
         (ks (cdr (nth 7 run)))
         (after (fn-sf-frontier-dir-result ks :ok)))
    (and (fn-bs-store-relation bs after) (equal (fn-sf-phase after) :reserved)))))
; No byte commit: the real attempted state before the root fence.
(must-fail
 (assert-event
  (let* ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                      ".allocation-test" (fn-bs-test-next)))
         (pair (nth 11 run))
         (after (fn-sf-frontier-dir-result (cdr pair) :ok)))
    (and (fn-bs-store-relation (car pair) after)
         (equal (fn-sf-phase after) :reserved)))))

(assert-event
 (let* ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                     ".allocation-test" (fn-bs-test-next)))
        (committed (car (nth 13 run)))
        (attempted (cdr (nth 13 run)))
        (data-durable (cdr (nth 7 run)))
        (bad-config (fn-bs-initial-image 4 nil (fn-bs-test-next)))
        (pending (car (nth 11 run))))
   (and (equal (fn-sf-phase attempted) :frontier-attempted)
        (fn-bs-frontier-directory-committedp bad-config attempted)
        (not (fn-bs-store-relation bad-config attempted))
        (fn-bs-store-relation committed data-durable)
        (fn-bs-frontier-directory-committedp committed data-durable)
        (not (equal (fn-sf-phase data-durable) :frontier-attempted))
        (fn-bs-store-relation pending attempted)
        (not (fn-bs-frontier-directory-committedp pending attempted)))))
