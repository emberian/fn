; Shared bounded barrier leaves. Actual READ/successor/sealer constructors own
; endpoint geometry and retain the returned serial in their real continuation.
; The writer constructor binds the actual HELD snapshot token and both cuts.
(in-package "ACL2")
(include-book "c-source-observer-state")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :c)

(defun fn2-c-source-reader-acquire (endpoint expected-receipt fn2-c-source-control fn2-c-source-readers)
 (declare (xargs :stobjs (fn2-c-source-control fn2-c-source-readers)
  :guard (and (fn2-c-source-control-wfp fn2-c-source-control) (fn2-c-source-readers-wfp fn2-c-source-readers))))
 (b* (((unless (and (< 0 (fn2-c-source-control-rows fn2-c-source-control))
                    (natp endpoint) (< endpoint (fn2-c-source-readers-rows fn2-c-source-readers))))
       (mv :bounds 0 fn2-c-source-control fn2-c-source-readers))
      ((when (equal (fn2-c-source-readers-live endpoint fn2-c-source-readers) 1))
       (mv (if (fn2-c-source-reader-current-p endpoint expected-receipt fn2-c-source-readers) :ok :stale)
           (if (fn2-c-source-reader-current-p endpoint expected-receipt fn2-c-source-readers) expected-receipt 0)
           fn2-c-source-control fn2-c-source-readers))
      ((unless (equal expected-receipt 0)) (mv :stale 0 fn2-c-source-control fn2-c-source-readers))
      ((unless (equal (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-idle*))
       (mv :busy 0 fn2-c-source-control fn2-c-source-readers))
      (receipt (+ 1 (fn2-c-source-control-next-receipt 0 fn2-c-source-control)))
      (count (+ 1 (fn2-c-source-control-readers 0 fn2-c-source-control)))
      ((unless (and (unsigned-byte-p 60 receipt) (unsigned-byte-p 32 count)
                    (<= count (fn2-c-source-readers-rows fn2-c-source-readers))))
       (mv :exhausted 0 fn2-c-source-control fn2-c-source-readers))
      (fn2-c-source-readers (fn2-c-source-readers-put endpoint `((live 1) (serial ,receipt)) fn2-c-source-readers))
      (fn2-c-source-control (fn2-c-source-control-put 0 `((readers ,count) (next-receipt ,receipt)) fn2-c-source-control)))
  (mv :ok receipt fn2-c-source-control fn2-c-source-readers)))

(defun fn2-c-source-reader-release (endpoint receipt fn2-c-source-control fn2-c-source-readers)
 (declare (xargs :stobjs (fn2-c-source-control fn2-c-source-readers)
  :guard (and (fn2-c-source-control-wfp fn2-c-source-control) (fn2-c-source-readers-wfp fn2-c-source-readers))))
 (b* (((unless (and (< 0 (fn2-c-source-control-rows fn2-c-source-control))
                    (natp endpoint) (< endpoint (fn2-c-source-readers-rows fn2-c-source-readers))))
       (mv :bounds *fn2-none* 0 fn2-c-source-control fn2-c-source-readers))
      ((unless (fn2-c-source-reader-current-p endpoint receipt fn2-c-source-readers))
       (mv :stale *fn2-none* 0 fn2-c-source-control fn2-c-source-readers))
      ((unless (posp (fn2-c-source-control-readers 0 fn2-c-source-control)))
       (mv :invariant *fn2-none* 0 fn2-c-source-control fn2-c-source-readers))
      (count (- (fn2-c-source-control-readers 0 fn2-c-source-control) 1))
      (wake (and (equal count 0)
                 (equal (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-pending*)))
      (target (if wake (fn2-c-source-control-writer-owner 0 fn2-c-source-control) *fn2-none*))
      (targetgen (if wake (fn2-c-source-control-writer-gen 0 fn2-c-source-control) 0))
      (fn2-c-source-readers (fn2-c-source-readers-put endpoint '((live 0) (serial 0)) fn2-c-source-readers))
      (fn2-c-source-control (fn2-c-source-control-put 0 `((readers ,count)
        (wake-pending ,(if wake 1 (fn2-c-source-control-wake-pending 0 fn2-c-source-control)))) fn2-c-source-control)))
  (mv :ok target targetgen fn2-c-source-control fn2-c-source-readers)))

(defun fn2-c-source-writer-poll (kind owner gen token cutcommit cutevent fn2-c-source-control)
 (declare (xargs :stobjs fn2-c-source-control :guard (fn2-c-source-control-wfp fn2-c-source-control)))
 (cond ((not (fn2-c-source-writer-receipt-p kind owner gen token cutcommit cutevent fn2-c-source-control))
        (mv :owner fn2-c-source-control))
       ((equal (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-uncertain*)
        (mv :uncertain fn2-c-source-control))
       ((equal (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-exclusive*)
        (mv (if (equal (fn2-c-source-control-readers 0 fn2-c-source-control) 0) :exclusive :invariant) fn2-c-source-control))
       ((not (equal (fn2-c-source-control-readers 0 fn2-c-source-control) 0))
        (mv :waiting fn2-c-source-control))
       (t (let ((fn2-c-source-control (fn2-c-source-control-put 0
                  `((phase ,*fn2-c-source-writer-phase-exclusive*) (wake-pending 0)) fn2-c-source-control)))
            (mv :exclusive fn2-c-source-control)))))

(defun fn2-c-source-writer-begin (kind owner gen token cutcommit cutevent fn2-c-source-control)
 (declare (xargs :stobjs fn2-c-source-control :guard (fn2-c-source-control-wfp fn2-c-source-control)))
 (cond ((not (and (< 0 (fn2-c-source-control-rows fn2-c-source-control))
                  (unsigned-byte-p 8 kind) (unsigned-byte-p 32 owner)
                  (unsigned-byte-p 60 gen) (posp gen) (unsigned-byte-p 60 token) (posp token)
                  (unsigned-byte-p 60 cutcommit) (unsigned-byte-p 60 cutevent)))
        (mv :bounds fn2-c-source-control))
       ((fn2-c-source-writer-receipt-p kind owner gen token cutcommit cutevent fn2-c-source-control)
        (fn2-c-source-writer-poll kind owner gen token cutcommit cutevent fn2-c-source-control))
       ((not (equal (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-idle*))
        (mv :busy fn2-c-source-control))
       (t (let ((fn2-c-source-control (fn2-c-source-control-put 0
                  `((phase ,*fn2-c-source-writer-phase-pending*) (writer-kind ,kind) (writer-owner ,owner)
                    (writer-gen ,gen) (writer-token ,token) (cut-commit ,cutcommit) (cut-event ,cutevent)
                    (wake-pending 0)) fn2-c-source-control)))
            (fn2-c-source-writer-poll kind owner gen token cutcommit cutevent fn2-c-source-control)))))

; Cancellation is only PENDING: after exclusive replacement starts, the real
; typed adopter must either prove terminal publication or retain uncertainty.
(defun fn2-c-source-writer-abort-pending (kind owner gen token cutcommit cutevent fn2-c-source-control)
 (declare (xargs :stobjs fn2-c-source-control :guard (fn2-c-source-control-wfp fn2-c-source-control)))
 (if (and (fn2-c-source-writer-receipt-p kind owner gen token cutcommit cutevent fn2-c-source-control)
          (equal (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-pending*))
     (let ((fn2-c-source-control (fn2-c-source-control-put 0
             `((phase ,*fn2-c-source-writer-phase-idle*) (writer-kind 0) (writer-owner 0) (writer-gen 0)
               (writer-token 0) (cut-commit 0) (cut-event 0) (wake-pending 0)) fn2-c-source-control)))
       (mv :aborted fn2-c-source-control))
   (mv :owner fn2-c-source-control)))

(fn2-c-source-control-preserves fn2-c-source-reader-acquire (endpoint expected-receipt fn2-c-source-control fn2-c-source-readers)
 :position 2 :prefix "-CONTROL" :disable nil
 :hyps ((fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
        (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)))

(fn2-c-source-readers-preserves fn2-c-source-reader-acquire (endpoint expected-receipt fn2-c-source-control fn2-c-source-readers)
 :position 3 :prefix "-READERS" :disable nil
 :hyps ((fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
        (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)))

(fn2-c-source-control-preserves fn2-c-source-reader-release (endpoint receipt fn2-c-source-control fn2-c-source-readers)
 :position 3 :prefix "-CONTROL" :disable nil
 :hyps ((fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
        (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)))

(fn2-c-source-readers-preserves fn2-c-source-reader-release (endpoint receipt fn2-c-source-control fn2-c-source-readers)
 :position 4 :prefix "-READERS" :disable nil
 :hyps ((fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
        (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)))

(fn2-c-source-control-preserves fn2-c-source-writer-poll
 (kind owner gen token cutcommit cutevent fn2-c-source-control) :position 1 :prefix "-CONTROL" :disable nil)

(fn2-c-source-control-preserves fn2-c-source-writer-begin
 (kind owner gen token cutcommit cutevent fn2-c-source-control) :position 1 :prefix "-CONTROL" :disable nil)

(fn2-c-source-control-preserves fn2-c-source-writer-abort-pending
 (kind owner gen token cutcommit cutevent fn2-c-source-control) :position 1 :prefix "-CONTROL" :disable nil)

; Logical aggregate carried from initialization by the actual transitions.
; This scan is a proof/model function, never a served admission/poll operation.
(defun fn2-c-source-reader-live-count (n fn2-c-source-readers)
 (declare (xargs :stobjs fn2-c-source-readers :measure (nfix n)
  :guard (and (fn2-c-source-readers-wfp fn2-c-source-readers)
              (natp n) (<= n (fn2-c-source-readers-rows fn2-c-source-readers)))))
 (if (zp n) 0
   (+ (if (equal (fn2-c-source-readers-live (- n 1) fn2-c-source-readers) 1) 1 0)
      (fn2-c-source-reader-live-count (- n 1) fn2-c-source-readers))))

(defun fn2-c-source-count-invariant-p (fn2-c-source-control fn2-c-source-readers)
 (declare (xargs :stobjs (fn2-c-source-control fn2-c-source-readers)
  :guard (and (fn2-c-source-control-wfp fn2-c-source-control) (fn2-c-source-readers-wfp fn2-c-source-readers))))
 (and (< 0 (fn2-c-source-control-rows fn2-c-source-control))
      (equal (fn2-c-source-control-readers 0 fn2-c-source-control)
             (fn2-c-source-reader-live-count (fn2-c-source-readers-rows fn2-c-source-readers) fn2-c-source-readers))))

(defthm fn2-c-source-count-invariant-init
 (implies (unsigned-byte-p 32 rows)
  (fn2-c-source-count-invariant-p
   (fn2-c-source-control-init 1 fn2-c-source-control)
   (fn2-c-source-readers-init rows fn2-c-source-readers))))

(defthm fn2-c-source-exclusive-has-no-live-endpoint
 (implies (and (fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
               (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)
               (fn2-c-source-count-invariant-p fn2-c-source-control fn2-c-source-readers)
               (fn2-c-source-writer-exclusive-p kind owner gen token cutcommit cutevent fn2-c-source-control)
               (natp endpoint) (< endpoint (fn2-c-source-readers-rows fn2-c-source-readers)))
          (equal (fn2-c-source-readers-live endpoint fn2-c-source-readers) 0)))

(defthm fn2-c-source-reader-acquire-preserves-count-invariant
 (implies (and (fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
               (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)
               (fn2-c-source-count-invariant-p fn2-c-source-control fn2-c-source-readers))
          (fn2-c-source-count-invariant-p (mv-nth 2 (fn2-c-source-reader-acquire endpoint expected-receipt fn2-c-source-control fn2-c-source-readers)) (mv-nth 3 (fn2-c-source-reader-acquire endpoint expected-receipt fn2-c-source-control fn2-c-source-readers)))))

(defthm fn2-c-source-reader-release-preserves-count-invariant
 (implies (and (fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
               (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)
               (fn2-c-source-count-invariant-p fn2-c-source-control fn2-c-source-readers))
          (fn2-c-source-count-invariant-p (mv-nth 3 (fn2-c-source-reader-release endpoint receipt fn2-c-source-control fn2-c-source-readers)) (mv-nth 4 (fn2-c-source-reader-release endpoint receipt fn2-c-source-control fn2-c-source-readers)))))

(defthm fn2-c-source-writer-begin-preserves-count-invariant
 (implies (and (fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
               (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)
               (fn2-c-source-count-invariant-p fn2-c-source-control fn2-c-source-readers))
          (fn2-c-source-count-invariant-p
           (mv-nth 1 (fn2-c-source-writer-begin kind owner gen token cutcommit cutevent fn2-c-source-control)) fn2-c-source-readers)))

(defthm fn2-c-source-writer-poll-preserves-count-invariant
 (implies (and (fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
               (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)
               (fn2-c-source-count-invariant-p fn2-c-source-control fn2-c-source-readers))
          (fn2-c-source-count-invariant-p
           (mv-nth 1 (fn2-c-source-writer-poll kind owner gen token cutcommit cutevent fn2-c-source-control)) fn2-c-source-readers)))

(defthm fn2-c-source-writer-abort-pending-preserves-count-invariant
 (implies (and (fn2-c-source-controlp fn2-c-source-control) (fn2-c-source-control-wfp fn2-c-source-control)
               (fn2-c-source-readersp fn2-c-source-readers) (fn2-c-source-readers-wfp fn2-c-source-readers)
               (fn2-c-source-count-invariant-p fn2-c-source-control fn2-c-source-readers))
          (fn2-c-source-count-invariant-p
           (mv-nth 1 (fn2-c-source-writer-abort-pending kind owner gen token cutcommit cutevent fn2-c-source-control)) fn2-c-source-readers)))
