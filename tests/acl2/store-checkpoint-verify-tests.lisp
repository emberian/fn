; fn: witnesses and teeth for books/store-checkpoint-verify.lisp (sweep
; 2026-10-03 S045: the staged checkpoint read back before its rename).
;
; The file is the one the writer's two loops write for the reachable store
; of tests/acl2/store-checkpoint-arena-tests (`sckat-e2e': the arena run,
; then the four tables).  The verify reads it as the host does
; (host/native/io.lisp fnn-state-checkpoint-verify): one segment at a time,
; the chunk alone in a fresh buffer, the frame (HEADER 0 N TRAILER) handed
; to fn-sccv-step.  The list fold over the same segments answers the same
; (fn-sccv-step-is-seg-step), and the KEYSTONE's conclusion holds on it.
; Mutation witnesses (labelled) flip a byte of a chunk, a header and a
; trailer, drop the last segment, repeat it, and change the sequence.
(in-package "ACL2")
(include-book "store-checkpoint-arena-tests")
(include-book "../../books/store-checkpoint-verify")

; The host-called step is guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-sccv-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccv-initial (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccv-final (w state)) :common-lisp-compliant)))

; The file as segments (octet lists), split by each header's LENGTH.
(defun sccvt-segs (octets fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (not (consp octets)))
      nil
    (let ((h (fn-scc-parse-header (take *fn-scc-segment-header-octets* octets))))
      (if (not h)
          (list octets)
        (let ((n (+ *fn-scc-segment-header-octets* (nth 2 h) *fn-frame-trailer-octets*)))
          (cons (take n octets) (sccvt-segs (nthcdr n octets) (1- fuel))))))))

; The host's read: each segment's chunk alone in the buffer, then the step.
(defun sccvt-host-fold (v segs fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (if (atom segs)
      (mv v fn-octets)
    (let* ((seg (car segs))
           (header (take *fn-scc-segment-header-octets* seg))
           (h (fn-scc-parse-header header))
           (n (if h (nth 2 h) 0))
           (chunk (take n (nthcdr *fn-scc-segment-header-octets* seg)))
           (trailer (take *fn-frame-trailer-octets*
                          (nthcdr (+ *fn-scc-segment-header-octets* n) seg)))
           (fn-octets (fn-octets-clear fn-octets))
           (fn-octets (fn-octets-append-list chunk fn-octets)))
      (sccvt-host-fold (fn-sccv-step v (list header 0 (len chunk) trailer) fn-octets)
                       (cdr segs) fn-octets))))

(defun sccvt-host (file sequence)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets)
      (sccvt-host-fold (fn-sccv-initial sequence) (sccvt-segs file 100000) fn-octets)
      (fn-sccv-final v))))

(defun sccvt-list (file sequence)
  (declare (xargs :verify-guards nil))
  (fn-sccv-final (fn-sccv-segs (fn-sccv-initial sequence) (sccvt-segs file 100000))))

; (Attachments evaluate in assert-event and defun bodies, not in defconst:
; the written file is a function.)
(defun sccvt-file ()
  (declare (xargs :verify-guards nil))
  (nth 4 (sckat-e2e nil nil)))
(defun sccvt-segs-of-file ()
  (declare (xargs :verify-guards nil))
  (sccvt-segs (sccvt-file) 100000))
(defun sccvt-sequence ()
  (declare (xargs :verify-guards nil))
  (nth 3 (fn-scc-parse-header (take *fn-scc-segment-header-octets* (sccvt-file)))))

(defun sccvt-flip (i file)
  (declare (xargs :verify-guards nil))
  (update-nth i (logxor 1 (nth i file)) file))

; The file the open loads (tests/acl2/store-checkpoint-arena-tests's
; KEYSTONE witness) is more than five segments, so the runs are not one
; segment each.
(assert-event
 (and (equal (car (car (nth 1 (sckat-e2e nil nil)))) :ok)
      (< 5 (len (sccvt-segs-of-file)))
      (equal (fn-scc-concat (sccvt-segs-of-file)) (sccvt-file))))

; KEYSTONE fn-sccv-final-ok-is-runs-ok, positive: the verify accepts the
; written file (the host's fold and the list fold alike) and its five runs
; join.
(assert-event
 (and (equal (sccvt-host (sccvt-file) (sccvt-sequence)) (list :ok (sccvt-sequence)))
      (equal (sccvt-list (sccvt-file) (sccvt-sequence)) (list :ok (sccvt-sequence)))
      (fn-sccv-runs-okp (sccvt-segs-of-file) *fn-sccv-runs* (sccvt-sequence))))

; KEYSTONE without its one hypothesis (the verify accepted): a file short of
; its last segment is refused, and its runs do not join.
(assert-event
 (let ((segs (butlast (sccvt-segs-of-file) 1)))
   (and (not (equal (car (sccvt-list (fn-scc-concat segs) (sccvt-sequence))) :ok))
        (not (fn-sccv-runs-okp segs *fn-sccv-runs* (sccvt-sequence))))))

; CORRUPTED FILE (mutation): one bit of a chunk (octet 50, inside the
; second segment's chunk), of the first header's count, and of the last
; trailer; each refused by the host's fold and the list fold.
(assert-event
 (let ((last (1- (len (sccvt-file)))))
   (and (< 50 (len (sccvt-file)))
        (equal (sccvt-host (sccvt-flip 50 (sccvt-file)) (sccvt-sequence)) '(:refused :segment))
        (equal (sccvt-list (sccvt-flip 50 (sccvt-file)) (sccvt-sequence)) '(:refused :segment))
        (equal (car (sccvt-host (sccvt-flip 13 (sccvt-file)) (sccvt-sequence))) :refused)
        (equal (sccvt-host (sccvt-flip last (sccvt-file)) (sccvt-sequence)) '(:refused :segment)))))

; CORRUPTED FILE (mutation): the last segment dropped (a short file), or
; repeated (trailing data), is refused.
(assert-event
 (and (equal (sccvt-host (fn-scc-concat (butlast (sccvt-segs-of-file) 1)) (sccvt-sequence))
             '(:refused :truncated))
      (not (equal (car (sccvt-host (append (sccvt-file) (car (last (sccvt-segs-of-file))))
                                   (sccvt-sequence)))
                  :ok))))

; Another publication's file (the sequence the host wrote is not the file's)
; is refused.
(assert-event
 (equal (sccvt-host (sccvt-file) (+ 1 (sccvt-sequence))) '(:refused :segment)))
