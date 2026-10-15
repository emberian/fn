; Projected process-death states for the five-step cleaning protocol.
; A cut is (OPERATION QUANTUM): MOVE byte prefixes, either publication's
; request prefix, unlink/directory-fence prefixes, and every bitmap prefix.
; The result observes DISK/SEGS only: bitmap progress cannot change either.
; Native cut-map correspondence is B2; this book introduces no native alias.
(in-package "ACL2")
(include-book "log-cleaning-root-observations")
(include-book "log-cleaning-move")
(include-book "log-cleaning-unlink")
(include-book "log-checkpoint-publication-witnesses")

(defun fn-lc-cut-publication (old old-header columns header disk r mode quantum fullp)
 (declare (xargs :guard t))
 (let* ((dirty (fn-lc-dirty old old-header columns header))
        (plan (ec-call (pgs-plan-commit disk r mode dirty (fn-lc-publication-alloc disk))))
        (n (len (fn-lc-publication-program plan)))
        (limit (if fullp n (min (nfix quantum) n)))
        (outcome (ec-call (fn-lc-proof-ok-outcomes limit))))
  (fn-lc-stage-value old old-header columns header disk r mode outcome)))

(defun-nx fn-lc-clean-basep (move disk r mode segs fn-lbc)
 (let* ((physical (fn-lc-physical-disk disk))
        (header (fn-lc-cold-adopted-header physical r mode))
        (image (fn-lc-open-image physical r mode segs)))
  ; A PRE-state catalog binding, independent of every proposed cut state.
  ; It is not the old-or-new-locator conclusion.
  (and (fn-lc-headerp header) (equal header (fn-lc-at 5 move))
       (fn-lc-segs-retain segs header) (equal (fn-lc-head image) :ok)
       (equal (fn-lc-columns (fn-lc-at 1 image)) (fn-lc-columns fn-lbc)))))

(defun fn-lc-clean-cutp (cut move disk)
 (declare (xargs :guard t) (ignore disk))
 (and (true-listp cut) (equal (len cut) 2)
      (member-equal (fn-lc-head cut)
        '(:move-write :move-sync :publish-a :publish-b :unlink :bitmap))
      (natp (fn-lc-at 1 cut))
      (or (not (equal (fn-lc-head cut) :move-write))
          (<= (fn-lc-at 1 cut)
              (+ (len (fn-lc-at 3 move))
                 (ec-call (fn-lg-pad-len (len (fn-lc-at 3 move))
                    (fn-lc-tail-unit (fn-lc-at 5 move)))))))))

(defun-nx fn-lc-clean-cut (move disk r mode segs fn-lc-pins tail cut fn-lbc)
 (let* ((physical (fn-lc-physical-disk disk))
        (old-header (fn-lc-cold-adopted-header physical r mode))
        (old-columns (fn-lc-cold-adopted-columns physical r mode))
        (operation (fn-lc-head cut)) (quantum (nfix (fn-lc-at 1 cut)))
        (cleaned (ec-call (fn-lc-clean move physical segs '(:ok :ok) fn-lbc)))
        (after (fn-lc-at 3 cleaned)))
  (cond
   ((not (equal (fn-lc-head cleaned) :ok)) (mv physical segs))
   ((equal operation :move-write)
    (if (zp quantum) (mv physical segs)
     (let* ((frame (fn-lc-at 3 move))
            (bytes (fn-lc-join frame (fn-bs-zeros
                     (ec-call (fn-lg-pad-len (len frame) (fn-lc-tail-unit (fn-lc-at 5 move)))))))
            (prefix (fn-lc-take quantum bytes))
            (entry (if (<= (len frame) quantum) (fn-lc-at 4 move) nil)))
      ; Unit zero appends exactly the actually-written bytes. A complete frame
      ; exposes its parser entry even if its following alignment write tears.
      (mv physical (fn-lc-append-prepared (list nil prefix entry)
                     (fn-lc-move-loc0 move) 0 segs)))))
   ((equal operation :move-sync) (mv physical after))
   (t
    (let* ((columns (fn-lc-columns (fn-lc-at 1 cleaned)))
           (header (fn-lc-replayed-header physical r mode after))
           (first (fn-lc-cut-publication old-columns old-header columns header
                     physical r mode quantum (not (equal operation :publish-a))))
           (disk-a (fn-lc-at 1 first)))
     (if (or (equal operation :publish-a) (not (equal (fn-lc-head first) :ok)))
         (mv disk-a after)
      (let* ((second (fn-lc-cut-publication columns header columns header disk-a r mode
                       quantum (not (equal operation :publish-b))))
             (disk-b (fn-lc-at 1 second)))
       (cond ((or (equal operation :publish-b) (not (equal (fn-lc-head second) :ok)))
              (mv disk-b after))
             ((and (equal operation :unlink) (zp quantum)) (mv disk-b after))
             (t
              (let* ((observed (fn-lc-capture-root-observations disk-b r after))
                     (outcome (if (or (equal operation :bitmap) (<= 2 quantum))
                                  '(:ok :ok) '(:ok)))
                     (unlinked (ec-call (fn-lc-unlink
                          (ec-call (fn-lbc-loc0 (fn-lc-move-sequence move) fn-lbc))
                          observed r fn-lc-pins tail after outcome (fn-lc-at 1 cleaned)))))
               ; All per-key bitmap cuts have this same disk/log projection.
               (mv (fn-lc-at 2 unlinked) (fn-lc-at 3 unlinked))))))))))))

(verify-guards fn-lc-clean-basep)
(verify-guards fn-lc-clean-cut)
