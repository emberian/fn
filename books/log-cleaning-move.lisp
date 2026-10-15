; LC MOVE model: one sealed maintenance packet, the existing K decision,
; append/fdatasync, then the two generated locator setters. No row replay.
(in-package "ACL2")
(include-book "log-cleaning")
(include-book "log-cleaning-replay")
(include-book "log-checkpoint-open")
(include-book "log-checkpoint-independent-guards")
(include-book "log-verified-map-properties")

; Plan: (:lc-move original-sequence segment frame entry header k root mode).






(defun fn-lc-plan-move (i header k r mode segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (if (or (not (natp i)) (not (< i (fn-lbc-count fn-lbc)))) :bad
  (let* ((row (ec-call (fn-lc-bound-row i fn-lbc segs)))
         (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
         (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs)))
         (segment (ec-call (fn-lb-log-model-segment id segs)))
         (start (len (fn-lc-at 1 segment)))
         (wire (ec-call (fn-lc-read-range a b segs)))
         (home (fn-lc-read-suf a b segs))
         (prev (fn-lc-at 3 (fn-lc-tail-scan segs header)))
         (frame (ec-call (fn-lc-move-frame prev i wire home)))
         (payload (ec-call (fn-lb-log-payload row segs)))
         (entry (list (len (fn-lc-at 2 segment)) start
                      (- (len frame) *fn-frame-trailer-octets*)
                      (+ start *fn-frame-header-octets* 32 12) (len wire)
                      (fn-record-payload row) payload
                      (ec-call (fn-lb-log-model-homes row)) i)))
   (list :lc-move i id frame entry header k r mode))))

; Freshness includes the parser directory, not only the current byte EOF.
; These targeted lookups exclude a stale descriptor shadowing the new entry.
(defun fn-lc-move-target-freshp (move segs)
 (declare (xargs :guard t))
 (let* ((segment (ec-call (fn-lb-log-model-segment (fn-lc-move-loc0 move) segs)))
        (entries (fn-lc-at 2 segment))
        (entry (fn-lc-at 4 move))
        (offset (nfix (fn-lc-at 3 entry)))
        (home (+ offset (nfix (fn-lc-at 4 entry)))))
  (and (not (ec-call (fn-lb-log-model-range-entry offset entries)))
       (not (ec-call (fn-lb-log-model-home-entry home entries))))))

(defun fn-lc-move-recordp (move fn-lbc segs)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let* ((i (fn-lc-move-sequence move))
        (header (fn-lc-at 5 move)) (frame (fn-lc-at 3 move))
        (entry (fn-lc-at 4 move)))
  (and (true-listp move) (equal (len move) 9)
       (equal (fn-lc-head move) :lc-move)
       (natp i) (< i (fn-lbc-count fn-lbc))
       (fn-lc-segsp segs) (natp (fn-lc-at 6 move))
       (fn-locp (fn-lc-move-loc0 move) (fn-lc-move-loc1 move))
       (fn-lc-segs-retain segs header)
       (equal (fn-lc-head (fn-lc-tail-scan segs header)) :ok)
       ; Complete original record and source range, not an assumed post-state.
       (let* ((row (ec-call (fn-lc-bound-row i fn-lbc segs)))
              (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
              (payload (ec-call (fn-lb-log-payload row segs))))
        (and (fn-held-p row) (equal (fn-record-sequence row) i)
             (not (fn-rcl-tombstonep payload))
             (not (equal (ec-call (fn-lc-read-range a b segs)) :bad))
             (not (equal (fn-lc-read-suf a b segs) :bad))
             ; The frame's width-limited PRE must decode to this very row
             ; and range; sealing alone does not establish that binding.
             (equal (fn-lc-move-event frame (fn-lc-tail-max header))
                    (list :move i (ec-call (fn-lc-read-range a b segs))
                          (fn-lc-read-suf a b segs)))
             (equal move (fn-lc-plan-move i header (fn-lc-at 6 move)
                             (fn-lc-at 7 move) (fn-lc-at 8 move) segs fn-lbc))))
       (fn-lb-log-model-entryp entry)
       (fn-lc-move-target-freshp move segs)
       (fn-lc-move-framep frame (fn-lc-at 3 (fn-lc-tail-scan segs header))
                                (fn-lc-tail-max header))
       ; Width is a locator/segment profile boundary, never a record-count cap.
       (< (+ (nfix (fn-lc-at 1 entry)) (len frame)) 4294967296))))



(defun fn-lc-clean (move disk segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (cond ((not (fn-lc-move-recordp move fn-lbc segs))
        (mv :invalid-move fn-lbc disk segs nil))
       ((not (equal (fn-lc-at 5 move)
               (fn-lc-cold-adopted-header disk (fn-lc-at 7 move) (fn-lc-at 8 move))))
        (mv :checkpoint-binding fn-lbc disk segs nil))
       (t
        (mv-let (answer fn-lbc proposed)
          (fn-lc-commit (list (fn-lc-move-packet move)) segs (fn-lc-at 5 move)
                         (fn-lc-at 6 move) fn-lbc)
         (if (not (equal answer :ok)) (mv answer fn-lbc disk proposed nil)
          (let* ((program (list (list :log-write (fn-lc-move-loc0 move)
                                      (fn-lc-at 1 (fn-lc-at 4 move)) (fn-lc-at 3 move))
                               '(:log-fdatasync)))
                 (done (fn-lc-outcome-ok-count outcome 2))
                 (trace (fn-lc-take (min 2 (+ 1 done)) program)))
           ; On uncertain write/fence, retain the possible appended bytes and
           ; the old columns; never advertise rollback of persistent bytes.
           (if (< done 2) (mv :uncertain fn-lbc disk proposed trace)
             (let ((fn-lbc (fn-lc-replay-move move fn-lbc)))
               (mv :ok fn-lbc disk proposed trace)))))))))

(verify-guards fn-lc-plan-move)
(verify-guards fn-lc-move-recordp)



(defthm fn-lc-maintenance-commit-columns-by-definition
 (equal (mv-nth 1 (fn-lc-commit (list (list nil frame entry)) segs header k fn-lbc)) fn-lbc)
 :hints (("Goal" :in-theory (e/d (fn-lc-commit fn-lc-commit-prepared fn-lc-append-prepared-columns)
  (fn-lc-tail-history fn-lc-tail-scan fn-lc-segs-retain fn-lc-prepared-recordsp
   fn-lc-prepare-tail fn-lbc-p)))))
(verify-guards fn-lc-clean
 :hints (("Goal" :in-theory (e/d (fn-lc-move-recordp fn-lc-move-packet fn-lc-count)
  (fn-lbc-p fn-lbc-count fn-lc-plan-move fn-lc-replay-move
   fn-lc-move-sequence fn-lc-move-loc0 fn-lc-move-loc1
   fn-lc-segsp fn-lc-segs-retain fn-lc-tail-scan fn-locp
   fn-lc-commit fn-lc-bound-row fn-lb-log-payload fn-lb-log-model-entryp
   fn-lc-move-framep fn-lc-cold-adopted-header)))))

(defthm fn-lc-clean-column-effect-by-definition
 (equal (mv-nth 1 (fn-lc-clean move disk segs outcome fn-lbc))
        (if (equal (mv-nth 0 (fn-lc-clean move disk segs outcome fn-lbc)) :ok)
            (fn-lc-replay-move move fn-lbc) fn-lbc))
 :hints (("Goal" :in-theory
  (e/d (fn-lc-clean fn-lc-move-packet)
       (fn-lc-move-recordp fn-lc-cold-adopted-header fn-lc-commit
        fn-lc-replay-move fn-lc-outcome-ok-count fn-lc-take
        fn-lc-move-loc0 fn-lc-move-sequence)))))
