; Bounded stored-DEFLATE window and protected-prefix authentication composition.
(in-package "ACL2")
(include-book "extent-window-stream")
(include-book "payload-window")

; (mode raw-plan decoded-length decoded-offset wanted budget ip end status)
; The raw subplan requests a zero-length window. Only decoded overlap writes
; the shared private output, while every protected prefix byte is hashed.
(defun fn-ewz-state (mode plan n offset wanted budget ip end status)
  (declare (xargs :guard t))
  (list mode plan n offset wanted budget ip end status))

(defun fn-ewz-begin (file eoff elen poff compressed decoded offset ticket incarnation lease expected dict
                     pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (natp file) (natp eoff) (natp elen) (natp poff)
                              (natp compressed) (natp decoded) (natp offset) (natp expected)
                              (fn-cbor-octet-listp dict) (<= (len dict) 65536))
                  :guard-hints (("Goal" :in-theory (enable fn-ews-begin fn-ewp-begin fn-ewp-state)))))
  (mv-let (plan pgs-digest-state)
    (fn-ews-begin file eoff elen poff compressed compressed ticket incarnation lease expected pgs-digest-state)
    (mv-let (fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (mv (fn-ewz-state
            (cond ((or (eq (nth 0 plan) :bounds) (< decoded offset)) :bounds)
                  ((not (fn-pzw-stored-admissiblep compressed decoded)) :codec-error)
                  ((zp compressed) :drain)
                  (t :scan))
            plan decoded offset (min 16384 (nfix (- decoded offset)))
            (fn-pzd-budget compressed decoded) 0 0 :more)
          pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))

(defun fn-ewz-compressed-completep (plan)
  (declare (xargs :guard (true-listp plan)))
  (<= (+ (nfix (nth 11 plan)) (nfix (nth 12 plan)))
      (+ (nfix (nth 2 plan)) (nfix (nth 7 plan)))))

(defun fn-ewz-effect (z pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state
                  :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (and (member-eq (nth 0 z) '(:scan :drain :decoded))
       (not (and (eq (nth 0 z) :drain) (fn-ewz-compressed-completep (nth 1 z))))
       (fn-ews-effect (nth 1 z) pgs-digest-state)))

(defun fn-ewz-publication (z)
  (declare (xargs :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (let ((plan (nth 1 z)))
    (and (eq (nth 0 z) :decoded) (fn-ewp-publication plan)
         (list (nth 8 plan) (nth 9 plan) (nth 10 plan)
               :decoded (nth 3 z) (nth 4 z)))))

(defun fn-ewz-decision-mode (decision)
  (declare (xargs :guard t))
  (cond ((eq decision :resume) :codec)
        ((eq decision :input) :scan)
        ((eq decision :drain) :drain)
        ((eq decision :decoded) :decoded)
        (t :codec-error)))

; The codec step never releases the input buffer. A new read effect remains
; unavailable until its pending span was consumed or a valid final drains it.
(defun fn-ewz-codec-tick (z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
  (declare (xargs :stobjs (fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
                  :guard (and (true-listp z) (true-listp (nth 1 z))) :verify-guards nil))
  (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z))
         (remaining (nth 5 z)) (before (fn-zin-tout fn-zin-st)))
    (if (not (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end)
                  (<= (- end ip) 64) (<= end (fn-octets-len fn-octets))))
        (mv :state (update-nth 0 :state z) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
      (mv-let (status left ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
        (fn-pzw-stored-chunk 1024 remaining ip end (nth 12 plan) (nth 2 z)
                              fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
        (mv-let (src count dst)
          (fn-pzw-select before (fn-zin-out-len fn-zin-out) (nth 3 z) (nth 4 z))
          (let* ((fn-ew-buffer (fn-ewb-copy src count dst fn-zin-out fn-ew-buffer))
                 (budget (fn-pzw-budget-left 1024 remaining left))
                 (complete (and (equal ip end) (fn-ewz-compressed-completep plan)))
                 (decision (fn-pzw-stored-decision status (nth 12 plan) (nth 2 z) budget complete fn-zin-st))
                 (next (fn-ewz-state (if (and (eq decision :input) (not (equal ip end)))
                                        :state (fn-ewz-decision-mode decision)) plan (nth 2 z) (nth 3 z)
                                    (nth 4 z) budget ip end status)))
            (mv decision next fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))))))

(local
 (defthm ewz-select-copy-guard
   (let ((r (fn-pzw-select produced count offset requested)))
     (and (natp (car r)) (natp (mv-nth 1 r)) (natp (mv-nth 2 r))
          (<= (mv-nth 1 r) 64)
          (<= (+ (car r) (mv-nth 1 r)) (nfix count))
          (<= (+ (mv-nth 2 r) (mv-nth 1 r)) 16384)))
   :hints (("Goal" :in-theory (enable fn-pzw-select min max nfix)))))

(verify-guards fn-ewz-codec-tick
  :hints (("Goal" :do-not-induct t
           :use (:instance ewz-select-copy-guard
                   (produced (fn-zin-tout fn-zin-st))
                   (count (fn-zin-out-len
                            (mv-nth 6 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                         (nth 12 (nth 1 z)) (nth 2 z)
                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
                   (offset (nth 3 z)) (requested (nth 4 z)))
           :in-theory (e/d (nfix) (fn-pzw-stored-chunk fn-pzw-select ewz-select-copy-guard)))))

; Scan completion hashes once before making its overlap available to the codec.
; Subsequent codec quanta retain the same input; they never hash it again.
(defun fn-ewz-read (effect io-status z fn-octets pgs-digest-state fn-ew-buffer)
  (declare (xargs :stobjs (fn-octets pgs-digest-state fn-ew-buffer)
                  :guard (and (true-listp z) (true-listp (nth 1 z))) :verify-guards nil))
  (let* ((plan (nth 1 z)) (issued (fn-ewz-effect z pgs-digest-state)))
    (if (or (not issued) (not (equal effect issued)))
        (mv :stale z pgs-digest-state fn-ew-buffer)
      (mv-let (status next-plan pgs-digest-state fn-ew-buffer)
        (fn-ews-read effect io-status plan fn-octets pgs-digest-state fn-ew-buffer)
        (let* ((span (fn-ewp-payload-span (nfix (nth 11 plan)) (nfix (nth 12 plan)) plan))
               (pending (and (eq (nth 0 z) :scan) (eq (nth 0 plan) :scan)
                             (eq status :continue) (< 0 (cadr span))))
               (next (fn-ewz-state (if pending :codec (nth 0 z)) next-plan (nth 2 z) (nth 3 z)
                                  (nth 4 z) (nth 5 z) (if pending (car span) (nth 6 z))
                                  (if pending (+ (car span) (cadr span)) (nth 7 z)) (nth 8 z))))
          (mv status next pgs-digest-state fn-ew-buffer))))))
(verify-guards fn-ewz-read)

; Hash-only ticks and final-stream draining. The host chooses this entry
; when mode is not :codec; fn-ewz-codec-tick owns the other scheduling quantum.
(defun fn-ewz-hash-tick (z pgs-digest-state fn-zin-st)
  (declare (xargs :stobjs (pgs-digest-state fn-zin-st)
                  :guard (and (true-listp z) (true-listp (nth 1 z))) :verify-guards nil))
  (let ((plan (nth 1 z)))
    (cond ((eq (nth 0 z) :codec) (mv :codec z pgs-digest-state))
          ((not (member-eq (nth 0 z) '(:scan :drain :decoded)))
           (mv (nth 0 z) z pgs-digest-state))
          ((and (eq (nth 0 z) :drain) (fn-ewz-compressed-completep plan))
           (let* ((decision (fn-pzw-stored-decision (nth 8 z) (nth 12 plan) (nth 2 z) (nth 5 z) t fn-zin-st))
                  (next (update-nth 0 (fn-ewz-decision-mode decision) z)))
             (mv decision next pgs-digest-state)))
          (t (mv-let (status plan pgs-digest-state)
               (fn-ews-tick plan pgs-digest-state)
               (mv status (update-nth 1 plan z) pgs-digest-state))))))
(verify-guards fn-ewz-hash-tick)

; Host dispatches this core action. A raw subplan status is never itself a
; compressed publication decision; only this combined gate returns :ready.
(defun fn-ewz-next-action (z pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state
                  :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (let ((publication (fn-ewz-publication z)) (plan (nth 1 z)))
    (cond (publication (list :ready publication))
          ((not (member-eq (nth 0 z) '(:codec :scan :drain :decoded)))
           (list :refused (nth 0 z) (nth 8 z)))
          ((not (member-eq (nth 0 plan) '(:scan :trailer :verified)))
           (list :refused :hash (nth 0 plan)))
          ((eq (nth 0 z) :codec) (list :codec))
          ((fn-ewz-effect z pgs-digest-state) (list :read (fn-ewz-effect z pgs-digest-state)))
          (t (list :tick)))))

(in-theory (disable fn-ewz-state fn-ewz-begin fn-ewz-compressed-completep
                    fn-ewz-effect fn-ewz-publication fn-ewz-decision-mode
                    fn-ewz-codec-tick fn-ewz-read fn-ewz-hash-tick fn-ewz-next-action))
