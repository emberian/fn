(in-package "ACL2")
(include-book "../../books/decoded-window-action-trajectory")

 ; Actual copy-action normalization teeth: no full decoder/budget claim.
; The positive witness reaches copy mode through the actual compressed API.
(defun pwzat-prime-read (fuel z pgs-digest-state fn-zin-st)
  (declare (xargs :stobjs (pgs-digest-state fn-zin-st)
                  :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (fn-ewz-effect z pgs-digest-state))
      (mv z pgs-digest-state)
    (mv-let (status z pgs-digest-state)
      (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)
      (declare (ignore status))
      (pwzat-prime-read (1- fuel) z pgs-digest-state fn-zin-st))))

; Reach the pending-copy controller state through its actual initializer,
; core-issued protected read, and first bounded codec tick.
(local
 (defthm pwzat-actual-codec-copy-reachable
  (let* ((c '(115 116 28 177 0 0))
         (msg (append '(9 8) c '(7)))
         (digest (fn-blake3 msg))
         (archive (append msg digest))
         (init (fn-ewz-begin 7 100 (len msg) 102 6 251 0 23 47 59
                             (fn-bch-pack digest) nil
                             (create-pgs-digest-state)
                             (create-fn-zin-st) nil nil nil))
         (prime (pwzat-prime-read 1024 (car init) (mv-nth 1 init) (mv-nth 2 init)))
         (effect (fn-ewz-effect (car prime) (mv-nth 1 prime)))
         (input (fn-b3-firstn (nth 5 effect) archive))
         (read (fn-ewz-read effect :ok (car prime) input (mv-nth 1 prime) (create-fn-ew-buffer)))
         (tick (fn-ewz-codec-tick (mv-nth 1 read) input
                                 (mv-nth 2 init) (mv-nth 3 init)
                                 (mv-nth 4 init) (mv-nth 5 init)
                                 (mv-nth 3 read))))
    (let ((z (mv-nth 1 tick)) (fn-octets input)
          (fn-zin-st (mv-nth 2 tick)) (fn-zin-win (mv-nth 3 tick))
          (fn-zin-tab (mv-nth 4 tick)) (fn-zin-out (mv-nth 5 tick))
          (fn-ew-buffer (mv-nth 6 tick)))
      (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z))
         (q (fn-pzw-quantum 1024 (nth 5 z)))
         (credit (nfix (nth 12 plan)))
         (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan))))
         (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st)))
    (and
     (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end)
          (<= (- end ip) 64) (<= end (fn-octets-len fn-octets))
          (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64)
          (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0))
          (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0))))
          (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
     (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64
                                      (nth 3 z) (nth 4 z)))
            (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win
                                 fn-zin-tab fn-zin-out fn-ew-buffer)))
       (and (equal (mv-nth 2 r) s1)
            (equal (mv-nth 3 r) (mv-nth 2 actions))
            (equal (mv-nth 4 r) (mv-nth 3 actions))
            (equal (mv-nth 5 r) (mv-nth 4 actions))
            (equal (mv-nth 6 r)
                   (fn-ewb-copy (car selection) (mv-nth 1 selection)
                                (mv-nth 2 selection) (mv-nth 4 actions)
                                fn-ew-buffer))))))))
   :rule-classes nil))

; Logical model buffers for hypothesis-removal witnesses. These are labelled
; corrupted-state/request witnesses, distinct from the reachable positive
; initializer/read/tick witness above. No guard checks are disabled.
(defconst *pwzat-model-win* (append (make-list 64 :initial-element 65)
                                 (make-list 65472 :initial-element 0)))
(defconst *pwzat-model-tab* (make-list 3494 :initial-element 0))
(defconst *pwzat-model-buffer* (list (make-list 16384 :initial-element 0)))
(defconst *pwzat-model-st* (list '(12 0 0 187 1 64 64 5 0 0 0 1 0 0 0 0 0 0 0 0)))
(defconst *pwzat-model-z* '(:codec (:trailer 7 100 9 8 0 0 9 23 47 59 102 6 6)
                                  251 0 251 1000 0 0 :full))

; Corrupted state/request: remove only mode.
(local (defthm pwzat-codec-copy-without-mode (let ((z (update-nth 0 :scan *pwzat-model-z*)) (fn-octets nil) (fn-zin-st *pwzat-model-st*) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (eq (nth 0 z) :codec)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only ip-natural.
(local (defthm pwzat-codec-copy-without-ip-natural (let ((z (update-nth 6 -1 *pwzat-model-z*)) (fn-octets nil) (fn-zin-st *pwzat-model-st*) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (natp ip)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only end-natural.
(local (defthm pwzat-codec-copy-without-end-natural (let ((z (update-nth 7 "1/2" *pwzat-model-z*)) (fn-octets (quote (0))) (fn-zin-st *pwzat-model-st*) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (natp end)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only ordered-span.
(local (defthm pwzat-codec-copy-without-ordered-span (let ((z (update-nth 6 1 *pwzat-model-z*)) (fn-octets nil) (fn-zin-st *pwzat-model-st*) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= ip end)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only bounded-span.
(local (defthm pwzat-codec-copy-without-bounded-span (let ((z (update-nth 7 65 *pwzat-model-z*)) (fn-octets (make-list 65 :initial-element 0)) (fn-zin-st *pwzat-model-st*) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= (- end ip) 64)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only input-bound.
(local (defthm pwzat-codec-copy-without-input-bound (let ((z (update-nth 7 1 *pwzat-model-z*)) (fn-octets nil) (fn-zin-st *pwzat-model-st*) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= end (fn-octets-len fn-octets))) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only positive-quantum.
(local (defthm pwzat-codec-copy-without-positive-quantum (let ((z (update-nth 5 0 *pwzat-model-z*)) (fn-octets nil) (fn-zin-st *pwzat-model-st*) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (posp q)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only copy-room.
(local (defthm pwzat-codec-copy-without-copy-room (let ((z (update-nth 2 126 *pwzat-model-z*)) (fn-octets nil) (fn-zin-st *pwzat-model-st*) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (equal (fn-pzw-room bound (fn-zin-tout s0)) 64)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only pending-mode.
(local (defthm pwzat-codec-copy-without-pending-mode (let ((z *pwzat-model-z*) (fn-octets nil) (fn-zin-st (fn-zin-set 0 0 *pwzat-model-st*)) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (equal (fn-zin-mode s0) 12)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only pending-count.
(local (defthm pwzat-codec-copy-without-pending-count (let ((z *pwzat-model-z*) (fn-octets nil) (fn-zin-st (fn-zin-set 3 1 (fn-zin-set 2 63 *pwzat-model-st*))) (fn-zin-win *pwzat-model-win*) (fn-zin-tab (fn-zin-tput 723 577 *pwzat-model-tab*)) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= 64 (fn-zin-n s0))) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only funded-copy.
(local (defthm pwzat-codec-copy-without-funded-copy (let ((z (update-nth 4 64 (update-nth 3 65473 (update-nth 2 65537 (update-nth 1 (update-nth 12 0 (nth 1 *pwzat-model-z*)) *pwzat-model-z*))))) (fn-octets nil) (fn-zin-st (fn-zin-set 6 65473 (fn-zin-set 7 0 *pwzat-model-st*))) (fn-zin-win *pwzat-model-win*) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer (list (make-list 16384 :initial-element 65)))) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0))))) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil :hints (("Goal" :do-not-induct t
 :expand ((:free (src count dst fn-octets fn-ew-buffer)
                  (fn-ewb-copy src count dst fn-octets fn-ew-buffer)))
 :in-theory (e/d (fn-ewb-copy fn-octets$a-get hide)
                  ((:executable-counterpart fn-ewb-copy)
                   (:executable-counterpart fn-octets-get)))))))

; Corrupted state/request: remove only window-ready.
(local (defthm pwzat-codec-copy-without-window-ready (let ((z *pwzat-model-z*) (fn-octets nil) (fn-zin-st *pwzat-model-st*) (fn-zin-win nil) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-tab-okp fn-zin-tab) (not (fn-zin-window-ready-p fn-zin-win)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pwz-copy-actions-output-count
                 (k 64) (fn-zin-st (fn-zin-set 7 11 *pwzat-model-st*))
                 (fn-zin-win nil) (fn-zin-tab *pwzat-model-tab*) (fn-zin-out nil)))
 :in-theory (e/d (hide)
                  ((:executable-counterpart fn-pwz-action-sequence)
                   (:definition fn-pwz-action-sequence)))))))

; Corrupted state/request: remove only table-ready.
(local (defthm pwzat-codec-copy-without-table-ready (let ((z *pwzat-model-z*) (fn-octets nil) (fn-zin-st *pwzat-model-st*) (fn-zin-win *pwzat-model-win*) (fn-zin-tab nil) (fn-zin-out nil) (fn-ew-buffer *pwzat-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (not (fn-zin-tab-okp fn-zin-tab)) (not (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 2 actions)) (equal (mv-nth 4 r) (mv-nth 3 actions)) (equal (mv-nth 5 r) (mv-nth 4 actions)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 4 actions) fn-ew-buffer)))))))) :rule-classes nil :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pwz-copy-actions-output-count
                 (k 64) (fn-zin-st (fn-zin-set 7 11 *pwzat-model-st*))
                 (fn-zin-win *pwzat-model-win*) (fn-zin-tab nil) (fn-zin-out nil)))
 :in-theory (e/d (hide)
                  ((:executable-counterpart fn-pwz-action-sequence)
                   (:definition fn-pwz-action-sequence)))))))
