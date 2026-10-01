(in-package "ACL2")
(include-book "../../books/decoded-window-copy-trajectory")
(include-book "extent-window-compressed-tests")

; External raw-DEFLATE fixture: 251 A octets. The whole decoder and the
; actual bounded controller both execute; ACL2 derives the archive digest.
(assert-event
 (let* ((c '(115 116 28 177 0 0))
        (msg (append '(9 8) c '(7)))
        (digest (fn-blake3 msg))
        (whole (fn-pzd-decode nil c 251))
        (bounded (ewzt-example msg (append msg digest) 2 (len c) 251 0
                               (fn-bch-pack digest))))
   (and (equal (car whole) :ok)
        (equal (len (cadr whole)) 251)
        (equal (car bounded) '(:ready (23 47 59 :decoded 0 251)))
        (< 1 (nth 2 bounded))
        (equal (nth 3 bounded) 251)
        (equal (nth 4 bounded) (cadr whole)))))

(defun pwzt-prime-read (fuel z pgs-digest-state fn-zin-st)
  (declare (xargs :stobjs (pgs-digest-state fn-zin-st)
                  :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (fn-ewz-effect z pgs-digest-state))
      (mv z pgs-digest-state)
    (mv-let (status z pgs-digest-state)
      (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)
      (declare (ignore status))
      (pwzt-prime-read (1- fuel) z pgs-digest-state fn-zin-st))))

; Reach the pending-copy controller state through its actual initializer,
; core-issued protected read, and first bounded codec tick.
(local
 (defthm pwzt-actual-codec-copy-reachable
  (let* ((c '(115 116 28 177 0 0))
         (msg (append '(9 8) c '(7)))
         (digest (fn-blake3 msg))
         (archive (append msg digest))
         (init (fn-ewz-begin 7 100 (len msg) 102 6 251 0 23 47 59
                             (fn-bch-pack digest) nil
                             (create-pgs-digest-state)
                             (create-fn-zin-st) nil nil nil))
         (prime (pwzt-prime-read 1024 (car init) (mv-nth 1 init) (mv-nth 2 init)))
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
     (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0)
                              (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil))
            (s1 (fn-zin-set 5 (car copy) s0))
            (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1))
            (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64
                                      (nth 3 z) (nth 4 z)))
            (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win
                                 fn-zin-tab fn-zin-out fn-ew-buffer)))
       (and (equal (mv-nth 2 r) s1)
            (equal (mv-nth 3 r) (mv-nth 1 copy))
            (equal (mv-nth 4 r) fn-zin-tab)
            (equal (mv-nth 5 r) (mv-nth 2 copy))
            (equal (mv-nth 6 r)
                   (fn-ewb-copy (car selection) (mv-nth 1 selection)
                                (mv-nth 2 selection) (mv-nth 2 copy)
                                fn-ew-buffer))))))))
   :rule-classes nil))

; Logical model buffers for hypothesis-removal witnesses. These are labelled
; corrupted-state/request witnesses, distinct from the reachable positive
; initializer/read/tick witness above. No guard checks are disabled.
(defconst *pwzt-model-win* (append (make-list 64 :initial-element 65)
                                 (make-list 65472 :initial-element 0)))
(defconst *pwzt-model-tab* (make-list 3494 :initial-element 0))
(defconst *pwzt-model-buffer* (list (make-list 16384 :initial-element 0)))
(defconst *pwzt-model-st* (list '(12 0 0 187 1 64 64 5 0 0 0 1 0 0 0 0 0 0 0 0)))
(defconst *pwzt-model-z* '(:codec (:trailer 7 100 9 8 0 0 9 23 47 59 102 6 6)
                                  251 0 251 1000 0 0 :full))

; Corrupted state/request: remove only mode.
(local (defthm pwzt-codec-copy-without-mode (let ((z (update-nth 0 :scan *pwzt-model-z*)) (fn-octets nil) (fn-zin-st *pwzt-model-st*) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (eq (nth 0 z) :codec)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only ip-natural.
(local (defthm pwzt-codec-copy-without-ip-natural (let ((z (update-nth 6 -1 *pwzt-model-z*)) (fn-octets nil) (fn-zin-st *pwzt-model-st*) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (natp ip)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only end-natural.
(local (defthm pwzt-codec-copy-without-end-natural (let ((z (update-nth 7 "1/2" *pwzt-model-z*)) (fn-octets (quote (0))) (fn-zin-st *pwzt-model-st*) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (natp end)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only ordered-span.
(local (defthm pwzt-codec-copy-without-ordered-span (let ((z (update-nth 6 1 *pwzt-model-z*)) (fn-octets nil) (fn-zin-st *pwzt-model-st*) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= ip end)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only bounded-span.
(local (defthm pwzt-codec-copy-without-bounded-span (let ((z (update-nth 7 65 *pwzt-model-z*)) (fn-octets (make-list 65 :initial-element 0)) (fn-zin-st *pwzt-model-st*) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= (- end ip) 64)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only input-bound.
(local (defthm pwzt-codec-copy-without-input-bound (let ((z (update-nth 7 1 *pwzt-model-z*)) (fn-octets nil) (fn-zin-st *pwzt-model-st*) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= end (fn-octets-len fn-octets))) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only positive-quantum.
(local (defthm pwzt-codec-copy-without-positive-quantum (let ((z (update-nth 5 0 *pwzt-model-z*)) (fn-octets nil) (fn-zin-st *pwzt-model-st*) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (posp q)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only copy-room.
(local (defthm pwzt-codec-copy-without-copy-room (let ((z (update-nth 2 126 *pwzt-model-z*)) (fn-octets nil) (fn-zin-st *pwzt-model-st*) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (equal (fn-pzw-room bound (fn-zin-tout s0)) 64)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only pending-mode.
(local (defthm pwzt-codec-copy-without-pending-mode (let ((z *pwzt-model-z*) (fn-octets nil) (fn-zin-st (fn-zin-set 0 0 *pwzt-model-st*)) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (equal (fn-zin-mode s0) 12)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only pending-count.
(local (defthm pwzt-codec-copy-without-pending-count (let ((z *pwzt-model-z*) (fn-octets nil) (fn-zin-st (fn-zin-set 3 0 *pwzt-model-st*)) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= 64 (fn-zin-n s0))) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only funded-copy.
(local (defthm pwzt-codec-copy-without-funded-copy (let ((z (update-nth 2 65536 (update-nth 1 (update-nth 12 0 (nth 1 *pwzt-model-z*)) *pwzt-model-z*))) (fn-octets nil) (fn-zin-st (fn-zin-set 6 65473 (fn-zin-set 7 0 *pwzt-model-st*))) (fn-zin-win *pwzt-model-win*) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab) (not (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0))))) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

; Corrupted state/request: remove only window-ready.
(local (defthm pwzt-codec-copy-without-window-ready (let ((z *pwzt-model-z*) (fn-octets nil) (fn-zin-st *pwzt-model-st*) (fn-zin-win nil) (fn-zin-tab *pwzt-model-tab*) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-tab-okp fn-zin-tab) (not (fn-zin-window-ready-p fn-zin-win)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil :hints (("Goal" :do-not-induct t
 :use ((:instance fn-zin-copy-len (k 64) (w 64) (d 1) (tout 64) (h 0)
         (fn-zin-win nil) (fn-zin-out nil)))
 :in-theory (disable fn-zin-copy-len fn-zin-copy-out-len (:executable-counterpart fn-zin-copy))))))

; Corrupted state/request: remove only table-ready.
(local (defthm pwzt-codec-copy-without-table-ready (let ((z *pwzt-model-z*) (fn-octets nil) (fn-zin-st *pwzt-model-st*) (fn-zin-win *pwzt-model-win*) (fn-zin-tab nil) (fn-zin-out nil) (fn-ew-buffer *pwzt-model-buffer*)) (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z)) (q (fn-pzw-quantum 1024 (nth 5 z))) (credit (nfix (nth 12 plan))) (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan)))) (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))) (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end) (<= (- end ip) 64) (<= end (fn-octets-len fn-octets)) (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64) (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0)) (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0)))) (fn-zin-window-ready-p fn-zin-win) (not (fn-zin-tab-okp fn-zin-tab)) (not (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0) (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil)) (s1 (fn-zin-set 5 (car copy) s0)) (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1)) (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1)) (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)) (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64 (nth 3 z) (nth 4 z))) (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (and (equal (mv-nth 2 r) s1) (equal (mv-nth 3 r) (mv-nth 1 copy)) (equal (mv-nth 4 r) fn-zin-tab) (equal (mv-nth 5 r) (mv-nth 2 copy)) (equal (mv-nth 6 r) (fn-ewb-copy (car selection) (mv-nth 1 selection) (mv-nth 2 selection) (mv-nth 2 copy) fn-ew-buffer)))))))) :rule-classes nil))

(defconst *pwzt-preset-model-win*
  (append (make-list 32768 :initial-element 0) '(65 66)
          (make-list 32766 :initial-element 0)))

; Complete positive split witness.
(local (defthm pwzt-copy-split-positive (let ((k1 64) (k2 123) (tout 64) (w 64) (d 1) (h 0) (fn-zin-win *pwzt-model-win*) (fn-zin-out nil)) (and (natp k1) (natp k2) (natp tout) (equal (fn-zin-copy (+ k1 k2) w d tout h fn-zin-win fn-zin-out) (let ((r (fn-zin-copy k1 w d tout h fn-zin-win fn-zin-out))) (fn-zin-copy k2 (car r) d (+ tout k1) h (mv-nth 1 r) (mv-nth 2 r)))))) :rule-classes nil))

; Logical corrupted-counter removal: k1-natural.
(local (defthm pwzt-copy-split-k1-natural (let ((k1 -1) (k2 2) (tout 64) (w 64) (d 1) (h 0) (fn-zin-win *pwzt-model-win*) (fn-zin-out nil)) (and (natp k2) (natp tout) (not (natp k1)) (not (equal (fn-zin-copy (+ k1 k2) w d tout h fn-zin-win fn-zin-out) (let ((r (fn-zin-copy k1 w d tout h fn-zin-win fn-zin-out))) (fn-zin-copy k2 (car r) d (+ tout k1) h (mv-nth 1 r) (mv-nth 2 r))))))) :rule-classes nil))

; Logical corrupted-counter removal: k2-natural.
(local (defthm pwzt-copy-split-k2-natural (let ((k1 2) (k2 -1) (tout 64) (w 64) (d 1) (h 0) (fn-zin-win *pwzt-model-win*) (fn-zin-out nil)) (and (natp k1) (natp tout) (not (natp k2)) (not (equal (fn-zin-copy (+ k1 k2) w d tout h fn-zin-win fn-zin-out) (let ((r (fn-zin-copy k1 w d tout h fn-zin-win fn-zin-out))) (fn-zin-copy k2 (car r) d (+ tout k1) h (mv-nth 1 r) (mv-nth 2 r))))))) :rule-classes nil))

; Logical corrupted-counter removal: tout-natural.
(local (defthm pwzt-copy-split-tout-natural (let ((k1 1) (k2 1) (tout -1) (w 0) (d 2) (h 2) (fn-zin-win *pwzt-preset-model-win*) (fn-zin-out nil)) (and (natp k1) (natp k2) (not (natp tout)) (not (equal (fn-zin-copy (+ k1 k2) w d tout h fn-zin-win fn-zin-out) (let ((r (fn-zin-copy k1 w d tout h fn-zin-win fn-zin-out))) (fn-zin-copy k2 (car r) d (+ tout k1) h (mv-nth 1 r) (mv-nth 2 r))))))) :rule-classes nil))
