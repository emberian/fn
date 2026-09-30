(in-package "ACL2")
(include-book "../../books/decoded-window-step-trajectory")

; Test-only source fixture: actual initializer and basic bounded scheduling.
(defun-nx pwzst-initial ()
  (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
(defun-nx pwzst-first-chunk ()
  (let ((init (pwzst-initial)))
    (fn-pzw-stored-chunk 1024 (fn-pzd-budget 6 251) 0 6 6 251
                         (car init) '(115 116 28 177 0 0)
                         (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init))))

(local
 (defthm pwzst-actual-step-positive
   (let* ((r (pwzst-first-chunk)) (s (mv-nth 3 r))
          (w (mv-nth 4 r)) (tab (mv-nth 5 r)) (out (mv-nth 6 r)))
     (and (posp 64) (equal (fn-zin-mode s) 12)
          (equal (fn-pwz-step-action-count 64 s w tab out) 64)
          (equal (fn-zin-step 64 s w tab out)
                 (fn-pwz-action-sequence (fn-pwz-step-action-count 64 s w tab out) s w tab out))))
   :rule-classes nil))

(local
 (defthm pwzst-actual-clipped-match-positive
   (let* ((r (pwzst-first-chunk)) (s (mv-nth 3 r))
          (w (mv-nth 4 r)) (tab (mv-nth 5 r)) (out (mv-nth 6 r))
          (k (min (fn-zin-n s) (min 7 (nfix (- (fn-zin-bomb-limit s) (fn-zin-tout s)))))))
     (and (equal (fn-zin-mode s) 12) (posp k) (equal k 7)
          (equal (let ((match (fn-zin-match 7 s w out)))
                   (mv (car match) (mv-nth 1 match) (mv-nth 2 match) tab (mv-nth 3 match)))
                 (fn-pwz-action-sequence k s w tab out))))
   :rule-classes nil))

(local
 (defthm pwzst-actual-loop-positive
   (let* ((r (pwzst-first-chunk)) (s (fn-zin-set 7 (+ 6 (fn-zin-tin (mv-nth 3 r))) (mv-nth 3 r)))
          (w (mv-nth 4 r)) (tab (mv-nth 5 r)) (c '(115 116 28 177 0 0)) (ip (mv-nth 2 r)))
     (and (equal (car (fn-zin-loop 1 ip 6 64 s c w tab nil)) :yield)
          (equal (fn-zin-loop 1 ip 6 64 s c w tab nil)
                 (fn-pwz-action-trajectory-loop 1 ip 6 64 s c w tab nil))))
   :hints (("Goal" :expand ((:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 0 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 100 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1023 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1024 ip end lim zs input win tab out)))))
   :rule-classes nil))

(local
 (defthm pwzst-actual-stored-chunk-positive
   (let* ((init (pwzst-initial)) (s (car init))
          (w (mv-nth 1 init)) (tab (mv-nth 2 init)) (out (mv-nth 3 init))
          (c '(115 116 28 177 0 0)))
     (and (fn-zin-window-ready-p w) (fn-zin-tab-okp tab)
          (equal (fn-pzw-stored-chunk 1 (fn-pzd-budget 6 251) 0 6 6 251 s c w tab out)
                 (fn-pwz-stored-action-trajectory 1 (fn-pzd-budget 6 251) 0 6 6 251 s c w tab out))))
   :hints (("Goal" :expand ((:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 0 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 100 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1023 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1024 ip end lim zs input win tab out)))))
   :rule-classes nil))

; Corrupted request: only the positive-room premise of the actual STEP join
; is absent. A genuine pending copy emits under ACT but STEP0 refuses bomb.
(local
 (defthm pwzst-step-room-removal
   (let* ((r (pwzst-first-chunk)) (s (mv-nth 3 r))
          (w (mv-nth 4 r)) (tab (mv-nth 5 r)) (out (mv-nth 6 r)))
     (and (not (posp 0))
          (not (equal (fn-zin-step 0 s w tab out)
                      (fn-pwz-action-sequence (fn-pwz-step-action-count 0 s w tab out) s w tab out)))))
   :rule-classes nil))

; Full caller witness starts at the actual bounded source state. Z is the
; controller record reconstructed from the exact first chunk's returned
; source tuple; it is not authority to publish a native buffer.
(defun-nx pwzst-codec-state ()
  (let ((r (pwzst-first-chunk)))
    (fn-ewz-state :codec '(:trailer 7 100 9 8 0 0 9 23 47 59 102 6 6)
                  251 0 251 (fn-pzw-budget-left 1024 (fn-pzd-budget 6 251) (mv-nth 1 r))
                  (mv-nth 2 r) 6 (car r))))

(local
 (defthm pwzst-actual-codec-positive
   (let* ((r (pwzst-first-chunk)) (s (mv-nth 3 r))
          (w (mv-nth 4 r)) (tab (mv-nth 5 r)) (out (mv-nth 6 r))
          (z (pwzst-codec-state)) (c '(115 116 28 177 0 0)) (buffer (create-fn-ew-buffer)))
     (and (fn-zin-window-ready-p w) (fn-zin-tab-okp tab)
          (equal (fn-ewz-codec-tick z c s w tab out buffer)
                 (fn-pwz-codec-action-trajectory z c s w tab out buffer))))
   :hints (("Goal" :expand ((:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 0 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 100 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1023 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1024 ip end lim zs input win tab out)))))
   :rule-classes nil))

; Corrupted buffers: affirm the retained hypothesis and show that the
; actual feed refusal differs from an unauthorized semantic replay.
(local
 (defthm pwzst-codec-window-removal
   (let* ((init (pwzst-initial)) (s (car init)) (tab (mv-nth 2 init))
          (z (fn-ewz-state :codec '(:scan 7 100 1 0 0 0 0 23 47 59 100 1 1)
                          0 0 0 100 0 0 :more)) (buffer (create-fn-ew-buffer)))
     (and (not (fn-zin-window-ready-p nil)) (fn-zin-tab-okp tab)
          (not (equal (fn-ewz-codec-tick z nil s nil tab nil buffer)
                      (fn-pwz-codec-action-trajectory z nil s nil tab nil buffer)))))
   :hints (("Goal" :expand ((:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 0 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 100 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1023 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1024 ip end lim zs input win tab out)))))
   :rule-classes nil))

(local
 (defthm pwzst-codec-table-removal
   (let* ((init (pwzst-initial)) (s (car init)) (w (mv-nth 1 init))
          (z (fn-ewz-state :codec '(:scan 7 100 1 0 0 0 0 23 47 59 100 1 1)
                          0 0 0 100 0 0 :more)) (buffer (create-fn-ew-buffer)))
     (and (fn-zin-window-ready-p w) (not (fn-zin-tab-okp nil))
          (not (equal (fn-ewz-codec-tick z nil s w nil nil buffer)
                      (fn-pwz-codec-action-trajectory z nil s w nil nil buffer)))))
   :hints (("Goal" :expand ((:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 0 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 100 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1023 ip end lim zs input win tab out))
(:free (ip end lim zs input win tab out) (fn-pwz-action-trajectory-loop 1024 ip end lim zs input win tab out)))))
   :rule-classes nil))

; Exact clipped-match premise removals, labelled corrupted state/request.
(local
 (defthm pwzst-clipped-match-mode-removal
   (let* ((r (pwzst-first-chunk)) (s (fn-zin-set 0 13 (mv-nth 3 r)))
          (w (mv-nth 4 r)) (tab (mv-nth 5 r)) (out (mv-nth 6 r))
          (k (min (fn-zin-n s) (min 7 (nfix (- (fn-zin-bomb-limit s) (fn-zin-tout s)))))))
     (and (not (equal (fn-zin-mode s) 12)) (posp k)
          (not (equal (let ((match (fn-zin-match 7 s w out)))
                        (mv (car match) (mv-nth 1 match) (mv-nth 2 match) tab (mv-nth 3 match)))
                      (fn-pwz-action-sequence k s w tab out)))))
   :rule-classes nil))

(local
 (defthm pwzst-clipped-match-count-removal
   (let* ((r (pwzst-first-chunk)) (s (mv-nth 3 r))
          (w (mv-nth 4 r)) (tab (mv-nth 5 r)) (out (mv-nth 6 r))
          (k (min (fn-zin-n s) (min 0 (nfix (- (fn-zin-bomb-limit s) (fn-zin-tout s)))))))
     (and (equal (fn-zin-mode s) 12) (not (posp k))
          (not (equal (let ((match (fn-zin-match 0 s w out)))
                        (mv (car match) (mv-nth 1 match) (mv-nth 2 match) tab (mv-nth 3 match)))
                      (fn-pwz-action-sequence k s w tab out)))))
   :rule-classes nil))

(local
 (defthm pwzst-stored-window-removal
   (let* ((init (pwzst-initial)) (s (car init)) (tab (mv-nth 2 init)))
     (and (not (fn-zin-window-ready-p nil)) (fn-zin-tab-okp tab)
          (not (equal (fn-pzw-stored-chunk 1 100 0 0 1 0 s nil nil tab nil)
                      (fn-pwz-stored-action-trajectory 1 100 0 0 1 0 s nil nil tab nil)))))
   :hints (("Goal" :expand ((:free (ip end lim zs input win tab out)
                                   (fn-pwz-action-trajectory-loop 1 ip end lim zs input win tab out)))))
   :rule-classes nil))

(local
 (defthm pwzst-stored-table-removal
   (let* ((init (pwzst-initial)) (s (car init)) (w (mv-nth 1 init)))
     (and (fn-zin-window-ready-p w) (not (fn-zin-tab-okp nil))
          (not (equal (fn-pzw-stored-chunk 1 100 0 0 1 0 s nil w nil nil)
                      (fn-pwz-stored-action-trajectory 1 100 0 0 1 0 s nil w nil nil)))))
   :hints (("Goal" :expand ((:free (ip end lim zs input win tab out)
                                   (fn-pwz-action-trajectory-loop 1 ip end lim zs input win tab out)))))
   :rule-classes nil))
