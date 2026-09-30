; Bounded compressed-payload chunks for the streaming extent reader.
; PRF-1112 / SCN-1020. This is a component, not yet a served-path claim.
; Reuses the resumable inflater; no second decoder and no whole payload
; list materialization. The caller retains selected output privately until
; exact decoded length and full extent authentication both succeed.
(in-package "ACL2")
(include-book "payload-deflate")

(defconst *fn-pzw-input-octets* 64)
(defconst *fn-pzw-output-octets* 64)
(defconst *fn-pzw-actions* 1024)

(defun fn-pzw-quantum (requested remaining)
  (declare (xargs :guard t))
  (min *fn-pzw-actions* (min (nfix requested) (nfix remaining))))

(defun fn-pzw-room (expected produced)
  (declare (xargs :guard t))
  ; One extra octet detects expansion past the committed decoded length.
  (min *fn-pzw-output-octets* (+ 1 (nfix (- (nfix expected) (nfix produced))))))

(defthm fn-pzw-room-bounds
  (and (posp (fn-pzw-room expected produced))
       (<= (fn-pzw-room expected produced) *fn-pzw-output-octets*))
  :rule-classes :rewrite)

(defun fn-pzw-chunk (requested remaining start end expected
                    fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (natp start) (natp end) (<= start end)
                              (<= (- end start) *fn-pzw-input-octets*)
                              (<= end (fn-octets-len fn-octets)))))
  ; Previous scratch output must already have been copied or discarded by
  ; the caller. The decoded position remains in fn-zin-st, not this buffer.
  (let ((fn-zin-out (fn-zin-out-clear fn-zin-out)))
    (fn-zin-feed (fn-pzw-quantum requested remaining) fn-zin-st start end
                 (fn-pzw-room expected (fn-zin-tout fn-zin-st))
                 fn-octets fn-zin-win fn-zin-tab fn-zin-out)))

(defthm fn-pzw-chunk-output-is-bounded
  (let ((r (fn-pzw-chunk requested remaining start end expected
                          fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (true-listp (mv-nth 6 r))
         (<= (len (mv-nth 6 r)) *fn-pzw-output-octets*)))
  :hints (("Goal" :in-theory (disable fn-zin-feed fn-pzw-room fn-pzw-quantum fn-zin-feed-out-bound fn-pzw-room-bounds)
           :use ((:instance fn-pzw-room-bounds (produced (fn-zin-tout fn-zin-st)))
                 (:instance fn-zin-feed-out-bound
                            (b (fn-pzw-quantum requested remaining))
                            (lim (fn-pzw-room expected (fn-zin-tout fn-zin-st)))
                            (fn-zin-out nil))))))

; Exact representation boundary: all decoder state/effects and produced
; bytes equal the existing logical resumable run over exactly this input
; span. This intentionally does not equate the old lookahead refusal domain.
(defthm fn-pzw-chunk-is-resumable-run
  (implies (and (natp start) (natp end) (<= start end)
                (<= end (len fn-octets))
                (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (equal
            (fn-pzw-chunk requested remaining start end expected
                          fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
            (let ((r (fn-zin-run (fn-pzw-quantum requested remaining) fn-zin-st
                                  (take (- end start) (nthcdr start fn-octets))
                                  (fn-pzw-room expected (fn-zin-tout fn-zin-st))
                                  fn-zin-win fn-zin-tab nil)))
              (mv (car r) (mv-nth 1 r) (+ start (mv-nth 2 r)) (mv-nth 3 r)
                  (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
  :hints (("Goal" :in-theory (disable fn-zin-feed fn-zin-loop fn-zin-run
                                      fn-pzw-quantum fn-pzw-room)
           :use ((:instance fn-zin-feed-unfolds
                            (b (fn-pzw-quantum requested remaining))
                            (lim (fn-pzw-room expected (fn-zin-tout fn-zin-st)))
                            (fn-zin-out nil))
                 (:instance fn-zin-loop-is-run
                            (b (fn-pzw-quantum requested remaining)) (ip start)
                            (x fn-octets)
                            (lim (fn-pzw-room expected (fn-zin-tout fn-zin-st)))
                            (fn-zin-out nil))))))


(defun fn-pzw-budget-left (requested remaining returned)
  (declare (xargs :guard t))
  (let ((q (fn-pzw-quantum requested remaining)))
    (- (nfix remaining) (- q (min q (nfix returned))))))

(defthm fn-pzw-budget-left-bounds
  (and (natp (fn-pzw-budget-left requested remaining returned))
       (<= (fn-pzw-budget-left requested remaining returned) (nfix remaining)))
  :hints (("Goal" :in-theory (enable fn-pzw-quantum))))

(defun fn-pzw-decision (status produced expected remaining compressed-complete)
  (declare (xargs :guard t))
  ; :decoded is PRIVATE codec completion, never permission to publish.
  ; The extent controller must separately authenticate the full prefix.
  ; Preserve the existing :more acceptance at end of compressed input.
  (cond ((< (nfix expected) (nfix produced)) (list :error :length))
        ((fn-pzd-endedp status)
         (cond ((and (equal status '(:refused :stream-ended))
                     (not (equal (nfix produced) (nfix expected))))
                (list :error :length))
               ((not compressed-complete)
                (if (eq status :more) :input :drain))
               ((equal (nfix produced) (nfix expected)) :decoded)
               (t (list :error :length))))
        ((consp status) (list :error status))
        ((zp (nfix remaining)) (list :error :yield))
        (t :resume)))

(defthm fn-pzw-decoded-has-exact-length
  (implies (equal (fn-pzw-decision status produced expected remaining complete) :decoded)
           (and complete (fn-pzd-endedp status)
                (equal (nfix produced) (nfix expected))))
  :rule-classes nil)

(defun fn-pzw-select (produced count offset requested)
  (declare (xargs :guard t))
  ; (scratch-source, count, private-window-destination), empty when disjoint.
  (let* ((base (nfix produced)) (n (min 64 (nfix count)))
         (off (nfix offset)) (want (min 16384 (nfix requested)))
         (start (max base off)) (end (min (+ base n) (+ off want))))
    (if (< start end) (mv (- start base) (- end start) (- start off))
      (mv 0 0 0))))

(defthm fn-pzw-select-bounded
  (let ((r (fn-pzw-select produced count offset requested)))
    (and (natp (car r)) (natp (mv-nth 1 r)) (natp (mv-nth 2 r))
         (<= (+ (car r) (mv-nth 1 r)) (min 64 (nfix count)))
         (<= (+ (mv-nth 2 r) (mv-nth 1 r)) (min 16384 (nfix requested))))))

(defthm fn-pzw-select-copied-position
  (let ((r (fn-pzw-select produced count offset requested)))
    (implies (< (nfix i) (mv-nth 1 r))
             (equal (+ (nfix produced) (car r) (nfix i))
                    (+ (nfix offset) (mv-nth 2 r) (nfix i))))))

(defun fn-pzw-stored-allowance (compressed)
  (declare (xargs :guard t))
  (fn-zin-stored-allowance compressed))

(defun fn-pzw-stored-admissiblep (compressed expected)
  (declare (xargs :guard t))
  (and (natp compressed) (natp expected)
       (<= expected (fn-pzw-stored-allowance compressed))))

(defun fn-pzw-stored-chunk (requested remaining start end compressed expected
                           fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (natp start) (natp end) (<= start end)
                              (<= (- end start) *fn-pzw-input-octets*)
                              (<= end (fn-octets-len fn-octets)))))
  ; Distinct stored-input policy: credit the declared compressed length
  ; during this call only. Never passed to the network decoder's state.
  ; The external state retains its real consumed-input count. Credit does
  ; not cause allocation: only scalar arithmetic; output is <=64, and its
  ; total is capped at min(N, 256*C+65536)+1, including a private sentinel.
  (let* ((credit (nfix compressed))
         (bound (min (nfix expected) (fn-pzw-stored-allowance compressed)))
         (fn-zin-st (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st)))
    (mv-let (status left ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (fn-pzw-chunk requested remaining start end bound
                    fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
      (let ((fn-zin-st (fn-zin-set 7 (nfix (- (fn-zin-tin fn-zin-st) credit)) fn-zin-st)))
        (mv status left ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))))

(defthm fn-pzw-stored-chunk-output-is-bounded
  (let ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                               fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (true-listp (mv-nth 6 r))
         (<= (len (mv-nth 6 r)) *fn-pzw-output-octets*)))
  :hints (("Goal" :in-theory (disable fn-pzw-chunk fn-pzw-stored-allowance))))

(defthm fn-pzw-stored-chunk-is-resumable-run
  (implies (and (natp start) (natp end) (<= start end)
                (<= end (len fn-octets))
                (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (equal
            (fn-pzw-stored-chunk requested remaining start end compressed expected
                                fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
            (let* ((credit (nfix compressed))
                   (bound (min (nfix expected) (fn-pzw-stored-allowance compressed)))
                   (state (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))
                   (r (fn-zin-run (fn-pzw-quantum requested remaining) state
                                  (take (- end start) (nthcdr start fn-octets))
                                  (fn-pzw-room bound (fn-zin-tout state))
                                  fn-zin-win fn-zin-tab nil))
                   (state2 (fn-zin-set 7 (nfix (- (fn-zin-tin (mv-nth 3 r)) credit))
                                       (mv-nth 3 r))))
              (mv (car r) (mv-nth 1 r) (+ start (mv-nth 2 r)) state2
                  (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
  :hints (("Goal" :in-theory (disable fn-pzw-chunk fn-zin-run fn-pzw-quantum
                                      fn-pzw-room fn-pzw-stored-allowance))))

(defthm fn-pzw-chunk-counts
  (implies (and (natp start)
                (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (let ((r (fn-pzw-chunk requested remaining start end expected
                                fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
             (and (natp (mv-nth 2 r)) (<= start (mv-nth 2 r))
                  (equal (fn-zin-tin (mv-nth 3 r))
                         (+ (fn-zin-tin fn-zin-st) (- (mv-nth 2 r) start)))
                  (equal (fn-zin-tout (mv-nth 3 r))
                         (+ (fn-zin-tout fn-zin-st) (len (mv-nth 6 r)))))))
  :hints (("Goal" :in-theory (disable fn-zin-loop fn-zin-feed fn-pzw-quantum
                                      fn-pzw-room fn-zin-loop-counts)
           :use ((:instance fn-zin-loop-counts
                            (b (fn-pzw-quantum requested remaining)) (ip start)
                            (lim (fn-pzw-room expected (fn-zin-tout fn-zin-st)))
                            (fn-zin-out nil))
                 (:instance fn-zin-feed-unfolds
                            (b (fn-pzw-quantum requested remaining))
                            (lim (fn-pzw-room expected (fn-zin-tout fn-zin-st)))
                            (fn-zin-out nil))))))

(defthm fn-pzw-stored-chunk-counts-real-input
  (implies (and (natp start)
                (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (let ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                       fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
             (and (natp (mv-nth 2 r)) (<= start (mv-nth 2 r))
                  (equal (fn-zin-tin (mv-nth 3 r))
                         (+ (fn-zin-tin fn-zin-st) (- (mv-nth 2 r) start)))
                  (equal (fn-zin-tout (mv-nth 3 r))
                         (+ (fn-zin-tout fn-zin-st) (len (mv-nth 6 r)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-pzw-chunk fn-pzw-stored-allowance fn-pzw-chunk-counts min)
           :use ((:instance fn-pzw-chunk-counts
                            (expected (min (nfix expected) (fn-pzw-stored-allowance compressed)))
                            (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st))
                                                  fn-zin-st)))))))

(defthm fn-pzw-chunk-output-room
  (<= (len (mv-nth 6 (fn-pzw-chunk requested remaining start end expected
                                 fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
      (fn-pzw-room expected (fn-zin-tout fn-zin-st)))
  :hints (("Goal" :in-theory (disable fn-zin-feed fn-pzw-room fn-pzw-quantum
                                      fn-zin-feed-out-bound)
           :use ((:instance fn-zin-feed-out-bound
                            (b (fn-pzw-quantum requested remaining))
                            (lim (fn-pzw-room expected (fn-zin-tout fn-zin-st)))
                            (fn-zin-out nil))))))

(defthm fn-pzw-stored-chunk-total-bound
  (implies (and (natp start)
                (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*)
                (<= (fn-zin-tout fn-zin-st)
                    (min (nfix expected) (fn-pzw-stored-allowance compressed))))
           (let ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                       fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
             (<= (fn-zin-tout (mv-nth 3 r))
                 (+ 1 (min (nfix expected) (fn-pzw-stored-allowance compressed))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-pzw-chunk fn-pzw-stored-allowance
                               fn-pzw-chunk-counts fn-pzw-chunk-output-room fn-pzw-chunk-output-is-bounded)
           :use ((:instance fn-pzw-chunk-counts
                            (expected (min (nfix expected) (fn-pzw-stored-allowance compressed)))
                            (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st))
                                                  fn-zin-st)))
                 (:instance fn-pzw-chunk-output-room
                            (expected (min (nfix expected) (fn-pzw-stored-allowance compressed)))
                            (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st))
                                                  fn-zin-st)))))))

(defun fn-pzw-stored-decision (status compressed expected remaining complete fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (cond ((not (fn-pzw-stored-admissiblep compressed expected)) (list :error :bomb))
        ((and complete (eql compressed 0) (eql expected 0)
              (eql (fn-zin-tin fn-zin-st) 0) (eql (fn-zin-tout fn-zin-st) 0))
         :decoded)
        (t (fn-pzw-decision
            (if (or complete (equal status '(:refused :stream-ended)))
                (fn-zin-stored-status status compressed fn-zin-st) status)
            (fn-zin-tout fn-zin-st) expected remaining complete))))

(defthm fn-pzw-stored-decoded-is-complete
  (implies (equal (fn-pzw-stored-decision status compressed expected remaining complete fn-zin-st)
                  :decoded)
           (and complete (fn-pzw-stored-admissiblep compressed expected)
                (equal (fn-zin-tout fn-zin-st) expected)
                (or (and (equal compressed 0) (equal expected 0)
                         (equal (fn-zin-tin fn-zin-st) 0))
                    (fn-zin-stored-terminalp status fn-zin-st))))
  :rule-classes nil)

; Actual machine witness generalized over all other state and all buffers:
; parsing LEN=0, NLEN=65535 of a non-final stored block, then completing
; that block, establishes the sync-flush terminal and changes no octets.
(defthm fn-pzw-empty-stored-block-establishes-terminal
  (implies (and (equal (fn-zin-mode fn-zin-st) 2)
                (equal (fn-zin-bits fn-zin-st) 4294901760)
                (equal (fn-zin-nbits fn-zin-st) 32)
                (equal (fn-zin-final fn-zin-st) 0))
           (let* ((a (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                  (b (fn-zin-act (mv-nth 1 a) (mv-nth 2 a) (mv-nth 3 a) (mv-nth 4 a))))
             (and (equal (car a) nil) (equal (car b) nil)
                  (fn-zin-stored-terminalp :more (mv-nth 1 b))
                  (equal (fn-zin-tout (mv-nth 1 b)) (fn-zin-tout fn-zin-st))
                  (equal (mv-nth 2 b) fn-zin-win)
                  (equal (mv-nth 3 b) fn-zin-tab)
                  (equal (mv-nth 4 b) fn-zin-out))))
  :hints (("Goal" :in-theory (enable fn-zin-act fn-zin-take fn-zin-block-end))))

(defun fn-pzw-initialize (dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (fn-cbor-octet-listp dict) (<= (len dict) 65536))))
  ; Lease admission must precede these fixed reserves. DICT is a pinned
  ; shipped preset (the table permits <=64 KiB), not a per-request list. Initialization does
  ; fixed <=65536+3494+64 buffer work, separately from a decoder quantum.
  (let* ((fn-zin-st (fn-zin-reset fn-zin-st))
         (fn-zin-out (fn-zin-out-clear fn-zin-out))
         (fn-zin-out (fn-zin-out-reserve 64 fn-zin-out)))
    (mv-let (h fn-zin-win fn-zin-tab) (fn-zin-payload-ready dict fn-zin-win fn-zin-tab)
      (let ((fn-zin-st (fn-zin-set 18 h fn-zin-st)))
        (mv fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))))

(defthm fn-pzw-initialize-establishes-buffers
  (implies (fn-cbor-octet-listp dict)
           (let ((r (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             (and (equal (len (mv-nth 1 r)) *fn-zin-win-octets*)
                  (equal (len (mv-nth 2 r)) *fn-zin-tab-octets*)
                  (fn-cbor-octet-listp (mv-nth 1 r))
                  (fn-cbor-octet-listp (mv-nth 2 r))
                  (equal (mv-nth 3 r) nil))))
  :hints (("Goal" :in-theory (disable fn-zin-payload-ready))))
