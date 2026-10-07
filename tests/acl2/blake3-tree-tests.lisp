; fn: teeth for the BLAKE3 window decomposition of books/blake3-tree.lisp.
;
; The keystones relate the reference tree (`fn-b3-node') to the window
; composition a streaming digest holds: the window subtree outputs, each at
; its own chunk counter, treed by the same largest-power-of-two split.  A
; theorem about the function's own recursion bounds nothing, so each keystone
; has positive witnesses on real multi-window inputs (2 and 3 windows at k=0
; and k=1, counter 0 and nonzero), a removal witness for each hypothesis that
; is load-bearing, and a mutation (a window at the wrong chunk counter) that
; the claim's equation rejects.
;
; Two hypotheses were ADDED to the statements recorded as owed, each because
; the statement is false without it (the removal witnesses below are the
; counterexamples): (natp counter), since a non-natural counter reaches the
; compression function raw while the window outputs read it through NFIX; and,
; on fn-b3-append-window, (consp prefix), since the window outputs of the
; empty input are one window (the empty input's), which the stack would then
; merge with.

(in-package "ACL2")
(include-book "../../books/blake3-tree")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

(defun fn-b3tt-input-from (i n)
  (declare (xargs :guard (and (natp i) (natp n)) :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (mod i 251) (fn-b3tt-input-from (+ i 1) n))
    nil))

(defmacro fn-b3tt-input (n) `(fn-b3tt-input-from 0 ,n))

; The decomposition, evaluated: 3 windows at k=0 (2500 octets: 1024, 1024,
; 452), 2 windows at k=0 (1025 octets), 2 windows at k=1 (2048-octet windows,
; 3000 octets), one window (1000 octets), at counter 0 and nonzero.
(assert-event
 (and (equal (fn-b3-node *fn-b3-iv* (fn-b3tt-input 2500) 0 0)
             (fn-b3-window-tree *fn-b3-iv* 0
               (fn-b3-window-outs *fn-b3-iv* 0 0 (fn-b3tt-input 2500) 0)))
      (equal (fn-b3-node *fn-b3-iv* (fn-b3tt-input 1025) 7 0)
             (fn-b3-window-tree *fn-b3-iv* 0
               (fn-b3-window-outs *fn-b3-iv* 0 7 (fn-b3tt-input 1025) 0)))
      (equal (fn-b3-node *fn-b3-iv* (fn-b3tt-input 3000) 3 0)
             (fn-b3-window-tree *fn-b3-iv* 0
               (fn-b3-window-outs *fn-b3-iv* 1 3 (fn-b3tt-input 3000) 0)))
      (equal (fn-b3-node *fn-b3-iv* (fn-b3tt-input 1000) 5 0)
             (fn-b3-window-tree *fn-b3-iv* 0
               (fn-b3-window-outs *fn-b3-iv* 0 5 (fn-b3tt-input 1000) 0))))
 :msg "blake3-tree: window decomposition at 3, 2, 2 (k=1) and 1 windows")

(defteeth fn-b3-node-is-window-tree
  :claim (((counter (natp counter)))
          (equal (fn-b3-node key octets counter flags)
                 (fn-b3-window-tree key flags
                   (fn-b3-window-outs key k counter octets flags))))
  :witness ((key *fn-b3-iv*) (octets (fn-b3tt-input 2500)) (counter 5)
            (flags 0) (k 0))
  :breaks ((counter ((key *fn-b3-iv*) (octets (fn-b3tt-input 3)) (counter -1)
                     (flags 0) (k 0))
                    :logical "a negative chunk counter is outside the natural-number domain"))
  :mutations ((wrong-counter
               (:conclusion
                (equal (fn-b3-node key octets counter flags)
                       (fn-b3-window-tree key flags
                         (fn-b3-window-outs key k (+ 1 counter) octets flags))))
               ((key *fn-b3-iv*) (octets (fn-b3tt-input 2500)) (counter 5)
                (flags 0) (k 0))
               :fault "the windows hashed at chunk counters shifted by one")))

;; fn-blake3-is-window-composition has no hypothesis: the equation holds for
; any object read as octets (both sides coerce alike), so the claim's
; hypothesis list is empty and there is no removal witness to give.  Teeth: a
; positive witness on 3 windows, and mutations that falsify the equation (a
; shifted chunk counter; the root flag).
(defteeth fn-blake3-is-window-composition
  :claim (()
          (equal (fn-blake3 m)
                 (fn-b3-output-root
                   (fn-b3-window-tree *fn-b3-iv* 0
                     (fn-b3-window-outs *fn-b3-iv* k 0 m 0)))))
  :witness ((m (fn-b3tt-input 2500)) (k 0))
  :breaks ()
  :mutations ((wrong-counter
               (:conclusion
                (equal (fn-blake3 m)
                       (fn-b3-output-root
                         (fn-b3-window-tree *fn-b3-iv* 0
                           (fn-b3-window-outs *fn-b3-iv* k 1 m 0)))))
               ((m (fn-b3tt-input 2500)) (k 0))
               :fault "the windows hashed at chunk counters shifted by one")
              (wrong-flags
               (:conclusion
                (equal (fn-blake3 m)
                       (fn-b3-output-root
                         (fn-b3-window-tree *fn-b3-iv* 1
                           (fn-b3-window-outs *fn-b3-iv* k 0 m 0)))))
               ((m (fn-b3tt-input 2500)) (k 0))
               :fault "the window tree's parents compressed under a stray flag bit")))

; More positive witnesses: 2 windows (k=0), 2 windows (k=1), the empty input,
; and a non-octet object (the equation holds there too).
(assert-event
 (and (equal (fn-blake3 (fn-b3tt-input 1025))
             (fn-b3-output-root
               (fn-b3-window-tree *fn-b3-iv* 0
                 (fn-b3-window-outs *fn-b3-iv* 0 0 (fn-b3tt-input 1025) 0))))
      (equal (fn-blake3 (fn-b3tt-input 3000))
             (fn-b3-output-root
               (fn-b3-window-tree *fn-b3-iv* 0
                 (fn-b3-window-outs *fn-b3-iv* 1 0 (fn-b3tt-input 3000) 0))))
      (equal (fn-blake3 nil)
             (fn-b3-output-root
               (fn-b3-window-tree *fn-b3-iv* 0
                 (fn-b3-window-outs *fn-b3-iv* 0 0 nil 0))))
      (equal (fn-blake3 (cons 300 (fn-b3tt-input 1100)))
             (fn-b3-output-root
               (fn-b3-window-tree *fn-b3-iv* 0
                 (fn-b3-window-outs *fn-b3-iv* 0 0
                                    (cons 300 (fn-b3tt-input 1100)) 0)))))
 :msg "fn-blake3-is-window-composition: 2 windows at k=0 and k=1, empty, non-octet")

(defteeth fn-b3-stack-fold-of-windows
  :claim (((counter (natp counter)))
          (equal (fn-b3-stack-fold key flags
                   (fn-b3-stack-push-all key flags k
                     (fn-b3-window-outs key k counter octets flags) nil))
                 (fn-b3-node key octets counter flags)))
  :witness ((key *fn-b3-iv*) (octets (fn-b3tt-input 2500)) (counter 5)
            (flags 0) (k 0))
  :breaks ((counter ((key *fn-b3-iv*) (octets (fn-b3tt-input 3)) (counter -1)
                     (flags 0) (k 0))
                    :logical "a negative chunk counter is outside the natural-number domain"))
  :mutations ((wrong-counter
               (:conclusion
                (equal (fn-b3-stack-fold key flags
                         (fn-b3-stack-push-all key flags k
                           (fn-b3-window-outs key k counter octets flags) nil))
                       (fn-b3-node key octets (+ 1 counter) flags)))
               ((key *fn-b3-iv*) (octets (fn-b3tt-input 2500)) (counter 5)
                (flags 0) (k 0))
               :fault "the node read at a counter shifted by one from the windows'")))

; The stack at k=0 over 4 windows (2 merges) and k=1 over 3 windows.
(assert-event
 (and (equal (fn-b3-stack-fold *fn-b3-iv* 0
               (fn-b3-stack-push-all *fn-b3-iv* 0 0
                 (fn-b3-window-outs *fn-b3-iv* 0 0 (fn-b3tt-input 4000) 0) nil))
             (fn-b3-node *fn-b3-iv* (fn-b3tt-input 4000) 0 0))
      (equal (fn-b3-stack-fold *fn-b3-iv* 0
               (fn-b3-stack-push-all *fn-b3-iv* 0 1
                 (fn-b3-window-outs *fn-b3-iv* 1 9 (fn-b3tt-input 5000) 0) nil))
             (fn-b3-node *fn-b3-iv* (fn-b3tt-input 5000) 9 0)))
 :msg "fn-b3-stack-fold-of-windows: 4 windows at k=0, 3 windows at k=1")

; fn-b3-append-window: the octet-listp hypotheses have no breaking value
; either (a non-octet prefix or window does not falsify the equation), so
; they are grouped, in the claim, with the hypotheses that do (the grouped
; claim translates to the same term as the flat theorem).  The group's
; removal witness is the empty prefix: its window outputs are the one window
; of the empty input, which the stack merges with the appended window.  The
; other individual hypotheses' counterexamples follow as assert-events.
(defteeth fn-b3-append-window
  :claim (((counter (natp counter))
           (windows (and (fn-b3-octet-listp prefix) (consp prefix)
                         (equal (mod (len prefix) (* 1024 (expt 2 (nfix k)))) 0)
                         (fn-b3-octet-listp w) (posp (len w))
                         (<= (len w) (* 1024 (expt 2 (nfix k)))))))
          (equal (fn-b3-stack-fold key flags
                   (fn-b3-cv-push key flags k
                     (fn-b3-node key w
                       (+ (nfix counter)
                          (* (expt 2 (nfix k))
                             (floor (len prefix) (* 1024 (expt 2 (nfix k))))))
                       flags)
                     (fn-b3-stack-push-all key flags k
                       (fn-b3-window-outs key k counter prefix flags) nil)))
                 (fn-b3-node key (append prefix w) counter flags)))
  :witness ((key *fn-b3-iv*) (flags 0) (k 0) (counter 5)
            (prefix (fn-b3tt-input 2048)) (w (fn-b3tt-input 1024)))
  :breaks ((counter ((key *fn-b3-iv*) (flags 0) (k 0) (counter -1)
                     (prefix (fn-b3tt-input 1024)) (w (fn-b3tt-input 10)))
                    :logical "a negative chunk counter is outside the natural-number domain")
           (windows ((key *fn-b3-iv*) (flags 0) (k 0) (counter 0)
                     (prefix nil) (w (fn-b3tt-input 10)))))
  :mutations ((unshifted-window-counter
               (:conclusion
                (equal (fn-b3-stack-fold key flags
                         (fn-b3-cv-push key flags k
                           (fn-b3-node key w (nfix counter) flags)
                           (fn-b3-stack-push-all key flags k
                             (fn-b3-window-outs key k counter prefix flags) nil)))
                       (fn-b3-node key (append prefix w) counter flags)))
               ((key *fn-b3-iv*) (flags 0) (k 0) (counter 5)
                (prefix (fn-b3tt-input 2048)) (w (fn-b3tt-input 1024)))
               :fault "the appended window hashed at the stream's base counter, not its own")))

(defun fn-b3tt-append (k counter prefix w c2)
  ; The append-window equation with the appended window at chunk counter C2.
  (equal (fn-b3-stack-fold *fn-b3-iv* 0
           (fn-b3-cv-push *fn-b3-iv* 0 k
             (fn-b3-node *fn-b3-iv* w c2 0)
             (fn-b3-stack-push-all *fn-b3-iv* 0 k
               (fn-b3-window-outs *fn-b3-iv* k counter prefix 0) nil)))
         (fn-b3-node *fn-b3-iv* (append prefix w) counter 0)))

; Positive: 1, 2 and 3 whole windows held (the 3-window stack cascades), k=0
; and k=1, counter 0 and nonzero; the appended window short, full.
(assert-event
 (and (fn-b3tt-append 0 0 (fn-b3tt-input 1024) (fn-b3tt-input 452) 1)
      (fn-b3tt-append 0 5 (fn-b3tt-input 2048) (fn-b3tt-input 1024) 7)
      (fn-b3tt-append 0 0 (fn-b3tt-input 3072) (fn-b3tt-input 1) 3)
      (fn-b3tt-append 1 3 (fn-b3tt-input 2048) (fn-b3tt-input 500) 5))
 :msg "fn-b3-append-window: 1, 2, 3 windows held at k=0 and k=1")

; Each individual hypothesis removed falsifies the equation (c2 is the
; statement's own counter expression at the instance).
(assert-event
 (and (not (fn-b3tt-append 0 -1 (fn-b3tt-input 1024) (fn-b3tt-input 10) 1))      ; counter not natural
      (not (fn-b3tt-append 0 0 nil (fn-b3tt-input 10) 0))                         ; prefix empty
      (not (fn-b3tt-append 0 0 (fn-b3tt-input 1000) (fn-b3tt-input 10) 0))        ; prefix not whole windows
      (not (fn-b3tt-append 0 0 (fn-b3tt-input 1024) nil 1))                       ; window empty
      (not (fn-b3tt-append 0 0 (fn-b3tt-input 1024) (fn-b3tt-input 1025) 1)))     ; window longer than W
 :msg "fn-b3-append-window: each added or load-bearing hypothesis has a counterexample")

;; fn-b3-append-window-state: the post-append STATE (not only its fold) is the
; state over the windows of prefix ++ w.  The hypotheses are those of
; fn-b3-append-window, grouped as there (the octet-listp ones have no
; breaking value).  The wrong-height mutation pushes the window at height
; k+1: the state differs (the fold would not show it).
(defteeth fn-b3-append-window-state
  :claim (((windows (and (fn-b3-octet-listp prefix) (consp prefix)
                         (equal (mod (len prefix) (* 1024 (expt 2 (nfix k)))) 0)
                         (fn-b3-octet-listp w) (posp (len w))
                         (<= (len w) (* 1024 (expt 2 (nfix k)))))))
          (equal (fn-b3-cv-push key flags k
                   (fn-b3-node key w
                     (+ (nfix counter)
                        (* (expt 2 (nfix k))
                           (floor (len prefix) (* 1024 (expt 2 (nfix k))))))
                     flags)
                   (fn-b3-stack-push-all key flags k
                     (fn-b3-window-outs key k counter prefix flags) nil))
                 (fn-b3-stack-push-all key flags k
                   (fn-b3-window-outs key k counter (append prefix w) flags) nil)))
  :witness ((key *fn-b3-iv*) (flags 0) (k 0) (counter 5)
            (prefix (fn-b3tt-input 3072)) (w (fn-b3tt-input 1024)))
  :breaks ((windows ((key *fn-b3-iv*) (flags 0) (k 0) (counter 0)
                     (prefix nil) (w (fn-b3tt-input 10)))))
  :mutations ((wrong-height
               (:conclusion
                (equal (fn-b3-cv-push key flags (+ 1 (nfix k))
                         (fn-b3-node key w
                           (+ (nfix counter)
                              (* (expt 2 (nfix k))
                                 (floor (len prefix) (* 1024 (expt 2 (nfix k))))))
                           flags)
                         (fn-b3-stack-push-all key flags k
                           (fn-b3-window-outs key k counter prefix flags) nil))
                       (fn-b3-stack-push-all key flags k
                         (fn-b3-window-outs key k counter (append prefix w) flags) nil)))
               ((key *fn-b3-iv*) (flags 0) (k 0) (counter 5)
                (prefix (fn-b3tt-input 3072)) (w (fn-b3tt-input 1024)))
               :fault "the appended window pushed at the wrong height, so it fails to merge")))

(assert-event
 (equal (fn-b3-cv-push *fn-b3-iv* 0 0
          (fn-b3-node *fn-b3-iv* (fn-b3tt-input 10) (+ (nfix -1) 1) 0)
          (fn-b3-stack-push-all *fn-b3-iv* 0 0
            (fn-b3-window-outs *fn-b3-iv* 0 -1 (fn-b3tt-input 1024) 0) nil))
        (fn-b3-stack-push-all *fn-b3-iv* 0 0
          (fn-b3-window-outs *fn-b3-iv* 0 -1
            (append (fn-b3tt-input 1024) (fn-b3tt-input 10)) 0) nil))
 :msg "fn-b3-append-window-state: a negative counter does not falsify it")

; Keyed and derive-key digests as window compositions.
(defteeth fn-blake3-keyed-is-window-composition
  :claim (()
          (equal (fn-blake3-keyed key m)
                 (fn-b3-output-root
                   (fn-b3-window-tree (fn-b3-words 8 (fn-b3-fix-octets key))
                                      *fn-b3-keyed-hash*
                     (fn-b3-window-outs (fn-b3-words 8 (fn-b3-fix-octets key)) k 0 m
                                        *fn-b3-keyed-hash*)))))
  :witness ((key (fn-b3tt-input 32)) (m (fn-b3tt-input 2500)) (k 0))
  :breaks ()
  :mutations ((wrong-counter
               (:conclusion
                (equal (fn-blake3-keyed key m)
                       (fn-b3-output-root
                         (fn-b3-window-tree (fn-b3-words 8 (fn-b3-fix-octets key))
                                            *fn-b3-keyed-hash*
                           (fn-b3-window-outs (fn-b3-words 8 (fn-b3-fix-octets key)) k 1 m
                                              *fn-b3-keyed-hash*)))))
               ((key (fn-b3tt-input 32)) (m (fn-b3tt-input 2500)) (k 0))
               :fault "the windows hashed at chunk counters shifted by one")
              (wrong-mode
               (:conclusion
                (equal (fn-blake3-keyed key m)
                       (fn-b3-output-root
                         (fn-b3-window-tree (fn-b3-words 8 (fn-b3-fix-octets key))
                                            0
                           (fn-b3-window-outs (fn-b3-words 8 (fn-b3-fix-octets key)) k 0 m 0)))))
               ((key (fn-b3tt-input 32)) (m (fn-b3tt-input 2500)) (k 0))
               :fault "the composition taken in hash mode, not keyed mode")))

(defteeth fn-blake3-derive-key-is-window-composition
  :claim (()
          (equal (fn-blake3-derive-key context m)
                 (fn-b3-output-root
                   (fn-b3-window-tree
                     (fn-b3-words 8 (fn-b3-hash *fn-b3-iv* *fn-b3-derive-key-context*
                                                (fn-b3-fix-octets context)))
                     *fn-b3-derive-key-material*
                     (fn-b3-window-outs
                       (fn-b3-words 8 (fn-b3-hash *fn-b3-iv* *fn-b3-derive-key-context*
                                                  (fn-b3-fix-octets context)))
                       k 0 m *fn-b3-derive-key-material*)))))
  :witness ((context (fn-b3tt-input 20)) (m (fn-b3tt-input 2500)) (k 0))
  :breaks ()
  :mutations ((wrong-counter
               (:conclusion
                (equal (fn-blake3-derive-key context m)
                       (fn-b3-output-root
                         (fn-b3-window-tree
                           (fn-b3-words 8 (fn-b3-hash *fn-b3-iv* *fn-b3-derive-key-context*
                                                      (fn-b3-fix-octets context)))
                           *fn-b3-derive-key-material*
                           (fn-b3-window-outs
                             (fn-b3-words 8 (fn-b3-hash *fn-b3-iv* *fn-b3-derive-key-context*
                                                        (fn-b3-fix-octets context)))
                             k 1 m *fn-b3-derive-key-material*)))))
               ((context (fn-b3tt-input 20)) (m (fn-b3tt-input 2500)) (k 0))
               :fault "the windows hashed at chunk counters shifted by one")))

(defteeth-check)
