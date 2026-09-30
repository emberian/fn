(in-package "ACL2")
(include-book "../../books/decoded-window-initial-source-counts")
(include-book "../../books/decoded-window-initial-retained-state")

; Reachable fresh actual initializer, complete unconditional source roster.
; Logical observer allocations are not asserted to be target allocations.
(defthm piw-literal-fresh-actual-initializer-positive
 (let* ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
        (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
        (win (create-fn-zin-win)) (tab (create-fn-zin-tab)) (out (create-fn-zin-out))
        (o (fn-piw-pwz-begin token 301 hash zin win tab out)) (trace (cdr o)))
  (and (fn-pwz-tokenp token) (fn-pwz-native-offsetp (cddr token))
       (equal (car o) (fn-pwz-begin token 301 hash zin win tab out))
       (equal (fn-piw-constructor-cells trace) 35)
       (equal (fn-piw-borrow-count 'fn-zin-set trace) 21)
       (equal (fn-pzt-count :ceiling trace) 3)
       (equal (fn-piw-reserve-octets trace) 69094)
       (equal (fn-piw-fill-octets trace) 69030)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (disable fn-piw-pwz-begin fn-pwz-begin create-pgs-digest-state create-fn-zin-st create-fn-zin-win create-fn-zin-tab create-fn-zin-out (:e fn-piw-pwz-begin) (:e fn-pwz-begin)))))

; Actual shipped preset source branch; full endpoint conclusion again.
(defthm piw-literal-shipped-actual-initializer-positive
 (let* ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 2220533217))
        (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
        (win (create-fn-zin-win)) (tab (create-fn-zin-tab)) (out (create-fn-zin-out))
        (o (fn-piw-pwz-begin token 301 hash zin win tab out)) (trace (cdr o)))
  (and (fn-pwz-tokenp token) (fn-pwz-native-offsetp (cddr token))
       (equal (car o) (fn-pwz-begin token 301 hash zin win tab out))
       (equal (fn-piw-constructor-cells trace) 35)
       (equal (fn-piw-borrow-count 'fn-zin-set trace) 21)
       (equal (fn-pzt-count :ceiling trace) 3)
       (equal (fn-piw-reserve-octets trace) 69094)
       (equal (fn-piw-fill-octets trace) 69030)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (disable fn-piw-pwz-begin fn-pwz-begin create-pgs-digest-state create-fn-zin-st create-fn-zin-win create-fn-zin-tab create-fn-zin-out (:e fn-piw-pwz-begin) (:e fn-pwz-begin)))))

; Unconditional source theorem has no hypotheses to remove. Separately
; labelled trace mutation refutes a different 34-cell tariff.
(defthm piw-literal-constructor-trace-mutation
 (and (equal (fn-piw-constructor-cells '((:constructor 14 a) (:constructor 12 b) (:constructor 9 c))) 35)
      (equal (fn-piw-constructor-cells '((:constructor 14 a) (:constructor 12 b) (:constructor 8 c))) 34)
      (not (equal (fn-piw-constructor-cells '((:constructor 14 a) (:constructor 12 b) (:constructor 8 c))) 35)))
 :rule-classes nil)

; Exact concrete reserve positive, old/new payload coexistence only.
(defthm piw-literal-concrete-reserve-positive
 (let* ((n 64) (b (create-fn-octets$c)) (old (fn-octets$c-buf-length b))
        (new (fn-octets$c-reserve n b)))
  (and (natp n)
       (equal (fn-octets$c-buf-length new) (max n old))
       (implies (<= n old) (equal new b))
       (implies (< old n) (<= (+ old (fn-octets$c-buf-length new)) (* 2 n)))))
 :rule-classes nil)

; Corrupted-state removal: fractional requested size is not executable input.
(defthm piw-literal-concrete-reserve-remove-natural
 (let* ((n 1/2) (b (create-fn-octets$c)) (old (fn-octets$c-buf-length b))
        (new (fn-octets$c-reserve n b)))
  (and (not (natp n))
       (not (and (equal (fn-octets$c-buf-length new) (max n old))
                 (implies (<= n old) (equal new b))
                 (implies (< old n) (<= (+ old (fn-octets$c-buf-length new)) (* 2 n)))))))
 :rule-classes nil)

; Oversized old concrete vector remains live. Fill64 does not authorize
; silently replacing a larger prior allocation with a 64-byte charge.
(defthm piw-literal-larger-concrete-reserve-retained
 (let* ((b (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
        (new (fn-octets$c-reserve 64 b)))
  (and (equal new b) (equal (fn-octets$c-buf-length new) 128)
       (not (equal (fn-octets$c-buf-length new) 64))))
 :rule-classes nil)

; Reachable prior cursor frames: actual node then split steps create a frame;
; actual reinitialization retains it while making depth zero, without hashing.
(defthm piw-literal-prior-digest-frame-retained-positive
 (let* ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
        (h0 (pgs-dc-begin 0 0 32 'old-capture 'old-lease (create-pgs-digest-state)))
        (h1 (mv-nth 1 (pgs-dc-step nil h0)))
        (h2 (mv-nth 1 (pgs-dc-step nil h1)))
        (r (fn-pwz-begin token 301 h2 (create-fn-zin-st)
                         (create-fn-zin-win) (create-fn-zin-tab) (create-fn-zin-out))))
  (and (equal (pgs-dc-framesi 0 h2) '(:left 128 256 1 nil))
       (equal (nth 15 (mv-nth 1 r)) (nth 15 h2))
       (not (equal (pgs-dc-framesi 0 h2) nil))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use ((:instance fn-pwz-actual-begin-retains-digest-frame-array
                   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
                   (incarnation 301)
                   (pgs-digest-state
                     (mv-nth 1 (pgs-dc-step nil
                      (mv-nth 1 (pgs-dc-step nil
                       (pgs-dc-begin 0 0 32 'old-capture 'old-lease (create-pgs-digest-state)))))))
                   (fn-zin-st (create-fn-zin-st))
                   (fn-zin-win (create-fn-zin-win))
                   (fn-zin-tab (create-fn-zin-tab))
                   (fn-zin-out (create-fn-zin-out))))
  :in-theory (disable fn-pwz-begin (:e fn-pwz-begin)))))

(defmacro piw-test-digest-width-conclusion (token incarnation hash zin win tab out)
 `(let* ((b (nfix (fn-pwz-nth 4 ,token)))
         (r (fn-pwz-begin ,token ,incarnation ,hash ,zin ,win ,tab ,out))
         (h (mv-nth 1 r)))
   (and (natp (ceiling b 64)) (<= (ceiling b 64) 144115188075855872)
        (<= (* 8 (ceiling b 64)) 1152921504606846976)
        (natp (ceiling b 8)) (<= (ceiling b 8) 1152921504606846976)
        (equal (pgs-dc-total h) (ceiling b 8))
        (equal (pgs-dc-end h) (ceiling b 8))
        (equal (pgs-dc-start h) 0) (equal (pgs-dc-pos h) 0)
        (equal (pgs-dc-counter h) 0) (equal (pgs-dc-depth h) 0)
        (equal (pgs-dc-power h) 1))))

(defthm piw-literal-actual-digest-source-width-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)))
  (and (fn-pwz-native-offsetp (cddr token))
       (piw-test-digest-width-conclusion token 301 (create-pgs-digest-state)
         (create-fn-zin-st) (create-fn-zin-win) (create-fn-zin-tab) (create-fn-zin-out))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use ((:instance fn-pwz-actual-begin-establishes-digest-source-widths
          (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
          (incarnation 301) (pgs-digest-state (create-pgs-digest-state))
          (fn-zin-st (create-fn-zin-st)) (fn-zin-win (create-fn-zin-win))
          (fn-zin-tab (create-fn-zin-tab)) (fn-zin-out (create-fn-zin-out))))
  :in-theory (disable fn-pwz-begin (:e fn-pwz-begin) create-pgs-digest-state
                      create-fn-zin-st create-fn-zin-win create-fn-zin-tab create-fn-zin-out))))

; Selected offset-profile removal, not a refusal of an admitted stored file.
(defthm piw-literal-digest-source-width-remove-native-profile
 (let ((token '(:decoded-window 17 7 0 1267650600228229401496703205376
                                0 1 0 99 1 0)))
  (and (not (fn-pwz-native-offsetp (cddr token)))
       (not (piw-test-digest-width-conclusion token 301 (create-pgs-digest-state)
         (create-fn-zin-st) (create-fn-zin-win) (create-fn-zin-tab) (create-fn-zin-out)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (disable fn-pwz-begin (:e fn-pwz-begin) create-pgs-digest-state
                      create-fn-zin-st create-fn-zin-win create-fn-zin-tab create-fn-zin-out))))
