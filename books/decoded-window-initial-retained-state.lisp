; PRF-1132: exact retained representation obligations at actual begin.
; No capacity or compiled-allocation adequacy follows from logical fill size.
(in-package "ACL2")
(include-book "decoded-window-initial-funding-domain")

(defthm fn-pwz-actual-begin-retains-digest-frame-array
 (let ((r (fn-pwz-begin token incarnation pgs-digest-state
                       fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  (equal (nth 15 (mv-nth 1 r)) (nth 15 pgs-digest-state)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pwz-begin fn-ewz-begin fn-ews-begin pgs-dcb-begin pgs-dc-begin)
     (fn-pwz-nth fn-pwz-dictionary fn-pzw-initialize fn-ewz-state fn-ewp-begin
      fn-ews-capture pgs-dcb-word-count fn-pzd-budget fn-pzw-stored-admissiblep nfix natp min)))))

; This is the concrete executive selected by each decoder buffer reserve
; export. It keeps an already larger allocation; it does not shrink to N.
(defthm fn-pwz-concrete-reserve-retains-or-grows-capacity
 (implies (natp n)
  (let* ((old (fn-octets$c-buf-length fn-octets$c))
         (new (fn-octets$c-reserve n fn-octets$c)))
   (and (equal (fn-octets$c-buf-length new) (max n old))
        (implies (<= n old) (equal new fn-octets$c))
        (implies (< old n) (<= (+ old (fn-octets$c-buf-length new)) (* 2 n))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-octets$c-reserve))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (local
  (defthm fn-piw-byte-ceiling-source-domains
   (implies (and (natp b) (< b 9223372036854775808))
    (and (natp (ceiling b 64)) (<= (ceiling b 64) 144115188075855872)
         (<= (* 8 (ceiling b 64)) 1152921504606846976)
         (natp (ceiling b 8)) (<= (ceiling b 8) 1152921504606846976)))
   :rule-classes nil))
 (local
  (defthm fn-piw-token-byte-field-by-definition
   (equal (fn-pwz-nth 4 token) (fn-pwz-nth 2 (cddr token)))
   :hints (("Goal" :in-theory (enable fn-pwz-nth)))))
 (local
  (defthm fn-piw-actual-begin-digest-scalars-by-definition
   (let* ((r (fn-pwz-begin token incarnation pgs-digest-state
                          fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          (h (mv-nth 1 r)) (b (nfix (fn-pwz-nth 4 token))))
    (and (equal (pgs-dc-total h) (ceiling b 8))
         (equal (pgs-dc-end h) (ceiling b 8))
         (equal (pgs-dc-start h) 0) (equal (pgs-dc-pos h) 0)
         (equal (pgs-dc-counter h) 0) (equal (pgs-dc-depth h) 0)
         (equal (pgs-dc-power h) 1)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
    :in-theory (e/d (fn-pwz-begin fn-ewz-begin fn-ews-begin pgs-dcb-begin
                      pgs-dc-begin pgs-dcb-word-count)
      (fn-pwz-nth fn-pwz-dictionary fn-pzw-initialize fn-ewz-state fn-ewp-begin
       fn-ews-capture fn-pzd-budget fn-pzw-stored-admissiblep nfix natp min ceiling))))))
 (defthm fn-pwz-actual-begin-establishes-digest-source-widths
  (implies (fn-pwz-native-offsetp (cddr token))
   (let* ((b (nfix (fn-pwz-nth 4 token)))
          (r (fn-pwz-begin token incarnation pgs-digest-state
                          fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          (h (mv-nth 1 r)))
    (and (natp (ceiling b 64)) (<= (ceiling b 64) 144115188075855872)
         (<= (* 8 (ceiling b 64)) 1152921504606846976)
         (natp (ceiling b 8)) (<= (ceiling b 8) 1152921504606846976)
         (equal (pgs-dc-total h) (ceiling b 8))
         (equal (pgs-dc-end h) (ceiling b 8))
         (equal (pgs-dc-start h) 0) (equal (pgs-dc-pos h) 0)
         (equal (pgs-dc-counter h) 0) (equal (pgs-dc-depth h) 0)
         (equal (pgs-dc-power h) 1))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :do-not '(preprocess)
   :use ((:instance fn-piw-byte-ceiling-source-domains (b (nfix (fn-pwz-nth 4 token))))
         fn-piw-actual-begin-digest-scalars-by-definition)
   :in-theory (e/d (fn-pwz-native-offsetp)
      (fn-pwz-begin fn-pwz-nth nfix ceiling natp)))))
)
