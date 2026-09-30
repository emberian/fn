; PRF-1132: actual host-called initializer funding preconditions.
; Source scalar/representation carry only; no complete job tariff/admission.
(in-package "ACL2")
(include-book "decoded-window-begin")
(include-book "decoded-window-profile")

; These unconditional component facts do not need a prior decoder invariant:
; actual initialization resets the decoder even on a malformed logical token.
(defthm fn-pwz-actual-begin-establishes-internal-widths
  (let ((r (fn-pwz-begin token incarnation pgs-digest-state
                        fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (fn-pzw-state-bits-widthp (mv-nth 2 r))
         (fn-pzw-state-walk-widthp (mv-nth 2 r))
         (fn-pzw-state-header-widthp (mv-nth 2 r))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use ((:instance fn-pzw-actual-initialize-bits-width (dict (fn-pwz-dictionary token)))
                         (:instance fn-pzw-actual-initialize-walk-width (dict (fn-pwz-dictionary token)))
                         (:instance fn-pzw-actual-initialize-header-width (dict (fn-pwz-dictionary token))))
           :in-theory
           (e/d (fn-pwz-begin fn-ewz-begin)
                (fn-pzw-initialize fn-pwz-dictionary fn-ews-begin
                 fn-ewz-state fn-pzd-budget nfix natp fn-pzw-stored-admissiblep
                 fn-pzw-state-bits-widthp fn-pzw-state-walk-widthp
                 fn-pzw-state-header-widthp)))))

(defthm fn-pwz-actual-begin-establishes-fixed-buffer-representation
  (let ((r (fn-pwz-begin token incarnation pgs-digest-state
                        fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 3 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 4 r)) *fn-zin-tab-octets*)
         (fn-cbor-octet-listp (mv-nth 3 r))
         (fn-cbor-octet-listp (mv-nth 4 r))
         (equal (mv-nth 5 r) nil)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn-pwz-dictionary-is-bounded-octets
                 (:instance fn-pzw-initialize-establishes-buffers (dict (fn-pwz-dictionary token))))
           :in-theory (e/d (fn-pwz-begin fn-ewz-begin)
                            (fn-pzw-initialize fn-pwz-dictionary fn-ews-begin
                             fn-ewz-state fn-pzd-budget nfix natp fn-pzw-stored-admissiblep)))))

(local
 (defthm fn-pwzif-control-projection-by-definition
   (let ((z (mv-nth 0 (fn-pwz-begin token incarnation pgs-digest-state
                         fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
     (equal (list (nth 2 z) (nth 3 z) (nth 4 z) (nth 5 z)
                  (nth 6 z) (nth 7 z) (nth 8 z))
            (list (nfix (fn-pwz-nth 9 token)) (nfix (fn-pwz-nth 7 token))
                  (min 16384 (nfix (- (nfix (fn-pwz-nth 9 token))
                                      (nfix (fn-pwz-nth 7 token)))))
                  (fn-pzd-budget (nfix (fn-pwz-nth 6 token))
                                 (nfix (fn-pwz-nth 9 token))) 0 0 :more)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess) :in-theory
            (e/d (fn-pwz-begin fn-ewz-begin fn-ewz-state)
                 (fn-pwz-nth nfix natp fn-pzd-budget fn-ews-begin
                  fn-pzw-initialize fn-pwz-dictionary fn-pzw-stored-admissiblep))))))

(local
 (defun fn-pwzif-nth-induct (count index fields)
   (if (zp index) (list count fields)
     (fn-pwzif-nth-induct (1- count) (1- index)
                         (if (consp fields) (cdr fields) nil)))))
(local
 (defthm fn-pwzif-nth-natural
   (implies (and (fn-pwz-naturals count fields)
                 (natp count) (natp index) (< index count))
            (natp (fn-pwz-nth index fields)))
   :hints (("Goal" :induct (fn-pwzif-nth-induct count index fields)
            :in-theory (enable fn-pwz-naturals fn-pwz-nth)))))
(local
 (defthm fn-pwzif-token-field-projection-by-definition
   (implies (and (consp token) (consp (cdr token)))
            (and (equal (fn-pwz-nth 6 token) (fn-pwz-nth 4 (cddr token)))
                 (equal (fn-pwz-nth 7 token) (fn-pwz-nth 5 (cddr token)))
                 (equal (fn-pwz-nth 9 token) (fn-pwz-nth 7 (cddr token)))))
   :hints (("Goal" :expand ((fn-pwz-nth 6 token) (fn-pwz-nth 5 (cdr token))
                            (fn-pwz-nth 7 token) (fn-pwz-nth 6 (cdr token))
                            (fn-pwz-nth 9 token) (fn-pwz-nth 8 (cdr token)))
            :in-theory (disable fn-pwz-nth)))))
(local
 (defthm fn-pwzif-token-scalars
   (implies (fn-pwz-tokenp token)
            (and (natp (fn-pwz-nth 6 token))
                 (natp (fn-pwz-nth 7 token))
                 (natp (fn-pwz-nth 9 token))
                 (<= (fn-pwz-nth 7 token) (fn-pwz-nth 9 token))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn-pwzif-nth-natural (count 9) (index 4) (fields (cddr token)))
                  (:instance fn-pwzif-nth-natural (count 9) (index 5) (fields (cddr token)))
                  (:instance fn-pwzif-nth-natural (count 9) (index 7) (fields (cddr token))))
            :in-theory
            (e/d (fn-pwz-tokenp fn-pwz-descriptorp)
                 (fn-pwz-naturals fn-pwz-nth fn-pzw-stored-admissiblep
                  fn-pwz-shipped-idp fn-pwzif-nth-natural natp))))))

; Source domains join the actual returned control fields, without a twin
; initializer or prior-state invariant. This is not a job-demand theorem.
(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pwz-actual-begin-establishes-control-funding-domain
   (implies (and (fn-pwz-tokenp token)
                 (fn-pwz-native-offsetp (cddr token)))
     (let* ((r (fn-pwz-begin token incarnation pgs-digest-state
                            fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
            (z (mv-nth 0 r)))
       (and (natp (nth 2 z)) (< (nth 2 z) 4722366482869645213696)
            (natp (nth 3 z)) (<= (nth 3 z) (nth 2 z))
            (natp (nth 4 z)) (<= (nth 4 z) 16384)
            (natp (nth 5 z)) (< (nth 5 z) 9444732965739290427392)
            (equal (nth 5 z)
                   (fn-pzd-budget (fn-pwz-nth 6 token) (fn-pwz-nth 9 token)))
            (equal (nth 6 z) 0) (equal (nth 7 z) 0)
            (equal (nth 8 z) :more))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :do-not '(preprocess)
            :use (fn-pwzif-control-projection-by-definition fn-pwzif-token-scalars
                  (:instance fn-pwz-actual-descriptor-establishes-decoder-funding-domain
                             (descriptor (cddr token))))
            :in-theory
            (e/d (fn-pwz-tokenp)
                 (fn-pwz-begin fn-ewz-begin fn-ewz-state fn-pwz-descriptorp
                  fn-pwz-nth fn-pwz-naturals fn-pwz-dictionary fn-pzw-initialize
                  fn-ews-begin fn-pzd-budget fn-pwz-native-offsetp
                  fn-pwzif-token-scalars))))))

(encapsulate
 ()
 (local
  (defthm fn-pwzif-reset-loop-below
    (implies (and (natp i) (natp j) (< j i) (< j 20))
             (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st))
                    (fn-zin-fld j fn-zin-st)))
    :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
             :in-theory (enable fn-zin-reset-loop)))))
 (local
  (defthm fn-pwzif-reset-loop-zero
    (implies (and (natp i) (natp j) (<= i j) (< j 18))
             (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) 0))
    :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
             :in-theory (enable fn-zin-reset-loop)))))
 (local
  (defthm fn-pwzif-initialize-zero-counters
    (let ((st (mv-nth 0 (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
      (and (equal (fn-zin-tin st) 0) (equal (fn-zin-tout st) 0)))
    :hints (("Goal" :in-theory
             (e/d (fn-pzw-initialize fn-zin-reset)
                  (fn-zin-reset-loop fn-zin-payload-ready))))))
 (defthm fn-pwz-actual-begin-establishes-zero-counters
   (let ((r (fn-pwz-begin token incarnation pgs-digest-state
                         fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
     (and (equal (fn-zin-tin (mv-nth 2 r)) 0)
          (equal (fn-zin-tout (mv-nth 2 r)) 0)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn-pwzif-initialize-zero-counters (dict (fn-pwz-dictionary token))))
            :in-theory (e/d (fn-pwz-begin fn-ewz-begin)
                             (fn-pzw-initialize fn-pwz-dictionary fn-ews-begin
                              fn-ewz-state fn-pzd-budget nfix natp
                              fn-pzw-stored-admissiblep
                              fn-pwzif-initialize-zero-counters)))))
)
