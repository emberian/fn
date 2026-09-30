(in-package "ACL2")
(include-book "../../books/decoded-window-initial-owner-source")
; Reachable resource-algebra fixture only. This supplied budget/demand is NOT
; an installed physical grant or an adequacy assertion. Seventeen actual PRS
; issues establish the spent identities before this decoded-window request.
(defun-nx fn-piozt-ledger ()
 (let* ((b '(1000000 0 2 1 1000)) (u '(1000 0 0 0 0))
        (r (fn-prs-repeat 17 b u '(0 0 0 0 0) '(0 0 0 0 0) 0 1000 '(0 0 0 0 1)))
        (l (fn-prl-build b (mv-nth 1 r) (mv-nth 0 r) nil u)))
  (mv-nth 1 (fn-prl-register l 7 '(64 0 1 0 0)))))
(defconst *piozt-descriptor* '(7 100 2048 120 1024 200 99 93100 0))
(defconst *piozt-demand* '(256 0 0 1 1))
(defmacro piozt-admitted () '(equal (mv-nth 0 (fn-pwz-admit (fn-piozt-ledger) *piozt-descriptor* *piozt-demand*)) :admitted))
(defmacro piozt-assigned (w)
 `(equal (mv-nth 0 (fn-pwx-acquire
   (mv-nth 2 (fn-pwz-admit (fn-piozt-ledger) *piozt-descriptor* *piozt-demand*))
   ,w (mv-nth 1 (fn-pwz-admit (fn-piozt-ledger) *piozt-descriptor* *piozt-demand*)))) :assigned))
(defmacro piozt-relation (w cw ct co)
 `(fn-pioz-initial-relation (fn-piozt-ledger) *piozt-descriptor* *piozt-demand*
   ,w 301 (create-pgs-digest-state) (create-fn-zin-st) ,cw ,ct ,co nil nil nil))
(local (defthm piozt-clear-capacity-and-fill
 (and (equal (fn-octets$c-buf-length (fn-octets$c-clear b)) (fn-octets$c-buf-length b))
      (equal (fn-octets$c-fill (fn-octets$c-clear b)) 0))
 :hints (("Goal" :in-theory (enable fn-octets$c-clear)))))
(local (defthm piozt-reserve-capacity-and-fill
 (implies (natp n)
  (and (equal (fn-octets$c-buf-length (fn-octets$c-reserve n b))
              (max n (fn-octets$c-buf-length b)))
       (equal (fn-octets$c-fill (fn-octets$c-reserve n b)) (fn-octets$c-fill b))))
 :hints (("Goal" :in-theory (enable fn-octets$c-reserve)))))
(local (defthm piozt-len-nthcdr
 (equal (len (nthcdr n xs)) (nfix (- (len xs) (nfix n))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr)))))

(local (defthm piozt-append-octet-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-octet o b))
        (+ 1 (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet)))))
(local (defthm piozt-append-back-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-back off n b))
        (+ n (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-append-back) (fn-oct-back-loop))))))
(local (defthm piozt-write-list-fill
 (implies (acl2-numberp (fn-octets$c-fill b))
  (equal (fn-octets$c-fill (fn-oct-write-list xs b))
         (+ (len xs) (fn-octets$c-fill b))))
 :hints (("Goal" :induct (fn-oct-write-list xs b)
            :in-theory (e/d (fn-oct-write-list) (fn-octets$c-append-octet))))))


(local (defthm piozt-back-loop-keeps-tail
 (implies (and (natp i) (<= end i))
  (equal (fn-octets$c-bufi i (fn-oct-back-loop src dst end c))
         (fn-octets$c-bufi i c)))
 :hints (("Goal" :induct (fn-oct-back-loop src dst end c)
                 :in-theory (enable fn-oct-back-loop fn-octets$c-bufi)))))
(local (defthm piozt-bufi-of-update-fill
 (equal (fn-octets$c-bufi i (update-fn-octets$c-fill n c)) (fn-octets$c-bufi i c))
 :hints (("Goal" :in-theory (enable fn-octets$c-bufi)))))
(local (defthm piozt-append-back-keeps-tail
 (implies (and (natp i) (natp n) (natp (fn-octets$c-fill c))
              (<= (+ (fn-octets$c-fill c) n) i)
              (<= (+ (fn-octets$c-fill c) n) (fn-octets$c-buf-length c)))
  (equal (fn-octets$c-bufi i (fn-octets$c-append-back off n c))
         (fn-octets$c-bufi i c)))
 :hints (("Goal" :use ((:instance piozt-back-loop-keeps-tail
        (src (- (fn-octets$c-fill c) off)) (dst (fn-octets$c-fill c))
        (end (+ (fn-octets$c-fill c) n))))
 :in-theory (e/d (fn-octets$c-append-back)
              (fn-oct-back-loop fn-octets$c-bufi update-fn-octets$c-fill piozt-back-loop-keeps-tail))))))
(local (defthm piozt-append-octet-keeps-tail
 (implies (and (natp i) (natp (fn-octets$c-fill c))
              (< (fn-octets$c-fill c) (fn-octets$c-buf-length c))
              (< (fn-octets$c-fill c) i))
  (equal (fn-octets$c-bufi i (fn-octets$c-append-octet o c))
         (fn-octets$c-bufi i c)))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet fn-octets$c-bufi)))))
(local (defthm piozt-write-list-keeps-tail
 (implies (and (natp i) (natp (fn-octets$c-fill c))
              (<= (+ (fn-octets$c-fill c) (len xs)) i)
              (<= (+ (fn-octets$c-fill c) (len xs)) (fn-octets$c-buf-length c)))
  (equal (fn-octets$c-bufi i (fn-oct-write-list xs c))
         (fn-octets$c-bufi i c)))
 :hints (("Goal" :induct (fn-oct-write-list xs c)
 :in-theory (e/d (fn-oct-write-list) (fn-octets$c-append-octet fn-octets$c-bufi fn-octets$c-buf-length fn-octets$c-fill))))))
(local (defthm piozt-clear-keeps-tail
 (equal (fn-octets$c-bufi i (fn-octets$c-clear c)) (fn-octets$c-bufi i c))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-clear) (update-fn-octets$c-fill fn-octets$c-bufi))))))
(local (defthm piozt-reserve-is-unchanged
 (implies (<= n (fn-octets$c-buf-length c)) (equal (fn-octets$c-reserve n c) c))
 :hints (("Goal" :in-theory (enable fn-octets$c-reserve)))))
(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm piozt-payload-ready-keeps-unused-tail
 (let ((r (fn-piwc-payload-ready dict cwin ctab)))
  (and (implies (and (natp i) (<= 65536 i) (< i (fn-octets$c-buf-length cwin)))
        (equal (fn-octets$c-bufi i (mv-nth 1 r)) (fn-octets$c-bufi i cwin)))
       (implies (and (natp i) (<= 3494 i) (< i (fn-octets$c-buf-length ctab)))
        (equal (fn-octets$c-bufi i (mv-nth 2 r)) (fn-octets$c-bufi i ctab)))))
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-piwc-payload-ready)
   (fn-octets$c-bufi fn-octets$c-buf-length fn-octets$c-fill fn-octets$c-clear
    fn-octets$c-reserve fn-octets$c-append-octet fn-octets$c-append-back
    fn-oct-write-list fn-oct-back-loop nthcdr (:e fn-octets$c-append-back)))))))
(local (defthm piozt-begin-keeps-unused-tail
 (let ((r (fn-piwc-begin token incarnation hash zin cwin ctab cout)))
  (and (implies (and (natp i) (<= 65536 i) (< i (fn-octets$c-buf-length cwin)))
        (equal (fn-octets$c-bufi i (mv-nth 3 r)) (fn-octets$c-bufi i cwin)))
       (implies (and (natp i) (<= 3494 i) (< i (fn-octets$c-buf-length ctab)))
        (equal (fn-octets$c-bufi i (mv-nth 4 r)) (fn-octets$c-bufi i ctab)))
       (implies (and (natp i) (<= 64 i) (< i (fn-octets$c-buf-length cout)))
        (equal (fn-octets$c-bufi i (mv-nth 5 r)) (fn-octets$c-bufi i cout)))))
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance piozt-payload-ready-keeps-unused-tail (dict (fn-pwz-dictionary token))))
 :in-theory (e/d (fn-piwc-begin fn-piwc-ewz-begin fn-piwc-initialize)
   (fn-piwc-payload-ready piozt-payload-ready-keeps-unused-tail
    fn-octets$c-bufi fn-octets$c-buf-length fn-octets$c-fill fn-octets$c-clear
    fn-octets$c-reserve fn-pwz-dictionary fn-pwz-nth fn-zin-reset fn-zin-set
    fn-ews-begin fn-ewz-state fn-pzd-budget fn-pzw-stored-admissiblep nfix nth natp
    (:e fn-pwz-dictionary)))))))
(local (defthm piozt-corr-implies-all-capacity-cells-typed
 (implies (and (fn-octets$corr c a) (natp i) (< i (fn-octets$c-buf-length c)))
          (fn-cbor-octetp (fn-octets$c-bufi i c)))
 :hints (("Goal" :in-theory (enable fn-octets$corr fn-octets$cp
                   fn-octets$c-buf-length fn-octets$c-bufi)))))
(local (defthm piozt-cp-implies-all-capacity-cells-typed
 (implies (and (fn-octets$cp c) (natp i) (< i (fn-octets$c-buf-length c)))
          (fn-cbor-octetp (fn-octets$c-bufi i c)))
 :hints (("Goal" :in-theory (enable fn-octets$cp fn-octets$c-buf-length fn-octets$c-bufi)))))

(defthm piozt-literal-complete-fresh-positive
 (let ((cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (create-fn-octets$c)) (w (fn-pxe-new 0)))
  (and (piozt-admitted) (piozt-assigned w)
       (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (fn-pioz-capacity-profilep cw ct co)
       (piozt-relation w cw ct co)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pioz-actual-issued-assigned-begin-source-boundary
  (ledger (fn-piozt-ledger)) (descriptor *piozt-descriptor*) (demand *piozt-demand*)
  (w (fn-pxe-new 0)) (incarnation 301) (hash (create-pgs-digest-state))
  (zin (create-fn-zin-st)) (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c))
  (awin nil) (atab nil) (aout nil)))
 :in-theory (e/d (fn-piozt-ledger fn-prs-repeat fn-prs-issue fn-prl-build fn-prl-register
  fn-prl-nth fn-prl-baseline fn-prl-binding fn-pwz-admit fn-pwx-acquire fn-pwx-rowp
  fn-pwx-tokenp fn-prw-phase fn-pwz-tokenp fn-pwz-descriptorp fn-pioz-capacity-profilep)
  (fn-pioz-initial-relation fn-piwc-begin fn-pwz-begin fn-octets$corr
   (:e fn-piwc-begin) (:e fn-pwz-begin))))))

(defthm piozt-literal-complete-retained-positive
 (let ((cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ct (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (co (resize-fn-octets$c-buf 128 (create-fn-octets$c))) (w (fn-pxe-new 0)))
  (and (piozt-admitted) (piozt-assigned w)
       (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (fn-pioz-capacity-profilep cw ct co)
       (piozt-relation w cw ct co)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pioz-actual-issued-assigned-begin-source-boundary
  (ledger (fn-piozt-ledger)) (descriptor *piozt-descriptor*) (demand *piozt-demand*)
  (w (fn-pxe-new 0)) (incarnation 301) (hash (create-pgs-digest-state))
  (zin (create-fn-zin-st)) (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ctab (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
  (awin nil) (atab nil) (aout nil)))
 :in-theory (e/d (fn-piozt-ledger fn-prs-repeat fn-prs-issue fn-prl-build fn-prl-register
  fn-prl-nth fn-prl-baseline fn-prl-binding fn-pwz-admit fn-pwx-acquire fn-pwx-rowp
  fn-pwx-tokenp fn-prw-phase fn-pwz-tokenp fn-pwz-descriptorp fn-pioz-capacity-profilep)
  (fn-pioz-initial-relation fn-piwc-begin fn-pwz-begin fn-octets$corr
   (:e fn-piwc-begin) (:e fn-pwz-begin))))))

; Corrupted concrete logical tail: not a valid UB8 executable input.
(defthm piozt-literal-remove-typed-window-array
 (let ((cw (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ct (create-fn-octets$c)) (co (create-fn-octets$c)) (w (fn-pxe-new 0)))
  (and (piozt-admitted) (piozt-assigned w)
       (not (fn-octets$cp cw))
       (fn-octets$cp ct)
       (fn-octets$cp co)
       (not (piozt-relation w cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance piozt-begin-keeps-unused-tail
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
    (cwin (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c)) (i 65536))
   (:instance fn-piwc-begin-keeps-initial-capacities
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (pgs-digest-state (create-pgs-digest-state)) (fn-zin-st (create-fn-zin-st))
    (cwin (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c)))
   (:instance piozt-cp-implies-all-capacity-cells-typed (c (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (i 65536))
   (:instance piozt-corr-implies-all-capacity-cells-typed
    (i 65536) (a (mv-nth 3 (fn-pwz-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) nil nil nil)))
    (c (mv-nth 3 (fn-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c))) (create-fn-octets$c) (create-fn-octets$c))))))
 :in-theory (e/d (fn-pioz-initial-relation fn-piozt-ledger fn-prs-repeat fn-prs-issue
 fn-prl-build fn-prl-register fn-prl-nth fn-prl-baseline fn-prl-binding fn-pwz-admit
 fn-pwx-acquire fn-pwx-rowp fn-pwx-tokenp fn-prw-phase fn-pwz-tokenp fn-pwz-descriptorp) (fn-piwc-begin fn-pwz-begin fn-octets$corr fn-octets$cp
  (:e fn-piwc-begin) (:e fn-pwz-begin)
  piozt-begin-keeps-unused-tail piozt-corr-implies-all-capacity-cells-typed
  piozt-cp-implies-all-capacity-cells-typed)))))

; Corrupted concrete logical tail: not a valid UB8 executable input.
(defthm piozt-literal-remove-typed-table-array
 (let ((cw (create-fn-octets$c)) (ct (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (co (create-fn-octets$c)) (w (fn-pxe-new 0)))
  (and (piozt-admitted) (piozt-assigned w)
       (fn-octets$cp cw)
       (not (fn-octets$cp ct))
       (fn-octets$cp co)
       (not (piozt-relation w cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance piozt-begin-keeps-unused-tail
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
    (cwin (create-fn-octets$c)) (ctab (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (cout (create-fn-octets$c)) (i 3494))
   (:instance fn-piwc-begin-keeps-initial-capacities
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (pgs-digest-state (create-pgs-digest-state)) (fn-zin-st (create-fn-zin-st))
    (cwin (create-fn-octets$c)) (ctab (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (cout (create-fn-octets$c)))
   (:instance piozt-cp-implies-all-capacity-cells-typed (c (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (i 3494))
   (:instance piozt-corr-implies-all-capacity-cells-typed
    (i 3494) (a (mv-nth 4 (fn-pwz-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) nil nil nil)))
    (c (mv-nth 4 (fn-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) (create-fn-octets$c) (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c))) (create-fn-octets$c))))))
 :in-theory (e/d (fn-pioz-initial-relation fn-piozt-ledger fn-prs-repeat fn-prs-issue
 fn-prl-build fn-prl-register fn-prl-nth fn-prl-baseline fn-prl-binding fn-pwz-admit
 fn-pwx-acquire fn-pwx-rowp fn-pwx-tokenp fn-prw-phase fn-pwz-tokenp fn-pwz-descriptorp) (fn-piwc-begin fn-pwz-begin fn-octets$corr fn-octets$cp
  (:e fn-piwc-begin) (:e fn-pwz-begin)
  piozt-begin-keeps-unused-tail piozt-corr-implies-all-capacity-cells-typed
  piozt-cp-implies-all-capacity-cells-typed)))))

; Corrupted concrete logical tail: not a valid UB8 executable input.
(defthm piozt-literal-remove-typed-output-array
 (let ((cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))) (w (fn-pxe-new 0)))
  (and (piozt-admitted) (piozt-assigned w)
       (fn-octets$cp cw)
       (fn-octets$cp ct)
       (not (fn-octets$cp co))
       (not (piozt-relation w cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance piozt-begin-keeps-unused-tail
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
    (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))) (i 64))
   (:instance fn-piwc-begin-keeps-initial-capacities
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (pgs-digest-state (create-pgs-digest-state)) (fn-zin-st (create-fn-zin-st))
    (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))))
   (:instance piozt-cp-implies-all-capacity-cells-typed (c (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))) (i 64))
   (:instance piozt-corr-implies-all-capacity-cells-typed
    (i 64) (a (mv-nth 5 (fn-pwz-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) nil nil nil)))
    (c (mv-nth 5 (fn-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) (create-fn-octets$c) (create-fn-octets$c) (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c))))))))
 :in-theory (e/d (fn-pioz-initial-relation fn-piozt-ledger fn-prs-repeat fn-prs-issue
 fn-prl-build fn-prl-register fn-prl-nth fn-prl-baseline fn-prl-binding fn-pwz-admit
 fn-pwx-acquire fn-pwx-rowp fn-pwx-tokenp fn-prw-phase fn-pwz-tokenp fn-pwz-descriptorp) (fn-piwc-begin fn-pwz-begin fn-octets$corr fn-octets$cp
  (:e fn-piwc-begin) (:e fn-pwz-begin)
  piozt-begin-keeps-unused-tail piozt-corr-implies-all-capacity-cells-typed
  piozt-cp-implies-all-capacity-cells-typed)))))
; Exact assignment is necessary while actual admission and typed arrays hold.
(defthm piozt-literal-remove-assigned-worker
 (let ((c (create-fn-octets$c)) (w '(0 nil :returned nil)))
  (and (piozt-admitted) (not (piozt-assigned w))
       (fn-octets$cp c) (fn-octets$cp c) (fn-octets$cp c)
       (not (piozt-relation w c c c))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-pioz-initial-relation fn-piozt-ledger fn-prs-repeat fn-prs-issue
 fn-prl-build fn-prl-register fn-prl-nth fn-prl-baseline fn-prl-binding fn-pwz-admit
 fn-pwx-acquire fn-pwx-rowp fn-pwx-tokenp fn-prw-phase fn-pwz-tokenp fn-pwz-descriptorp
 fn-pwx-work-permittedp fn-pwx-boundp)
 (fn-piwc-begin fn-pwz-begin fn-octets$corr (:e fn-piwc-begin) (:e fn-pwz-begin))))))

; Mutation: change the assigned request ticket while retaining the actual
; issued token, complete typed initializer and live worker association.
(defthm piozt-literal-ticket-mutation
 (let* ((c (create-fn-octets$c)) (w (fn-pxe-new 0))
        (a (fn-pwz-admit (fn-piozt-ledger) *piozt-descriptor* *piozt-demand*))
        (x (fn-pwx-acquire (mv-nth 2 a) w (mv-nth 1 a))))
  (and (piozt-admitted) (piozt-assigned w)
       (fn-octets$cp c) (fn-octets$cp c) (fn-octets$cp c)
       (piozt-relation w c c c)
       (not (fn-pwx-work-permittedp (mv-nth 2 x) (mv-nth 1 x)
              '(:decoded-window 18 7 100 2048 120 1024 200 99 93100 0)))))
 :rule-classes nil
 :hints (("Goal" :use piozt-literal-complete-fresh-positive
 :in-theory (e/d (fn-piozt-ledger fn-prs-repeat fn-prs-issue fn-prl-build fn-prl-register
 fn-prl-nth fn-prl-baseline fn-prl-binding fn-pwz-admit fn-pwx-acquire fn-pwx-rowp
 fn-pwx-tokenp fn-prw-phase fn-pwz-tokenp fn-pwz-descriptorp fn-pwx-work-permittedp fn-pwx-boundp)
 (fn-pioz-initial-relation fn-piwc-begin fn-pwz-begin fn-octets$corr
  (:e fn-piwc-begin) (:e fn-pwz-begin))))))

; Mutation: a constructor does not shrink larger already retained backing.
(defthm piozt-literal-retained-backing-mutation
 (let* ((cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c)))
        (ct (resize-fn-octets$c-buf 4000 (create-fn-octets$c)))
        (co (resize-fn-octets$c-buf 128 (create-fn-octets$c))) (w (fn-pxe-new 0))
        (rc (fn-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)
               301 (create-pgs-digest-state) (create-fn-zin-st) cw ct co)))
  (and (piozt-admitted) (piozt-assigned w)
       (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (piozt-relation w cw ct co)
       (equal (fn-octets$c-buf-length (mv-nth 3 rc)) 70000)
       (equal (fn-octets$c-buf-length (mv-nth 4 rc)) 4000)
       (equal (fn-octets$c-buf-length (mv-nth 5 rc)) 128)
       (not (equal (+ (fn-octets$c-buf-length (mv-nth 3 rc))
                      (fn-octets$c-buf-length (mv-nth 4 rc))
                      (fn-octets$c-buf-length (mv-nth 5 rc))) 69094))))
 :rule-classes nil
 :hints (("Goal" :use (piozt-literal-complete-retained-positive
 (:instance fn-piwc-begin-keeps-initial-capacities
  (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301)
  (pgs-digest-state (create-pgs-digest-state)) (fn-zin-st (create-fn-zin-st))
  (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c)))
  (ctab (resize-fn-octets$c-buf 4000 (create-fn-octets$c)))
  (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))))
 :in-theory (disable fn-pioz-initial-relation fn-piwc-begin fn-pwz-begin
  fn-pwz-admit fn-pwx-acquire fn-octets$corr (:e fn-piwc-begin) (:e fn-pwz-begin)))))
