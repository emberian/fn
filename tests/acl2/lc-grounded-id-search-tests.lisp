; Cgen entry points over real, fresh FN-LBC objects. The searched domain is
; the named finite packet/publication families, not arbitrary FN-LBC values.
(in-package "ACL2")
(include-book "lc-bounded-check-tests")
(include-book "lc-publication-teeth-tests")

(defun lct-id3-input (code)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((code (mod (nfix code) 24))
        (wire (fn-la-payload-wire *lct-payload*))
        (home (fn-lb-log-model-home-frame (lct-held 0)))
        (frame (fn-lc-move-frame *fn-lg-genesis* 0 wire home))
        (header (list :lc-header (list 0 0 0 0 *fn-lg-genesis*) 2 nil nil
                      (list (list :lc-tail-policy 1 1024))))
        (segs (if (equal (mod code 2) 0) '((0 nil nil))
                '((0 nil nil) (1 nil nil))))
        (records (case (mod (floor code 2) 3)
                   (0 nil) (1 (list (list nil frame nil))) (otherwise '(bad))))
        (k (mod (floor code 6) 4)))
  (list records segs header k)))

(defun lct-id3-grounded-check (code fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let* ((input (lct-id3-input code)) (records (nth 0 input))
        (segs (nth 1 input)) (header (nth 2 input)) (k (nth 3 input)))
  (mv-let (answer fn-lbc post-segs) (fn-lc-commit records segs header k fn-lbc)
   (declare (ignore answer))
   (mv (subsetp-equal (fn-lc-seg-ids post-segs) (fn-lc-seg-ids segs)) fn-lbc))))

(defthm lct-id3-check-is-the-claim
 (equal (mv-nth 0 (lct-id3-grounded-check code fn-lbc))
        (let* ((input (lct-id3-input code))
               (out (fn-lc-commit (nth 0 input) (nth 1 input)
                                 (nth 2 input) (nth 3 input) fn-lbc)))
         (subsetp-equal (fn-lc-seg-ids (mv-nth 2 out))
                        (fn-lc-seg-ids (nth 1 input)))))
 :hints (("Goal" :in-theory (e/d (lct-id3-grounded-check)
                                (lct-id3-input fn-lc-commit)))))

(defun lct-id3-search (code)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (result fn-lbc) (lct-id3-grounded-check code fn-lbc) result)))

(defun lct-id4-input (code)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((code (mod (nfix code) 96))
        (old (fn-lc-proof-empty-columns))
        (old-header (fn-lc-proof-header 20))
        (header (fn-lc-proof-header (+ 20 (mod code 4))))
        (disk (fn-lc-proof-image-disk (fn-lc-pages old old-header)))
        (mode (if (equal (mod (floor code 4) 2) 0) :eager :lazy))
        (cut (mod (floor code 8) 12))
        (outcome (append (fn-lc-proof-ok-outcomes cut) '(:torn))))
  (list old old-header header disk mode outcome)))

(defun lct-id4-grounded-check (code fn-lbc)
 (declare (xargs :stobjs fn-lbc
                 :guard (and (fn-lbc-p fn-lbc) (fn-lc-test-created-state-p fn-lbc))
                 :verify-guards nil))
 (let* ((input (ec-call (lct-id4-input code))) (old (fn-lc-at 0 input))
        (old-header (fn-lc-at 1 input)) (header (fn-lc-at 2 input))
        (disk (fn-lc-at 3 input)) (mode (fn-lc-at 4 input)) (outcome (fn-lc-at 5 input)))
  (mv-let (accepted fn-lbc)
   (fn-lc-stage-publishes-the-allocation-state-native-tooth-0
    old old-header header disk :lc mode '((0 nil nil)) outcome fn-lbc)
   (mv-let (conclusion fn-lbc)
    (fn-lc-stage-publishes-the-allocation-state-native-tooth-1
     old old-header header disk :lc mode '((0 nil nil)) outcome fn-lbc)
    (mv (implies accepted conclusion) fn-lbc)))))

(verify-guards lct-id4-grounded-check)

(defthm lct-id4-check-is-the-claim
 (equal (mv-nth 0 (lct-id4-grounded-check code fn-lbc))
        (let* ((input (lct-id4-input code))
               (header (nth 2 input))
               (out (fn-lc-stage (nth 0 input) (nth 1 input) header (nth 3 input)
                                 :lc (nth 4 input) '((0 nil nil))
                                 (nth 5 input) fn-lbc)))
         (implies (equal (mv-nth 0 out) :ok)
                  (and (equal (fn-lc-header-next-id
                               (fn-lc-adopted-header (mv-nth 2 out) :lc (nth 4 input)))
                              (fn-lc-header-next-id header))
                       (equal (fn-lc-header-exhaustedp
                               (fn-lc-adopted-header (mv-nth 2 out) :lc (nth 4 input)))
                              (fn-lc-header-exhaustedp header))))))
 :hints (("Goal" :in-theory
  (e/d (lct-id4-grounded-check
        fn-lc-stage-publishes-the-allocation-state-native-tooth-0
        fn-lc-stage-publishes-the-allocation-state-native-tooth-1
        fn-lc-stage-publishes-the-allocation-state-native-tooth-0-logic
        fn-lc-stage-publishes-the-allocation-state-native-tooth-1-logic)
       (lct-id4-input fn-lc-stage fn-lc-adopted-header
        fn-lc-header-next-id fn-lc-header-exhaustedp)))))

(defun lct-id4-search (code)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (result fn-lbc) (lct-id4-grounded-check code fn-lbc) result)))

(verify-guards lct-id4-search
 :hints (("Goal" :in-theory (enable fn-lc-test-created-state-p))))

(with-guard-checking-event :none (assert-event (lct-id3-search 0)))
(with-guard-checking-event :none (assert-event (lct-id3-search 2)))
(with-guard-checking-event :none (assert-event (lct-id4-search 0)))
(with-guard-checking-event :none (assert-event (lct-id4-search 88)))
