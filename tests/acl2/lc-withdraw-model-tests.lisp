(in-package "ACL2")
(include-book "lc-bounded-check-tests")
(include-book "../../books/log-cleaning-withdraw")
(include-book "../../books/log-cleaning-unlink")

(defun lcw-held (seq)
 (declare (xargs :guard t))
 (fn-held-make (nfix seq) (+ 1 (nfix seq)) 0
  (if (equal seq 0) "<a@x>" "<b@x>") (nfix seq) '("g") "o" "s" "e" 1 5
  (fn-hf-make 24 14 1 (list nil nil nil (ec-call (fn-hnov-of *lct-payload*))))
  (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
  (list (cons "g" (+ 1 (nfix seq)))) nil))
(defun lcw-input ()
 (declare (xargs :guard t))
 (ec-call (fn-lb-log-model-append (lcw-held 1) *lct-payload* 1
             (ec-call (fn-lb-log-model-append (lcw-held 0) *lct-payload* 1 nil)))))
(defun lcw-test (target by fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let* ((rows (list (lcw-held 0) (lcw-held 1))) (segs (lcw-input))
        (fn-lbc (ec-call (fn-lbc-open-rebuild rows segs fn-lbc)))
        (before (ec-call (fn-lc-locators-resolve fn-lbc segs)))
        (a (fn-lbc-word :loc0 0 fn-lbc)) (b (fn-lbc-word :loc1 0 fn-lbc))
        (summary (ec-call (fn-lbc-live-summary "g" fn-lbc))))
  (mv-let (answer fn-lbc after)
   (fn-lc-withdraw target by fn-lbc segs)
   (mv (list before summary answer
         (equal (list (ec-call (fn-lbc-at 0 fn-lbc after))
                      (ec-call (fn-lbc-at 1 fn-lbc after)))
                (ec-call (fn-cat-mark-withdrawn target (len rows) by rows)))
         (equal a (fn-lbc-word :loc0 0 fn-lbc))
         (equal b (fn-lbc-word :loc1 0 fn-lbc))
         (equal segs after) (ec-call (fn-lc-locators-resolve fn-lbc after))
         (ec-call (fn-lbc-live-summary "g" fn-lbc))
         (ec-call (fn-lbc-withdrawn target fn-lbc))) fn-lbc))))
(defun lcw-fixture (target by)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (out fn-lbc) (lcw-test target by fn-lbc) out)))
(verify-guards lcw-test)
(verify-guards lcw-fixture)

(assert-event
 (equal (lcw-fixture 0 1237940039285380274899124224)
        '(t (2 1 2 3) :ok t t t t t (1 2 2 3) (2 . 1237940039285380274899124224))))
(assert-event
 (equal (lcw-fixture 1 7)
        '(t (2 1 2 3) :ok t t t t t (1 1 1 3) (2 . 7))))
(assert-event
 (equal (lcw-fixture 2 7)
        '(t (2 1 2 3) :invalid-withdraw t t t t t (2 1 2 3) nil)))

(defun lcw-unlink-test (disk pins tail outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let* ((segs (fn-lc-join (lcw-input) '((2 nil nil))))
        (fn-lbc (ec-call (fn-lbc-open-rebuild (list (lcw-held 0) (lcw-held 1)) segs fn-lbc))))
  (mv-let (answer fn-lbc afterdisk aftersegs trace)
   (fn-lc-unlink 2 disk :lc pins tail segs outcome fn-lbc)
   (mv (list answer (equal afterdisk disk)
          (consp (ec-call (fn-lb-log-model-segment 2 aftersegs)))
          (ec-call (fn-lc-locators-resolve fn-lbc aftersegs)) trace) fn-lbc))))
(defun lcw-unlink-fixture (disk pins tail outcome)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (out fn-lbc) (lcw-unlink-test disk pins tail outcome fn-lbc) out)))
(verify-guards lcw-unlink-test)
(verify-guards lcw-unlink-fixture)
(assert-event
 (equal (lcw-unlink-fixture nil nil 3 '(:ok :ok))
        '(:ok t nil t ((:unlink :segment 2) (:directory-fsync)))))
(assert-event
 (equal (lcw-unlink-fixture nil nil 3 '(:ok :uncertain))
        '(:uncertain t nil t ((:unlink :segment 2) (:directory-fsync)))))
(assert-event
 (equal (lcw-unlink-fixture nil '((0 . 2)) 3 '(:ok :ok))
        '(:referenced t t t nil)))
(assert-event
 (equal (lcw-unlink-fixture nil nil 2 '(:ok :ok))
        '(:referenced t t t nil)))
; Unknown physical roots are conservatively retained until their decoded
; slot-observation bridge has supplied a proven live set.
(assert-event
 (equal (lcw-unlink-fixture '(nil (:lc :unknown)) nil 3 '(:ok :ok))
        '(:referenced t t t nil)))
