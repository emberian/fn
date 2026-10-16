; Authentication must precede setting a bit; reopen must discard stale bits.
(in-package "ACL2")
(include-book "../../books/log-verified-map-reset")
(include-book "lb-column-read-cost-teeth")
(defun fn-lbvt-corrupt-log ()
 (declare (xargs :guard t :verify-guards nil))
 (let* ((log (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil))
        (segment (car log)))
  (list (update-nth 1 (update-nth 0 255 (cadr segment)) segment))))
(defun fn-lbvt-blind-mark (seg entry log fn-lb-vmap)
 (declare (ignore log) (xargs :stobjs fn-lb-vmap :guard t))
 (let ((fn-lb-vmap (update-fn-lb-vmap-index
                   (cons (cons seg entry) (fn-lb-vmap-index fn-lb-vmap)) fn-lb-vmap)))
  (fn-lb-vmap-bits-put (cons seg entry) t fn-lb-vmap)))
(defthm fn-lbvt-corrupt-entry-is-real-and-bad
 (and (equal (nth 3 (car (caddar (fn-lbvt-corrupt-log)))) 6)
      (consp (fn-lb-entry-octets 1 6 (fn-lbvt-corrupt-log)))
      (not (fn-arx-entry-ok (fn-lb-entry-octets 1 6 (fn-lbvt-corrupt-log))
                           (fn-lb-entry-protected-len 1 6 (fn-lbvt-corrupt-log)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 (executable-counterpart-theory :here)))))
(defthm fn-lbvt-mark-whole-positive
 (and (fn-lb-verified-invp (fn-lbvt-corrupt-log) '(nil nil))
      (fn-lb-verified-invp (fn-lbvt-corrupt-log)
        (fn-lb-vmap-mark 1 6 (fn-lbvt-corrupt-log) '(nil nil))))
 :rule-classes nil
 :hints (("Goal" :use fn-lbvt-corrupt-entry-is-real-and-bad
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-verified-invp fn-lb-verified-entries-invp fn-lb-vmap-index-covers fn-lb-vmap-mark nth)))))
(defthm fn-lbvt-mark-fault-whole-positive
 (and (fn-lb-verified-invp (fn-lbvt-corrupt-log) '(nil nil))
      (fn-lb-verified-invp (fn-lbvt-corrupt-log)
        (fn-lb-vmap-mark 1 6 (fn-lbvt-corrupt-log) '(nil nil)))
      (not (fn-lb-verified-invp (fn-lbvt-corrupt-log)
        (fn-lbvt-blind-mark 1 6 (fn-lbvt-corrupt-log) '(nil nil)))))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbvt-mark-whole-positive fn-lbvt-corrupt-entry-is-real-and-bad)
  :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-verified-invp fn-lb-verified-entries-invp fn-lb-vmap-index-covers
    fn-lbvt-blind-mark fn-lb-vmap-bits-put update-fn-lb-vmap-index fn-lb-vmap-index
    nth update-nth hons-assoc-equal member-equal)))))
(defthm fn-lbvt-mark-removal
 (and (not (fn-lb-verified-invp (fn-lbvt-corrupt-log) '((((1 . 6) . t)) ((1 . 6)))))
      (not (fn-lb-verified-invp (fn-lbvt-corrupt-log)
        (fn-lb-vmap-mark 1 6 (fn-lbvt-corrupt-log) '((((1 . 6) . t)) ((1 . 6)))))))
 :rule-classes nil
 :hints (("Goal" :use fn-lbvt-corrupt-entry-is-real-and-bad
  :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-verified-invp fn-lb-verified-entries-invp fn-lb-vmap-index-covers fn-lb-vmap-mark nth member-equal)))))
(defteeth fn-lb-verified-invp-of-mark
 :claim (((verified (fn-lb-verified-invp log fn-lb-vmap-v)))
   (fn-lb-verified-invp log (fn-lb-vmap-mark seg entry log fn-lb-vmap-v)))
 :subject fn-lb-vmap-mark
 :witness ((log (fn-lbvt-corrupt-log)) (fn-lb-vmap-v '(nil nil)) (seg 1) (entry 6))
 :witness-lemma fn-lbvt-mark-whole-positive
 :breaks ((verified ((log (fn-lbvt-corrupt-log)) (fn-lb-vmap-v '((((1 . 6) . t)) ((1 . 6)))) (seg 1) (entry 6))
  :lemma fn-lbvt-mark-removal))
 :mutations ((blind-authentication (:conclusion (fn-lb-verified-invp log (fn-lbvt-blind-mark seg entry log fn-lb-vmap-v)))
  ((log (fn-lbvt-corrupt-log)) (fn-lb-vmap-v '(nil nil)) (seg 1) (entry 6))
  :fault "Set the bit without checking the stored entry trailer" :lemma fn-lbvt-mark-fault-whole-positive)))
(defthm fn-lbvt-clear-whole-positive
 (fn-lb-verified-invp (fn-lbvt-corrupt-log)
  (fn-lb-vmap-clear '((((1 . 6) . t)) ((1 . 6)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lb-verified-invp-of-clear (log (fn-lbvt-corrupt-log)) (fn-lb-vmap-v '((((1 . 6) . t)) ((1 . 6)))))) :in-theory (theory 'ground-zero))))
(defthm fn-lbvt-clear-fault-whole-positive
 (and (fn-lb-verified-invp (fn-lbvt-corrupt-log)
        (fn-lb-vmap-clear '((((1 . 6) . t)) ((1 . 6)))))
      (not (fn-lb-verified-invp (fn-lbvt-corrupt-log) '((((1 . 6) . t)) ((1 . 6))))))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbvt-clear-whole-positive fn-lbvt-mark-removal)
  :in-theory (theory 'ground-zero))))
(defteeth fn-lb-verified-invp-of-clear
 :claim (nil (fn-lb-verified-invp log (fn-lb-vmap-clear fn-lb-vmap-v)))
 :subject fn-lb-vmap-clear
 :witness ((log (fn-lbvt-corrupt-log)) (fn-lb-vmap-v '((((1 . 6) . t)) ((1 . 6)))))
 :witness-lemma fn-lbvt-clear-whole-positive :breaks ()
 :mutations ((retain-before-reopen (:conclusion (fn-lb-verified-invp log fn-lb-vmap-v))
  ((log (fn-lbvt-corrupt-log)) (fn-lb-vmap-v '((((1 . 6) . t)) ((1 . 6)))))
  :fault "Reopen retains the old verification map over changed bytes"
  :lemma fn-lbvt-clear-fault-whole-positive)))
(defun fn-lbvt-native-mark-clear-control ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lb-vmap
  (mv-let (ok fn-lb-vmap)
   (let* ((good (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil))
          (bad (fn-lbvt-corrupt-log))
          (fn-lb-vmap (fn-lb-vmap-mark 1 6 bad fn-lb-vmap))
          (refused (not (fn-lb-verified-bit 1 6 fn-lb-vmap)))
          (fn-lb-vmap (fn-lb-vmap-mark 1 6 good fn-lb-vmap))
          (accepted (fn-lb-verified-bit 1 6 fn-lb-vmap))
          (fn-lb-vmap (fn-lb-vmap-clear fn-lb-vmap)))
    (mv (and refused accepted (not (fn-lb-verified-bit 1 6 fn-lb-vmap))
             (equal (fn-lb-vmap-index fn-lb-vmap) nil)) fn-lb-vmap)) ok)))
(with-guard-checking-event t (assert-event (fn-lbvt-native-mark-clear-control)))
