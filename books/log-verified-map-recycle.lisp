; Recycle clears victim authorization and preserves all other entries.
(in-package "ACL2")
(include-book "log-verified-map")

(local (defthm fn-lbp-recycle-other-segment
 (implies (not (equal seg victim))
 (equal (fn-lb-log-model-segment seg (fn-lb-log-model-recycle victim log)) (fn-lb-log-model-segment seg log)))
 :hints (("Goal" :induct (fn-lb-log-model-recycle victim log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-recycle fn-lb-log-model-segment))))))

(local (defthm fn-lbp-recycle-other-range
 (implies (not (equal seg victim))
 (equal (fn-lb-log-model-read-range seg offset length (fn-lb-log-model-recycle victim log)) (fn-lb-log-model-read-range seg offset length log)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-read-range fn-lbp-recycle-other-segment))))))

(defthm fn-lb-log-recycle-preserves-other-entry
 (implies (not (equal seg victim))
 (and (equal (fn-lb-entry-octets seg entry (fn-lb-log-model-recycle victim log)) (fn-lb-entry-octets seg entry log))
      (equal (fn-lb-entry-protected-len seg entry (fn-lb-log-model-recycle victim log)) (fn-lb-entry-protected-len seg entry log))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-entry-octets fn-lb-entry-protected-len fn-lbp-recycle-other-range fn-lbp-recycle-other-segment)))))

(local (defun fn-lbp-victim-index-covers (bits keys victim)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp bits)
 (and (implies (and (equal (cdar bits) t) (equal (caaar bits) victim)) (member-equal (caar bits) keys))
      (fn-lbp-victim-index-covers (cdr bits) keys victim)) t)))

(local (defun fn-lbp-no-victim-marks (bits victim)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp bits)
 (and (not (and (equal (cdar bits) t) (equal (caaar bits) victim)))
      (fn-lbp-no-victim-marks (cdr bits) victim)) t)))

(local (defthm fn-lbp-index-covers-victim
 (implies (fn-lb-vmap-index-covers bits keys) (fn-lbp-victim-index-covers bits keys victim))
 :hints (("Goal" :induct (fn-lb-vmap-index-covers bits keys)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-vmap-index-covers fn-lbp-victim-index-covers))))))

(local (defthm fn-lbp-victim-index-step
 (implies (fn-lbp-victim-index-covers bits (cons key keys) victim)
 (fn-lbp-victim-index-covers (if (equal (car key) victim) (hons-remove-assoc key bits) bits) keys victim))
 :hints (("Goal" :induct (fn-lbp-victim-index-covers bits (cons key keys) victim)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbp-victim-index-covers hons-remove-assoc member-equal))))))

(local (defthm fn-lbp-member-of-subset
 (implies (and (subsetp-equal a b) (member-equal x a)) (member-equal x b))
 :hints (("Goal" :induct (subsetp-equal a b) :in-theory (union-theories (theory 'ground-zero) '(subsetp-equal member-equal))))))

(local (defthm fn-lbp-subset-cons-right
 (implies (subsetp-equal a b) (subsetp-equal a (cons x b)))
 :hints (("Goal" :induct (subsetp-equal a b) :in-theory (union-theories (theory 'ground-zero) '(subsetp-equal member-equal))))))

(local (defthm fn-lbp-subset-transitive
 (implies (and (subsetp-equal a b) (subsetp-equal b c)) (subsetp-equal a c))
 :rule-classes nil
 :hints (("Goal" :induct (subsetp-equal a b) :in-theory (union-theories (theory 'ground-zero) '(subsetp-equal fn-lbp-member-of-subset))))))

(local (defthm fn-lbp-remove-assoc-is-subset
 (subsetp-equal (hons-remove-assoc key bits) bits)
 :hints (("Goal" :induct (hons-remove-assoc key bits) :in-theory (union-theories (theory 'ground-zero) '(hons-remove-assoc subsetp-equal member-equal fn-lbp-subset-cons-right))))))

(local (defthm fn-lbp-remove-assoc-subset-transfer
 (implies (subsetp-equal a (hons-remove-assoc key bits)) (subsetp-equal a bits))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbp-subset-transitive (b (hons-remove-assoc key bits)) (c bits)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbp-remove-assoc-is-subset))))))

(local (defthm fn-lbp-victim-index-step-rest
 (implies (and (consp keys) (fn-lbp-victim-index-covers bits keys victim))
 (fn-lbp-victim-index-covers (if (equal (caar keys) victim) (hons-remove-assoc (car keys) bits) bits) (cdr keys) victim))
 :hints (("Goal" :do-not-induct t
 :cases ((equal keys (cons (car keys) (cdr keys))))
 :use ((:instance fn-lbp-victim-index-step (key (car keys)) (keys (cdr keys))))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbp-victim-index-step-matching
 (implies (and (consp keys) (fn-lbp-victim-index-covers bits keys victim) (equal (caar keys) victim))
 (fn-lbp-victim-index-covers (hons-remove-assoc (car keys) bits) (cdr keys) victim))
 :hints (("Goal" :use ((:instance fn-lbp-victim-index-step-rest)) :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbp-victim-index-step-other
 (implies (and (consp keys) (fn-lbp-victim-index-covers bits keys victim) (not (equal (caar keys) victim)))
 (fn-lbp-victim-index-covers bits (cdr keys) victim))
 :hints (("Goal" :use ((:instance fn-lbp-victim-index-step-rest)) :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbp-subset-reflexive
 (subsetp-equal a a)
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(subsetp-equal member-equal fn-lbp-subset-cons-right))))))

(local (defthm fn-lbp-recycle-keys-bits-subset
 (subsetp-equal (nth 0 (fn-lb-vmap-recycle-keys keys victim fn-lb-vmap)) (nth 0 fn-lb-vmap))
 :hints (("Goal" :induct (fn-lb-vmap-recycle-keys keys victim fn-lb-vmap)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-vmap-recycle-keys fn-lb-vmap-bits-rem fn-lbp-remove-assoc-subset-transfer fn-lbp-subset-reflexive subsetp-equal nth update-nth))))))

(local (defthm fn-lbp-covered-pair-member
 (implies (and (fn-lb-vmap-index-covers bits keys) (member-equal pair bits) (equal (cdr pair) t)) (member-equal (car pair) keys))
 :hints (("Goal" :induct (fn-lb-vmap-index-covers bits keys)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-vmap-index-covers member-equal))))))

(local (defthm fn-lbp-verified-pair-member
 (implies (and (fn-lb-verified-entries-invp bits log) (member-equal pair bits) (equal (cdr pair) t))
 (fn-arx-entry-ok (fn-lb-entry-octets (caar pair) (cdar pair) log) (fn-lb-entry-protected-len (caar pair) (cdar pair) log)))
 :hints (("Goal" :induct (fn-lb-verified-entries-invp bits log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-verified-entries-invp member-equal))))))

(local (defthm fn-lbp-index-covers-subset
 (implies (and (fn-lb-vmap-index-covers old keys) (subsetp-equal bits old)) (fn-lb-vmap-index-covers bits keys))
 :hints (("Goal" :induct (fn-lb-vmap-index-covers bits keys)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-vmap-index-covers subsetp-equal fn-lbp-covered-pair-member))))))

(local (defthm fn-lbp-retained-key-member
 (iff (member-equal key (fn-lb-vmap-retain-keys keys victim))
 (and (not (equal (car key) victim)) (member-equal key keys)))
 :hints (("Goal" :induct (fn-lb-vmap-retain-keys keys victim)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-vmap-retain-keys member-equal))))))

(local (defthm fn-lbp-index-covers-retained
 (implies (and (fn-lb-vmap-index-covers bits keys) (fn-lbp-no-victim-marks bits victim))
 (fn-lb-vmap-index-covers bits (fn-lb-vmap-retain-keys keys victim)))
 :hints (("Goal" :induct (fn-lb-vmap-index-covers bits keys)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-vmap-index-covers fn-lbp-no-victim-marks fn-lbp-retained-key-member))))))

(local (defthm fn-lbp-verified-subset-after-recycle
 (implies (and (fn-lb-verified-entries-invp old log) (subsetp-equal bits old) (fn-lbp-no-victim-marks bits victim))
 (fn-lb-verified-entries-invp bits (fn-lb-log-model-recycle victim log)))
 :hints (("Goal" :induct (fn-lb-verified-entries-invp bits log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-verified-entries-invp fn-lbp-no-victim-marks subsetp-equal fn-lbp-verified-pair-member fn-lb-log-recycle-preserves-other-entry))))))

(local (defthm fn-lbp-victim-index-empty-bits
 (implies (atom bits) (fn-lbp-victim-index-covers bits keys victim))
 :hints (("Goal" :in-theory '(fn-lbp-victim-index-covers)))))

(local (defthm fn-lbp-no-victim-marks-empty-bits
 (implies (atom bits) (fn-lbp-no-victim-marks bits victim))
 :hints (("Goal" :in-theory '(fn-lbp-no-victim-marks)))))

(local (defthm fn-lbp-victim-index-atom-is-no-marks
 (implies (and (atom keys) (fn-lbp-victim-index-covers bits keys victim)) (fn-lbp-no-victim-marks bits victim))
 :hints (("Goal" :induct (fn-lbp-victim-index-covers bits keys victim)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbp-victim-index-covers fn-lbp-no-victim-marks member-equal))))))

(local (defthm fn-lbp-recycle-keys-has-no-victim-marks
 (implies (fn-lbp-victim-index-covers (nth 0 fn-lb-vmap) keys victim)
 (fn-lbp-no-victim-marks (nth 0 (fn-lb-vmap-recycle-keys keys victim fn-lb-vmap)) victim))
 :hints (("Goal" :induct (fn-lb-vmap-recycle-keys keys victim fn-lb-vmap)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-vmap-recycle-keys fn-lb-vmap-bits-rem fn-lbp-victim-index-step-matching fn-lbp-victim-index-step-other fn-lbp-victim-index-atom-is-no-marks fn-lbp-victim-index-empty-bits fn-lbp-no-victim-marks-empty-bits nth update-nth))))))

(local (defthm fn-lbp-recycle-bits-subset
 (subsetp-equal (nth 0 (fn-lb-vmap-recycle victim fn-lb-vmap)) (nth 0 fn-lb-vmap))
 :hints (("Goal" :use ((:instance fn-lbp-recycle-keys-bits-subset (keys (fn-lb-vmap-index fn-lb-vmap))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-vmap-recycle fn-lb-vmap-index update-fn-lb-vmap-index nth update-nth))))))

(local (defthm fn-lbp-recycle-has-no-victim-marks
 (implies (fn-lb-vmap-index-covers (nth 0 fn-lb-vmap) (nth 1 fn-lb-vmap))
 (fn-lbp-no-victim-marks (nth 0 (fn-lb-vmap-recycle victim fn-lb-vmap)) victim))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbp-index-covers-victim (bits (nth 0 fn-lb-vmap)) (keys (nth 1 fn-lb-vmap)))
       (:instance fn-lbp-recycle-keys-has-no-victim-marks (keys (nth 1 fn-lb-vmap))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-vmap-recycle fn-lb-vmap-index update-fn-lb-vmap-index nth update-nth))))))

(local (defthm fn-lbp-no-victim-marks-no-lookup
 (implies (fn-lbp-no-victim-marks bits victim)
 (not (equal (cdr (hons-assoc-equal (cons victim entry) bits)) t)))
 :hints (("Goal" :induct (fn-lbp-no-victim-marks bits victim)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbp-no-victim-marks hons-assoc-equal))))))

(defthm fn-lb-vmap-recycle-clears-segment
 (implies (fn-lb-vmap-index-covers (nth 0 fn-lb-vmap) (nth 1 fn-lb-vmap))
 (not (fn-lb-verified-bit victim entry (fn-lb-vmap-recycle victim fn-lb-vmap))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbp-recycle-has-no-victim-marks)
       (:instance fn-lbp-no-victim-marks-no-lookup (bits (nth 0 (fn-lb-vmap-recycle victim fn-lb-vmap)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-verified-bit fn-lb-vmap-bits-get)))))

(local (defthm fn-lbp-vmap-index-of-recycle
 (equal (nth 1 (fn-lb-vmap-recycle victim fn-lb-vmap)) (fn-lb-vmap-retain-keys (nth 1 fn-lb-vmap) victim))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-vmap-recycle fn-lb-vmap-index update-fn-lb-vmap-index nth update-nth))))))

(defthm fn-lb-verified-invp-of-recycle
 (implies (fn-lb-verified-invp log fn-lb-vmap)
 (fn-lb-verified-invp (fn-lb-log-model-recycle victim log) (fn-lb-vmap-recycle victim fn-lb-vmap)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbp-recycle-bits-subset)
       (:instance fn-lbp-recycle-has-no-victim-marks)
       (:instance fn-lbp-index-covers-subset (old (nth 0 fn-lb-vmap)) (bits (nth 0 (fn-lb-vmap-recycle victim fn-lb-vmap))) (keys (nth 1 fn-lb-vmap)))
       (:instance fn-lbp-index-covers-retained (bits (nth 0 (fn-lb-vmap-recycle victim fn-lb-vmap))) (keys (nth 1 fn-lb-vmap)))
       (:instance fn-lbp-verified-subset-after-recycle (old (nth 0 fn-lb-vmap)) (bits (nth 0 (fn-lb-vmap-recycle victim fn-lb-vmap)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-verified-invp fn-lbp-vmap-index-of-recycle)))))

(local (defthm fn-lbp-assoc-after-remove
 (equal (hons-assoc-equal q (hons-remove-assoc key bits))
 (if (equal q key) nil (hons-assoc-equal q bits)))
 :hints (("Goal" :induct (hons-remove-assoc key bits)
 :in-theory (union-theories (theory 'ground-zero) '(hons-remove-assoc hons-assoc-equal))))))

(local (defthm fn-lbp-recycle-keys-other-bit
 (implies (not (equal seg victim))
 (equal (fn-lb-verified-bit seg entry (fn-lb-vmap-recycle-keys keys victim fn-lb-vmap)) (fn-lb-verified-bit seg entry fn-lb-vmap)))
 :hints (("Goal" :induct (fn-lb-vmap-recycle-keys keys victim fn-lb-vmap)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-vmap-recycle-keys fn-lb-vmap-bits-rem fn-lb-verified-bit fn-lb-vmap-bits-get fn-lbp-assoc-after-remove nth update-nth))))))

(defthm fn-lb-vmap-recycle-preserves-other-bits
 (implies (not (equal seg victim))
 (equal (fn-lb-verified-bit seg entry (fn-lb-vmap-recycle victim fn-lb-vmap)) (fn-lb-verified-bit seg entry fn-lb-vmap)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbp-recycle-keys-other-bit (keys (fn-lb-vmap-index fn-lb-vmap))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-vmap-recycle fn-lb-vmap-index fn-lb-verified-bit fn-lb-vmap-bits-get update-fn-lb-vmap-index nth update-nth)))))

(local (defthm fn-lbp-recycle-segment-ids
 (implies (fn-lc-seg-ids-allocatedp log next-id exhaustedp)
 (fn-lc-seg-ids-allocatedp (fn-lb-log-model-recycle victim log) next-id exhaustedp))
 :hints (("Goal" :induct (fn-lb-log-model-recycle victim log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-recycle fn-lc-seg-ids-allocatedp))))))

(local (defthm fn-lbp-retain-key-ids
 (implies (fn-lc-key-ids-allocatedp keys next-id exhaustedp)
 (fn-lc-key-ids-allocatedp (fn-lb-vmap-retain-keys keys victim) next-id exhaustedp))
 :hints (("Goal" :induct (fn-lb-vmap-retain-keys keys victim)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-vmap-retain-keys fn-lc-key-ids-allocatedp))))))

(defthm fn-lb-vmap-recycle-preserves-segment-ids-below-next
 (implies (fn-lc-segment-ids-below-next next-id exhaustedp log (fn-lb-vmap-index fn-lb-vmap))
 (fn-lc-segment-ids-below-next next-id exhaustedp (fn-lb-log-model-recycle victim log)
 (fn-lb-vmap-index (fn-lb-vmap-recycle victim fn-lb-vmap))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbp-recycle-segment-ids)
       (:instance fn-lbp-retain-key-ids (keys (fn-lb-vmap-index fn-lb-vmap))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lc-segment-ids-below-next fn-lb-vmap-index fn-lbp-vmap-index-of-recycle)))))
