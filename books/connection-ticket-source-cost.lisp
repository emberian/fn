; Source accounting of ACTUAL STATE-ticket finish/fault. Live native publication
; lowering is a separate matched coordinate; logical ADD-PAIR is not charged as
; a native constructor. No operation ticket is bypassed by these observers.
(in-package "ACL2")
(include-book "connection-operation-ticket")
(include-book "allocation-turn-source-cost")
(local (include-book "arithmetic-5/top" :dir :system))
(local (defthm fn-coptc-at-mv-nth
 (implies (natp n) (equal (fn-atsc-at n x) (mv-nth n x)))
 :hints (("Goal" :induct (fn-atsc-at n x) :in-theory (enable fn-atsc-at)))))
(local (defthm fn-coptc-fields
 (and (equal (fn-atsc-value (list value cells ops sites)) value)
      (equal (fn-atsc-cells (list value cells ops sites)) (nfix cells))
      (equal (fn-atsc-ops (list value cells ops sites)) ops)
      (equal (fn-atsc-sites (list value cells ops sites)) sites))
 :hints (("Goal" :in-theory (enable fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-atsc-at)))))

(defun fn-coptc-update (key val xs)
 (declare (xargs :guard (and (natp key) (true-listp xs)) :measure (nfix key)))
 (if (zp key)
     (list (cons val (cdr xs)) 1 nil '(update-nth))
   (let ((tail (fn-coptc-update (1- key) val (cdr xs))))
    (list (cons (car xs) (fn-atsc-value tail)) (+ 1 (fn-atsc-cells tail))
          (cons (list :subtract (list key 1)) (fn-atsc-ops tail))
          (cons 'update-nth (fn-atsc-sites tail))))))
(defthm fn-coptc-update-observes-result
 (equal (fn-atsc-value (fn-coptc-update key val xs)) (update-nth key val xs))
 :hints (("Goal" :induct (fn-coptc-update key val xs) :in-theory (enable update-nth))))
(defthm fn-coptc-update-source-census
 (implies (natp key)
  (and (equal (fn-atsc-cells (fn-coptc-update key val xs)) (+ 1 key))
       (equal (len (fn-atsc-ops (fn-coptc-update key val xs))) key)))
 :hints (("Goal" :induct (fn-coptc-update key val xs))))

(defun fn-coptc-finish (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
  :guard (fn-aec-pool-statep fn-page-read-pool) :verify-guards nil))
 (let ((ticket (fn-owner-connection-operation-ticket state)))
  (if (not (and ticket (fn-omk-widthp ticket 16)
                (eq (fn-omk-at 0 ticket) :connection-operation-ticket)
                (equal slot (fn-omk-at 7 ticket)) (equal nonce (fn-omk-at 8 ticket))
                (member-eq (fn-omk-at 1 ticket) '(:prepaid :started :refused))))
      (mv nil :recovery-required fn-allocation-turn-slots fn-page-read-pool state
          0 nil (list (list 'fn-owner-index-connection-finish (list slot nonce ticket))))
    (let* ((intent (fn-coptc-update 1 :finish-intent ticket))
           (state (f-put-global 'fn-owner-connection-operation-ticket (fn-atsc-value intent) state)))
     (mv-let (word fn-allocation-turn-slots fn-page-read-pool cells ops sites)
      (fn-atsc-finish slot nonce fn-allocation-turn-slots fn-page-read-pool)
      (declare (ignore cells))
      (let* ((done (if (eq word :left) (fn-coptc-update 1 :finished ticket) nil))
             (state (if (eq word :left)
                        (f-put-global 'fn-owner-connection-operation-ticket (fn-atsc-value done) state) state)))
       (mv nil word fn-allocation-turn-slots fn-page-read-pool state
           (+ (fn-atsc-cells intent) (if (eq word :left) (fn-atsc-cells done) 0))
           (fn-atsc-append (fn-atsc-ops intent)
             (fn-atsc-append ops (if (eq word :left) (fn-atsc-ops done) nil)))
           (fn-atsc-append
             (list (list 'fn-owner-index-connection-finish (list slot nonce ticket))
                   (list 'f-put-global (list 'fn-owner-connection-operation-ticket (fn-atsc-value intent))))
             (fn-atsc-append sites
               (if (eq word :left)
                   (list (list 'f-put-global (list 'fn-owner-connection-operation-ticket (fn-atsc-value done)))) nil)))))))))

)

(defthm fn-coptc-finish-observes-complete-actual-result
 (equal (let ((seen (fn-coptc-finish slot nonce slots pool state)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen) (mv-nth 4 seen)))
        (fn-owner-index-connection-finish slot nonce slots pool state))
 :hints (("Goal" :in-theory
          (disable fn-atsc-finish fn-ats-finish-owned fn-coptc-update
                   fn-owner-connection-operation-ticket fn-omk-at fn-omk-widthp
                   fn-atsc-value fn-atsc-ops fn-atsc-cells fn-atsc-sites)
          :use (fn-atsc-finish-observes-complete-actual-result)))
 :rule-classes nil)

(local (defthm fn-coptc-fixed-ticket-list
 (implies (fn-omk-widthp x n) (true-listp x))
 :hints (("Goal" :in-theory (enable fn-omk-widthp)))))
(verify-guards fn-coptc-finish
 :hints (("Goal" :in-theory
          (disable fn-atsc-finish fn-aec-pool-statep fn-owner-connection-operation-ticket
                   fn-omk-at fn-omk-widthp fn-coptc-update fn-atsc-value))))

(local (defthm fn-coptc-ats-word
 (equal (mv-nth 0 (fn-atsc-finish slot nonce slots pool))
        (mv-nth 0 (fn-ats-finish-owned slot nonce slots pool)))
 :hints (("Goal" :use fn-atsc-finish-observes-complete-actual-result
          :in-theory (disable fn-atsc-finish fn-ats-finish-owned)))))
(local (defthm fn-coptc-ats-left-condition
 (equal (equal (mv-nth 0 (fn-ats-finish-owned slot nonce slots pool)) :left)
        (and (fn-ats-matchingp slot nonce slots pool)
             (member-eq (fn-prp-alloc-mode pool) '(:active :draining))
             (posp (fn-prp-alloc-active-turns pool))))
 :hints (("Goal" :in-theory (disable fn-ats-matchingp fn-aec-installationp fn-aec-statep)))))
(local (defthm fn-coptc-append-length
 (equal (len (fn-atsc-append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (fn-atsc-append a b)))))
(defthm fn-coptc-actual-left-ticket-source-census
 (implies (eq (mv-nth 1 (fn-owner-index-connection-finish slot nonce slots pool state)) :left)
  (and (equal (mv-nth 5 (fn-coptc-finish slot nonce slots pool state)) 4)
       (equal (len (mv-nth 6 (fn-coptc-finish slot nonce slots pool state))) 3)))
 :hints (("Goal" :in-theory
  (disable fn-ats-finish-owned fn-atsc-finish fn-ats-matchingp fn-owner-connection-operation-ticket
           fn-omk-at fn-omk-widthp fn-coptc-update fn-atsc-cells fn-atsc-ops fn-atsc-value
           fn-coptc-ats-left-condition)
  :use (fn-coptc-ats-left-condition fn-atsc-finish-observes-complete-actual-result
        fn-atsc-finish-source-census-by-definition)))
 :rule-classes nil)

(defthm fn-coptc-all-finish-paths-ticket-source-bound
 (let ((seen (fn-coptc-finish slot nonce slots pool state)))
  (and (<= (mv-nth 5 seen) 4) (<= (len (mv-nth 6 seen)) 3)))
 :hints (("Goal" :in-theory
  (disable fn-atsc-finish fn-ats-finish-owned fn-ats-matchingp
           fn-owner-connection-operation-ticket fn-omk-at fn-omk-widthp fn-coptc-update
           fn-atsc-cells fn-atsc-ops fn-atsc-value)
  :use fn-atsc-finish-source-census-by-definition))
 :rule-classes nil)

(defun fn-coptc-fault (fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
  :guard (and (fn-aec-pool-statep fn-page-read-pool)
              (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))))
 (mv-let (word fn-allocation-turn-slots fn-page-read-pool)
  (fn-ats-uncertain-internal fn-allocation-turn-slots fn-page-read-pool)
  (mv nil word fn-allocation-turn-slots fn-page-read-pool state
      0 nil '(fn-owner-index-connection-fault fn-ats-uncertain-internal fn-aec-pool-uncertain-internal))))
(defthm fn-coptc-fault-observes-complete-actual-result
 (equal (let ((seen (fn-coptc-fault slots pool state)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen) (mv-nth 4 seen)))
        (fn-owner-index-connection-fault slots pool state))
 :hints (("Goal" :in-theory (disable fn-ats-uncertain-internal)))
 :rule-classes nil)
