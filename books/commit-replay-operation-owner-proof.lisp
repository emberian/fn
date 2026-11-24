; Operation ownership before the executor harvests a posted completion.
; Free and retired slots have no live owner. A reservation sets the
; owner kind, and every successfully peeked completion names an active slot.
(in-package "ACL2")
(include-book "vocab")
(fn2-book-layer :b)

(local (defthm fn2-op-owner-mv-choice
  (equal (mv-nth n (if c x y)) (if c (mv-nth n x) (mv-nth n y)))))
(local (defthm fn2-op-owner-mv-cons
  (equal (mv-nth n (cons x y)) (if (zp n) x (mv-nth (- n 1) y)))))

(local (defun fn2-op-owner-setter-facts (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let ((setter (fn2-columns-col-name 'fn2-ops (fn2-columns-pre "SET-" (car fields)))))
      (list* (fn2-columns-sym setter "-NTH") (fn2-columns-sym setter "-ROWS")
             (fn2-op-owner-setter-facts (cdr fields)))))))

(defun fn2-op-owner-active-p (slot kind fn2-ops)
 (declare (xargs :stobjs fn2-ops :guard (fn2-ops-wfp fn2-ops)))
 (or (not (and (natp slot) (< slot (fn2-ops-rows fn2-ops))))
     (member-equal (fn2-ops-phase slot fn2-ops) (list *fn2-op-phase-free* *fn2-op-phase-retired*))
     (equal (fn2-ops-owner-kind slot fn2-ops) kind)))

(defun-sk fn2-op-active-owners-p (kind ops)
 (forall slot (fn2-op-owner-active-p slot kind ops)))

(defthm fn2-ops-posted-slot-is-active
 (let* ((pk (fn2-ops-peek-posted ops)) (s (mv-nth 1 pk)))
  (implies (equal (car pk) t)
           (and (natp s) (< s (fn2-ops-rows ops))
                (not (member-equal (fn2-ops-phase s ops) (list *fn2-op-phase-free* *fn2-op-phase-retired*))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-ops-peek-posted-slot))
          :in-theory (e/d (fn2-ops-peek-posted fn2-completion-phasep fn2-op-slotp)
            (fn2-ops-phase fn2-ops-rows fn2-ops-post-count fn2-ops-post-head fn2-ops-posted-fifoi
             fn2-ops-posted-fifo-length fn2-ops-c0-posted fn2-ops-c0-harvested fn2-ops-c1-posted fn2-ops-c1-harvested)))))

(defthm fn2-ops-next-owner-from-active-owners
 (implies (and (fn2-op-active-owners-p kind ops) (mv-nth 0 (fn2-ops-next-owner ops)))
          (equal (mv-nth 1 (fn2-ops-next-owner ops)) kind))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories '(fn2-ops-next-owner fn2-op-owner-active-p
                 fn2-op-owner-mv-choice fn2-op-owner-mv-cons car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)
                 (:t fn2-ops-peek-posted) mv-nth) (theory 'minimal-theory))
          :use ((:instance fn2-op-active-owners-p-necc (slot (mv-nth 1 (fn2-ops-peek-posted ops))))
                fn2-ops-posted-slot-is-active))))

(local (defmacro fn2-op-row-owner-theory (&rest terms)
 `(union-theories
     (quote ,terms)
     (union-theories
        '(fn2-op-owner-active-p fn2-ops-rows fn2-ops-phase fn2-ops-phase$ai
          fn2-ops-owner-kind fn2-ops-owner-kind$ai nth-update-nth (:e equal) member-equal (:e <) (:e binary-+) (:e unary--)
          car-cons cdr-cons (:e member-equal) (:e nfix) nfix natp (:e zp))
        (fn2-op-owner-setter-facts (strip-cars
            (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-ops) world))))))))

(defthm fn2-op-active-owner-of-clear
 (implies (natp i)
          (iff (fn2-op-owner-active-p i okind (fn2-ops-clear-row slot gen next ops))
               (or (equal (nfix slot) i) (fn2-op-owner-active-p i okind ops))))
 :hints (("Goal" :in-theory (fn2-op-row-owner-theory fn2-ops-clear-row))))

(defthm fn2-op-reserve-keeps-active-owner-at
 (implies (fn2-op-owner-active-p i okind ops)
          (fn2-op-owner-active-p i okind
             (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release ops))))
 :hints (("Goal" :do-not-induct t
          :in-theory (fn2-op-row-owner-theory fn2-op-reserve fn2-op-slotp fn2-ops-clear-row
               update-fn2-ops-free-head update-fn2-ops-free-count update-fn2-ops-reserved-credits
               nth-update-nth mv-nth fn2-op-owner-mv-cons fn2-op-owner-mv-choice (:e mv-nth)
               (:t fn2-op-reserve) (:t fn2-ops-clear-row) fn2-ops-set-gen-nth
               fn2-ops-free-head fn2-ops-free-count fn2-ops-reserved-credits))))

(defthm fn2-op-reserve-keeps-active-owners
 (implies (fn2-op-active-owners-p okind ops)
          (fn2-op-active-owners-p okind
             (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release ops))))
 :hints (("Goal" :expand ((fn2-op-active-owners-p okind
                      (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release ops))))
          :in-theory nil
          :use ((:instance fn2-op-active-owners-p-necc (kind okind)
                    (slot (fn2-op-active-owners-p-witness okind
                     (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release ops)))))
                (:instance fn2-op-reserve-keeps-active-owner-at
                    (i (fn2-op-active-owners-p-witness okind
                     (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release ops)))))))))

(defthm fn2-op-owner-outside-table
 (implies (or (not (natp i)) (<= (fn2-ops-rows ops) i))
          (fn2-op-owner-active-p i kind ops))
 :hints (("Goal" :in-theory '(fn2-op-owner-active-p))))

(defthm fn2-ops-initializing-remaining-rows-keeps-owner-at
 (implies (and (natp i) (natp slot) (natp (fn2-ops-rows ops))
               (or (<= slot i) (fn2-op-owner-active-p i kind ops)))
          (fn2-op-owner-active-p i kind (fn2-ops-init-rows slot gen ops)))
 :hints (("Goal" :induct (fn2-ops-init-rows slot gen ops)
          :in-theory (e/d (fn2-ops-init-rows fn2-op-active-owner-of-clear)
                          (fn2-ops-clear-row fn2-op-owner-active-p fn2-ops-rows)))))

(defthm fn2-ops-initial-rows-only-have-active-owner-at
 (implies (natp (fn2-ops-rows ops))
          (fn2-op-owner-active-p i kind (fn2-ops-init-rows 0 gen ops)))
 :hints (("Goal" :cases ((natp i))
          :use ((:instance fn2-ops-initializing-remaining-rows-keeps-owner-at (slot 0)))
          :in-theory '(fn2-op-owner-outside-table natp (:e natp) (:e equal) (:e <)))))

(defthm fn2-op-table-initialization-has-active-owner
 (implies (natp (fn2-ops-rows (fn2-ops-init profile ops)))
          (fn2-op-owner-active-p i kind (fn2-ops-init profile ops)))
 :hints (("Goal" :in-theory '(fn2-ops-init fn2-ops-initial-rows-only-have-active-owner-at fn2-ops-init-rows-rows))))

(defthm fn2-op-table-initialization-has-only-active-owner
 (implies (natp (fn2-ops-rows (fn2-ops-init profile ops)))
          (fn2-op-active-owners-p kind (fn2-ops-init profile ops)))
 :hints (("Goal" :expand ((fn2-op-active-owners-p kind (fn2-ops-init profile ops)))
                 :in-theory '(fn2-op-table-initialization-has-active-owner))))

(local (defmacro fn2-op-check-owner-after-update (fn &rest runes)
 `(make-event
   (let* ((f ',fn) (args (formals f (w state))) (call (cons f args))
          (out (if (equal (stobjs-out f (w state)) '(fn2-ops)) call
                 (list 'mv-nth (position-eq 'fn2-ops (stobjs-out f (w state))) call))))
    (value
     `(defthm ,(fn2-columns-sym f "-KEEPS-ACTIVE-OWNER-AT")
       (implies (fn2-op-owner-active-p i owner fn2-ops)
                (fn2-op-owner-active-p i owner ,out))
       :hints (("Goal" :do-not-induct t :in-theory (fn2-op-row-owner-theory
              ,f fn2-op-owner-mv-choice fn2-op-owner-mv-cons mv-nth (:e mv-nth) ,@',runes))))))))
)

(fn2-op-check-owner-after-update fn2-op-set-range)
(fn2-op-check-owner-after-update fn2-op-set-capability)
(fn2-op-check-owner-after-update fn2-op-set-storage)
(fn2-op-check-owner-after-update fn2-op-set-cancel-target)
(fn2-op-check-owner-after-update fn2-op-enqueue fn2-op-slotp fn2-op-phase-code fn2-op-handle-code
 update-fn2-ops-out-sloti update-fn2-ops-out-geni update-fn2-ops-out-tail update-fn2-ops-queued
 update-fn2-ops-reserved-credits update-nth-array)
(fn2-op-check-owner-after-update fn2-op-unreserve fn2-ops-clear-row
 update-fn2-ops-free-head update-fn2-ops-free-count update-fn2-ops-reserved-credits)
(fn2-op-check-owner-after-update fn2-op-recycle fn2-ops-clear-row fn2-op-slotp
 update-fn2-ops-free-head update-fn2-ops-free-count update-fn2-ops-retired-count)
(defthm fn2-op-finish-keeps-active-owner-at
 (implies (fn2-op-owner-active-p i owner ops)
          (fn2-op-owner-active-p i owner (mv-nth 1 (fn2-op-finish slot gen ops))))
 :hints (("Goal" :in-theory (union-theories
              '(fn2-op-finish fn2-op-recycle-keeps-active-owner-at fn2-op-owner-mv-choice fn2-op-owner-mv-cons
                (:e zp) (:e binary-+) (:e unary--) (:e equal) car-cons cdr-cons mv-nth)
              (theory 'minimal-theory)))))

(defthm fn2-op-ack-one-keeps-active-owner-at
 (implies (fn2-op-owner-active-p i owner ops)
          (fn2-op-owner-active-p i owner (mv-nth 1 (fn2-outbox-ack 1 ops))))
 :hints (("Goal"  :do-not-induct t
          :expand ((fn2-outbox-submit-prefix 1 ops)
                   (:free (x) (fn2-outbox-submit-prefix 0 x))
                   (fn2-outbox-prefixp 1 (fn2-ops-out-head ops) ops)
                   (:free (x y) (fn2-outbox-prefixp 0 x y)))
          :in-theory (fn2-op-row-owner-theory
        fn2-outbox-ack fn2-outbox-prefixp fn2-outbox-submit-prefix fn2-op-phase-code fn2-op-handle-code fn2-op-slotp
        fn2-op-owner-mv-choice fn2-op-owner-mv-cons mv-nth (:e mv-nth)
        fn2-ops-queued fn2-ops-out-head update-fn2-ops-out-head update-fn2-ops-queued))))

(defthm fn2-op-post-result-keeps-active-owner
 (iff (fn2-op-owner-active-p i owner
        (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 ops))
      (fn2-op-owner-active-p i owner ops))
 :hints (("Goal" :do-not-induct t :in-theory (fn2-op-row-owner-theory
        fn2-post-result fn2-count-stray update-fn2-ops-stray update-fn2-ops-posted-fifoi
        update-fn2-ops-post-tail update-fn2-ops-post-count update-nth-array))))
(defthm fn2-op-harvest-keeps-active-owner
 (implies (fn2-op-owner-active-p i owner ops)
          (fn2-op-owner-active-p i owner (mv-nth 4 (fn2-harvest-next ops))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn2-ops-posted-slot-is-active))
          :in-theory (fn2-op-row-owner-theory
             fn2-harvest-next fn2-ops-latch-peer mv-nth fn2-op-owner-mv-choice fn2-op-owner-mv-cons
             (:t fn2-ops-peek-posted) update-fn2-ops-post-head update-fn2-ops-post-count
             update-fn2-ops-seen-peer-family update-fn2-ops-seen-peer-port update-fn2-ops-seen-peer-w0
             update-fn2-ops-seen-peer-w1 update-fn2-ops-seen-peer-w2 update-fn2-ops-seen-peer-w3))))
