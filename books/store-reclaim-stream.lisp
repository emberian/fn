; fn: the reclaim's rewrite streamed one record at a time (lane compact-arena,
; 2026-09-27; PKT-686 item 2).
;
; `store reclaim' reads each committed record once and keeps, besides
; counts, only (a) the Message-IDs it rewrites, (b) the octets it frees and
; (c) the rewritten history while it fits one unit (*fn-cc-max-events*
; events, *fn-cc-max-octets* octets; SPANS records that it passed one).
; `fn-rcls-step' reads ONE record and carries (USED MSGIDS-REVERSED FREED
; NEW-REVERSED SIZE SPANS), so the host hands ACL2 one record at a time and
; holds, beside its own octet vectors, one record's list.
;
; `fn-rcls-fold-of-init': over the fold of the records from `fn-rcls-init'
; under a context, the carried quantities are the whole-history ones of
; books/store-reclaim-pack.lisp (`fn-rclp-rewritten-msgids',
; `fn-rclp-freed', `fn-rclp-events').  books/store-log-reclaim.lisp's
; keystone `fn-lgr-decide-stream-is-lgr-decide' rests on it.
; Host: host/checkpoint-host.lisp `fn-store-reclaim-context',
; `fn-store-reclaim-init', `fn-store-reclaim-step', from
; host/native/checkpoint.lisp `fnn-log-reclaim-steps'.  (The pack decision
; this fold once fed, `fn-rcls-decide', went with the pack layer.)
(in-package "ACL2")
(include-book "store-reclaim-pack")

(local (in-theory (disable fn-rclp-event fn-rclp-rewrites-p)))

(defun fn-rcls-init ()
  (declare (xargs :guard t))
  (list 0 nil 0 nil 32 nil))

(defun fn-rcls-msgid (octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-msgid (fn-record-result-record (fn-record-decode-exact octets))))

; One record: counted; its Message-ID kept when rewritten; its freed octets
; added; its rewritten event kept while the rewritten prefix fits one link.
(defun fn-rcls-step (acc octets ctx)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((used (+ 1 (nfix (nth 0 acc))))
         (e (fn-rclp-event octets ctx))
         (size (+ (nfix (nth 4 acc)) (len e) 5))
         (spans (or (nth 5 acc)
                    (< *fn-cc-max-events* used)
                    (< *fn-cc-max-octets* size))))
    (list used
          (if (fn-rclp-rewrites-p octets ctx)
              (cons (fn-rcls-msgid octets) (nth 1 acc))
            (nth 1 acc))
          (+ (fix (nth 2 acc)) (- (len octets) (len e)))
          (if spans nil (cons e (nth 3 acc)))
          size
          (if spans t nil))))

(defun fn-rcls-fold (events ctx acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (fn-rcls-fold (cdr events) ctx (fn-rcls-step acc (car events) ctx))
    acc))

; -----------------------------------------------------------------------------
; What the fold carries.

(defun fn-rcls-size (events ctx)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (+ (len (fn-rclp-event (car events) ctx)) 5 (fn-rcls-size (cdr events) ctx))
    0))

(defthm fn-rcls-size-is-event-octets-size
  (equal (+ 32 (fn-rcls-size events ctx))
         (fn-cc-event-octets-size (fn-rclp-events events ctx)))
  :hints (("Goal" :induct (fn-rclp-events events ctx)
           :in-theory (enable fn-cc-event-octets-size))))

(local
 (defthm fn-rcls-step-parts
   (let ((a (fn-rcls-step acc e ctx)))
     (and (equal (nth 0 a) (+ 1 (nfix (nth 0 acc))))
          (equal (nth 1 a) (if (fn-rclp-rewrites-p e ctx)
                               (cons (fn-rcls-msgid e) (nth 1 acc))
                             (nth 1 acc)))
          (equal (nth 2 a) (+ (fix (nth 2 acc)) (- (len e) (len (fn-rclp-event e ctx)))))
          (equal (nth 4 a) (+ (nfix (nth 4 acc)) (len (fn-rclp-event e ctx)) 5))
          (iff (nth 5 a) (or (nth 5 acc)
                             (< *fn-cc-max-events* (+ 1 (nfix (nth 0 acc))))
                             (< *fn-cc-max-octets*
                                (+ (nfix (nth 4 acc)) (len (fn-rclp-event e ctx)) 5))))))))

(local (in-theory (disable fn-rcls-step fn-rcls-msgid)))

(local
 (defthm fn-rcls-fold-used
   (equal (nth 0 (fn-rcls-fold events ctx acc))
          (if (consp events) (+ (nfix (nth 0 acc)) (len events)) (nth 0 acc)))
   :hints (("Goal" :induct (fn-rcls-fold events ctx acc)))))

(local
 (defthm fn-rcls-fold-msgids
   (equal (nth 1 (fn-rcls-fold events ctx acc))
          (revappend (fn-rclp-rewritten-msgids events ctx) (nth 1 acc)))
   :hints (("Goal" :induct (fn-rcls-fold events ctx acc)
            :in-theory (enable fn-rcls-msgid)))))

(local
 (defthm fn-rcls-fold-freed
   (equal (nth 2 (fn-rcls-fold events ctx acc))
          (if (consp events) (+ (fix (nth 2 acc)) (fn-rclp-freed events ctx)) (nth 2 acc)))
   :hints (("Goal" :induct (fn-rcls-fold events ctx acc)))))

(local
 (defthm fn-rcls-fold-size
   (equal (nth 4 (fn-rcls-fold events ctx acc))
          (if (consp events) (+ (nfix (nth 4 acc)) (fn-rcls-size events ctx)) (nth 4 acc)))
   :hints (("Goal" :induct (fn-rcls-fold events ctx acc)))))

(local
 (defthm fn-rcls-size-natp
   (natp (fn-rcls-size events ctx))
   :rule-classes :type-prescription))

; Length and size only grow, so the prefix passes one link exactly when the
; whole history does (or it already had).
(local
 (defthm fn-rcls-fold-spans
   (implies (consp events)
            (iff (nth 5 (fn-rcls-fold events ctx acc))
                 (or (nth 5 acc)
                     (< *fn-cc-max-events* (+ (nfix (nth 0 acc)) (len events)))
                     (< *fn-cc-max-octets* (+ (nfix (nth 4 acc))
                                              (fn-rcls-size events ctx))))))
   :hints (("Goal" :induct (fn-rcls-fold events ctx acc)))))

(local
 (defthm fn-rcls-fold-spans-sticky
   (implies (nth 5 acc)
            (nth 5 (fn-rcls-fold events ctx acc)))
   :hints (("Goal" :induct (fn-rcls-fold events ctx acc)))))

(local
 (defthm fn-rcls-not-spans-before
   (implies (not (nth 5 (fn-rcls-fold events ctx acc)))
            (not (nth 5 acc)))
   :hints (("Goal" :use fn-rcls-fold-spans-sticky))))

(local
 (defthm fn-rcls-step-new
   (implies (not (nth 5 (fn-rcls-step acc e ctx)))
            (equal (nth 3 (fn-rcls-step acc e ctx))
                   (cons (fn-rclp-event e ctx) (nth 3 acc))))
   :hints (("Goal" :in-theory (enable fn-rcls-step)))))

(local
 (defthm fn-rcls-fold-new
   (implies (not (nth 5 (fn-rcls-fold events ctx acc)))
            (equal (nth 3 (fn-rcls-fold events ctx acc))
                   (revappend (fn-rclp-events events ctx) (nth 3 acc))))
   :hints (("Goal" :induct (fn-rcls-fold events ctx acc)
            :in-theory (disable fn-rcls-fold-spans)))))

; -----------------------------------------------------------------------------
; The fold read as the whole-history quantities.

(local
 (defthm fn-rcls-rev-of-revappend-nil
   (equal (rev (revappend x nil)) (list-fix x))))

(local
 (defthm fn-rcls-events-true-listp
   (implies (true-listp events)
            (true-listp (fn-rclp-events events ctx)))))

(local
 (defthm fn-rcls-rewritten-msgids-true-listp
   (true-listp (fn-rclp-rewritten-msgids events ctx))
   :rule-classes :type-prescription))

(local
 (defthm fn-rcls-len-of-events
   (equal (len (fn-rclp-events events ctx)) (len events))))

(local
 (defthm fn-rcls-atom-msgids-of-atom
   (implies (not (consp events))
            (equal (fn-rclp-rewritten-msgids events ctx) nil))))

(local
 (defthm fn-rcls-freed-of-atom
   (implies (not (consp events)) (equal (fn-rclp-freed events ctx) 0))))

(local
 (defthm fn-rcls-fold-of-atom
   (implies (not (consp events))
            (equal (fn-rcls-fold events ctx acc) acc))))

;; The fold from the start, read as the whole-history quantities.
(defthm fn-rcls-fold-of-init
  (implies (true-listp records)
           (let ((acc (fn-rcls-fold records ctx (fn-rcls-init))))
             (and (equal (nfix (nth 0 acc)) (len records))
                  (equal (rev (nth 1 acc)) (fn-rclp-rewritten-msgids records ctx))
                  (equal (nth 2 acc) (fn-rclp-freed records ctx))
                  (iff (nth 5 acc)
                       (or (< *fn-cc-max-events* (len (fn-rclp-events records ctx)))
                           (< *fn-cc-max-octets*
                              (fn-cc-event-octets-size (fn-rclp-events records ctx)))))
                  (implies (not (nth 5 acc))
                           (equal (rev (nth 3 acc)) (fn-rclp-events records ctx))))))
  :rule-classes nil
  :hints (("Goal" :cases ((consp records)) :do-not-induct t
           :use ((:instance fn-rcls-size-is-event-octets-size (events records)))
           :in-theory (disable fn-rcls-fold fn-rcls-size-is-event-octets-size
                               fn-cc-event-octets-size))))
