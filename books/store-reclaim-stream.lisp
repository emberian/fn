; fn: the reclaim's rewrite streamed one record at a time (lane compact-arena,
; 2026-09-27; PKT-686 item 2).
;
; `store reclaim' reads each committed record once and keeps, besides the
; count, only (a) the Message-IDs it rewrites and (b) the octets it frees.
; `fn-rcls-step' reads ONE record and carries (USED MSGIDS-REVERSED FREED), so
; the host hands ACL2 one record at a time and holds, beside its own octet
; vectors of the rewrites, one record's list.  (Until lane log-leftovers,
; 2026-09-27, the fold also carried the pack era's rewritten history while it
; fit one unit and SPANS, which the log's decision never read: flip-cleanup's
; packet P5.)
;
; `fn-rcls-fold-of-init': over the fold of the records from `fn-rcls-init'
; under a context, the carried quantities are the whole-history ones of
; books/store-reclaim-pack.lisp (`fn-rclp-rewritten-msgids', `fn-rclp-freed').
; books/store-log-reclaim.lisp's keystone `fn-lgr-decide-stream-is-lgr-decide'
; rests on it.  Host: host/checkpoint-host.lisp `fn-store-reclaim-context',
; `fn-store-reclaim-init', `fn-store-reclaim-step', from
; host/native/checkpoint.lisp `fnn-log-reclaim-steps'.
(in-package "ACL2")
(include-book "store-reclaim-pack")

(local (in-theory (disable fn-rclp-event fn-rclp-rewrites-p)))

(defun fn-rcls-init ()
  (declare (xargs :guard t))
  (list 0 nil 0))

(defun fn-rcls-msgid (octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-msgid (fn-record-result-record (fn-record-decode-exact octets))))

; One record: counted; its Message-ID kept when rewritten; its freed octets
; added.
(defun fn-rcls-step (acc octets ctx)
  (declare (xargs :guard t :verify-guards nil))
  (list (+ 1 (nfix (nth 0 acc)))
        (if (fn-rclp-rewrites-p octets ctx)
            (cons (fn-rcls-msgid octets) (nth 1 acc))
          (nth 1 acc))
        (+ (fix (nth 2 acc)) (- (len octets) (len (fn-rclp-event octets ctx))))))

(defun fn-rcls-fold (events ctx acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (fn-rcls-fold (cdr events) ctx (fn-rcls-step acc (car events) ctx))
    acc))

; -----------------------------------------------------------------------------
; What the fold carries.

(local
 (defthm fn-rcls-step-parts
   (let ((a (fn-rcls-step acc e ctx)))
     (and (equal (nth 0 a) (+ 1 (nfix (nth 0 acc))))
          (equal (nth 1 a) (if (fn-rclp-rewrites-p e ctx)
                               (cons (fn-rcls-msgid e) (nth 1 acc))
                             (nth 1 acc)))
          (equal (nth 2 a) (+ (fix (nth 2 acc)) (- (len e) (len (fn-rclp-event e ctx)))))))))

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

; -----------------------------------------------------------------------------
; The fold read as the whole-history quantities.

(local
 (defthm fn-rcls-rev-of-revappend-nil
   (equal (rev (revappend x nil)) (list-fix x))))

(local
 (defthm fn-rcls-rewritten-msgids-true-listp
   (true-listp (fn-rclp-rewritten-msgids events ctx))
   :rule-classes :type-prescription))

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
                  (equal (nth 2 acc) (fn-rclp-freed records ctx)))))
  :rule-classes nil
  :hints (("Goal" :cases ((consp records)) :do-not-induct t
           :in-theory (disable fn-rcls-fold))))
