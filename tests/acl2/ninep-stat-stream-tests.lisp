(in-package "ACL2")
(include-book "../../books/ninep-stat-stream")

; Logical full-wire fixture only; the served subject emits one concrete byte.
(defun-nx n9pst-run (fuel cursor fn-octets)
 (declare (xargs :stobjs fn-octets :measure (nfix fuel) :verify-guards nil
                 :hints (("Goal" :in-theory (disable fn-9pst-reply-step)))))
 (if (zp fuel) (mv :quantum cursor fn-octets)
  (mv-let (word next fn-octets) (fn-9pst-reply-step cursor fn-octets)
   (if (eq word :yield) (n9pst-run (1- fuel) next fn-octets)
    (mv word next fn-octets)))))

(defconst *n9pst-directory-entry*
 '(48 0 0 0 0 0 0 0 128 0 0 0 0 7 0 0 0 0 0 0 0
   109 1 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   1 0 97 0 0 0 0 0 0))

(defthm n9pst-stat-full-literal-wire-positive
 (let* ((stat (mv-nth 1 (fn-9pst-begin "a" '(128 0 7) 0)))
        (reply (mv-nth 1 (fn-9pst-reply-begin :stat 3 64 0 stat)))
        (result (n9pst-run 60 reply (create-fn-octets))))
  (and (fn-9pst-ready-p stat)
       (equal (mv-nth 0 result) :reply-ready)
       (equal (mv-nth 2 result)
              (append '(59 0 0 0 125 3 0 50 0) *n9pst-directory-entry*))
       (equal (fn-9pst-reply-step (mv-nth 1 result) (mv-nth 2 result)) result)
       (equal (fn-9p-metadata-at 4 (fn-9p-metadata-at 3 (mv-nth 1 result))) 50)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (fuel cursor fn-octets) (n9pst-run fuel cursor fn-octets)))
                 :in-theory (enable fn-octets-len fn-octets-append-octet))))

(defthm n9pst-directory-full-integral-wire-positive
 (let* ((stat (mv-nth 1 (fn-9pst-begin "a" '(128 0 7) 0)))
        (reply (mv-nth 1 (fn-9pst-reply-begin :directory-read 4 64 50 stat)))
        (result (n9pst-run 62 reply (create-fn-octets))))
  (and (fn-9pst-ready-p stat)
       (equal (mv-nth 0 result) :reply-ready)
       (equal (mv-nth 2 result)
              (append '(61 0 0 0 117 4 0 50 0 0 0) *n9pst-directory-entry*))
       (equal (len (mv-nth 2 result)) 61)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (fuel cursor fn-octets) (n9pst-run fuel cursor fn-octets)))
                 :in-theory (enable fn-octets-len fn-octets-append-octet))))

(defthm n9pst-small-count-hypothesis-removal
 (let ((stat (mv-nth 1 (fn-9pst-begin "a" '(128 0 7) 0))))
  (and (fn-9pst-ready-p stat) (equal (fn-9p-metadata-at 4 stat) 0)
       (< 4 65535) (fn-9p-profile-msizep 64)
       (<= (+ 11 (fn-9p-metadata-at 5 stat)) 64)
       (natp 49) (not (<= (fn-9p-metadata-at 5 stat) 49))
       (equal (fn-9pst-reply-begin :directory-read 4 64 49 stat)
              '(:reply-unrepresentable nil))))
 :rule-classes nil)

; Mutation: fabricated completion position with un-emitted stat body.
(defthm n9pst-corrupt-completion-cursor-refuses-full-effect
 (let* ((stat (mv-nth 1 (fn-9pst-begin "a" '(128 0 7) 0)))
        (cursor (list :ninep-stat-reply :stat 3 stat 59 59))
        (buffer (fn-octets-from-list (make-list 59 :initial-element 0) (create-fn-octets))))
  (and (fn-9pst-ready-p stat) (equal (fn-octets-len buffer) 59)
       (not (equal (fn-9p-metadata-at 4 stat) 50))
       (equal (fn-9pst-reply-step cursor buffer)
              (list :recovery-required cursor buffer))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-octets-len fn-octets-from-list))))
