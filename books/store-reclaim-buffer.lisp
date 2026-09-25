; fn: the tombstone-aware duplicate-versus-conflict verdict over the octet
; buffer (STO-014, PRF-088, D27).
;
; The native owner asks the D25 question with the submitted payload in the
; octet buffer (host/owner-host.lisp fn-owner-existing-action-buffer, called
; from host/native/owner.lisp fnn-owner-attempt).  Once `store reclaim' can
; leave a tombstone in the article list, that question must be
; `fn-rcl-existing-action' (books/store-reclaim), not
; `fn-pb-existing-action'.  This book is its buffer twin.
;
; A live held payload is compared in place exactly as
; `fn-pbb-existing-action' does.  A held tombstone is compared by digest:
; the submission's octets (or, when the tombstone kept a D25 source under
; the submission's own agent, the submission's source) are sliced out of
; the buffer once and hashed by `fn-sha256-stobj'.  That slice is one list
; the size of the submission, built only on the resend-of-a-reclaimed-
; article path; the live path conses nothing new.
;
; Keystone: `fn-rclb-existing-action-is-rcl-existing-action', over the
; buffer's logical value, with the stobj recognizer as the only hypothesis.
(in-package "ACL2")
(include-book "store-reclaim")
(include-book "poster-bytes-buffer")
(include-book "sha256-stobj")

(defun fn-rclb-same-as-tombstonep (msgid fn-octets tomb)
  (declare (xargs :stobjs fn-octets :guard t))
  (let* ((agent (fn-pbb-path-agent fn-octets))
         (a (fn-pbb-source-index agent msgid fn-octets)))
    (if (and (fn-rcl-tomb-sourcep tomb)
             (equal agent (fn-rcl-tomb-agent tomb))
             a)
        (equal (fn-sha256-stobj
                (fn-oct-slice-list a (fn-octets-len fn-octets) fn-octets))
               (fn-rcl-tomb-source-digest tomb))
      (equal (fn-sha256-stobj
              (fn-oct-slice-list 0 (fn-octets-len fn-octets) fn-octets))
             (fn-rcl-tomb-octets-digest tomb)))))

(defun fn-rclb-same-articlep (msgid fn-octets held-payload)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (fn-rcl-tombstonep held-payload)
      (fn-rclb-same-as-tombstonep msgid fn-octets held-payload)
    (fn-pbb-same-articlep msgid fn-octets held-payload)))

(defun fn-rclb-existing-action (msgid fn-octets groups s)
  ; `fn-rcl-existing-action' with the submitted payload in the buffer.
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((article (fn-find-article
                  msgid (fn-state-articles
                         (fn-node-acceptance (fn-sn-node s))))))
    (if article
        (if (and (fn-rclb-same-articlep (fn-record-string-octets msgid) fn-octets
                                        (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

(local
 (defthm fn-rclb-octets-true-listp
   (implies (fn-octets-p fn-octets) (true-listp fn-octets))
   :hints (("Goal" :in-theory (enable fn-octets-p)))))

(local
 (defthm fn-rclb-take-all
   (implies (true-listp x) (equal (take (len x) x) x))))

(local
 (defthm fn-rclb-take-len-nthcdr
   (implies (and (true-listp x) (natp i) (<= i (len x)))
            (equal (take (- (len x) i) (nthcdr i x)) (nthcdr i x)))))

(defthm fn-rclb-same-as-tombstonep-is-rcl
  (implies (fn-octets-p fn-octets)
           (equal (fn-rclb-same-as-tombstonep msgid fn-octets tomb)
                  (fn-rcl-same-as-tombstonep msgid fn-octets tomb)))
  :hints (("Goal" :use (fn-rclb-octets-true-listp
                        fn-pbb-path-agent-is-pb-path-agent)
                  :in-theory (e/d (fn-pb-subject fn-octets-len)
                                  (fn-sha256 fn-rcl-tomb-sourcep fn-rcl-tomb-agent
                                   fn-pb-path-agent fn-inj-source-of fn-octets-p
                                   fn-pbb-path-agent-is-pb-path-agent
                                   fn-rcl-tomb-source-digest fn-rcl-tomb-octets-digest)))))

;  KEYSTONE (the buffer twin).  On the buffer's logical value the host's
; buffer call is the tombstone-aware verdict of books/store-reclaim.
(defthm fn-rclb-existing-action-is-rcl-existing-action
  (implies (fn-octets-p fn-octets)
           (equal (fn-rclb-existing-action msgid fn-octets groups s)
                  (fn-rcl-existing-action msgid fn-octets groups s)))
  :hints (("Goal" :in-theory (e/d (fn-rcl-existing-action)
                                  (fn-rclb-same-as-tombstonep fn-rcl-same-as-tombstonep
                                   fn-rcl-tombstonep)))))

(in-theory (disable fn-rclb-existing-action fn-rclb-same-articlep
                    fn-rclb-same-as-tombstonep))
