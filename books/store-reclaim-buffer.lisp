; fn: the tombstone-aware duplicate-versus-conflict verdict over the octet
; buffer (STO-014, PRF-088, D27).
;
; The native owner asks the D25 question with the submitted payload in the
; octet buffer (host/owner-host.lisp fn-owner-existing-action-buffer, called
; from host/native/owner.lisp fnn-owner-attempt; its verdict is
; books/post-identity-index.lisp fn-pidx-existing-action).  Once `store
; reclaim' can leave a tombstone in the article list, the comparison must be
; `fn-rcl-same-articlep' (books/store-reclaim), not `fn-pb-same-articlep'.
; This book is its buffer twin, `fn-rclb-same-articlep'.
;
; A live held payload is compared in place exactly as
; `fn-pbb-same-articlep' does.  A held tombstone is compared by digest.
; The whole submission is digested in place (`fn-sha256-of-prefixed-buffer',
; books/sha256-buffer, with the empty prefix).  When the tombstone kept a D25
; source under the submission's own agent, the submission's source is D32's
; description (K A B) (books/poster-bytes-buffer `fn-pbb-source-index'): the
; octets st[K..A) then st[B..).  Those two ranges are sliced into one list
; the size of the source and hashed by `fn-sha256-stobj'; that list is built
; only on the resend-of-a-reclaimed-article path (a two-range buffer digest
; reader would remove it; recorded as open in the record).  The live path
; conses nothing new.
;
; Keystone: `fn-rclb-same-articlep-is-rcl-same-articlep', over the buffer's
; logical value, with the stobj recognizer as the only hypothesis.
(in-package "ACL2")
(include-book "store-reclaim")
(include-book "poster-bytes-buffer")
(include-book "sha256-stobj")
(include-book "sha256-buffer")

(defun fn-rclb-desc-digest (d fn-octets)
  ; SHA-256 of the octets the description D names in the buffer.
  (declare (xargs :stobjs fn-octets
                  :guard (fn-pbb-descp d (fn-octets-len fn-octets))))
  (fn-sha256-stobj
   (append (fn-oct-slice-list (car d) (cadr d) fn-octets)
           (fn-oct-slice-list (caddr d) (fn-octets-len fn-octets) fn-octets))))

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

(defthm fn-rclb-desc-digest-is-sha256-of-desc-list
  (implies (and (true-listp fn-octets) (fn-pbb-descp d (len fn-octets)))
           (equal (fn-rclb-desc-digest d fn-octets)
                  (fn-sha256 (fn-pbb-desc-list d fn-octets))))
  :hints (("Goal" :in-theory (enable fn-octets-len))))

(defun fn-rclb-same-as-tombstonep (msgid fn-octets tomb)
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints
                  (("Goal" :use ((:instance fn-pbb-source-index-bounds
                                            (agent (fn-pbb-path-agent msgid fn-octets))))
                    :in-theory (enable fn-octets-len)))))
  (let* ((agent (fn-pbb-path-agent msgid fn-octets))
         (d (fn-pbb-source-index agent msgid fn-octets)))
    (if (and (fn-rcl-tomb-sourcep tomb)
             (equal agent (fn-rcl-tomb-agent tomb))
             d)
        (equal (fn-rclb-desc-digest d fn-octets)
               (fn-rcl-tomb-source-digest tomb))
      (equal (fn-sha256-of-prefixed-buffer nil fn-octets)
             (fn-rcl-tomb-octets-digest tomb)))))

(defun fn-rclb-same-articlep (msgid fn-octets held-payload)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (fn-rcl-tombstonep held-payload)
      (fn-rclb-same-as-tombstonep msgid fn-octets held-payload)
    (fn-pbb-same-articlep msgid fn-octets held-payload)))

(defthm fn-rclb-same-as-tombstonep-is-rcl
  (implies (fn-octets-p fn-octets)
           (equal (fn-rclb-same-as-tombstonep msgid fn-octets tomb)
                  (fn-rcl-same-as-tombstonep msgid fn-octets tomb)))
  :hints (("Goal" :use (fn-rclb-octets-true-listp
                        fn-pbb-path-agent-is-pb-path-agent
                        (:instance fn-pbb-source-index-is-inj-source-of
                                   (agent (fn-pb-path-agent fn-octets msgid)))
                        (:instance fn-pbb-source-index-bounds
                                   (agent (fn-pb-path-agent fn-octets msgid)))
                        (:instance fn-sha256-of-prefixed-buffer-is-sha256 (prefix nil)))
                  :in-theory (e/d (fn-pb-subject)
                                  (fn-sha256 fn-rcl-tomb-sourcep fn-rcl-tomb-agent
                                   fn-pb-path-agent fn-inj-source-of fn-octets-p
                                   fn-pbb-path-agent-is-pb-path-agent
                                   fn-pbb-source-index-is-inj-source-of
                                   fn-pbb-source-index-bounds
                                   fn-sha256-of-prefixed-buffer-is-sha256
                                   fn-pbb-source-index fn-pbb-desc-list
                                   fn-sha256-of-prefixed-buffer fn-pbb-descp
                                   fn-rclb-desc-digest
                                   fn-rcl-tomb-source-digest fn-rcl-tomb-octets-digest)))))

;  KEYSTONE (the buffer comparison).  On the buffer's logical value the
; tombstone-aware buffer comparison is books/store-reclaim's list one.  The
; host's buffer verdict, books/post-identity-index.lisp
; fn-pidx-existing-action (host/owner-host.lisp
; fn-owner-existing-action-buffer, fn-owner-prepare-buffer), compares with
; fn-rclb-same-articlep against the bytes read through the arena, and
; fn-pidx-existing-action-is-store-existing-action equates it with the
; Store's entry fn-store-existing-action.  (The whole-store buffer verdict
; fn-rclb-existing-action compared with the held handle and was retired,
; PKT-EG-4.)
(defthm fn-rclb-same-articlep-is-rcl-same-articlep
  (implies (fn-octets-p fn-octets)
           (equal (fn-rclb-same-articlep msgid fn-octets held-payload)
                  (fn-rcl-same-articlep msgid fn-octets held-payload)))
  :hints (("Goal" :in-theory (e/d (fn-rclb-same-articlep fn-rcl-same-articlep)
                                  (fn-rclb-same-as-tombstonep fn-rcl-same-as-tombstonep
                                   fn-rcl-tombstonep fn-pbb-same-articlep fn-pb-same-articlep
                                   fn-octets-p))
           :use ((:instance fn-pbb-same-articlep-is-pb-same-articlep)
                 (:instance fn-rclb-same-as-tombstonep-is-rcl (tomb held-payload))
                 fn-rclb-octets-true-listp))))

(in-theory (disable fn-rclb-same-articlep
                    fn-rclb-same-as-tombstonep fn-rclb-desc-digest))
