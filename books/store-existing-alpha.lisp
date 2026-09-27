; fn: the duplicate-post checks over the arena (records-flip; D25; PKT-635).
;
; Since the flip the acceptance articles hold HANDLES (books/store-intern.lisp):
; fn-sn-existing-action (books/store-node.lisp, the byte-identity decision)
; and fn-pb-existing-action (books/poster-bytes.lisp, D25's source-keyed
; decision) compare the offered octets with the handle when applied to the
; live store, so a true resend is a :conflict and their keystones speak of a
; store the flipped node never holds.  They remain the SPECIFICATION over
; the wire view: this book reads each over ALPHA of the acceptance articles
; (fn-articles-wire-of: every handle replaced by the bytes under it) and
; relates it to the entry the host calls, fn-store-existing-action
; (host/store-node-host.lisp fn-store-sn-existing-action and
; fn-store-sn-prepare; host/owner-host.lisp fn-owner-prepare and
; fn-owner-existing-action-buffer through fn-pidx-existing-action).
;
;   fn-sn-action-over / fn-pb-action-over    the two decisions over an article
;                                            list; the store forms are them over
;                                            the store's articles (-by-definition).
; KEYSTONES (subject fn-store-existing-action):
;   fn-store-existing-action-is-pb-over-alpha
;       where the held bytes are no tombstone, the entry's verdict is D25's
;       source-keyed decision over alpha;
;   fn-store-existing-action-refines-byte-identity-over-alpha
;       the entry answers for exactly the Message-IDs the store holds, and a
;       byte-identical resend (the bytes under the held handle, same groups)
;       is :duplicate.
; Teeth: tests/acl2/store-existing-alpha-tests.lisp.
(in-package "ACL2")
(include-book "store-intern")
(include-book "store-node-existing-invariants")

; -----------------------------------------------------------------------------
; The two decisions over an article list.

(fn-payload-kind fn-sn-action-over :wire "the verdict over alpha (octet articles)")
(defun fn-sn-action-over (msgid payload groups articles)
  (declare (xargs :guard t))
  (let ((article (fn-find-article msgid articles)))
    (if article
        (if (and (equal payload (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

(fn-payload-kind fn-pb-action-over :wire "the verdict over alpha (octet articles)")
(defun fn-pb-action-over (msgid payload groups articles)
  (declare (xargs :guard t))
  (let ((article (fn-find-article msgid articles)))
    (if article
        (if (and (fn-pb-same-articlep (fn-record-string-octets msgid) payload
                                      (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

(defthm fn-sn-existing-action-is-action-over-by-definition
  (equal (fn-sn-existing-action msgid payload groups s)
         (fn-sn-action-over msgid payload groups
                            (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
  :hints (("Goal" :in-theory (enable fn-sn-existing-action))))

(defthm fn-pb-existing-action-is-action-over-by-definition
  (equal (fn-pb-existing-action msgid payload groups s)
         (fn-pb-action-over msgid payload groups
                            (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
  :hints (("Goal" :in-theory (enable fn-pb-existing-action))))

; ALPHA of the store's acceptance articles.
(defun fn-sn-alpha-articles (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-articles-wire-of (fn-state-articles (fn-node-acceptance (fn-sn-node s))) fn-arena))

(local (defthm fn-sea-find-article-of-articles-wire-of
  (implies (stringp msgid)
           (equal (fn-find-article msgid (fn-articles-wire-of articles fn-arena))
                  (let ((a (fn-find-article msgid articles)))
                    (and a
                         (fn-make-article (fn-article-msgid a)
                                          (fn-handle-bytes (fn-article-payload a) fn-arena)
                                          (fn-article-groups a) (fn-article-memberships a)
                                          (fn-article-pin a) (fn-article-stamp a))))))
  :hints (("Goal" :in-theory (e/d (fn-find-article fn-articles-wire-of) (fn-handle-bytes))))))

; -----------------------------------------------------------------------------
; KEYSTONE.  Where the bytes under the held handle are no tombstone (nothing
; was reclaimed under this Message-ID), the entry's verdict is D25's
; source-keyed decision over alpha: the answer fn-pb-existing-action gave
; when the store retained the bytes themselves.  The Message-ID is a string
; (the host passes the parsed header's).
(defthm fn-store-existing-action-is-pb-over-alpha
  (implies (and (stringp msgid)
                (not (fn-rcl-tombstonep
                      (fn-handle-bytes
                       (fn-article-payload
                        (fn-find-article msgid (fn-state-articles
                                                (fn-node-acceptance (fn-sn-node s)))))
                       fn-arena))))
           (equal (fn-store-existing-action msgid payload groups s fn-arena)
                  (fn-pb-action-over msgid payload groups
                                     (fn-sn-alpha-articles s fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-store-existing-action fn-rcl-same-articlep)
                                  (fn-handle-bytes fn-pb-same-articlep
                                   fn-rcl-same-as-tombstonep)))))

; KEYSTONE.  The entry answers for exactly the Message-IDs the store holds
; (the byte-identity decision over alpha is non-nil at the same ones), and,
; where the held bytes are no tombstone, a resend whose octets are the bytes
; under the held handle with the same groups is :duplicate.  (A tombstone's
; resend is decided by digest, fn-rcl-same-as-tombstonep: store-reclaim.)
(defthm fn-store-existing-action-refines-byte-identity-over-alpha
  (implies (stringp msgid)
           (and (iff (fn-store-existing-action msgid payload groups s fn-arena)
                     (fn-sn-action-over msgid payload groups
                                        (fn-sn-alpha-articles s fn-arena)))
                (implies (and (not (fn-rcl-tombstonep
                                    (fn-handle-bytes
                                     (fn-article-payload
                                      (fn-find-article msgid (fn-state-articles
                                                              (fn-node-acceptance (fn-sn-node s)))))
                                     fn-arena)))
                              (equal (fn-sn-action-over msgid payload groups
                                                        (fn-sn-alpha-articles s fn-arena))
                                     :duplicate))
                         (equal (fn-store-existing-action msgid payload groups s fn-arena)
                                :duplicate))))
  :hints (("Goal" :in-theory (e/d (fn-store-existing-action fn-rcl-same-articlep
                                   fn-pb-same-articlep)
                                  (fn-handle-bytes)))))

(in-theory (disable fn-sn-action-over fn-pb-action-over fn-sn-alpha-articles))
