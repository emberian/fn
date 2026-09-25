; fn: witnesses and teeth for books/store-reclaim-buffer.lisp (D13, STO-014,
; PRF-088): the tombstone-aware duplicate-versus-conflict verdict the native
; owner asks with the submission in the octet buffer
; (host/owner-host.lisp fn-owner-existing-action-buffer, fn-owner-prepare-buffer).
;
; The store is the owner fixture of octets-stobj-tests with its one held
; article reclaimed: its payload replaced by `fn-rcl-tombstone-of'.  The
; exec path runs on a live local buffer, the way the host runs it.
(in-package "ACL2")
(include-book "../../books/store-reclaim-buffer")
(include-book "std/testing/must-fail" :dir :system)
(include-book "octets-stobj-tests")

(defconst *rbt-mo* (fn-record-string-octets *ost-msgid*))
(defconst *rbt-tomb* (fn-rcl-tombstone-of *ost-held* *rbt-mo*))
(assert-event (and (fn-rcl-tombstonep *rbt-tomb*) (fn-rcl-tomb-sourcep *rbt-tomb*)))

; The owner store with the article reclaimed.  The acceptance state sits at
; some index of the node; find it rather than name the layout, then check
; the accessors read the reclaimed state back.
(defun rbt-index-of (x xs i)
  (declare (xargs :guard (natp i) :verify-guards nil))
  (if (consp xs)
      (if (equal (car xs) x) i (rbt-index-of x (cdr xs) (1+ i)))
    nil))
(defconst *rbt-node* (fn-sn-node *ost-s*))
(defconst *rbt-acc* (fn-node-acceptance *rbt-node*))
(defconst *rbt-k* (rbt-index-of *rbt-acc* *rbt-node* 0))
(assert-event (natp *rbt-k*))
(defconst *rbt-acc2* (fn-rcl-reclaim-state *rbt-acc* *ost-msgid* *rbt-tomb*))
(defconst *rbt-s*
  (update-nth 3 (update-nth *rbt-k* *rbt-acc2* *rbt-node*) *ost-s*))
(assert-event
 (and (equal (fn-node-acceptance (fn-sn-node *rbt-s*)) *rbt-acc2*)
      (equal (fn-article-payload
              (fn-find-article *ost-msgid*
                               (fn-state-articles (fn-node-acceptance (fn-sn-node *rbt-s*)))))
             *rbt-tomb*)))

(defun rbt-existing-action (msgid payload groups s)
  (declare (xargs :guard (fn-cbor-octet-listp payload) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (let ((fn-octets (fn-octets-from-list payload fn-octets)))
        (mv (fn-rclb-existing-action msgid fn-octets groups s) fn-octets))
      r)))

; The keystone fn-rclb-existing-action-is-rcl-existing-action, both sides,
; on the reclaimed store: the same octets resent, the same source
; re-injected (the source-digest arm), a changed body, other groups, an
; unknown Message-ID.
(assert-event
 (and (equal (fn-rcl-existing-action *ost-msgid* *ost-held* *ost-groups* *rbt-s*) :duplicate)
      (equal (rbt-existing-action *ost-msgid* *ost-held* *ost-groups* *rbt-s*) :duplicate)
      (equal (fn-rcl-existing-action *ost-msgid* *ost-reinjected* *ost-groups* *rbt-s*)
             :duplicate)
      (equal (rbt-existing-action *ost-msgid* *ost-reinjected* *ost-groups* *rbt-s*)
             :duplicate)
      (equal (fn-rcl-existing-action *ost-msgid* *ost-changed* *ost-groups* *rbt-s*) :conflict)
      (equal (rbt-existing-action *ost-msgid* *ost-changed* *ost-groups* *rbt-s*) :conflict)
      (equal (rbt-existing-action *ost-msgid* *ost-held* (cons "fn.other" *ost-groups*)
                                  *rbt-s*)
             :conflict)
      (equal (rbt-existing-action "<ost-absent@example.invalid>" *ost-held* *ost-groups*
                                  *rbt-s*)
             nil)))

; Why the switch matters: on the reclaimed store the old buffer call calls
; a resend of the reclaimed article a conflict.
(assert-event
 (equal (ost-existing-action *ost-msgid* *ost-held* *ost-groups* *rbt-s*) :conflict))
; And on the live store the new call is the old one.
(assert-event
 (and (equal (rbt-existing-action *ost-msgid* *ost-held* *ost-groups* *ost-s*) :duplicate)
      (equal (rbt-existing-action *ost-msgid* *ost-changed* *ost-groups* *ost-s*) :conflict)))

; The keystone's one hypothesis, (fn-octets-p fn-octets): the held octets
; with an improper tail.  The buffer reads to its length and digests the
; held octets (:duplicate); the list test digests the improper value.
(defconst *rbt-improper* (append *ost-held* 3))
(assert-event (not (fn-octets-p *rbt-improper*)))
(defthm rbt-t-improper-buffer-reads-to-its-length
  (equal (fn-rclb-existing-action *ost-msgid* *rbt-improper* *ost-groups* *rbt-s*)
         :duplicate)
  :rule-classes nil)
(must-fail
 (defthm rbt-t-existing-action-without-octets-p
   (equal (fn-rclb-existing-action *ost-msgid* *rbt-improper* *ost-groups* *rbt-s*)
          (fn-rcl-existing-action *ost-msgid* *rbt-improper* *ost-groups* *rbt-s*))))
