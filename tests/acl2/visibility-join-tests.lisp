; Teeth for books/visibility-join.lisp (NNT-019, PRF-115).  The Store below
; is built from `fn-sn-initial' by the I/O, prepare and finish transitions
; the host drives (host/store-node-host.lisp): a target T is accepted, then a
; cancel C naming it is accepted by `fn-sn-finish' -- the completion the
; withdrawal keystone is about.  C's withdrawal record is the one C3's
; refresh derives for a namespace grant over fn.test (constructed here the
; way tests/acl2/control-visible-tests.lisp constructs it), and T is absent
; from the visible list, so a fresh reader is answered 430.  Then T is
; reclaimed to its tombstone.  The owner of the served-reply keystone is
; tests/acl2/poster-bytes-tests.lisp's `*pbt-owner*'.
;
; Each keystone has a reachable witness asserting its antecedent and
; conclusion, and one must-fail per hypothesis: every retained hypothesis
; checked true, the omitted one false, the conclusion refuted by evaluation.
; The (stringp msgid) removals are corrupted-state witnesses (a Store never
; holds a non-string Message-ID) and are labelled so.
(in-package "ACL2")
(include-book "../../books/visibility-join")
(include-book "../../books/control-visible")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)
(include-book "poster-bytes-tests")

(defun vjt-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                 :frontier-file :ok)
                       :frontier-replace :ok)
            :frontier-directory :ok))
(defun vjt-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                       :record-link :ok)
            :record-directory :ok))

; The index of the acceptance state inside the node, found rather than named.
(defun vjt-index-of (x xs i)
  (declare (xargs :guard (natp i) :verify-guards nil))
  (if (consp xs)
      (if (equal (car xs) x) i (vjt-index-of x (cdr xs) (1+ i)))
    nil))

(defconst *vjt-groups* '("control.cancel" "fn.test"))
(defconst *vjt-t* "<vj-target@example.invalid>")
(defconst *vjt-c* "<vj-cancel@example.invalid>")
(defconst *vjt-absent* "<vj-absent@example.invalid>")
(defconst *vjt-crlf* '(13 10))
(defconst *vjt-t-payload*
  (append (fn-record-string-octets "Newsgroups: fn.test") *vjt-crlf*
          (fn-record-string-octets "Message-ID: <vj-target@example.invalid>")
          *vjt-crlf* *vjt-crlf* (fn-record-string-octets "lost reply") *vjt-crlf*))
(defconst *vjt-changed*
  (append (fn-record-string-octets "Newsgroups: fn.test") *vjt-crlf*
          (fn-record-string-octets "Message-ID: <vj-target@example.invalid>")
          *vjt-crlf* *vjt-crlf* (fn-record-string-octets "lost replY") *vjt-crlf*))
(defconst *vjt-c-payload*
  (append (fn-record-string-octets "Newsgroups: fn.test") *vjt-crlf*
          (fn-record-string-octets "Control: cancel <vj-target@example.invalid>")
          *vjt-crlf* *vjt-crlf* (fn-record-string-octets "cancel") *vjt-crlf*))

(defconst *vjt-t-record*
  (fn-record-make 0 0 0 *vjt-t* *vjt-t-payload* '("fn.test") "vj-pin-1"
                  "vj-subject" "vj-release" 2 841000000))
(defconst *vjt-c-record*
  (fn-record-make 1 1 1 *vjt-c* *vjt-c-payload* '("control.cancel") "vj-pin-2"
                  "vj-subject" "vj-release" 2 841000001))

(defconst *vjt-one*
  (fn-sn-finish (vjt-publish (fn-spc-prepare
                              (vjt-reserve (fn-sn-initial *vjt-groups* 10))
                              *vjt-t-record*))))
; S of the withdrawal keystone: C prepared and published, not yet completed.
(defconst *vjt-completing*
  (vjt-publish (fn-spc-prepare (vjt-reserve *vjt-one*) *vjt-c-record*)))
(defconst *vjt-two* (fn-sn-finish *vjt-completing*))

(assert-event (fn-sn-statep *vjt-two*))
(assert-event (equal (fn-article-msgids (fn-vj-articles *vjt-two*)) (list *vjt-c* *vjt-t*)))
(assert-event (fn-sn-completion-enabledp *vjt-completing*))

; C3: C withdraws T under a namespace grant over fn.test (T is unsigned).
(defconst *vjt-p* (make-list 32 :initial-element 17))
(defconst *vjt-p-hex* (fn-record-octets-string (fn-stx-hex-octets *vjt-p*)))
(defconst *vjt-verdicts* (list (cons *vjt-c* (fn-stx-make-verdict :verified *vjt-p* 1))))
(defconst *vjt-ws*
  (list (fn-ctl-withdrawal-make *vjt-t* *vjt-c* *vjt-p-hex* (list "fn.test") 1)))
(assert-event
 (let ((arts (fn-vj-articles *vjt-two*)))
   (and (fn-acceptedp *vjt-t* arts)
        (not (fn-acceptedp *vjt-t* (fn-ctl-visible-articles arts *vjt-ws* *vjt-verdicts*)))
        (fn-acceptedp *vjt-c* (fn-ctl-visible-articles arts *vjt-ws* *vjt-verdicts*))
        (fn-ctl-withdrawal-status *vjt-t* *vjt-ws* arts *vjt-verdicts*))))

; The buffer entry, run on a live local buffer as the host runs it.
(defun vjt-buffer-action (msgid payload groups s)
  (declare (xargs :guard (fn-cbor-octet-listp payload) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (let ((fn-octets (fn-octets-from-list payload fn-octets)))
        (mv (fn-rclb-existing-action msgid fn-octets groups s) fn-octets))
      r)))

; -----------------------------------------------------------------------------
; fn-vj-a-completion-keeps-a-held-message-id-answered.  Witness: T held
; before C's completion; after it (T withdrawn) the same source is
; :duplicate and a changed one :conflict on both entries.
(assert-event (and (stringp *vjt-t*) (fn-acceptedp *vjt-t* (fn-vj-articles *vjt-completing*))))
(assert-event
 (and (equal (fn-rcl-existing-action *vjt-t* *vjt-t-payload* '("fn.test") *vjt-two*) :duplicate)
      (equal (vjt-buffer-action *vjt-t* *vjt-t-payload* '("fn.test") *vjt-two*) :duplicate)
      (equal (fn-rcl-existing-action *vjt-t* *vjt-changed* '("fn.test") *vjt-two*) :conflict)
      (equal (vjt-buffer-action *vjt-t* *vjt-changed* '("fn.test") *vjt-two*) :conflict)))
; Teeth (1): drop "held": a Message-ID not held before is not held after,
; and the decision answers nil (a fresh prepare).
(assert-event (and (stringp *vjt-absent*)
                   (not (fn-acceptedp *vjt-absent* (fn-vj-articles *vjt-completing*)))))
(must-fail
 (assert-event (member-equal (vjt-buffer-action *vjt-absent* *vjt-t-payload* '("fn.test")
                                                *vjt-two*)
                             '(:duplicate :conflict))))
; Teeth (2), corrupted state: drop (stringp msgid).  A Store whose article
; list starts with a non-article holds the Message-ID nil; the lookup stops
; at the non-article and the decision answers nil.
(defconst *vjt-corrupt*
  (let* ((node (fn-sn-node *vjt-completing*))
         (acc (fn-node-acceptance node))
         (acc2 (fn-make-state (fn-state-groups acc) (fn-state-nexts acc)
                              (cons nil (fn-state-articles acc))
                              (fn-state-next-txid acc) (fn-state-pending acc)
                              (fn-state-fenced acc))))
    (update-nth 3 (update-nth (vjt-index-of acc node 0) acc2 node) *vjt-completing*)))
(assert-event (and (not (stringp nil)) (fn-acceptedp nil (fn-vj-articles *vjt-corrupt*))))
(must-fail
 (assert-event (member-equal (fn-rcl-existing-action nil *vjt-t-payload* '("fn.test")
                                                     (fn-sn-finish *vjt-corrupt*))
                             '(:duplicate :conflict))))

; -----------------------------------------------------------------------------
; fn-vj-reclamation-keeps-a-held-message-id-answered.  T, withdrawn, is
; reclaimed to its tombstone; the resend of its source is still :duplicate
; (the tombstone's digest), a changed source :conflict.
(defconst *vjt-acc* (fn-node-acceptance (fn-sn-node *vjt-two*)))
(defconst *vjt-tomb* (fn-rcl-tombstone-of *vjt-t-payload* (fn-record-string-octets *vjt-t*)))
(defconst *vjt-reclaimed*
  (let ((node (fn-sn-node *vjt-two*)))
    (update-nth 3 (update-nth (vjt-index-of *vjt-acc* node 0)
                              (fn-rcl-reclaim-state *vjt-acc* *vjt-t* *vjt-tomb*) node)
                *vjt-two*)))
(assert-event
 (and (stringp *vjt-t*)
      (fn-acceptedp *vjt-t* (fn-state-articles *vjt-acc*))
      (equal (fn-vj-articles *vjt-reclaimed*)
             (fn-state-articles (fn-rcl-reclaim-state *vjt-acc* *vjt-t* *vjt-tomb*)))
      (fn-rcl-tombstonep (fn-article-payload
                          (fn-find-article *vjt-t* (fn-vj-articles *vjt-reclaimed*))))))
(assert-event
 (and (equal (fn-rcl-existing-action *vjt-t* *vjt-t-payload* '("fn.test") *vjt-reclaimed*)
             :duplicate)
      (equal (vjt-buffer-action *vjt-t* *vjt-t-payload* '("fn.test") *vjt-reclaimed*)
             :duplicate)
      (equal (vjt-buffer-action *vjt-t* *vjt-changed* '("fn.test") *vjt-reclaimed*)
             :conflict)))
; Teeth (1): drop "held".
(assert-event (not (fn-acceptedp *vjt-absent* (fn-state-articles *vjt-acc*))))
(must-fail
 (assert-event (member-equal (vjt-buffer-action *vjt-absent* *vjt-t-payload* '("fn.test")
                                                *vjt-reclaimed*)
                             '(:duplicate :conflict))))
; Teeth (2): drop "S2 is the reclaimed Store": the initial Store holds nothing.
(defconst *vjt-empty* (fn-sn-initial *vjt-groups* 10))
(assert-event (not (equal (fn-vj-articles *vjt-empty*)
                          (fn-state-articles (fn-rcl-reclaim-state *vjt-acc* *vjt-t*
                                                                   *vjt-tomb*)))))
(must-fail
 (assert-event (member-equal (vjt-buffer-action *vjt-t* *vjt-t-payload* '("fn.test")
                                                *vjt-empty*)
                             '(:duplicate :conflict))))
; Teeth (3), corrupted state: drop (stringp msgid).
(defconst *vjt-corrupt-acc*
  (fn-make-state (fn-state-groups *vjt-acc*) (fn-state-nexts *vjt-acc*)
                 (cons nil (fn-state-articles *vjt-acc*))
                 (fn-state-next-txid *vjt-acc*) (fn-state-pending *vjt-acc*)
                 (fn-state-fenced *vjt-acc*)))
(defconst *vjt-corrupt-reclaimed*
  (let ((node (fn-sn-node *vjt-two*)))
    (update-nth 3 (update-nth (vjt-index-of *vjt-acc* node 0)
                              (fn-rcl-reclaim-state *vjt-corrupt-acc* *vjt-t* *vjt-tomb*)
                              node)
                *vjt-two*)))
(assert-event (and (fn-acceptedp nil (fn-state-articles *vjt-corrupt-acc*))
                   (equal (fn-vj-articles *vjt-corrupt-reclaimed*)
                          (fn-state-articles (fn-rcl-reclaim-state *vjt-corrupt-acc*
                                                                   *vjt-t* *vjt-tomb*)))))
(must-fail
 (assert-event (member-equal (fn-rcl-existing-action nil *vjt-t-payload* '("fn.test")
                                                     *vjt-corrupt-reclaimed*)
                             '(:duplicate :conflict))))

; -----------------------------------------------------------------------------
; fn-vj-a-held-message-id-is-answered-441, on the owner of poster-bytes-tests
; (connection 0 in flight, nothing consumed) over the withdrawn Store and
; over the reclaimed one.
(defun vjt-reply (o id msgid payload s)
  (car (fn-own-outcome o id (vjt-buffer-action msgid payload '("fn.test") s))))
(defconst *vjt-441*
  (list (fn-pb-served-reply *pbt-owner* 0 :duplicate)
        (fn-pb-served-reply *pbt-owner* 0 :conflict)))
(assert-event (equal *vjt-441* (list *pbt-duplicate-line* *pbt-conflict-line*)))
(assert-event
 (and (fn-own-find-conn 0 (fn-own-conns *pbt-owner*))
      (fn-own-inflight *pbt-owner*)
      (equal (fn-own-sub-id (fn-own-inflight *pbt-owner*)) 0)
      (not (fn-own-completion-consumedp *pbt-owner*))))
(assert-event
 (and (equal (vjt-reply *pbt-owner* 0 *vjt-t* *vjt-t-payload* *vjt-two*) *pbt-duplicate-line*)
      (equal (vjt-reply *pbt-owner* 0 *vjt-t* *vjt-changed* *vjt-two*) *pbt-conflict-line*)
      (equal (vjt-reply *pbt-owner* 0 *vjt-t* *vjt-t-payload* *vjt-reclaimed*)
             *pbt-duplicate-line*)))
(defmacro vjt-441-fails (o id msgid s)
  `(must-fail
    (assert-event
     (member-equal (vjt-reply ,o ,id ,msgid *vjt-t-payload* ,s)
                   (list (fn-pb-served-reply ,o ,id :duplicate)
                         (fn-pb-served-reply ,o ,id :conflict))))))
; Teeth, one per hypothesis.
; (1) no connection with that id.
(assert-event (not (fn-own-find-conn 7 (fn-own-conns *pbt-owner*))))
(vjt-441-fails *pbt-owner* 7 *vjt-t* *vjt-two*)
; (2) nothing in flight.
(defconst *vjt-idle*
  (fn-own-make nil nil (list *pbt-conn*) 1 4 nil nil *pbt-b* nil *pbt-config* nil nil nil))
(assert-event (and (fn-own-find-conn 0 (fn-own-conns *vjt-idle*))
                   (not (fn-own-inflight *vjt-idle*))))
(vjt-441-fails *vjt-idle* 0 *vjt-t* *vjt-two*)
; (3) the in-flight submission is another connection's.
(assert-event (not (equal (fn-own-sub-id (fn-own-inflight (pbt-owner 3 nil))) 0)))
(vjt-441-fails (pbt-owner 3 nil) 0 *vjt-t* *vjt-two*)
; (4) a completion was consumed.
(assert-event (fn-own-completion-consumedp *pbt-consumed*))
(vjt-441-fails *pbt-consumed* 0 *vjt-t* *vjt-two*)
; (5), corrupted state: a non-string Message-ID.
(vjt-441-fails *pbt-owner* 0 nil *vjt-corrupt*)
; (6) the Message-ID is not held.
(vjt-441-fails *pbt-owner* 0 *vjt-absent* *vjt-two*)
