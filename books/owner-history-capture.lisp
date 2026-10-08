; Capture metadata under O; realize its pinned resident prefix outside O.
(in-package "ACL2")
(include-book "owner-state-accessors")
(include-book "state-globals")
(include-book "owner-checkpoint-writer")
(include-book "owner-publication-lifecycle")
(include-book "owner-reclaim")
(include-book "store-reclaim-owner-holders")
(include-book "store-genesis")
(include-book "history-columns-relation")
(include-book "owner-retain-transitions")


(defun fn-owner-store-profile (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-store-profile state)
      (f-get-global 'fn-owner-store-profile state)
    nil))

(defun fn-owner-sco-budget (override profile)
  (declare (xargs :guard t))
  (if (natp override) override (fn-ock-capture-budget profile)))

(defun fn-hsc-complete-capture (kind captured records)
 (declare (xargs :guard t))
 (if (and (eq kind :reclaim) (consp captured) (eq (car captured) :refused))
     captured
   (ec-call (update-nth (if (eq kind :checkpoint) 2 0) records captured))))
(in-theory (disable fn-hsc-complete-capture))

(defun fn-owner-sco-capture-of (records override free revision state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state) :verify-guards nil))
  (let* ((st (fn-own-store (fn-owner-core state)))
         ; (len records), the snoc-list's carried count:
         ; fn-sf-records-count-is-used-by-definition.
         (count (fn-sf-records-count (fn-sn-files st)))
         (durable (fn-owner-sco-global 'fn-owner-sco-durable state))
         (profile (fn-owner-store-profile state))
         (state (f-put-global 'fn-owner-sco-attempted count state))
         ; the publication in flight, bound to the count it captures
         (state (f-put-global 'fn-owner-sco-inflight count state))
         ; RL-02: the capture's identity, its serial
         ; (books/owner-publication-lifecycle.lisp fn-opl-next-serial): the
         ; count alone is not one (a :backoff retry recaptures it)
         (serial (fn-opl-next-serial (fn-owner-sco-global 'fn-owner-sco-serial state)))
         (state (f-put-global 'fn-owner-sco-serial serial state))
         ; PKT-868: the capture answers a standing request.
         (state (f-put-global 'fn-owner-sco-requested nil state)))
    (value (list (fn-owner-sco-global 'fn-owner-sco-base state)
                 (fn-sn-config-history st)
                 records
                 (fn-bs-profile-max-record-octets profile)
                 count
                 (- count (if (natp durable) durable 0))
                 (fn-owner-sco-budget override profile)
                 (fn-sf-frontier (fn-sn-files st))
                 free
                 revision
                 (fn-owner-sco-global 'fn-owner-sco-base-payloads state)
                 ; the store's identity for the history image's binding
                 ; (books/history-image-binding.lisp): the genesis record's
                 ; node identity and the history salt
                 (let ((v (and (boundp-global 'fn-store-genesis state)
                               (f-get-global 'fn-store-genesis state))))
                   (list (if (and (consp v) (equal (car v) :genesis) (consp (cdr v)))
                             (fn-gen-node (cadr v))
                           nil)
                         (fn-gen-verdict-salt v)))
                 ; RL-02: the serial the settlement of an abandonment names
                 ; (fn-owner-sco-publication-abandoned)
                 serial))))

(verify-guards fn-owner-sco-capture-of)

(defun fn-owner-sco-capture (override free revision state)
 (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
 (fn-owner-sco-capture-of (fn-sf-records (fn-sn-files (fn-owner-store state))) override free revision state))
(defun fn-owner-sco-capture-served (override free revision state)
 (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
 (fn-owner-sco-capture-of nil override free revision state))
(defthm fn-owner-sco-capture-served-is-reference
 (implies (fn-hist-of-storep records (fn-owner-store st))
  (and (equal (fn-hsc-complete-capture ':checkpoint
                (mv-nth 1 (fn-owner-sco-capture-served override free revision st)) records)
              (mv-nth 1 (fn-owner-sco-capture override free revision st)))
       (equal (mv-nth 2 (fn-owner-sco-capture-served override free revision st))
              (mv-nth 2 (fn-owner-sco-capture override free revision st)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-owner-sco-capture-served fn-owner-sco-capture fn-owner-sco-capture-of fn-hsc-complete-capture
     fn-hist-of-storep fn-owner-store update-nth nth zp car-cons cdr-cons)))))
(in-theory (disable fn-owner-sco-capture-served fn-owner-sco-capture fn-owner-sco-capture-of))

(defun fn-owner-oex-capture-of (records state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state) :verify-guards nil))
  (let* ((st (fn-own-store (fn-owner-core state)))
         (files (fn-sn-files st)))
    (value (list records
                 (fn-sf-records-count files)
                 (fn-sn-config-history st)
                 (fn-sf-frontier files)))))

(verify-guards fn-owner-oex-capture-of)

(defun fn-owner-oex-capture ( state)
 (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
 (fn-owner-oex-capture-of (fn-sf-records (fn-sn-files (fn-owner-store state)))  state))
(defun fn-owner-oex-capture-served ( state)
 (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
 (fn-owner-oex-capture-of nil  state))
(defthm fn-owner-oex-capture-served-is-reference
 (implies (fn-hist-of-storep records (fn-owner-store st))
  (and (equal (fn-hsc-complete-capture ':export
                (mv-nth 1 (fn-owner-oex-capture-served  st)) records)
              (mv-nth 1 (fn-owner-oex-capture  st)))
       (equal (mv-nth 2 (fn-owner-oex-capture-served  st))
              (mv-nth 2 (fn-owner-oex-capture  st)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-owner-oex-capture-served fn-owner-oex-capture fn-owner-oex-capture-of fn-hsc-complete-capture
     fn-hist-of-storep fn-owner-store update-nth nth zp car-cons cdr-cons)))))
(in-theory (disable fn-owner-oex-capture-served fn-owner-oex-capture fn-owner-oex-capture-of))

(defun fn-owner-orc-capture-of (records mode clock override free revision state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state) :verify-guards nil))
  (let* ((st (fn-own-store (fn-owner-core state)))
         (count (fn-sf-records-count (fn-sn-files st)))
         (profile (fn-owner-store-profile state))
         (v (fn-cfg-value (fn-ocfg-config (fn-owner-ocfg state))))
         ; S038: the capture decides admission itself, over the slot as it is
         ; now, in this mutex hold (books/owner-reclaim.lisp
         ; fn-orc-capture-slot, KEYSTONE fn-orc-capture-takes-only-a-free-slot).
         ; The request's answer, taken in an earlier quantum, decides nothing.
         (slot (fn-orc-capture-slot mode count
                                    (fn-owner-sco-global 'fn-owner-orc-pass state)
                                    (fn-owner-sco-global 'fn-owner-sco-inflight state))))
    (if (not (eq (car slot) :capture))
        ; refused by name (:in-flight, :queued): the slot is untouched
        (value (list :refused (car slot)))
      (let* ((state (f-put-global 'fn-owner-orc-pass (cadr slot) state))
             (state (f-put-global 'fn-owner-sco-inflight (caddr slot) state))
             (stamp (fn-record-stamp-of-observation clock)))
        (value (list records count v st profile
                     (fn-sn-config-history st)
                     (fn-sf-frontier (fn-sn-files st))
                     (and profile (fn-owner-sco-budget override profile))
                     free revision
                     (and (natp stamp) stamp)
                     (and profile (fn-bs-profile-max-record-octets profile))
                     ; The owner's feed queues, a holder the Store does not
                     ; carry (books/store-reclaim-owner-holders): read here, on
                     ; the mutex, with the Store it goes with.
                     (fn-rcl-owner-feed-holders (fn-owner-core state))))))))

(verify-guards fn-owner-orc-capture-of)

(defun fn-owner-orc-capture (mode clock override free revision state)
 (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
 (fn-owner-orc-capture-of (fn-sf-records (fn-sn-files (fn-owner-store state))) mode clock override free revision state))
(defun fn-owner-orc-capture-served (mode clock override free revision state)
 (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
 (fn-owner-orc-capture-of nil mode clock override free revision state))
(defthm fn-owner-orc-capture-served-is-reference
 (implies (fn-hist-of-storep records (fn-owner-store st))
  (and (equal (fn-hsc-complete-capture ':reclaim
                (mv-nth 1 (fn-owner-orc-capture-served mode clock override free revision st)) records)
              (mv-nth 1 (fn-owner-orc-capture mode clock override free revision st)))
       (equal (mv-nth 2 (fn-owner-orc-capture-served mode clock override free revision st))
              (mv-nth 2 (fn-owner-orc-capture mode clock override free revision st)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-owner-orc-capture-served fn-owner-orc-capture fn-owner-orc-capture-of fn-hsc-complete-capture
     fn-hist-of-storep fn-owner-store update-nth nth zp car-cons cdr-cons)))))
(in-theory (disable fn-owner-orc-capture-served fn-owner-orc-capture fn-owner-orc-capture-of))

(defthm fn-owner-sco-capture-served-preserves-retain-state
 (implies (fn-owner-retain-statep state)
  (fn-owner-retain-statep (mv-nth 2 (fn-owner-sco-capture-served override free revision state))))
 :hints (("Goal" :in-theory '(fn-owner-sco-capture-served fn-owner-sco-capture-of
                       fn-owner-retain-statep fn-owner-ocfg-of-other-global-put
                       fn-owner-bound-of-other-global-put
                       fn-owner-retain-carry-of-other-global-put car-cons cdr-cons))))

(defthm fn-owner-oex-capture-served-preserves-retain-state
 (implies (fn-owner-retain-statep state)
  (fn-owner-retain-statep (mv-nth 2 (fn-owner-oex-capture-served  state))))
 :hints (("Goal" :in-theory '(fn-owner-oex-capture-served fn-owner-oex-capture-of
                       fn-owner-retain-statep fn-owner-ocfg-of-other-global-put
                       fn-owner-bound-of-other-global-put
                       fn-owner-retain-carry-of-other-global-put car-cons cdr-cons))))

(defthm fn-owner-orc-capture-served-preserves-retain-state
 (implies (fn-owner-retain-statep state)
  (fn-owner-retain-statep (mv-nth 2 (fn-owner-orc-capture-served mode clock override free revision state))))
 :hints (("Goal" :in-theory '(fn-owner-orc-capture-served fn-owner-orc-capture-of
                       fn-owner-retain-statep fn-owner-ocfg-of-other-global-put
                       fn-owner-bound-of-other-global-put
                       fn-owner-retain-carry-of-other-global-put car-cons cdr-cons))))
