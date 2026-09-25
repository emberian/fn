; host/spike-storage-host.lisp -- spike/storage (D28): ACL2 :program wrappers
; for the storage-at-scale spike.  Every function here is a SPIKE deferral:
; it is :program code, not a certified book, and each block names the proof
; or ACL2 owner a dev re-implementation owes.  Record:
; planning/evidence/spike-storage-2026-09-25.md.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; A. The owner opens from the open the store already made.
;
;; SPIKE: defers the theorem that the stashed state equals what
;; fn-owner-recover computes: both are fn-cpo-open-observed over the same
;; config records, frontier and history under the store lock (full path), or
;; fn-sco-open of the checkpoint (P3 keystone
;; fn-sn-recover-from-checkpoint-equals-full-recover).

(defun fn-spk-stash-opened (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-spk-opened
                             (cons (f-get-global 'fn-store-sn state)
                                   (f-get-global 'fn-store-cfg state))
                             state)))
    (value :stashed)))

(defun fn-spk-clear-opened (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-spk-opened nil state)))
    (value :cleared)))

(defun fn-spk-owner-recover-opened (max-conns state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((stash (and (boundp-global 'fn-spk-opened state)
                     (f-get-global 'fn-spk-opened state)))
         (s (car stash))
         (cfg (cdr stash)))
    (if (or (not (consp stash)) (null s) (not (natp max-conns))
            (not (equal (fn-sf-phase (fn-sn-files s)) :recovering)))
        (value :fault)
      (let* ((state (fn-owner-install-ocfg
                     (fn-ocfg-make
                      (fn-own-configure (fn-own-start s max-conns)
                                        (fn-owner-post-config cfg))
                      cfg nil nil)
                     state))
             (state (f-put-global 'fn-owner-feed-intents nil state))
             (state (f-put-global 'fn-owner-store-profile nil state))
             (state (f-put-global 'fn-owner-feed-inputs
                                  (fn-fc-table-initial-state) state))
             (state (f-put-global 'fn-spk-opened nil state)))
        (value :recovering)))))


; -----------------------------------------------------------------------------
; C2. Release and reclaim (D13, STO-010 capability C).
;
; `release': an operator's release record for an article's archive
; undertaking (its id, subject and evidence as the ledger holds them), in the
; store's side namespace releases/.  `reclaim': an article whose archive
; undertaking a release record names, that no other undertaking holds, older
; than the operator's age rule, and whose identity replay does not read its
; body, gets the stub payload (C1) in its record, its article and the
; checkpoint; the Message-ID, groups, memberships (article numbers), pin,
; stamp, binding, retention ledger and verdicts stay.
;
; Why a side namespace: the model cannot release an archive undertaking.
; fn-node-statep (books/node.lisp) requires every binding id among the live
; pins and every article to have a live archive pin, and
; fn-replay-apply-retention-event refuses a bound id.  Admitting the release
; in replay broke fn-replay-apply-record-non-nil-is-node-state at once
; (hbox certify-20260925T081250Z-2847123).  So the ledger keeps charging a
; released article; reclaim frees its bytes, not its charge.
;
;; SPIKE: defers, as book theorems dev owes:
;;  1. fn-spk-reclaim-preserves-decisions: the open of the history with the
;;     plan's records stubbed equals the stub transform of the open of the
;;     original history, on every slot but article payloads (acceptance,
;;     numbering, frontiers, bindings, retention, keyring, index, verdicts,
;;     snapshots, identity-next, consumer, topic, event index).  The spike
;;     checks it executably (`reclaim --verify', fn-spk-decisions).
;;  2. fn-spk-stub-identity-invariant: for an eligible record, fn-stx-delta
;;     and fn-stx-verdict-of-octets are the same on the stub (checked per
;;     record here, against the current keyring only).
;;  3. The archive release as a Store event: relax fn-node-statep to binding
;;     ids within pins or releases, admit a bound :archive release in
;;     fn-replay-apply-retention-event, re-prove the node invariants; then
;;     the release is replayed history, not a side record, and it frees its
;;     charge.  The authority of an operator release (D13's policy) is open.
;;  4. Consumer pins: any registered consumer refuses the whole reclaim
;;     (conservative); the per-consumer pin bound is dev's.

(defun fn-spk-sn (state)
  (declare (xargs :stobjs state :mode :program))
  (f-get-global 'fn-store-sn state))

(defun fn-spk-find-binding (msgid bindings)
  (declare (xargs :mode :program))
  (cond ((atom bindings) nil)
        ((equal (fn-node-binding-msgid (car bindings)) msgid) (car bindings))
        (t (fn-spk-find-binding msgid (cdr bindings)))))

(defun fn-spk-subject-heldp (subject pins)
  (declare (xargs :mode :program))
  (cond ((atom pins) nil)
        ((equal (fn-retain-obligation-subject (car pins)) subject) t)
        (t (fn-spk-subject-heldp subject (cdr pins)))))

(defun fn-spk-subject-releasedp (subject releases)
  (declare (xargs :mode :program))
  (cond ((atom releases) nil)
        ((equal (fn-retain-release-subject (car releases)) subject) t)
        (t (fn-spk-subject-releasedp subject (cdr releases)))))

; The release event for MSGID: (:release id subject evidence charge), or a
; keyword saying why not.
(defun fn-spk-release-event (msgid-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-spk-sn state))
         (node (fn-sn-node s))
         (msgid (fn-store-octets->string msgid-octets))
         (binding (fn-spk-find-binding msgid (fn-node-bindings node)))
         (pin (and binding
                   (fn-retain-find-id (fn-node-binding-id binding)
                                      (fn-retain-pins (fn-node-retention node))))))
    (value
     (cond ((null binding) :unknown)
           ((not (consp pin)) :not-held)
           (t (list :release
                    (fn-record-string-octets (fn-retain-obligation-id pin))
                    (fn-record-string-octets (fn-retain-obligation-subject pin))
                    (fn-record-string-octets (fn-retain-obligation-evidence pin))
                    (fn-retain-obligation-charge pin)))))))

; The article msgids in store order (oldest first), for `release --first K'.
(defun fn-spk-released-fal (ids fal)
  (declare (xargs :mode :program))
  (if (atom ids) fal
    (fn-spk-released-fal (cdr ids) (hons-acons (fn-store-octets->string (car ids)) t fal))))

(defun fn-spk-held-msgids (articles bindings released n acc)
  (declare (xargs :mode :program))
  (if (or (atom articles) (zp n)) acc
    (let* ((m (fn-article-msgid (car articles)))
           (b (fn-spk-find-binding m bindings)))
      (if (and b (not (hons-get (fn-node-binding-id b) released)))
          (fn-spk-held-msgids (cdr articles) bindings released (- n 1)
                              (cons (fn-record-string-octets m) acc))
        (fn-spk-held-msgids (cdr articles) bindings released n acc)))))

; The K oldest articles no release record names yet.
(defun fn-spk-oldest-held (k released-ids state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((node (fn-sn-node (fn-spk-sn state)))
         (articles (reverse (fn-state-articles (fn-node-acceptance node)))))
    (value (reverse (fn-spk-held-msgids articles (fn-node-bindings node)
                                        (fn-spk-released-fal released-ids nil) k nil)))))

; Eligibility of one article: :eligible or the reason it is kept.  RELEASED
; is a fast alist of the obligation ids an operator release record names.
(defun fn-spk-subject-held-by-other (subject id pins)
  (declare (xargs :mode :program))
  (cond ((atom pins) nil)
        ((and (equal (fn-retain-obligation-subject (car pins)) subject)
              (not (equal (fn-retain-obligation-id (car pins)) id)))
         t)
        (t (fn-spk-subject-held-by-other subject id (cdr pins)))))

(defun fn-spk-article-verdict (a now older-than pins released bindings keyring gen)
  (declare (xargs :mode :program))
  (let* ((msgid (fn-article-msgid a))
         (payload (fn-article-payload a))
         (b (fn-spk-find-binding msgid bindings))
         (stamp (fn-article-stamp a)))
    (cond ((fn-spk-stub-info payload) :already-reclaimed)
          ((null b) :no-binding)
          ((not (hons-get (fn-node-binding-id b) released)) :held)
          ((fn-spk-subject-held-by-other (fn-node-binding-subject b)
                                         (fn-node-binding-id b) pins)
           :held-by-other)
          ((and (posp older-than) (not (natp stamp))) :legacy-stamp)
          ((and (posp older-than) (> (+ stamp older-than) now)) :too-young)
          (t (let ((stub (fn-spk-stub payload msgid)))
               (if (and (equal (fn-stx-delta payload keyring) (fn-stx-delta stub keyring))
                        (equal (fn-stx-verdict-of-octets payload keyring gen)
                               (fn-stx-verdict-of-octets stub keyring gen)))
                   :eligible
                 :identity-reads-body))))))

(defun fn-spk-count (key alist)
  (declare (xargs :mode :program))
  (let ((p (assoc-equal key alist)))
    (put-assoc-equal key (+ 1 (if p (cdr p) 0)) alist)))

(defun fn-spk-plan-articles (articles now older-than pins releases bindings keyring gen
                                      fal counts freed)
  ; RELEASES: the fast alist of released obligation ids.
  (declare (xargs :mode :program))
  (if (atom articles) (mv fal counts freed)
    (let* ((a (car articles))
           (v (fn-spk-article-verdict a now older-than pins releases bindings keyring gen)))
      (if (eq v :eligible)
          (let ((stub (fn-spk-stub (fn-article-payload a) (fn-article-msgid a))))
            (fn-spk-plan-articles (cdr articles) now older-than pins releases bindings
                                  keyring gen
                                  (hons-acons (fn-article-msgid a) stub fal)
                                  (fn-spk-count v counts)
                                  (+ freed (- (len (fn-article-payload a)) (len stub)))))
        (fn-spk-plan-articles (cdr articles) now older-than pins releases bindings
                              keyring gen fal (fn-spk-count v counts) freed)))))

; Plan: sets global fn-spk-reclaim (a fast alist msgid -> stub payload) and
; answers (:ok COUNTS FREED-OCTETS) or (:refused REASON).
(defun fn-spk-reclaim-plan (now older-than released-ids state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-spk-sn state))
         (node (fn-sn-node s))
         (ret (fn-node-retention node))
         (consumer (fn-sn-consumer s)))
    (if (and (consp consumer) (consp (fn-cp-nth 5 consumer)))
        (value (list :refused :consumer-pins))
      (mv-let (fal counts freed)
        (fn-spk-plan-articles (fn-state-articles (fn-node-acceptance node))
                              now older-than (fn-retain-pins ret) (fn-spk-released-fal released-ids nil)
                              (fn-node-bindings node) (fn-sn-keyring s)
                              (fn-sn-keyring-generation s) nil nil 0)
        (let ((state (f-put-global 'fn-spk-reclaim fal state)))
          (value (list :ok counts freed)))))))

(defun fn-spk-reclaim-set (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-spk-reclaim state) (f-get-global 'fn-spk-reclaim state) nil))

; The stub transform of one record / article / record list / article list.
(defun fn-spk-stub-record (r fal)
  (declare (xargs :mode :program))
  (if (fn-record-p r)
      (let ((hit (hons-get (fn-record-msgid r) fal)))
        (if hit
            (fn-record-make (fn-record-sequence r) (fn-record-txid r)
                            (fn-record-generation r) (fn-record-msgid r) (cdr hit)
                            (fn-record-groups r) (fn-record-obligation-id r)
                            (fn-record-content-subject r) (fn-record-release-evidence r)
                            (fn-record-charge r) (fn-record-stamp r))
          r))
    r))

(defun fn-spk-stub-records (rs fal)
  (declare (xargs :mode :program))
  (if (atom rs) nil
    (cons (fn-spk-stub-record (car rs) fal) (fn-spk-stub-records (cdr rs) fal))))

(defun fn-spk-stub-articles (as fal)
  (declare (xargs :mode :program))
  (if (atom as) nil
    (let* ((a (car as)) (hit (hons-get (fn-article-msgid a) fal)))
      (cons (if hit
                (fn-make-article (fn-article-msgid a) (cdr hit) (fn-article-groups a)
                                 (fn-article-memberships a) (fn-article-pin a)
                                 (fn-article-stamp a))
              a)
            (fn-spk-stub-articles (cdr as) fal)))))

(defun fn-spk-stub-node (node fal)
  (declare (xargs :mode :program))
  (let ((acc (fn-node-acceptance node)))
    (fn-node-make-state
     (fn-make-state (fn-state-groups acc) (fn-state-nexts acc)
                    (fn-spk-stub-articles (fn-state-articles acc) fal)
                    (fn-state-next-txid acc) (fn-state-pending acc) (fn-state-fenced acc))
     (fn-node-retention node) (fn-node-stage node) (fn-node-bindings node))))

; The event index (books/consumer-event-index) maps each sequence to its
; whole event, so a stubbed record is put again at its sequence.
(defun fn-spk-stub-event-index (records fal index)
  (declare (xargs :mode :program))
  (if (atom records) index
    (let ((r (car records)))
      (fn-spk-stub-event-index
       (cdr records) fal
       (if (and (fn-record-p r) (hons-get (fn-record-msgid r) fal))
           (fn-cei-put (fn-record-sequence r) (fn-spk-stub-record r fal) index)
         index)))))

(defun fn-spk-stub-sco (c fal)
  (declare (xargs :mode :program))
  (let ((cpr (fn-sco-cpr c)))
    (fn-sco-make (fn-spk-stub-records (fn-sco-records c) fal)
                 (if (fn-sco-pausedp cpr)
                     (let ((cn (fn-sco-at 1 cpr)))
                       (fn-sco-paused (fn-cnode-make (fn-spk-stub-node (fn-cnode-node cn) fal)
                                                     (fn-cnode-config cn))
                                      (fn-sco-at 2 cpr) (fn-sco-at 3 cpr)))
                   cpr)
                 (fn-sco-identity c) (fn-sco-consumer c) (fn-sco-topic c)
                 (fn-spk-stub-event-index (fn-sco-records c) fal (fn-sco-event-index c)))))

; The stubbed record octets the host writes: ((SEQUENCE . OCTETS) ...) for
; every record in the recovered history the plan names, in order.
(defun fn-spk-stubbed-record-octets (rs fal acc)
  (declare (xargs :mode :program))
  (if (atom rs) (reverse acc)
    (let ((r (car rs)))
      (if (and (fn-record-p r) (hons-get (fn-record-msgid r) fal))
          (fn-spk-stubbed-record-octets
           (cdr rs) fal
           (cons (cons (fn-record-sequence r)
                       (fn-rcon-store-event-encode (fn-spk-stub-record r fal)))
                 acc))
        (fn-spk-stubbed-record-octets (cdr rs) fal acc)))))

(defun fn-spk-reclaim-records (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-spk-stubbed-record-octets
          (fn-sf-records (fn-sn-files (fn-spk-sn state))) (fn-spk-reclaim-set state) nil)))

; The next checkpoint after the reclaim: the open's checkpoint stubbed and
; extended over the stubbed suffix, or (full-replay open) the capture of the
; stubbed history.  (OCTETS S) or :unencodable.
(defun fn-spk-reclaim-checkpoint-octets (segment-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((fal (fn-spk-reclaim-set state))
         (st (fn-spk-sn state))
         (records (fn-spk-stub-records (fn-sf-records (fn-sn-files st)) fal))
         (configs (fn-sn-config-history st))
         (old (fn-store-sco-current state))
         (next (if (and old (<= (fn-sco-sequence old) (len records)))
                   (fn-spk-sco-extend (fn-spk-stub-sco old fal) configs
                                      (nthcdr (fn-sco-sequence old) records))
                 (fn-spk-sco-capture configs records)))
         (octets (fn-scc-file-octets next segment-octets)))
    (if (equal octets :unencodable) (value :unencodable)
      (value (list octets (fn-sco-sequence next))))))

; Every decision-bearing slot of an opened Store with article payloads
; dropped.  `reclaim --verify' compares it before and after.
(defun fn-spk-article-keys (as)
  (declare (xargs :mode :program))
  (if (atom as) nil
    (let ((a (car as)))
      (cons (list (fn-article-msgid a) (fn-article-groups a) (fn-article-memberships a)
                  (fn-article-pin a) (fn-article-stamp a))
            (fn-spk-article-keys (cdr as))))))

(defun fn-spk-decisions (s)
  (declare (xargs :mode :program))
  (let* ((node (fn-sn-node s)) (acc (fn-node-acceptance node)))
    (list (fn-state-groups acc) (fn-state-nexts acc) (fn-state-next-txid acc)
          (fn-spk-article-keys (fn-state-articles acc))
          (fn-node-retention node) (fn-node-bindings node)
          (fn-sn-keyring s) (fn-sn-index s) (fn-sn-keyring-generation s)
          (fn-sn-verdicts s) (fn-sn-keyring-snapshots s) (fn-sn-identity-next s)
          (fn-sn-consumer s) (fn-sn-topic s))))

; `reclaim --verify': (a) the full open of the stubbed history, (b) the open
; of the stubbed checkpoint over the stubbed suffix, (c) the pre-reclaim open.
; Answers (DECISIONS-EQUAL CHECKPOINT-EQUALS-FULL PAYLOADS-STUBBED).
(defun fn-spk-diff-slots (a b i)
  (declare (xargs :mode :program))
  (cond ((or (atom a) (atom b)) nil)
        ((equal (car a) (car b)) (fn-spk-diff-slots (cdr a) (cdr b) (+ 1 i)))
        (t (cons i (fn-spk-diff-slots (cdr a) (cdr b) (+ 1 i))))))

(defun fn-spk-reclaim-verify (frontier state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((fal (fn-spk-reclaim-set state))
         (st (fn-spk-sn state))
         (records (fn-spk-stub-records (fn-sf-records (fn-sn-files st)) fal))
         (configs (fn-sn-config-history st))
         (full (fn-spk-cpo-open-observed configs frontier records))
         (old (fn-store-sco-current state))
         (via (if old
                  (fn-spk-sco-open (fn-spk-stub-sco old fal) configs frontier
                                   (nthcdr (fn-sco-sequence old) records))
                full))
         (fs (fn-sn-open-state full)))
    (value (list (and (fn-spk-open-okp full)
                      (equal (fn-spk-decisions fs) (fn-spk-decisions st)))
                 (equal via full)
                 (equal (fn-spk-stub-articles
                         (fn-state-articles (fn-node-acceptance (fn-sn-node st))) fal)
                        (fn-state-articles (fn-node-acceptance (fn-sn-node fs))))
                 (fn-spk-diff-slots (fn-spk-decisions fs) (fn-spk-decisions st) 0)
                 (equal (fn-sn-event-index fs)
                        (fn-spk-stub-event-index (fn-sf-records (fn-sn-files st)) fal
                                                 (fn-sn-event-index st)))))))

; -----------------------------------------------------------------------------
; D. Chained packs: link codec (P5).
;
; A link is  "FNPL" 01 | lower u64 | boundary u64 | pred u64 (2^64-1: none)
; | pred-header-digest 32 | count u64 | count x record-digest 32 | count x
; (u32 length, record octets), sealed as an FN frame by the host (fnn-seal).
; The header digest covers everything before the record bodies, so a
; reclaim that stubs a record in place keeps the chain: a body is admitted
; when its digest is the listed one, or it is that record with a stub payload.
;
;; SPIKE: defers the book: fn-spk-link-decode-of-encode; the chain keystone
;; (PRF-073 over a chain): the concatenation of the selected chain's records
;; plus the suffix is the identical record list, and every crash cut of
;; publishing a link or the selection leaves the previous chain selected;
;; the chain-length bound in the profile; and the stub admission's claim
;; that only the payload changed (checked here field by field).

(defun fn-spk-u64 (n)
  (declare (xargs :mode :program))
  (let ((n (nfix n)))
    (list (logand (ash n -56) 255) (logand (ash n -48) 255) (logand (ash n -40) 255)
          (logand (ash n -32) 255) (logand (ash n -24) 255) (logand (ash n -16) 255)
          (logand (ash n -8) 255) (logand n 255))))

(defun fn-spk-u32 (n)
  (declare (xargs :mode :program))
  (list (logand (ash n -24) 255) (logand (ash n -16) 255) (logand (ash n -8) 255)
        (logand n 255)))

(defun fn-spk-get-uint (x k acc)
  (declare (xargs :mode :program))
  (if (or (zp k) (atom x)) acc
    (fn-spk-get-uint (cdr x) (- k 1) (+ (* 256 acc) (car x)))))

(defconst *fn-spk-no-pred* (- (expt 2 64) 1))
(defconst *fn-spk-link-magic* '(70 78 80 76 1))

(defun fn-spk-digests (records)
  (declare (xargs :mode :program))
  (if (atom records) nil
    (append (fn-frame-digest (car records)) (fn-spk-digests (cdr records)))))

(defun fn-spk-bodies (records)
  (declare (xargs :mode :program))
  (if (atom records) nil
    (append (fn-spk-u32 (len (car records))) (car records) (fn-spk-bodies (cdr records)))))

(defun fn-spk-link-header (lower boundary pred pred-digest digests count)
  (declare (xargs :mode :program))
  (append *fn-spk-link-magic* (fn-spk-u64 lower) (fn-spk-u64 boundary)
          (fn-spk-u64 pred) pred-digest (fn-spk-u64 count) digests))

; The link payload octets for RECORDS (octet lists, sequences lower..), with
; the original-record digest list DIGESTS (nil: computed from RECORDS).
(defun fn-spk-link-encode (lower pred pred-digest records digests)
  (declare (xargs :mode :program))
  (let* ((count (len records))
         (digests (or digests (fn-spk-digests records))))
    (append (fn-spk-link-header lower (+ lower count) pred pred-digest digests count)
            (fn-spk-bodies records))))

(defun fn-spk-split-digests (x k acc)
  (declare (xargs :mode :program))
  (if (zp k) (mv (reverse acc) x)
    (fn-spk-split-digests (nthcdr 32 x) (- k 1) (cons (take 32 x) acc))))

(defun fn-spk-read-bodies (x k acc)
  (declare (xargs :mode :program))
  (if (zp k) (if (atom x) (reverse acc) :trailing)
    (if (< (len (take 4 x)) 4) :truncated
      (let ((n (fn-spk-get-uint x 4 0)) (rest (nthcdr 4 x)))
        (if (< (len rest) n) :truncated
          (fn-spk-read-bodies (nthcdr n rest) (- k 1) (cons (take n rest) acc)))))))

; A stubbed body: it decodes as a record whose payload is a stub.
(defun fn-spk-stub-body-p (body)
  (declare (xargs :mode :program))
  (let ((r (fn-store-decode-records (list body))))
    (and (consp r) (fn-record-p (car r))
         (fn-spk-stub-info (fn-record-payload (car r))) t)))

(defun fn-spk-bodies-match (bodies digests)
  (declare (xargs :mode :program))
  (cond ((atom bodies) t)
        ((or (equal (fn-frame-digest (car bodies)) (car digests))
             (fn-spk-stub-body-p (car bodies)))
         (fn-spk-bodies-match (cdr bodies) (cdr digests)))
        (t nil)))

; Decode a link payload: (:ok LOWER BOUNDARY PRED PRED-DIGEST HEADER-DIGEST
; DIGESTS BODIES) or (:bad REASON).
(defun fn-spk-link-decode (x)
  (declare (xargs :mode :program))
  (if (not (fn-spk-prefixp *fn-spk-link-magic* x)) (list :bad :magic)
    (let* ((y (nthcdr 5 x))
           (lower (fn-spk-get-uint y 8 0))
           (boundary (fn-spk-get-uint (nthcdr 8 y) 8 0))
           (pred (fn-spk-get-uint (nthcdr 16 y) 8 0))
           (pred-digest (take 32 (nthcdr 24 y)))
           (count (fn-spk-get-uint (nthcdr 56 y) 8 0))
           (hlen (+ 5 64 (* 32 count))))
      (if (or (< (len y) 64) (not (equal boundary (+ lower count))) (< (len x) hlen))
          (list :bad :header)
        (mv-let (digests rest) (fn-spk-split-digests (nthcdr 64 y) count nil)
          (let ((bodies (fn-spk-read-bodies rest count nil)))
            (cond ((not (true-listp bodies)) (list :bad bodies))
                  ((not (fn-spk-bodies-match bodies digests)) (list :bad :record-digest))
                  (t (list :ok lower boundary pred pred-digest
                           (fn-frame-digest (take hlen x)) digests bodies)))))))))

(defun fn-spk-link-rebody (x new-bodies)
  ; The same header with NEW-BODIES (a reclaim's in-place rewrite).
  (declare (xargs :mode :program))
  (let ((d (fn-spk-link-decode x)))
    (if (not (eq (car d) :ok)) :bad
      (let ((count (len (nth 7 d))))
        (append (take (+ 5 64 (* 32 count)) x) (fn-spk-bodies new-bodies))))))

(defun fn-spk-no-pred () (declare (xargs :mode :program)) *fn-spk-no-pred*)
