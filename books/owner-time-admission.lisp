; fn: a slow or stalled disk refuses the POST command itself, 440, before
; the client sends the article (lane time-model-2, 2026-09-27, slice 2 of
; planning/design-time-model-2026-09-27.md section 3.4; PRF-323).
;
; Slice 1 refused a POST try-later AFTER its article (441, the queued
; submission shed).  RFC 3977 section 6.3.1 gives the initial response 440
; ("Posting not permitted") for a POST the server will not take now, so the
; client does not send an article for nothing.  The served machine already
; answers 440 at the command when the owner's injection configuration does
; not permit posting (books/served-catalog-chain.lisp fn-scr-post-step: the
; offered POST under (fn-inj-config-allow config) = nil).  So the served
; read, while the disk sheds (books/owner-time-model.lisp fn-otm-admit-post
; = :shed at the read's recorded time), runs over the owner's value with
; the posting bit off, and the bit is put back after it: the read is the
; read of a node that does not permit posting, and nothing else about the
; owner changes.  The configuration itself (durable, published) is never
; touched: the bit is the read's input, not a reconfiguration.
;
; Lane log-leftovers (2026-09-27) adds two things to the shed read:
;   - the 440 at the command and the 441 of an article whose POST got 340
;     before the disk went slow carry ACL2's disk reason (fn-otm-post-command-
;     line, fn-otm-shed-line) in place of the served machine's generic
;     texts, when the connection's posting bit was on before the read (so the
;     refusal is the disk's, never a configuration's) -- fn-otm-disk-effects;
;   - PKT-858: a peer's read (IHAVE, CHECK) runs with the disk-slow posture
;     in the owner's refused-offer memory (books/peer-inbound.lisp
;     *fn-peer-shed-entry*, fn-peer-shed-p), which the peer session is
;     re-pinned with (books/owner.lisp fn-own-conn-live-session), so every
;     well-formed offer is :defer :disk-slow (436 / 431,
;     fn-peer-shed-offer-is-disk-slow); the entry is taken out after the read.
;     While the disk sheds a peer's read is admitted as a reader-class
;     quantum (fn-otm-peer-read-class): the transit class waits for the
;     barrier.
;
; The subject is fn-otm-read-span, which host/owner-host.lisp
; fn-owner-chunk-span-at calls with S, the gate's scheduler value the host
; read in the same quantum (host/native/owner.lisp
; fnn-owner-handle-chunk-read, after the read's :served clock event): the
; admission and the reason lines are ACL2's over that one value.
(in-package "ACL2")
(include-book "owner-time-model")
(include-book "protocol-table") ; reply texts: (fn-proto-text ROW KEY)
(include-book "owner-reader-read")

; The injection configuration with its posting bit set to ALLOW; the other
; fields as they are.
(defun fn-otm-cfg-with-allow (cfg allow)
  (declare (xargs :guard t))
  (if (consp cfg) (cons allow (cdr cfg)) (list allow)))

; The served step reads the CONNECTION's injection configuration
; (books/owner.lisp fn-own-served-conn: fn-own-conn-config, the snapshot the
; connection holds), so the bit is set on connection ID's record; the owner
; and every other connection are as they were.
(defun fn-otm-conn-with-allow (c allow)
  (declare (xargs :guard t))
  (if (and (true-listp c) (< 6 (len c)))
      (update-nth 6 (fn-otm-cfg-with-allow (fn-own-conn-config c) allow) c)
    c))

(defun fn-otm-owner-with-allow (oc id allow)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (c (fn-own-find-conn id (fn-own-conns o))))
    (if c
        (fn-ocfg-with-owner
         oc (fn-own-set-conns o (fn-own-replace-conn (fn-otm-conn-with-allow c allow)
                                                     (fn-own-conns o))))
      oc)))

; The posting bit connection ID's read runs with.
(defun fn-otm-conn-allow (oc id)
  (declare (xargs :guard t))
  (fn-inj-config-allow
   (fn-own-conn-config (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))

; The owner with its refused-offer memory set to MEM, every other field as
; it is.
(defun fn-otm-ocfg-with-refused (oc mem)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (fn-ocfg-with-owner
     oc (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
                     (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
                     (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
                     (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) mem))))

; The memory without the disk-slow posture's entries.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-otm-strip-shed-loop (mem acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp mem)
      (if (and (consp (car mem)) (equal (car (car mem)) :disk-slow))
          (fn-otm-strip-shed-loop (cdr mem) acc)
        (fn-otm-strip-shed-loop (cdr mem) (cons (car mem) acc)))
    (revappend acc mem)))

(defun fn-otm-strip-shed (mem)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp mem)
           (if (and (consp (car mem)) (equal (car (car mem)) :disk-slow))
               (fn-otm-strip-shed (cdr mem))
             (cons (car mem) (fn-otm-strip-shed (cdr mem))))
         mem)
       :exec (fn-otm-strip-shed-loop mem nil)))

(local
 (defthm fn-otm-strip-shed-loop-is-revappend
   (equal (fn-otm-strip-shed-loop mem acc)
          (revappend acc (fn-otm-strip-shed mem)))
   :hints (("Goal" :induct (fn-otm-strip-shed-loop mem acc)
                   :in-theory (union-theories '(fn-otm-strip-shed-loop fn-otm-strip-shed revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-otm-strip-shed-loop)

(verify-guards fn-otm-strip-shed
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-otm-strip-shed)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-otm-strip-shed-loop-is-revappend (acc nil))))))


; The owner a shed read runs over: connection ID's posting bit off, the
; posture's entry at the front of the refused-offer memory.
(defun fn-otm-shed-ocfg (oc id)
  (declare (xargs :guard t))
  (let ((oc1 (fn-otm-owner-with-allow oc id nil)))
    (fn-otm-ocfg-with-refused
     oc1 (cons *fn-peer-shed-entry* (fn-own-refused (fn-ocfg-owner oc1))))))

; The owner after it: the posture's entries out, connection ID's bit ALLOW.
(defun fn-otm-unshed-ocfg (oc id allow)
  (declare (xargs :guard t))
  (fn-otm-owner-with-allow
   (fn-otm-ocfg-with-refused oc (fn-otm-strip-shed (fn-own-refused (fn-ocfg-owner oc))))
   id allow))

; The generic lines the served machine renders with posting off.
(defconst *fn-otm-generic-440*
  (fn-nntp-reply-effect (fn-nntp-crlf (fn-nntp-string-octets (fn-proto-text "POST" :not-permitted)))))
(defconst *fn-otm-generic-441*
  (fn-nntp-reply-effect
   (fn-nntp-crlf (fn-nntp-string-octets (fn-post-refusal-line :posting-disallowed)))))

; Each generic 440 is L440, each generic 441 L441; every other effect as it is.
(defun fn-otm-disk-effects (effects l440 l441)
  (declare (xargs :guard t))
  (if (consp effects)
      (cons (cond ((equal (car effects) *fn-otm-generic-440*) (fn-nntp-reply-effect l440))
                  ((equal (car effects) *fn-otm-generic-441*) (fn-nntp-reply-effect l441))
                  (t (car effects)))
            (fn-otm-disk-effects (cdr effects) l440 l441))
    nil))

; The served read, admitted or not, at the gate's value S.
(defun fn-otm-read-span (oc views id i end cache s fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (eq (fn-otm-admit-post s) :shed)
      (let* ((allow (fn-otm-conn-allow oc id))
             (result (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end cache
                                       fn-octets fn-arena fn-cat))
             (effects (fn-own-tls-result-effects result)))
        (fn-own-tls-make-result
         (fn-own-tls-result-consumed result)
         (if allow
             (fn-otm-disk-effects effects (fn-otm-post-command-reply s) (fn-otm-shed-reply s))
           effects)
         (fn-otm-unshed-ocfg (fn-own-tls-result-owner result) id allow)
         (fn-own-tls-result-repinned result)))
    (fn-orr-read-span oc views id i end cache fn-octets fn-arena fn-cat)))

; The class a peer connection's read enters the gate as: while the disk
; sheds, a reader-class quantum (admitted while the batch is in flight; the
; read runs under the disk-slow posture), else the transit class.
(defun fn-otm-peer-read-class (s)
  (declare (xargs :guard t))
  (if (eq (fn-otm-admit-post s) :shed) :reader :transit))

; Whether a peer's read admitted as CLASS runs at the gate's value S: a
; reader-class peer read runs only while the disk sheds (the disk recovered
; between the choice and the admission: the read is retried as transit).
(defun fn-otm-peer-read-proceeds-p (class s)
  (declare (xargs :guard t))
  (or (not (eq class :reader)) (eq (fn-otm-admit-post s) :shed)))

;; Admitted, the read is the reader read exactly: every theorem about
;; fn-orr-read-span (PRF-288, PRF-296) is a theorem about the host's call.
(defthm fn-otm-read-span-when-admitted-unfolds
  (implies (not (eq (fn-otm-admit-post s) :shed))
           (equal (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat)
                  (fn-orr-read-span oc views id i end cache fn-octets fn-arena fn-cat))))

;; The served machine's 440 under a closed posting bit is the one effect
;; *fn-otm-generic-440*: fn-otm-disk-effects replaces exactly that reply.
(defthm fn-otm-closed-posting-answers-the-generic-440
  (implies (and (fn-post-sessionp ps)
                (not (fn-post-session-awaiting ps))
                (not (fn-inj-config-allow config))
                (fn-post-offeredp
                 (fn-nntp-result-effects
                  (fn-scr-step (fn-post-session-base ps) archive index verdicts
                               (fn-post-reader-env config observation)
                               wire-event v fn-arena fn-cat))))
           (equal (fn-post-result-effects
                   (fn-scr-post-step ps archive index verdicts config observation injection
                                     wire-event v fn-arena fn-cat))
                  (list *fn-otm-generic-440*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-post-step fn-post-single fn-nntp-single
                                fn-post-result-effects-of-fn-post-make-result
                                fn-nntp-result-effects fn-nntp-make-result
                                (:e fn-nntp-reply-effect) (:e fn-nntp-crlf)
                                (:e fn-nntp-string-octets) cdr-cons)
                              (theory 'minimal-theory)))))

;; ... and its 441 for :posting-disallowed (books/nntp-post.lisp: the
;; refusal is fn-post-single of fn-post-refusal-line) is *fn-otm-generic-441*.
(defthm fn-otm-posting-disallowed-refusal-is-the-generic-441
  (equal (fn-post-single ps (fn-post-refusal-line :posting-disallowed))
         (list *fn-otm-generic-441*))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-post-single fn-nntp-single
                                fn-nntp-result-effects fn-nntp-make-result
                                (:e fn-nntp-reply-effect) (:e fn-nntp-crlf)
                                (:e fn-nntp-string-octets) (:e fn-post-refusal-line)
                                cdr-cons)
                              (theory 'minimal-theory)))))

(defthm fn-otm-cfg-with-allow-allow
  (equal (fn-inj-config-allow (fn-otm-cfg-with-allow cfg allow)) allow)
  :hints (("Goal" :in-theory (enable fn-inj-config-allow fn-inj-nth fn-inj-car))))

(local
 (defthm fn-otm-ocfg-owner-of-with-owner
   (equal (fn-ocfg-owner (fn-ocfg-with-owner oc o)) o)
   :hints (("Goal" :in-theory (enable fn-ocfg-owner fn-ocfg-with-owner fn-ocfg-make)))))

(local
 (defthm fn-otm-conns-of-set-conns
   (equal (fn-own-conns (fn-own-set-conns o conns)) conns)
   :hints (("Goal" :in-theory (enable fn-own-conns fn-own-set-conns fn-own-make)))))

; The seventh field of a record of the owner's shape, replaced (the proof
; with update-nth open cost 840,000 prover steps; this one, a few thousand).
(local
 (defthm fn-otm-update-nth-6-shape
   (implies (and (true-listp c) (< 6 (len c)))
            (and (equal (car (update-nth 6 v c)) (car c))
                 (equal (car (cdr (cdr (cdr (cdr (cdr (cdr (update-nth 6 v c)))))))) v)))
   :hints (("Goal" :expand ((update-nth 6 v c) (update-nth 5 v (cdr c)) (update-nth 4 v (cddr c))
                            (update-nth 3 v (cdddr c)) (update-nth 2 v (cddddr c))
                            (update-nth 1 v (cdr (cddddr c))) (update-nth 0 v (cddr (cddddr c))))
            :in-theory (disable update-nth)))))

(local
 (defthm fn-otm-conn-with-allow-id-and-config
   (and (equal (fn-own-conn-id (fn-otm-conn-with-allow c allow)) (fn-own-conn-id c))
        (implies (and (true-listp c) (< 6 (len c)))
                 (equal (fn-own-conn-config (fn-otm-conn-with-allow c allow))
                        (fn-otm-cfg-with-allow (fn-own-conn-config c) allow))))
   :hints (("Goal" :in-theory (union-theories '(fn-own-conn-id fn-own-conn-config
                                                fn-otm-conn-with-allow)
                                              (theory 'minimal-theory))
            :expand ((update-nth 6 (fn-otm-cfg-with-allow (fn-own-conn-config c) allow) c))
            :use ((:instance fn-otm-update-nth-6-shape
                             (v (fn-otm-cfg-with-allow
                                 (car (cdr (cdr (cdr (cdr (cdr (cdr c))))))) allow))))))))

(local
 (defthm fn-otm-find-conn-of-replace-same
   (implies (and (fn-own-find-conn id conns) (equal (fn-own-conn-id c) id))
            (equal (fn-own-find-conn id (fn-own-replace-conn c conns)) c))
   :hints (("Goal" :in-theory (enable fn-own-find-conn fn-own-replace-conn)))))

(local
 (defthm fn-otm-find-conn-id
   (implies (fn-own-find-conn id conns)
            (equal (fn-own-conn-id (fn-own-find-conn id conns)) id))
   :hints (("Goal" :in-theory (enable fn-own-find-conn)))))

;; The refused-offer memory is the owner's fifteenth field; the exchange
;; touches it and nothing the posting bit or the connections read.
(local
 (defthm fn-otm-with-refused-fields
   (let ((o2 (fn-ocfg-owner (fn-otm-ocfg-with-refused oc mem))))
     (and (equal (fn-own-refused o2) mem)
          (equal (fn-own-conns o2) (fn-own-conns (fn-ocfg-owner oc)))))
   :hints (("Goal" :in-theory (enable fn-own-conns fn-own-refused fn-own-make)))))

(local
 (defthm fn-otm-conn-allow-of-with-refused
   (equal (fn-otm-conn-allow (fn-otm-ocfg-with-refused oc mem) id)
          (fn-otm-conn-allow oc id))
   :hints (("Goal" :in-theory (e/d (fn-otm-conn-allow) (fn-otm-ocfg-with-refused))))))

(local
 (defthm fn-otm-refused-of-with-allow
   (equal (fn-own-refused (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow)))
          (fn-own-refused (fn-ocfg-owner oc)))
   :hints (("Goal" :in-theory (enable fn-otm-owner-with-allow fn-own-refused fn-own-set-conns
                                      fn-own-make)))))

;; The posture's entries never outlive the read: after the strip no lookup
;; of the posture's key finds one, so no session re-pinned later is under it.
(defthm fn-otm-strip-shed-leaves-no-posture
  (not (fn-rof-lookup :disk-slow (fn-otm-strip-shed mem)))
  :hints (("Goal" :in-theory (enable fn-rof-lookup))))

;; And a memory the posture never touched comes back as it was.
(defun fn-otm-shed-free-p (mem)
  (declare (xargs :guard t))
  (if (consp mem)
      (and (not (and (consp (car mem)) (equal (car (car mem)) :disk-slow)))
           (fn-otm-shed-free-p (cdr mem)))
    t))

(defthm fn-otm-strip-shed-of-marked
  (implies (fn-otm-shed-free-p mem)
           (equal (fn-otm-strip-shed (cons *fn-peer-shed-entry* mem)) mem)))

;; The disk's lines replace the generic ones and nothing else: no generic
;; 440 or posting-disallowed 441 is left, as many effects as before, and an
;; effect that is neither is kept.
(defthm fn-otm-disk-effects-names-the-disk
  (implies (and (not (equal (fn-nntp-reply-effect l440) *fn-otm-generic-440*))
                (not (equal (fn-nntp-reply-effect l441) *fn-otm-generic-441*))
                (not (equal (fn-nntp-reply-effect l440) *fn-otm-generic-441*))
                (not (equal (fn-nntp-reply-effect l441) *fn-otm-generic-440*)))
           (let ((es (fn-otm-disk-effects effects l440 l441)))
             (and (not (member-equal *fn-otm-generic-440* es))
                  (not (member-equal *fn-otm-generic-441* es))
                  (equal (len es) (len effects)))))
  :hints (("Goal" :in-theory (disable fn-nntp-reply-effect))))

(defthm fn-otm-disk-effects-keeps-the-rest
  (implies (and (not (member-equal *fn-otm-generic-440* effects))
                (not (member-equal *fn-otm-generic-441* effects))
                (true-listp effects))
           (equal (fn-otm-disk-effects effects l440 l441) effects)))

(local
 (defthm fn-otm-shed-read-posting-off
   (let ((c (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
     (implies (and c (fn-own-conn-shapep c))
              (not (fn-otm-conn-allow (fn-otm-shed-ocfg oc id) id))))
   :hints (("Goal" :in-theory (e/d (fn-otm-shed-ocfg fn-otm-owner-with-allow fn-otm-conn-allow
                                    fn-own-conn-shapep)
                                   (fn-otm-cfg-with-allow fn-orr-read-span fn-own-find-conn
                                    fn-own-replace-conn fn-otm-conn-with-allow
                                    fn-otm-ocfg-with-refused))))))

(local
 (defthm fn-otm-shed-read-posture
   (fn-peer-shed-p (fn-peer-with-refused ps (fn-own-refused (fn-ocfg-owner (fn-otm-shed-ocfg oc id)))))
   :hints (("Goal" :in-theory (e/d (fn-otm-shed-ocfg fn-peer-shed-p fn-rof-lookup)
                                   (fn-otm-ocfg-with-refused fn-otm-owner-with-allow))))))

(local
 (defthm fn-otm-shed-read-effects
   (implies (eq (fn-otm-admit-post s) :shed)
            (equal (fn-own-tls-result-effects
                    (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat))
                   (if (fn-otm-conn-allow oc id)
                       (fn-otm-disk-effects
                        (fn-own-tls-result-effects
                         (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end cache
                                           fn-octets fn-arena fn-cat))
                        (fn-otm-post-command-reply s) (fn-otm-shed-reply s))
                     (fn-own-tls-result-effects
                      (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end cache
                                        fn-octets fn-arena fn-cat)))))
   :hints (("Goal" :in-theory (e/d (fn-otm-read-span)
                                   (fn-orr-read-span fn-otm-shed-ocfg fn-otm-unshed-ocfg
                                    fn-otm-conn-allow fn-otm-disk-effects
                                    fn-otm-post-command-reply fn-otm-shed-reply
                                    fn-otm-admit-post))))))

(local
 (defthm fn-otm-shed-read-restores-the-bit
   (implies (and (eq (fn-otm-admit-post s) :shed)
                 (fn-own-conn-shapep
                  (fn-own-find-conn id (fn-own-conns
                                        (fn-ocfg-owner
                                         (fn-own-tls-result-owner
                                          (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end cache
                                                            fn-octets fn-arena fn-cat)))))))
            (equal (fn-otm-conn-allow
                    (fn-own-tls-result-owner
                     (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat))
                    id)
                   (fn-otm-conn-allow oc id)))
   :hints (("Goal" :in-theory (e/d (fn-otm-read-span fn-otm-unshed-ocfg fn-otm-owner-with-allow
                                    fn-otm-conn-allow fn-own-conn-shapep)
                                   (fn-orr-read-span fn-otm-shed-ocfg fn-otm-cfg-with-allow
                                    fn-own-find-conn fn-own-replace-conn fn-otm-conn-with-allow
                                    fn-otm-ocfg-with-refused fn-otm-disk-effects
                                    fn-otm-admit-post))))))

(local
 (defthm fn-otm-shed-read-strips-the-posture
   (implies (eq (fn-otm-admit-post s) :shed)
            (equal (fn-own-refused
                    (fn-ocfg-owner
                     (fn-own-tls-result-owner
                      (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat))))
                   (fn-otm-strip-shed
                    (fn-own-refused
                     (fn-ocfg-owner
                      (fn-own-tls-result-owner
                       (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end cache
                                         fn-octets fn-arena fn-cat)))))))
   :hints (("Goal" :in-theory (e/d (fn-otm-read-span fn-otm-unshed-ocfg)
                                   (fn-orr-read-span fn-otm-shed-ocfg fn-otm-owner-with-allow
                                    fn-otm-ocfg-with-refused fn-otm-disk-effects
                                    fn-otm-admit-post))))))

;; KEYSTONE (PRF-323, slice 2: 440 at the command; extended by lane
;; log-leftovers: the disk's reason on the wire, PKT-858's posture).
;; Connection ID's read while the disk sheds at the gate's value S:
;;  - runs with posting not permitted (when its record has the shape the
;;    owner makes) and under the disk-slow posture: a peer session re-pinned
;;    with the read's refused-offer memory is fn-peer-shed-p, so every
;;    well-formed offer is :defer :disk-slow (fn-peer-shed-offer-is-disk-slow);
;;  - its effects are that read's, with each generic 440 and posting-
;;    disallowed 441 replaced by ACL2's disk lines (fn-otm-post-command-reply,
;;    fn-otm-shed-reply at S) exactly when the connection's posting bit was on
;;    before the read (the refusal is the disk's); with the bit off they are
;;    the read's own (the configuration refuses, not the disk);
;;  - afterwards the connection, if still open, has the posting bit it had
;;    before, and the refused-offer memory is the read's with the posture's
;;    entries out.
;; The slow disk changes what this read answers, never the node's or the
;; connection's configuration.
(defthm fn-otm-read-span-while-shedding
  (implies (eq (fn-otm-admit-post s) :shed)
           (let* ((shed (fn-otm-shed-ocfg oc id))
                  (inner (fn-orr-read-span shed views id i end cache fn-octets fn-arena fn-cat))
                  (r (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat))
                  (c (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
             (and (implies (and c (fn-own-conn-shapep c))
                           (not (fn-otm-conn-allow shed id)))
                  (fn-peer-shed-p (fn-peer-with-refused ps (fn-own-refused (fn-ocfg-owner shed))))
                  (equal (fn-own-tls-result-effects r)
                         (if (fn-otm-conn-allow oc id)
                             (fn-otm-disk-effects (fn-own-tls-result-effects inner)
                                                  (fn-otm-post-command-reply s)
                                                  (fn-otm-shed-reply s))
                           (fn-own-tls-result-effects inner)))
                  (implies (fn-own-conn-shapep
                            (fn-own-find-conn id (fn-own-conns
                                                  (fn-ocfg-owner
                                                   (fn-own-tls-result-owner inner)))))
                           (equal (fn-otm-conn-allow (fn-own-tls-result-owner r) id)
                                  (fn-otm-conn-allow oc id)))
                  (equal (fn-own-refused (fn-ocfg-owner (fn-own-tls-result-owner r)))
                         (fn-otm-strip-shed
                          (fn-own-refused (fn-ocfg-owner (fn-own-tls-result-owner inner))))))))
  :hints (("Goal" :in-theory (union-theories '(fn-otm-shed-read-posting-off
                                                fn-otm-shed-read-posture
                                                fn-otm-shed-read-effects
                                                fn-otm-shed-read-restores-the-bit
                                                fn-otm-shed-read-strips-the-posture)
                                              (theory 'minimal-theory)))))

;; The peer read's class (host/native/mux.lisp fnn-mux-step through
;; host/native/owner.lisp fnn-owner-peer-read-class): a reader-class peer
;; read runs only while the disk sheds, so it is never a reader-view read of
;; the live node without the posture.
(defthm fn-otm-peer-reader-read-only-while-shedding
  (implies (and (equal class :reader) (fn-otm-peer-read-proceeds-p class s))
           (equal (fn-otm-admit-post s) :shed))
  :rule-classes nil)

(defthm fn-otm-peer-read-class-is-reader-exactly-while-shedding
  (iff (equal (fn-otm-peer-read-class s) :reader)
       (equal (fn-otm-admit-post s) :shed)))

;; The command step under a configuration that does not permit posting:
;; a POST is never offered -- the session never awaits an article -- so no
;; article is read and nothing is submitted; RFC 3977 section 6.3.1's 440
;; is the reply fn-scr-post-step renders.
(defthm fn-otm-closed-posting-never-awaits-an-article
  (implies (and (fn-post-sessionp ps)
                (not (fn-post-session-awaiting ps))
                (not (fn-inj-config-allow config)))
           (not (fn-post-session-awaiting
                 (fn-post-result-session
                  (fn-scr-post-step ps archive index verdicts config observation injection
                                    wire-event v fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-post-step
                                fn-post-result-session-of-fn-post-make-result
                                fn-post-session-awaiting-of-fn-post-make-session)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-otm-read-span fn-otm-owner-with-allow fn-otm-conn-allow
                    fn-otm-shed-ocfg fn-otm-unshed-ocfg fn-otm-ocfg-with-refused))
