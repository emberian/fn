; fn: what the owner holds in flight, across reads (lane admission-gap,
; 2026-09-28; PRF-377's frame, invariant and completion policy).
;
; books/owner-article-slots.lisp admits a read by what the owner holds after
; it (fn-oas-held: the connections in article mode, the queued submissions,
; the batch in flight).  This book shows three facts about the host's read,
; fn-oas-read-span (host/owner-host.lisp fn-owner-chunk-span-at), from the
; shape of every layer under it: each touches connection ID's record only
; (fn-scar-finish-read replaces or removes it and enqueues at most the one
; decision the read's effects carry; fn-ocfg-with-read-owner only pins;
; fn-orr-read-span only swaps the view; the shed read only ID's posting bit
; and the refused-offer memory; the refusal tiers only ID's wire).
;
; KEYSTONE `fn-oah-read-span-leaves-the-others-article-mode' (the frame): a
; read of connection ID leaves every other connection's record, and with it
; its wire mode, as it was.
; KEYSTONE `fn-oah-read-span-keeps-held-within-the-slots' (the invariant):
; a read from an owner holding at most SLOTS leaves it holding at most SLOTS,
; whatever connection it is and whatever the read carried -- in particular
; a TAKETHIS (RFC 4644 section 2.5), a pipelined IHAVE or a small POST whose
; command and whole article arrive in one socket read, which enters article
; mode and leaves it within the read with one more submission queued.
; Every read therefore keeps "held <= slots": a sequence of reads of any
; connections starting within the slots stays within them.
; KEYSTONE `fn-oas-read-span-never-blocks-an-admitted-article' (reserve-to-
; finish): a connection in article mode reads exactly as the read before
; the slots whenever its read completes the article or only continues it;
; `fn-oah-admitted-read-keeps-what-it-completed': otherwise (the read
; completed the article and began another) the result is that read with the
; begun article closed -- what the read completed is kept, the whole-read
; refusal is unreachable for an admitted connection.
;
; Not claimed here: the queue's growth by the control channel and BP
; deliveries (no connection's read; their heap is the figure's in-flight
; request); that the served fold stops after one submission (PKT-600) --
; the theorems hold without it.

(in-package "ACL2")
(include-book "owner-article-slots")

; -----------------------------------------------------------------------------
; The connection list: ID's records replaced or removed.

(defun fn-oah-count (conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (+ (if (fn-oas-conn-articlep (car conns)) 1 0) (fn-oah-count (cdr conns)))
    0))

(defun fn-oah-bit (c)
  (declare (xargs :guard t))
  (if (fn-oas-conn-articlep c) 1 0))

(local
 (defthm fn-oah-article-conns-onto-is-count
   (implies (acl2-numberp n)
            (equal (fn-oas-article-conns-onto conns n) (+ n (fn-oah-count conns))))
   :hints (("Goal" :in-theory (disable fn-oas-conn-articlep)))))

(defthm fn-oah-article-conns-is-count
  (equal (fn-oas-article-conns conns) (fn-oah-count conns)))

(defthm fn-oah-remove-of-replace
  (implies (equal (fn-own-conn-id c) id)
           (equal (fn-own-remove-conn id (fn-own-replace-conn c conns))
                  (fn-own-remove-conn id conns)))
  :hints (("Goal" :in-theory (enable fn-own-remove-conn fn-own-replace-conn))))

(defthm fn-oah-remove-of-remove
  (equal (fn-own-remove-conn id (fn-own-remove-conn id conns))
         (fn-own-remove-conn id conns))
  :hints (("Goal" :in-theory (enable fn-own-remove-conn))))

(defthm fn-oah-find-of-remove-other
  (implies (not (equal id2 id))
           (equal (fn-own-find-conn id2 (fn-own-remove-conn id conns))
                  (fn-own-find-conn id2 conns)))
  :hints (("Goal" :in-theory (enable fn-own-remove-conn fn-own-find-conn))))

(defthm fn-oah-find-of-remove-same
  (not (fn-own-find-conn id (fn-own-remove-conn id conns)))
  :hints (("Goal" :in-theory (enable fn-own-remove-conn fn-own-find-conn))))

(defthm fn-oah-find-of-replace-same
  (implies (and (fn-own-find-conn id conns) (equal (fn-own-conn-id c) id))
           (equal (fn-own-find-conn id (fn-own-replace-conn c conns)) c))
  :hints (("Goal" :in-theory (enable fn-own-find-conn fn-own-replace-conn))))

(defthm fn-oah-find-conn-id
  (implies (fn-own-find-conn id conns)
           (equal (fn-own-conn-id (fn-own-find-conn id conns)) id))
  :hints (("Goal" :in-theory (enable fn-own-find-conn))))

;; ID's records other than the first in article mode: EXTRA.
(defun fn-oah-extra (conns id)
  (declare (xargs :guard t))
  (- (- (fn-oah-count conns) (fn-oah-count (fn-own-remove-conn id conns)))
     (fn-oah-bit (fn-own-find-conn id conns))))

(local
 (defthm fn-oah-count-of-remove
   (and (<= (fn-oah-count (fn-own-remove-conn id conns)) (fn-oah-count conns))
        (implies (fn-oas-conn-articlep (fn-own-find-conn id conns))
                 (<= (+ 1 (fn-oah-count (fn-own-remove-conn id conns)))
                     (fn-oah-count conns))))
   :hints (("Goal" :induct (fn-own-remove-conn id conns)
            :in-theory (e/d (fn-own-remove-conn fn-own-find-conn) (fn-oas-conn-articlep))))
   :rule-classes :linear))

(defthm fn-oah-extra-nonneg
  (<= 0 (fn-oah-extra conns id))
  :hints (("Goal" :in-theory (disable fn-oas-conn-articlep fn-oah-count)))
  :rule-classes :linear)

(defthm fn-oah-extra-of-replace
  (implies (and (fn-own-find-conn id conns) (equal (fn-own-conn-id c) id))
           (equal (fn-oah-extra (fn-own-replace-conn c conns) id)
                  (fn-oah-extra conns id)))
  :hints (("Goal" :in-theory (e/d (fn-own-remove-conn fn-own-replace-conn fn-own-find-conn)
                                  (fn-oas-conn-articlep)))))

(defthm fn-oah-extra-of-remove
  (equal (fn-oah-extra (fn-own-remove-conn id conns) id) 0))

(in-theory (disable fn-oah-extra fn-oah-bit fn-oah-count))

; -----------------------------------------------------------------------------
; The quantities of an owner record, and the layers that keep them.

(defun fn-oah-others (o id)
  (declare (xargs :guard t))
  (fn-own-remove-conn id (fn-own-conns o)))

(defun fn-oah-art (o id)
  (declare (xargs :guard t))
  (fn-oah-bit (fn-own-find-conn id (fn-own-conns o))))

(defun fn-oah-ex (o id)
  (declare (xargs :guard t))
  (fn-oah-extra (fn-own-conns o) id))

(in-theory (disable fn-oah-others fn-oah-art fn-oah-ex))

;; What the owner holds, by the quantities.
(defthm fn-oah-held-is
  (equal (fn-oas-held oc)
         (+ (fn-oah-count (fn-oah-others (fn-ocfg-owner oc) id))
            (fn-oah-ex (fn-ocfg-owner oc) id)
            (fn-oah-art (fn-ocfg-owner oc) id)
            (len (fn-own-queue (fn-ocfg-owner oc)))
            (fn-oas-inflight-count (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-oas-held fn-oah-extra fn-oah-others fn-oah-ex fn-oah-art))))

(defthm fn-oah-articlep-is-art
  (equal (fn-oas-articlep oc id)
         (equal (fn-oah-art (fn-ocfg-owner oc) id) 1))
  :hints (("Goal" :in-theory (enable fn-oas-articlep fn-oah-bit fn-oah-art))))

(defthm fn-oah-art-bound
  (<= (fn-oah-art o id) 1)
  :hints (("Goal" :in-theory (enable fn-oah-art fn-oah-bit)))
  :rule-classes :linear)

(defthm fn-oah-art-natp
  (natp (fn-oah-art o id))
  :hints (("Goal" :in-theory (enable fn-oah-art fn-oah-bit)))
  :rule-classes :type-prescription)

;; KEEPS O2 O ID: every quantity the same.
(defun-nx fn-oah-keeps (o2 o id)
  (and (equal (fn-oah-others o2 id) (fn-oah-others o id))
       (equal (fn-oah-ex o2 id) (fn-oah-ex o id))
       (equal (fn-oah-art o2 id) (fn-oah-art o id))
       (equal (fn-own-queue o2) (fn-own-queue o))
       (equal (fn-own-inflight o2) (fn-own-inflight o))))

;; STEPS O2 O ID: a read's change -- the others and the batch as they were,
;; at most one more submission queued, no more extra records.
(defun-nx fn-oah-steps (o2 o id)
  (and (equal (fn-oah-others o2 id) (fn-oah-others o id))
       (<= (fn-oah-ex o2 id) (fn-oah-ex o id))
       (<= (len (fn-own-queue o2)) (+ 1 (len (fn-own-queue o))))
       (equal (fn-own-inflight o2) (fn-own-inflight o))))

(defthm fn-oah-steps-after-keeps
  (implies (and (fn-oah-keeps o3 o2 id) (fn-oah-steps o2 o1 id) (fn-oah-keeps o1 o id))
           (fn-oah-steps o3 o id)))

(defthm fn-oah-keeps-refl
  (fn-oah-keeps o o id))

(defthm fn-oah-steps-refl
  (fn-oah-steps o o id))

(local
 (defthm fn-oah-owner-accessors-of-make
   (and (equal (fn-own-conns (fn-own-make store view conns next-id max-conns pending ledger clock
                                          facts config queue inflight feeds node-secret refused))
               conns)
        (equal (fn-own-queue (fn-own-make store view conns next-id max-conns pending ledger clock
                                          facts config queue inflight feeds node-secret refused))
               queue)
        (equal (fn-own-inflight (fn-own-make store view conns next-id max-conns pending ledger clock
                                             facts config queue inflight feeds node-secret refused))
               inflight))
   :hints (("Goal" :in-theory (enable fn-own-conns fn-own-queue fn-own-inflight fn-own-make)))))

(local
 (defthm fn-oah-ocfg-owner-of-make
   (equal (fn-ocfg-owner (fn-ocfg-make owner config pins staged)) owner)
   :hints (("Goal" :in-theory (enable fn-ocfg-owner fn-ocfg-make)))))

(local
 (defthm fn-oah-tls-accessors
   (and (equal (fn-own-tls-result-owner (fn-own-tls-make-result consumed effects owner repinned))
               owner)
        (equal (fn-own-tls-result-consumed (fn-own-tls-make-result consumed effects owner repinned))
               consumed)
        (equal (fn-own-tls-result-effects (fn-own-tls-make-result consumed effects owner repinned))
               effects)
        (equal (fn-own-tls-result-repinned (fn-own-tls-make-result consumed effects owner repinned))
               repinned))
   :hints (("Goal" :in-theory (enable fn-own-tls-result-owner fn-own-tls-result-consumed
                                      fn-own-tls-result-effects fn-own-tls-result-repinned
                                      fn-own-tls-make-result)))))

; The posting bit: ID's record with another configuration, same id, same wire.
(local
 (defthm fn-oah-conn-with-allow-fields
   (and (equal (fn-own-conn-id (fn-otm-conn-with-allow c allow)) (fn-own-conn-id c))
        (equal (fn-oas-conn-articlep (fn-otm-conn-with-allow c allow))
               (fn-oas-conn-articlep c)))
   :hints (("Goal" :in-theory (enable fn-otm-conn-with-allow fn-own-conn-id fn-own-conn-wire
                                      fn-oas-conn-articlep)))))

(local
 (defthm fn-oah-bit-of-with-allow
   (equal (fn-oah-bit (fn-otm-conn-with-allow c allow)) (fn-oah-bit c))
   :hints (("Goal" :in-theory (e/d (fn-oah-bit) (fn-otm-conn-with-allow fn-oas-conn-articlep))))))

(defthm fn-oah-with-allow-keeps
  (fn-oah-keeps (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow)) (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (e/d (fn-otm-owner-with-allow fn-ocfg-with-owner fn-own-set-conns
                                   fn-oah-others fn-oah-ex fn-oah-art)
                                  (fn-otm-conn-with-allow fn-own-replace-conn fn-own-find-conn
                                   fn-own-remove-conn fn-oas-conn-articlep)))))

(defthm fn-oah-with-refused-keeps
  (fn-oah-keeps (fn-ocfg-owner (fn-otm-ocfg-with-refused oc mem)) (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (enable fn-otm-ocfg-with-refused fn-ocfg-with-owner
                                     fn-oah-others fn-oah-ex fn-oah-art))))

(defthm fn-oah-with-view-keeps
  (fn-oah-keeps (fn-ocfg-owner (fn-ocfg-with-view oc v)) (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (enable fn-ocfg-with-view fn-own-with-view fn-ocfg-with-owner
                                     fn-oah-others fn-oah-ex fn-oah-art))))

(defthm fn-oah-at-reader-view-keeps
  (fn-oah-keeps (fn-ocfg-owner (fn-ocfg-at-reader-view oc views)) (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (union-theories '(fn-ocfg-at-reader-view fn-oah-keeps-refl)
                                              (theory 'minimal-theory))
           :use ((:instance fn-oah-with-view-keeps
                            (v (fn-ocv-reader-view views (fn-own-view (fn-ocfg-owner oc)))))))))

(defthm fn-oah-with-read-owner-owner
  (equal (fn-ocfg-owner (fn-ocfg-with-read-owner oc id o repinned)) o)
  :hints (("Goal" :in-theory (enable fn-ocfg-with-read-owner))))

(in-theory (disable fn-oah-keeps))

; -----------------------------------------------------------------------------
; The read itself: fn-scar-finish-read replaces or removes ID's record and
; enqueues at most one decision.

(local
 (defthm fn-oah-enqueue-fields
   (and (equal (fn-own-conns (fn-own-enqueue o sub)) (fn-own-conns o))
        (equal (len (fn-own-queue (fn-own-enqueue o sub))) (+ 1 (len (fn-own-queue o))))
        (equal (fn-own-inflight (fn-own-enqueue o sub)) (fn-own-inflight o)))
   :hints (("Goal" :in-theory (enable fn-own-enqueue fn-ag-append)))))

(local
 (defthm fn-oah-set-conns-fields
   (and (equal (fn-own-conns (fn-own-set-conns o conns)) conns)
        (equal (fn-own-queue (fn-own-set-conns o conns)) (fn-own-queue o))
        (equal (fn-own-inflight (fn-own-set-conns o conns)) (fn-own-inflight o)))
   :hints (("Goal" :in-theory (enable fn-own-set-conns)))))

(defthm fn-oah-finish-read-steps
  (implies (and (equal conn (fn-own-find-conn id (fn-own-conns o))) conn)
           (fn-oah-steps (cdr (fn-scar-finish-read o conn result live)) o id))
  :hints (("Goal" :in-theory (e/d (fn-scar-finish-read fn-oah-others fn-oah-ex fn-oah-art)
                                  (fn-own-enqueue fn-own-set-conns fn-own-replace-conn
                                   fn-own-remove-conn fn-own-find-conn fn-scar-conn-boundedp
                                   fn-own-sub-make-author fn-served-submission
                                   fn-own-conn-make-group-indexed)))))

(defthm fn-oah-scr-own-read-span-steps
  (fn-oah-steps (fn-own-tls-result-owner
                 (fn-scr-own-read-span o id i end fn-octets fn-arena fn-cat))
                o id)
  :hints (("Goal" :in-theory (e/d (fn-scr-own-read-span)
                                  (fn-scar-finish-read fn-oah-steps fn-scr-step-span-fast
                                   fn-own-find-conn)))))

(defthm fn-oah-scr-ocfg-read-span-steps
  (fn-oah-steps (fn-ocfg-owner (fn-own-tls-result-owner
                                (fn-scr-ocfg-read-span oc id i end fn-octets fn-arena fn-cat)))
                (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (e/d (fn-scr-ocfg-read-span)
                                  (fn-scr-own-read-span fn-oah-steps fn-ocfg-with-read-owner)))))

(defthm fn-oah-orr-read-span-steps
  (fn-oah-steps (fn-ocfg-owner (fn-own-tls-result-owner
                                (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat)))
                (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (union-theories '(fn-orr-read-span fn-oah-tls-accessors)
                                             (theory 'minimal-theory))
           :use ((:instance fn-oah-steps-after-keeps
                            (o3 (fn-ocfg-owner
                                 (fn-ocfg-with-view
                                  (fn-own-tls-result-owner
                                   (fn-scr-ocfg-read-span (fn-ocfg-at-reader-view oc views)
                                                          id i end fn-octets fn-arena fn-cat))
                                  (fn-own-view (fn-ocfg-owner oc)))))
                            (o2 (fn-ocfg-owner
                                 (fn-own-tls-result-owner
                                  (fn-scr-ocfg-read-span (fn-ocfg-at-reader-view oc views)
                                                         id i end fn-octets fn-arena fn-cat))))
                            (o1 (fn-ocfg-owner (fn-ocfg-at-reader-view oc views)))
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-oah-with-view-keeps
                            (oc (fn-own-tls-result-owner
                                 (fn-scr-ocfg-read-span (fn-ocfg-at-reader-view oc views)
                                                        id i end fn-octets fn-arena fn-cat)))
                            (v (fn-own-view (fn-ocfg-owner oc))))
                 (:instance fn-oah-scr-ocfg-read-span-steps
                            (oc (fn-ocfg-at-reader-view oc views)))
                 (:instance fn-oah-scr-ocfg-read-span-steps)
                 (:instance fn-oah-at-reader-view-keeps)))))

;; The shed read's two owner changes: ID's posting bit and the memory.
(defthm fn-oah-keeps-trans
  (implies (and (fn-oah-keeps o2 o1 id) (fn-oah-keeps o1 o id))
           (fn-oah-keeps o2 o id))
  :hints (("Goal" :in-theory (enable fn-oah-keeps))))

(defthm fn-oah-shed-ocfg-keeps
  (fn-oah-keeps (fn-ocfg-owner (fn-otm-shed-ocfg oc id)) (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (union-theories '(fn-otm-shed-ocfg) (theory 'minimal-theory))
           :use ((:instance fn-oah-keeps-trans
                            (o2 (fn-ocfg-owner (fn-otm-shed-ocfg oc id)))
                            (o1 (fn-ocfg-owner (fn-otm-owner-with-allow oc id nil)))
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-oah-with-refused-keeps
                            (oc (fn-otm-owner-with-allow oc id nil))
                            (mem (cons *fn-peer-shed-entry*
                                       (fn-own-refused
                                        (fn-ocfg-owner (fn-otm-owner-with-allow oc id nil))))))
                 (:instance fn-oah-with-allow-keeps (allow nil))))))

(defthm fn-oah-unshed-ocfg-keeps
  (fn-oah-keeps (fn-ocfg-owner (fn-otm-unshed-ocfg oc id allow)) (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (union-theories '(fn-otm-unshed-ocfg) (theory 'minimal-theory))
           :use ((:instance fn-oah-keeps-trans
                            (o2 (fn-ocfg-owner (fn-otm-unshed-ocfg oc id allow)))
                            (o1 (fn-ocfg-owner
                                 (fn-otm-ocfg-with-refused
                                  oc (fn-otm-strip-shed (fn-own-refused (fn-ocfg-owner oc))))))
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-oah-with-refused-keeps
                            (mem (fn-otm-strip-shed (fn-own-refused (fn-ocfg-owner oc)))))
                 (:instance fn-oah-with-allow-keeps
                            (oc (fn-otm-ocfg-with-refused
                                 oc (fn-otm-strip-shed (fn-own-refused (fn-ocfg-owner oc))))))))))

;; The host's read before the slots (the shed read included).
(defthm fn-oah-otm-read-span-steps
  (fn-oah-steps (fn-ocfg-owner (fn-own-tls-result-owner
                                (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat)))
                (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (union-theories '(fn-otm-read-span fn-oah-tls-accessors)
                                             (theory 'minimal-theory))
           :use ((:instance fn-oah-steps-after-keeps
                            (o3 (fn-ocfg-owner
                                 (fn-otm-unshed-ocfg
                                  (fn-own-tls-result-owner
                                   (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end
                                                     fn-octets fn-arena fn-cat))
                                  id (fn-otm-conn-allow oc id))))
                            (o2 (fn-ocfg-owner
                                 (fn-own-tls-result-owner
                                  (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end
                                                    fn-octets fn-arena fn-cat))))
                            (o1 (fn-ocfg-owner (fn-otm-shed-ocfg oc id)))
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-oah-unshed-ocfg-keeps
                            (oc (fn-own-tls-result-owner
                                 (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end
                                                   fn-octets fn-arena fn-cat)))
                            (allow (fn-otm-conn-allow oc id)))
                 (:instance fn-oah-shed-ocfg-keeps)
                 (:instance fn-oah-orr-read-span-steps (oc (fn-otm-shed-ocfg oc id)))
                 (:instance fn-oah-orr-read-span-steps)))))

(in-theory (disable fn-oah-steps))

; -----------------------------------------------------------------------------
; The refusal tiers.



; -----------------------------------------------------------------------------
; The refusal tiers touch ID's record only.

(local
 (defthm fn-oah-bit-of-closed
   (equal (fn-oah-bit (fn-oas-conn-closed c)) 0)
   :hints (("Goal" :in-theory (e/d (fn-oah-bit) (fn-oas-conn-closed fn-oas-conn-articlep))))))

(local
 (defthm fn-oah-ocfg-owner-of-with-owner
   (equal (fn-ocfg-owner (fn-ocfg-with-owner oc o)) o)
   :hints (("Goal" :in-theory (enable fn-ocfg-with-owner)))))

;; Closing ID: the others, the extra records, the queue and the batch as they
;; were; ID not in article mode.
(defthm fn-oah-owner-closed-fields
  (let ((o2 (fn-ocfg-owner (fn-oas-owner-closed oc id)))
        (o (fn-ocfg-owner oc)))
    (and (equal (fn-oah-others o2 id) (fn-oah-others o id))
         (equal (fn-oah-ex o2 id) (fn-oah-ex o id))
         (equal (fn-oah-art o2 id) 0)
         (equal (fn-own-queue o2) (fn-own-queue o))
         (equal (fn-own-inflight o2) (fn-own-inflight o))))
  :hints (("Goal" :in-theory (e/d (fn-oas-owner-closed fn-oah-others fn-oah-ex fn-oah-art)
                                  (fn-oas-conn-closed fn-own-replace-conn fn-own-find-conn
                                   fn-own-remove-conn fn-own-set-conns fn-oas-conn-articlep)))))

(defthm fn-oah-posting-off-read-steps
  (fn-oah-steps (fn-ocfg-owner (fn-own-tls-result-owner
                                (fn-oas-posting-off-read oc views id i end s
                                                         fn-octets fn-arena fn-cat)))
                (fn-ocfg-owner oc) id)
  :hints (("Goal" :in-theory (union-theories '(fn-oas-posting-off-read fn-oah-tls-accessors)
                                             (theory 'minimal-theory))
           :use ((:instance fn-oah-steps-after-keeps
                            (o3 (fn-ocfg-owner
                                 (fn-otm-owner-with-allow
                                  (fn-own-tls-result-owner
                                   (fn-otm-read-span (fn-otm-owner-with-allow oc id nil) views id
                                                     i end s fn-octets fn-arena fn-cat))
                                  id (fn-otm-conn-allow oc id))))
                            (o2 (fn-ocfg-owner
                                 (fn-own-tls-result-owner
                                  (fn-otm-read-span (fn-otm-owner-with-allow oc id nil) views id
                                                    i end s fn-octets fn-arena fn-cat))))
                            (o1 (fn-ocfg-owner (fn-otm-owner-with-allow oc id nil)))
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-oah-with-allow-keeps
                            (oc (fn-own-tls-result-owner
                                 (fn-otm-read-span (fn-otm-owner-with-allow oc id nil) views id
                                                   i end s fn-octets fn-arena fn-cat)))
                            (allow (fn-otm-conn-allow oc id)))
                 (:instance fn-oah-with-allow-keeps (allow nil))
                 (:instance fn-oah-otm-read-span-steps (oc (fn-otm-owner-with-allow oc id nil)))))))

(defthm fn-oah-others-of-close-result
  (equal (fn-oah-others (fn-ocfg-owner (fn-own-tls-result-owner (fn-oas-close-result r id))) id)
         (fn-oah-others (fn-ocfg-owner (fn-own-tls-result-owner r)) id))
  :hints (("Goal" :in-theory (e/d (fn-oas-close-result) (fn-oas-owner-closed)))))

(defthm fn-oah-others-of-whole-refusal
  (equal (fn-oah-others (fn-ocfg-owner (fn-own-tls-result-owner (fn-oas-whole-refusal oc id i end)))
                        id)
         (fn-oah-others (fn-ocfg-owner oc) id))
  :hints (("Goal" :in-theory (e/d (fn-oas-whole-refusal) (fn-oas-owner-closed)))))

(defthm fn-oah-others-of-tiers
  (implies (equal (fn-oah-others (fn-ocfg-owner (fn-own-tls-result-owner r1)) id)
                  (fn-oah-others (fn-ocfg-owner oc) id))
           (equal (fn-oah-others (fn-ocfg-owner (fn-own-tls-result-owner
                                                 (fn-oas-tiers oc r1 id i end slots)))
                                 id)
                  (fn-oah-others (fn-ocfg-owner oc) id)))
  :hints (("Goal" :in-theory (e/d (fn-oas-tiers)
                                  (fn-oas-close-result fn-oas-whole-refusal fn-oas-over-p)))))

(local
 (defthm fn-oah-steps-others
   (implies (fn-oah-steps o2 o id)
            (equal (fn-oah-others o2 id) (fn-oah-others o id)))
   :hints (("Goal" :in-theory (enable fn-oah-steps)))))

(defthm fn-oah-otm-read-span-others
  (equal (fn-oah-others (fn-ocfg-owner (fn-own-tls-result-owner
                                        (fn-otm-read-span oc views id i end s
                                                          fn-octets fn-arena fn-cat)))
                        id)
         (fn-oah-others (fn-ocfg-owner oc) id))
  :hints (("Goal" :in-theory (disable fn-otm-read-span fn-oah-otm-read-span-steps)
           :use fn-oah-otm-read-span-steps)))

(defthm fn-oah-posting-off-read-others
  (equal (fn-oah-others (fn-ocfg-owner (fn-own-tls-result-owner
                                        (fn-oas-posting-off-read oc views id i end s
                                                                 fn-octets fn-arena fn-cat)))
                        id)
         (fn-oah-others (fn-ocfg-owner oc) id))
  :hints (("Goal" :in-theory (disable fn-oas-posting-off-read fn-oah-posting-off-read-steps)
           :use fn-oah-posting-off-read-steps)))

(defthm fn-oah-read-span-others
  (equal (fn-oah-others (fn-ocfg-owner (fn-own-tls-result-owner
                                        (fn-oas-read-span oc views id i end s slots
                                                          fn-octets fn-arena fn-cat)))
                        id)
         (fn-oah-others (fn-ocfg-owner oc) id))
  :hints (("Goal" :in-theory (e/d (fn-oas-read-span)
                                  (fn-otm-read-span fn-oas-posting-off-read fn-oas-tiers
                                   fn-oas-over-p fn-oas-articlep fn-oah-articlep-is-art)))))

;; The frame, as the connection list: every connection other than ID, in
;; order, is as it was.
(defthm fn-oah-read-span-keeps-the-other-records
  (equal (fn-own-remove-conn
          id (fn-own-conns (fn-ocfg-owner (fn-own-tls-result-owner
                                           (fn-oas-read-span oc views id i end s slots
                                                             fn-octets fn-arena fn-cat)))))
         (fn-own-remove-conn id (fn-own-conns (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (e/d (fn-oah-others) (fn-oas-read-span fn-oah-read-span-others))
           :use fn-oah-read-span-others)))

;; KEYSTONE (the frame).  A read of connection ID leaves every other
;; connection's record as it was, and with it the connection's article mode.
(defthm fn-oah-read-span-leaves-the-others-article-mode
  (implies (not (equal id2 id))
           (let ((oc1 (fn-own-tls-result-owner
                       (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat))))
             (and (equal (fn-own-find-conn id2 (fn-own-conns (fn-ocfg-owner oc1)))
                         (fn-own-find-conn id2 (fn-own-conns (fn-ocfg-owner oc))))
                  (equal (fn-oas-articlep oc1 id2) (fn-oas-articlep oc id2)))))
  :hints (("Goal" :in-theory (e/d (fn-oas-articlep)
                                  (fn-oas-read-span fn-oah-read-span-keeps-the-other-records
                                   fn-oah-find-of-remove-other fn-own-find-conn
                                   fn-own-remove-conn fn-oah-articlep-is-art))
           :use ((:instance fn-oah-read-span-keeps-the-other-records)
                 (:instance fn-oah-find-of-remove-other
                            (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-oah-find-of-remove-other
                            (conns (fn-own-conns (fn-ocfg-owner
                                                  (fn-own-tls-result-owner
                                                   (fn-oas-read-span oc views id i end s slots
                                                                     fn-octets fn-arena
                                                                     fn-cat))))))))))

; -----------------------------------------------------------------------------
; The invariant.

;; KEYSTONE (held <= slots between reads).  A read -- of any connection,
;; carrying anything -- from an owner holding at most SLOTS leaves it holding
;; at most SLOTS.
(defthm fn-oah-read-span-keeps-held-within-the-slots
  (implies (<= (fn-oas-held oc) (nfix slots))
           (<= (fn-oas-held (fn-own-tls-result-owner
                             (fn-oas-read-span oc views id i end s slots
                                               fn-octets fn-arena fn-cat)))
               (nfix slots)))
  :hints (("Goal" :in-theory (e/d (fn-oas-over-p)
                                  (fn-oas-read-span fn-oas-held fn-oas-articlep
                                   fn-oas-whole-refusal fn-oah-held-is fn-oah-articlep-is-art))
           :use (fn-oas-read-span-cases
                 (:instance fn-oas-whole-refusal-held)))))

; -----------------------------------------------------------------------------
; The completion policy.

(local
 (defthm fn-oah-steps-bound
   (implies (fn-oah-steps o2 o id)
            (and (equal (fn-oah-others o2 id) (fn-oah-others o id))
                 (<= (fn-oah-ex o2 id) (fn-oah-ex o id))
                 (<= (len (fn-own-queue o2)) (+ 1 (len (fn-own-queue o))))
                 (equal (fn-own-inflight o2) (fn-own-inflight o))))
   :hints (("Goal" :in-theory (enable fn-oah-steps)))))

(defthm fn-oah-otm-read-span-bounds
  (let ((o2 (fn-ocfg-owner (fn-own-tls-result-owner
                            (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat))))
        (o (fn-ocfg-owner oc)))
    (and (<= (fn-oah-ex o2 id) (fn-oah-ex o id))
         (<= (len (fn-own-queue o2)) (+ 1 (len (fn-own-queue o))))
         (equal (fn-oas-inflight-count o2) (fn-oas-inflight-count o))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-oah-steps fn-oas-inflight-count)
                                  (fn-otm-read-span fn-oah-otm-read-span-steps))
           :use fn-oah-otm-read-span-steps)))

;; What the owner holds after the read before the slots, from an admitted
;; connection: at most what it held, plus one when the read left ID in
;; article mode with one more submission queued.
(defthm fn-oah-admitted-otm-held
  (let* ((r (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat))
         (o1 (fn-ocfg-owner (fn-own-tls-result-owner r))))
    (implies (fn-oas-articlep oc id)
             (<= (fn-oas-held (fn-own-tls-result-owner r))
                 (+ (fn-oas-held oc)
                    (fn-oah-art o1 id) -1
                    (- (len (fn-own-queue o1)) (len (fn-own-queue (fn-ocfg-owner oc))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oah-held-is) (fn-otm-read-span fn-oas-held)))))

;; KEYSTONE (no completion deadlock: RESERVE-TO-FINISH).  A connection
;; already in article mode was admitted with a whole article's credit, and
;; the slots never stop a read of it that completes the article or only
;; continues it: that read is the read before this book exactly, whatever the
;; slots and whatever else is held.  An admitted upload therefore completes
;; (or is refused by name past the body limit, books/wire.lisp's
;; :body-overlimit, 441) without waiting for any other, and partial uploads
;; cannot hold the pool in a state where each needs more of it to finish.
(defthm fn-oas-read-span-never-blocks-an-admitted-article
  (let ((r (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat)))
    (implies (and (fn-oas-articlep oc id)
                  (or (not (fn-oas-articlep (fn-own-tls-result-owner r) id))
                      (equal (len (fn-own-queue (fn-ocfg-owner (fn-own-tls-result-owner r))))
                             (len (fn-own-queue (fn-ocfg-owner oc))))))
             (equal (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat)
                    r)))
  :hints (("Goal" :in-theory (e/d (fn-oas-over-p)
                                  (fn-otm-read-span fn-oas-held fn-oah-held-is
                                   fn-oas-read-span-when-held-unfolds))
           :use (fn-oah-admitted-otm-held
                 fn-oas-read-span-when-held-unfolds))))

;; Closing an article-mode connection releases its slot.
(defthm fn-oah-close-result-held
  (equal (fn-oas-held (fn-own-tls-result-owner (fn-oas-close-result r id)))
         (- (fn-oas-held (fn-own-tls-result-owner r))
            (fn-oah-art (fn-ocfg-owner (fn-own-tls-result-owner r)) id)))
  :hints (("Goal" :in-theory (e/d (fn-oas-close-result fn-oah-held-is)
                                  (fn-oas-owner-closed fn-oas-held)))))

;; Otherwise -- the read completed the admitted article and began another
;; -- the host's read is that read with the begun article closed (400 and
;; close): what the read completed is kept, and the whole-read refusal is
;; unreachable for an admitted connection.
(defthm fn-oah-admitted-read-keeps-what-it-completed
  (let ((r (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat)))
    (implies (fn-oas-articlep oc id)
             (or (equal (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat)
                        r)
                 (equal (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat)
                        (fn-oas-close-result r id)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oas-read-span fn-oas-tiers fn-oas-over-p)
                                  (fn-otm-read-span fn-oas-held fn-oah-held-is
                                   fn-oas-close-result fn-oas-whole-refusal
                                   fn-oas-posting-off-read))
           :use (fn-oah-admitted-otm-held
                 (:instance fn-oah-close-result-held
                            (r (fn-otm-read-span oc views id i end s fn-octets fn-arena
                                                 fn-cat)))))))
