; fn: a reader entry during a batch's barrier leaves the owner as it found it,
; and no configuration publication runs under a capture (lane scheduler-3,
; 2026-09-27; coordinator decision PKT-828, continuing lane scheduler-2-rebase).
;
; books/owner-reader-view.lisp runs a reader quantum during a barrier at the
; READER VIEW: the entry runs on the owner with the captured view in place of
; the working view, and the working view is put back after it.  It proved the
; owner at the captured view is related (fn-ocl-relation-of-a-view-captured-
; before-appends); it did not restate the relation AFTER the entry, with the
; working view restored.  This book does, for the function the host calls.
;
;   KEYSTONE fn-orr-read-span-at-a-captured-view-restores-the-owner.  The
;   subject is fn-orr-read-span, which host/owner-host.lisp fn-owner-chunk-span
;   calls for every served socket region (host/native/owner.lisp
;   fnn-owner-handle-chunk through fnn-core-buffer-state): the span read at the
;   reader view while a capture is held, the working view put back.  Under the
;   carried reader relation (books/config-owner-read-invariants.lisp
;   fn-ocri-relation) of the working owner and of the owner at the capture,
;   whose Store has only appended records since under the same configuration
;   history and configuration, and with the carried catalog corresponding to
;   the reader's connection at the captured view (books/served-catalog-chain.lisp
;   fn-scr-owner-catalogp, the premise of the span read's own keystone
;   fn-scr-ocfg-read-span-is-reference-under-ocl-relation), the owner after the
;   entry
;     - is related again (fn-ocri-relation, hence fn-ocl-relation),
;     - has the working view back, and the working owner's Store, next id,
;       connection bound, pending, ledger, clock, facts, configuration and
;       staged record: the entry changes its connections (the reader's
;       session, its pin, a queued submission) and nothing else,
;     - and its reply is the reference read (fn-ocfg-read) of the owner at the
;       captured view over the octets it consumed: the reader reads the
;       durable view, never the batch in flight.
;   With no capture held it is the span read itself.
;
;   KEYSTONE fn-ocvp-reader-view-is-at-the-current-generation.  The keystone
;   above needs the configuration at the capture to be the configuration at
;   the read.  In the capture discipline's publication model (the views of
;   books/owner-reader-view.lisp fn-ocv-capture, each tagged with the
;   configuration generation it was captured under, and a :publish event that
;   is legal only when no capture is held), along every legal run the reader
;   view carries the current generation.  A publication is legal only with no
;   capture held because it runs as the :control class
;   (fn-ocs-publication-class; host/native/owner.lisp fnn-owner-handle-chunk
;   runs an XREDEEM's publication in a quantum of that class, as the control
;   socket's live reconfiguration already runs), which the scheduler never
;   picks while a batch is in flight (fn-ocs-a-publication-waits-for-the-
;   complete), and the committer holds a capture only while a batch is in
;   flight (START captures, COMPLETE with no next batch releases).
(in-package "ACL2")
(include-book "owner-reader-view")
(include-book "served-catalog-chain")
(include-book "config-owner-read-invariants")

; -----------------------------------------------------------------------------
; The host's reader entry (host/owner-host.lisp fn-owner-chunk-span).

(defun fn-orr-read-span (oc views id i end fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (consp views)
      (let ((result (fn-scr-ocfg-read-span (fn-ocfg-at-reader-view oc views)
                                           id i end fn-octets fn-arena fn-cat)))
        (fn-own-tls-make-result
         (fn-own-tls-result-consumed result)
         (fn-own-tls-result-effects result)
         (fn-ocfg-with-view (fn-own-tls-result-owner result)
                            (fn-own-view (fn-ocfg-owner oc)))
         (fn-own-tls-result-repinned result)))
    (fn-scr-ocfg-read-span oc id i end fn-octets fn-arena fn-cat)))

; -----------------------------------------------------------------------------
; The view exchange touches the view and nothing else.

(defthm fn-orr-with-view-fields
  (let ((o2 (fn-ocfg-owner (fn-ocfg-with-view oc v)))
        (o (fn-ocfg-owner oc)))
    (and (equal (fn-own-view o2) v)
         (equal (fn-own-store o2) (fn-own-store o))
         (equal (fn-own-conns o2) (fn-own-conns o))
         (equal (fn-own-next-id o2) (fn-own-next-id o))
         (equal (fn-own-max-conns o2) (fn-own-max-conns o))
         (equal (fn-own-pending o2) (fn-own-pending o))
         (equal (fn-own-ledger o2) (fn-own-ledger o))
         (equal (fn-own-clock o2) (fn-own-clock o))
         (equal (fn-own-facts o2) (fn-own-facts o))
         (equal (fn-own-queue o2) (fn-own-queue o))
         (fn-own-shapep o2)
         (fn-ocfg-shapep (fn-ocfg-with-view oc v))
         (equal (fn-ocfg-config (fn-ocfg-with-view oc v)) (fn-ocfg-config oc))
         (equal (fn-ocfg-pins (fn-ocfg-with-view oc v)) (fn-ocfg-pins oc))
         (equal (fn-ocfg-staged (fn-ocfg-with-view oc v)) (fn-ocfg-staged oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-with-owner fn-own-with-view))))

(defthm fn-orr-ocfg-read-keeps-the-rest
  (let ((oc2 (cdr (fn-ocfg-read oc id octets fn-arena))))
    (and (equal (fn-own-view (fn-ocfg-owner oc2)) (fn-own-view (fn-ocfg-owner oc)))
         (equal (fn-own-store (fn-ocfg-owner oc2)) (fn-own-store (fn-ocfg-owner oc)))
         (equal (fn-own-next-id (fn-ocfg-owner oc2)) (fn-own-next-id (fn-ocfg-owner oc)))
         (equal (fn-own-max-conns (fn-ocfg-owner oc2)) (fn-own-max-conns (fn-ocfg-owner oc)))
         (equal (fn-own-pending (fn-ocfg-owner oc2)) (fn-own-pending (fn-ocfg-owner oc)))
         (equal (fn-own-ledger (fn-ocfg-owner oc2)) (fn-own-ledger (fn-ocfg-owner oc)))
         (equal (fn-own-clock (fn-ocfg-owner oc2)) (fn-own-clock (fn-ocfg-owner oc)))
         (equal (fn-own-facts (fn-ocfg-owner oc2)) (fn-own-facts (fn-ocfg-owner oc)))
         (equal (fn-ocfg-config oc2) (fn-ocfg-config oc))
         (equal (fn-ocfg-staged oc2) (fn-ocfg-staged oc))))
  :hints (("Goal" :use ((:instance fn-ocl-own-read-keeps-owner-control (o (fn-ocfg-owner oc)))
                        (:instance fn-ocl-own-read-keeps-store (o (fn-ocfg-owner oc))))
           :in-theory (e/d (fn-ocfg-read fn-ocfg-with-read-owner fn-own-read)
                           (fn-ocl-own-read-keeps-owner-control fn-ocl-own-read-keeps-store
                            fn-own-read-full)))))

; -----------------------------------------------------------------------------
; The relation reads the view only through its two view conjuncts, and those
; read only the Store, the configuration and the view.

(defthm fn-orr-view-historyp-reads-store-and-view
  (implies (equal (fn-own-store o1) (fn-own-store o))
           (equal (fn-ocl-view-historyp (fn-own-with-view o1 (fn-own-view o)))
                  (fn-ocl-view-historyp o)))
  :hints (("Goal" :in-theory (e/d (fn-ocl-view-historyp fn-own-with-view)
                                  (fn-cst-replay-node fn-node-statep fn-ctl-visible-state)))))

(defthm fn-orr-view-configp-reads-config-store-and-view
  (implies (and (equal (fn-own-store (fn-ocfg-owner oc1)) (fn-own-store (fn-ocfg-owner oc)))
                (equal (fn-ocfg-config oc1) (fn-ocfg-config oc)))
           (equal (fn-ocl-view-configp (fn-ocfg-with-view oc1 (fn-own-view (fn-ocfg-owner oc))))
                  (fn-ocl-view-configp oc)))
  :hints (("Goal" :in-theory (e/d (fn-ocl-view-configp)
                                  (fn-cst-replay-node fn-node-statep fn-ctl-visible-state
                                   fn-cpr-replay fn-ocfg-with-view)))))

(defthm fn-orr-conns-historyp-of-with-view
  (equal (fn-ocl-conns-historyp (fn-ocfg-with-view oc v) conns)
         (fn-ocl-conns-historyp oc conns))
  :hints (("Goal" :in-theory (e/d (fn-ocl-conns-historyp fn-ocl-conn-historyp fn-ocfg-conn-config)
                                  (fn-ocfg-with-view)))))

(defthm fn-orr-config-historyp-of-with-view
  (equal (fn-ocl-config-historyp (fn-ocfg-with-view oc v))
         (fn-ocl-config-historyp oc))
  :hints (("Goal" :in-theory (e/d (fn-ocl-config-historyp) (fn-ocfg-with-view)))))

(defthm fn-orr-relation-of-with-view
  (implies (and (fn-ocl-relation y)
                (fn-ocl-view-historyp (fn-ocfg-owner (fn-ocfg-with-view y w)))
                (fn-ocl-view-configp (fn-ocfg-with-view y w)))
           (fn-ocl-relation (fn-ocfg-with-view y w)))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation)
                                  (fn-ocfg-with-view
                                   fn-ocl-view-historyp fn-ocl-view-configp
                                   fn-ocl-conns-historyp fn-ocl-config-historyp
                                   fn-ocfg-pins-okp fn-ocfg-conns-pinnedp fn-ocfg-pins-pin-conns-only
                                   fn-own-ledger-durablep fn-own-facts-okp fn-cst-relation
                                   fn-ocl-unique-conn-idsp fn-own-ids-below-next-p
                                   fn-cfgp fn-cfg-recordp)))))

; -----------------------------------------------------------------------------
; The entry, one step at a time: the owner at the captured view carries the
; reader relation; the span read there is the historical read and keeps it;
; putting the working view back keeps it.

(defthm fn-orr-reader-relation-at-a-captured-view
  (implies (and (fn-ocri-relation oc0)
                (fn-ocri-relation oc)
                (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                       (append (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))
                               extra))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0))))
                (equal (fn-ocfg-config oc) (fn-ocfg-config oc0)))
           (fn-ocri-relation (fn-ocfg-with-view oc (fn-own-view (fn-ocfg-owner oc0)))))
  :hints (("Goal" :use ((:instance fn-ocl-relation-of-a-view-captured-before-appends))
           :in-theory (e/d (fn-ocri-relation)
                           (fn-ocl-relation-of-a-view-captured-before-appends
                            fn-ocl-relation fn-ocfg-with-view fn-ocri-viewp fn-ocri-conns-p)))))

(defthm fn-orr-reader-relation-indexed
  (implies (fn-ocri-relation oc)
           (and (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocri-relation fn-ocri-viewp fn-scar-view-indexedp))))

(defthm fn-orr-span-read-is-historical-read
  (implies (and (fn-ocri-relation x)
                (fn-scr-owner-catalogp (fn-ocfg-owner x) id fn-arena fn-cat)
                (natp i) (natp end))
           (let* ((r (fn-scr-ocfg-read-span x id i end fn-octets fn-arena fn-cat))
                  (full (fn-ocfg-read x id (take (fn-own-tls-result-consumed r)
                                                 (fn-oct-slice-list i end fn-octets))
                                      fn-arena)))
             (and (equal (fn-own-tls-result-effects r) (car full))
                  (equal (fn-own-tls-result-owner r) (cdr full)))))
  :hints (("Goal" :use ((:instance fn-scr-ocfg-read-span-is-reference-under-ocl-relation (oc x))
                        (:instance fn-ocri-host-tls-read-refines-historical-read
                                   (oc x) (octets (fn-oct-slice-list i end fn-octets)))
                        (:instance fn-orr-reader-relation-indexed (oc x)))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(defthm fn-orr-span-read-keeps-the-reader-relation-and-the-rest
  (implies (and (fn-ocri-relation x)
                (fn-scr-owner-catalogp (fn-ocfg-owner x) id fn-arena fn-cat)
                (natp i) (natp end))
           (let* ((x2 (fn-own-tls-result-owner
                       (fn-scr-ocfg-read-span x id i end fn-octets fn-arena fn-cat))))
             (and (fn-ocri-relation x2)
                  (equal (fn-own-view (fn-ocfg-owner x2)) (fn-own-view (fn-ocfg-owner x)))
                  (equal (fn-own-store (fn-ocfg-owner x2)) (fn-own-store (fn-ocfg-owner x)))
                  (equal (fn-own-next-id (fn-ocfg-owner x2)) (fn-own-next-id (fn-ocfg-owner x)))
                  (equal (fn-own-max-conns (fn-ocfg-owner x2)) (fn-own-max-conns (fn-ocfg-owner x)))
                  (equal (fn-own-pending (fn-ocfg-owner x2)) (fn-own-pending (fn-ocfg-owner x)))
                  (equal (fn-own-ledger (fn-ocfg-owner x2)) (fn-own-ledger (fn-ocfg-owner x)))
                  (equal (fn-own-clock (fn-ocfg-owner x2)) (fn-own-clock (fn-ocfg-owner x)))
                  (equal (fn-own-facts (fn-ocfg-owner x2)) (fn-own-facts (fn-ocfg-owner x)))
                  (equal (fn-ocfg-config x2) (fn-ocfg-config x))
                  (equal (fn-ocfg-staged x2) (fn-ocfg-staged x)))))
  :hints (("Goal" :use ((:instance fn-orr-span-read-is-historical-read)
                        (:instance fn-ocri-read-preserves-historical-reader-relation
                                   (oc x)
                                   (octets (take (fn-own-tls-result-consumed
                                                  (fn-scr-ocfg-read-span x id i end fn-octets fn-arena fn-cat))
                                                 (fn-oct-slice-list i end fn-octets))))
                        (:instance fn-orr-ocfg-read-keeps-the-rest
                                   (oc x)
                                   (octets (take (fn-own-tls-result-consumed
                                                  (fn-scr-ocfg-read-span x id i end fn-octets fn-arena fn-cat))
                                                 (fn-oct-slice-list i end fn-octets)))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(defthm fn-orr-own-with-view-fields
  (and (equal (fn-own-view (fn-own-with-view o v)) v)
       (equal (fn-own-store (fn-own-with-view o v)) (fn-own-store o))
       (equal (fn-own-conns (fn-own-with-view o v)) (fn-own-conns o))
       (equal (fn-own-next-id (fn-own-with-view o v)) (fn-own-next-id o))
       (equal (fn-own-max-conns (fn-own-with-view o v)) (fn-own-max-conns o))
       (equal (fn-own-pending (fn-own-with-view o v)) (fn-own-pending o))
       (equal (fn-own-ledger (fn-own-with-view o v)) (fn-own-ledger o))
       (equal (fn-own-clock (fn-own-with-view o v)) (fn-own-clock o))
       (equal (fn-own-facts (fn-own-with-view o v)) (fn-own-facts o))
       (equal (fn-own-queue (fn-own-with-view o v)) (fn-own-queue o)))
  :hints (("Goal" :in-theory (enable fn-own-with-view))))

(defthm fn-orr-relation-view-conjuncts
  (implies (fn-ocl-relation oc)
           (and (fn-ocl-view-historyp (fn-ocfg-owner oc))
                (fn-ocl-view-configp oc)))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation)
                                  (fn-ocl-view-historyp fn-ocl-view-configp)))))

(defthm fn-orr-with-view-owner
  (equal (fn-ocfg-owner (fn-ocfg-with-view oc v))
         (fn-own-with-view (fn-ocfg-owner oc) v))
  :hints (("Goal" :in-theory (enable fn-ocfg-with-owner))))

(defthm fn-orr-restoring-the-working-view-keeps-the-reader-relation
  (implies (and (fn-ocri-relation oc)
                (fn-ocri-relation x2)
                (equal (fn-own-store (fn-ocfg-owner x2)) (fn-own-store (fn-ocfg-owner oc)))
                (equal (fn-ocfg-config x2) (fn-ocfg-config oc)))
           (fn-ocri-relation (fn-ocfg-with-view x2 (fn-own-view (fn-ocfg-owner oc)))))
  :hints (("Goal" :use ((:instance fn-orr-relation-of-with-view
                                   (y x2) (w (fn-own-view (fn-ocfg-owner oc))))
                        (:instance fn-orr-view-historyp-reads-store-and-view
                                   (o1 (fn-ocfg-owner x2)) (o (fn-ocfg-owner oc)))
                        (:instance fn-orr-view-configp-reads-config-store-and-view
                                   (oc1 x2))
                        (:instance fn-orr-relation-view-conjuncts))
           :in-theory (e/d (fn-ocri-relation)
                           (fn-orr-relation-of-with-view
                            fn-orr-view-historyp-reads-store-and-view
                            fn-orr-view-configp-reads-config-store-and-view
                            fn-orr-relation-view-conjuncts fn-ocfg-with-view
                            fn-ocl-relation fn-ocl-view-historyp fn-ocl-view-configp
                            fn-ocri-viewp fn-ocri-conns-p fn-own-with-view)))))

(defthm fn-orr-tls-result-of-make
  (and (equal (fn-own-tls-result-owner (fn-own-tls-make-result c e o r)) o)
       (equal (fn-own-tls-result-effects (fn-own-tls-make-result c e o r)) e)
       (equal (fn-own-tls-result-consumed (fn-own-tls-make-result c e o r)) c)
       (equal (fn-own-tls-result-repinned (fn-own-tls-make-result c e o r)) r))
  :hints (("Goal" :in-theory (enable fn-own-tls-make-result fn-own-tls-result-owner
                                     fn-own-tls-result-effects fn-own-tls-result-consumed
                                     fn-own-tls-result-repinned))))

; -----------------------------------------------------------------------------
; KEYSTONE (the read-preservation theorem of the served path during a
; barrier).  The subject is fn-orr-read-span, host/owner-host.lisp
; fn-owner-chunk-span's call.  VIEWS is the committer's capture
; (fn-owner-reader-views), its first the view of the owner OC0 at the capture;
; OC is the working owner at the read, whose Store has only appended EXTRA
; since, under the same configuration history and configuration.
(defthm fn-orr-read-span-at-a-captured-view-restores-the-owner
  (implies (and (consp views)
                (equal (car views) (fn-own-view (fn-ocfg-owner oc0)))
                (fn-ocri-relation oc0)
                (fn-ocri-relation oc)
                (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                       (append (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))
                               extra))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0))))
                (equal (fn-ocfg-config oc) (fn-ocfg-config oc0))
                (fn-scr-owner-catalogp (fn-ocfg-owner (fn-ocfg-with-view oc (car views)))
                                       id fn-arena fn-cat)
                (natp i) (natp end))
           (let* ((r (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat))
                  (oc2 (fn-own-tls-result-owner r))
                  (o2 (fn-ocfg-owner oc2))
                  (o (fn-ocfg-owner oc)))
             (and (fn-ocri-relation oc2)
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-pending o2) (fn-own-pending o))
                  (equal (fn-own-ledger o2) (fn-own-ledger o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o))
                  (equal (fn-ocfg-config oc2) (fn-ocfg-config oc))
                  (equal (fn-ocfg-staged oc2) (fn-ocfg-staged oc))
                  (equal (fn-own-tls-result-effects r)
                         (car (fn-ocfg-read (fn-ocfg-with-view oc (car views)) id
                                            (take (fn-own-tls-result-consumed r)
                                                  (fn-oct-slice-list i end fn-octets))
                                            fn-arena))))))
  :hints (("Goal" :use ((:instance fn-orr-reader-relation-at-a-captured-view)
                        (:instance fn-orr-span-read-keeps-the-reader-relation-and-the-rest
                                   (x (fn-ocfg-with-view oc (car views))))
                        (:instance fn-orr-span-read-is-historical-read
                                   (x (fn-ocfg-with-view oc (car views))))
                        (:instance fn-orr-restoring-the-working-view-keeps-the-reader-relation
                                   (x2 (fn-own-tls-result-owner
                                        (fn-scr-ocfg-read-span (fn-ocfg-with-view oc (car views))
                                                               id i end fn-octets fn-arena fn-cat)))))
           :in-theory (union-theories '(fn-orr-read-span fn-ocfg-at-reader-view fn-ocv-reader-view
                                        fn-orr-tls-result-of-make fn-orr-with-view-fields)
                                      (theory 'minimal-theory)))))

; With no capture held the entry is the span read of the working owner, which
; keeps the reader relation and everything but the connections.
(defthm fn-orr-read-span-without-a-capture-is-the-span-read-by-definition
  (implies (not (consp views))
           (equal (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat)
                  (fn-scr-ocfg-read-span oc id i end fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory (union-theories '(fn-orr-read-span) (theory 'minimal-theory)))))

(in-theory (disable fn-orr-read-span))

; -----------------------------------------------------------------------------
; The publication model: no configuration is published under a capture.
; P = (VIEWS W G): the capture (books/owner-reader-view.lisp fn-ocv-capture of
; the working view tagged with the generation, (W . G)), the working view's
; record count and the configuration generation.  Events: (:start K),
; (:next K), (:unnext), (:complete), (:drop) as the committer's, and
; (:publish), a configuration publication (a live `policy set', an operator's
; account request, an XREDEEM).

(defun fn-ocvp-views (p) (declare (xargs :guard t)) (if (consp p) (car p) nil))
(defun fn-ocvp-w (p) (declare (xargs :guard t))
  (nfix (if (and (consp p) (consp (cdr p))) (cadr p) 0)))
(defun fn-ocvp-g (p) (declare (xargs :guard t))
  (nfix (if (and (consp p) (consp (cdr p)) (consp (cddr p))) (caddr p) 0)))
(defun fn-ocvp-make (views w g) (declare (xargs :guard t)) (list views w g))
(defun fn-ocvp-init () (declare (xargs :guard t)) (fn-ocvp-make nil 0 0))

; A START only with no capture, a START-NEXT behind one, a COMPLETE with one
; held; a publication only with none (its class is never picked in flight).
(defun fn-ocvp-legalp (p ev)
  (declare (xargs :guard t))
  (let ((views (fn-ocvp-views p))
        (kind (if (consp ev) (car ev) nil)))
    (cond ((eq kind :start) (not (consp views)))
          ((eq kind :next) (and (consp views) (not (consp (cdr views)))))
          ((eq kind :unnext) (and (consp views) (consp (cdr views))))
          ((eq kind :complete) (consp views))
          ((eq kind :drop) (and (consp views) (not (consp (cdr views)))))
          ((eq kind :publish) (not (consp views)))
          (t nil))))

(defun fn-ocvp-step (p ev)
  (declare (xargs :guard t))
  (let* ((views (fn-ocvp-views p)) (w (fn-ocvp-w p)) (g (fn-ocvp-g p))
         (kind (if (consp ev) (car ev) nil))
         (k (nfix (if (and (consp ev) (consp (cdr ev))) (cadr ev) 0)))
         (current (cons w g)))
    (cond ((eq kind :start) (fn-ocvp-make (fn-ocv-capture views :start current) (+ w k) g))
          ((eq kind :next) (fn-ocvp-make (fn-ocv-capture views :next current) (+ w k) g))
          ((eq kind :publish) (fn-ocvp-make views w (+ 1 g)))
          (t (fn-ocvp-make (fn-ocv-capture views kind current) w g)))))

(defun fn-ocvp-all-at-generation (views g)
  (declare (xargs :guard t))
  (if (consp views)
      (and (consp (car views)) (equal (cdr (car views)) g)
           (fn-ocvp-all-at-generation (cdr views) g))
    t))

(defun fn-ocvp-inv (p)
  (declare (xargs :guard t))
  (fn-ocvp-all-at-generation (fn-ocvp-views p) (fn-ocvp-g p)))

(defthm fn-ocvp-capture-keeps-the-generation
  (implies (and (fn-ocvp-all-at-generation views g)
                (consp current) (equal (cdr current) g))
           (fn-ocvp-all-at-generation (fn-ocv-capture views event current) g)))

(defthm fn-ocvp-accessors-of-make
  (and (equal (fn-ocvp-views (fn-ocvp-make views w g)) views)
       (equal (fn-ocvp-w (fn-ocvp-make views w g)) (nfix w))
       (equal (fn-ocvp-g (fn-ocvp-make views w g)) (nfix g))))

(defthm fn-ocvp-step-preserves-inv
  (implies (and (fn-ocvp-inv p) (fn-ocvp-legalp p ev))
           (fn-ocvp-inv (fn-ocvp-step p ev)))
  :hints (("Goal" :in-theory (disable fn-ocv-capture fn-ocvp-make fn-ocvp-views
                                      fn-ocvp-w fn-ocvp-g))))

(defun fn-ocvp-legal-run-p (p evs)
  (declare (xargs :guard t :measure (acl2-count evs)))
  (if (consp evs)
      (and (fn-ocvp-legalp p (car evs))
           (fn-ocvp-legal-run-p (fn-ocvp-step p (car evs)) (cdr evs)))
    t))

(defun fn-ocvp-run (p evs)
  (declare (xargs :guard t :measure (acl2-count evs)))
  (if (consp evs) (fn-ocvp-run (fn-ocvp-step p (car evs)) (cdr evs)) p))

(defthm fn-ocvp-run-preserves-inv
  (implies (and (fn-ocvp-inv p) (fn-ocvp-legal-run-p p evs))
           (fn-ocvp-inv (fn-ocvp-run p evs)))
  :hints (("Goal" :in-theory (disable fn-ocvp-step fn-ocvp-inv fn-ocvp-legalp))))

; KEYSTONE (no publication under a capture).  Along every legal run from an
; idle owner the reader view was captured under the current configuration
; generation: the configuration the keystone above requires equal at the
; capture and at the read is.
(defthm fn-ocvp-reader-view-is-at-the-current-generation
  (implies (fn-ocvp-legal-run-p (fn-ocvp-init) evs)
           (let ((p (fn-ocvp-run (fn-ocvp-init) evs)))
             (equal (cdr (fn-ocv-reader-view (fn-ocvp-views p)
                                             (cons (fn-ocvp-w p) (fn-ocvp-g p))))
                    (fn-ocvp-g p))))
  :hints (("Goal" :use ((:instance fn-ocvp-run-preserves-inv (p (fn-ocvp-init))))
           :in-theory (e/d (fn-ocv-reader-view fn-ocvp-inv)
                           (fn-ocvp-run-preserves-inv fn-ocvp-run fn-ocvp-legal-run-p
                            (fn-ocvp-init))))))

; -----------------------------------------------------------------------------
; The class a configuration publication runs as, named for the host
; (host/native/owner.lisp fnn-owner-handle-chunk: an XREDEEM's publication;
; the control socket's live reconfiguration is already this class): the
; scheduler never picks it while a batch is in flight, so it waits for the
; COMPLETE without holding the owner.
(defun fn-ocs-publication-class ()
  (declare (xargs :guard t))
  :control)

(defthm fn-ocs-a-publication-waits-for-the-complete
  (implies (fn-ocs-in-flight-p (fn-ocs-phase s))
           (not (equal (mv-nth 0 (fn-ocs-next s w)) (fn-ocs-publication-class))))
  :hints (("Goal" :use fn-ocs-in-flight-admits-only-inspect-commit-and-reader
           :in-theory (disable fn-ocs-next fn-ocs-phase fn-ocs-in-flight-p
                               fn-ocs-in-flight-admits-only-inspect-commit-and-reader))))
