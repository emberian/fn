;; Schema, core child, wait kind, and partition registration for fn2-ctl and fn2-cns (layer E).
;; Arm bodies and helper operations live in books/cns.lisp (a leaf book).
(in-package "ACL2")
(include-book "cns-edges")
(include-book "accounts")
(include-book "machines-a")
(include-book "machines-a-costs")
(include-book "machine-arms")
(fn2-book-layer :e)

(defconst *fn2-cns-esub-dimension*
  (position-eq :subscription-edge (strip-cars *fn2-account-holdings*)))
(assert-event (natp *fn2-cns-esub-dimension*))
(defun fn2-cns-edge-rows (profile)
  (declare (xargs :guard t))
  (nfix (fn2-account-profile-capacity *fn2-cns-esub-dimension* profile)))
(defun fn2-cns-edges-profilep (profile)
  (declare (xargs :guard t))
  (let ((cap (fn2-account-profile-capacity *fn2-cns-esub-dimension* profile)))
    (and (natp cap) (<= cap (fn2-cns-edge-rows profile))
         (unsigned-byte-p 31 (fn2-cns-edge-rows profile)))))
(defcorechild fn2-core-cns-edges fn2-cns-edges
 :init (fn2-cns-edges-init (fn2-cns-edge-rows profile) fn2-cns-edges)
 :profilep (fn2-cns-edges-profilep profile)
 :why "A parked consumer wait's subscription edges and the streams' wake buckets (D8's rows, e-surface 7): survive the waiter's park until its wake or cancel.")

(defwait :wait-row :ready fn2-cns-wait-ready-p :grant fn2-cns-wait-grant-one :tables (fn2-core-machines fn2-core-cns-edges)
 :doc "A consumer wait parked on its stream's edge, woken once the publish hook pushed its bucket.")

(defmacro fn2-cns-wait-events ()
 '(progn
   ;; the :wait-row source
   (defun fn2-cns-core-ready (fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-cns-edges (fn2-core-cns-edges fn2-core)))
       (r) (fn2-cns-ready-p fn2-cns-edges) r))
   (defun fn2-cns-core-grant (fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-cns-edges (fn2-core-cns-edges fn2-core))
                 (fn2-machines (fn2-core-machines fn2-core))
                 (fn2-control (fn2-core-control fn2-core)))
       (w fn2-cns-edges fn2-machines fn2-control)
       (fn2-cns-grant-one fn2-cns-edges fn2-machines fn2-control)
       (mv w fn2-core)))
   (fn2-core-preserves fn2-cns-core-grant (fn2-core) :position 1 :rows nil)
   (defthm fn2-cns-core-grant-live
     (implies (fn2-cns-core-ready fn2-core)
              (not (equal (mv-nth 0 (fn2-cns-core-grant fn2-core)) *fn2-none*)))
     :hints (("Goal" :in-theory (e/d (fn2-cns-core-ready fn2-cns-core-grant) (fn2-cns-grant-one fn2-cns-ready-p))
                     :use ((:instance fn2-cns-grant-one-live
                                      (fn2-cns-edges (fn2-core-cns-edges fn2-core))
                                      (fn2-machines (fn2-core-machines fn2-core))
                                      (fn2-control (fn2-core-control fn2-core)))))))
   (in-theory (disable fn2-cns-core-ready fn2-cns-core-grant))
   (fn2-wait-attach :wait-row fn2-cns-core-grant)
   (defattach (fn2-cns-wait-ready-p fn2-cns-core-ready) (fn2-cns-wait-grant-one fn2-cns-core-grant)
    :hints (("Goal" :use ((:instance fn2-cns-core-grant-live) (:instance fn2-cns-core-grant-wait-kids) (:instance fn2-cns-core-grant-wait-directory)))))))

;; A control connection's one range holds its frames (at most this many
;; octets a receive or send) and, after a request, the reply the request row
;; builds there (the page's items, books/cns.lisp fn2-cns-item-fits): it is
;; the profile's smallest pool class of at least this many octets, so a page
;; holds record items in any profile, whatever its class numbering.
(defconst *fn2-ctl-io-bytes* 4096)

(defun fn2-ctl-capacity (profile)
  (declare (xargs :guard t))
  (if (and (alistp profile) (assoc-equal :control-connections profile))
      (nfix (fn2-profile-get :control-connections profile))
    2))
(defun fn2-cns-capacity (profile)
  (declare (xargs :guard t))
  (nfix (fn2-profile-get :cns profile)))
(defthm fn2-ctl-capacity-natp (natp (fn2-ctl-capacity profile)) :rule-classes :type-prescription)
(defthm fn2-cns-capacity-natp (natp (fn2-cns-capacity profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-ctl-capacity fn2-cns-capacity))

(defmachine fn2-ctl
 :phases (:free :greeting :frame :dispatch :waiting :reply :closing :draining :retired)
 :fields ((cap-index :u32) (cap-nonce :u32) (rx-slot :link) (rx-gen :u60) (tx-slot :link) (tx-gen :u60)
          (fill :u32) (pos :u32) (flen :u32) (fkind :u8) (cns :link) (cns-gen :u60) (owner :bool)
          (tx-off :u32) (tx-len :u32) (request :u32) (pending :u32) (borrows :u32) (stopped :bool)
          (peer-family :u8) (peer-w0 :u32) (cmd :u8) (posture :u8)
          ;; served authority (AUTHORITY-20261105 section 1): the connection's
          ;; durable principal, whether it administers (an owner connection not
          ;; yet bound), whether it has done consumer work, and its auth request
          (principal :u60) (admin :bool) (worked :bool) (auth :link) (auth-gen :u60)
          (next-free :link))
 :holds ((:greeting :connection-row :rx-range) (:frame :connection-row :rx-range)
         (:dispatch :connection-row :rx-range) (:waiting :connection-row :rx-range)
         (:reply :connection-row :rx-range) (:closing :connection-row :rx-range)
         (:draining :connection-row :rx-range))
 :budget (:bytes 8192 :steps 32 :descriptors 4)
 :capacity (fn2-ctl-capacity profile)
 :admission (:phase :greeting :ranges ((:rx-range :slot rx-slot :gen rx-gen :class (:bytes *fn2-ctl-io-bytes*)))
             :copy (peer-family peer-w0)
             :clear (fill pos flen fkind cns-gen owner tx-off tx-len request pending borrows stopped cmd posture
                     principal admin worked auth-gen))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (rx-slot *fn2-none*) (tx-slot *fn2-none*) (cns *fn2-none*) (auth *fn2-none*)
           (next-free fn2-machine-initial-next-free))
 :arms ((:free) (:greeting) (:frame) (:dispatch) (:waiting) (:reply) (:closing) (:draining) (:retired))
 :observes ((:receive-result) (:send-result) (:borrow-released) (:close-result)))

(defmachine-registry fn2-ctl)

(defmachine fn2-cns
 :phases (:free :decode :check :lookup :read :page :fetch :park :commit :append :draining :retired)
 :fields ((ctl :link) (ctl-gen :u60) (request :u32) (fpos :u32) (flen :u32) (fkind :u8)
          (verb (:enum fn2-cns-verb (:none :register :read :wait :ack :position :status :append :fetch
                                     :rebase :unregister)))
          (consumer :u60) (epoch :u32) (op :u60) (to :u60) (cstart :u60) (page-limit :u16) (wait-ms :u32)
          (cpos :u60) (version :u60) (pub-frontier :u60) (count :u32) (more :bool)
          (outcome (:enum fn2-cns-outcome (:none :accepted :refused :uncertain))) (reason :u8)
          (posted (:enum fn2-cns-posted (:none :accepted :unchanged :refused :uncertain))) (posted-word :u8)
          (edge :link) (txn :link) (txn-gen :u60) (tx-slot :link) (tx-gen :u60)
          ;; an append (e-surface.md 3.3) is a POST: the upload row this
          ;; request owns, fed from the frame's article octets at FSTART
          ;; (FED of them written, FEED-MODE the feed's line state, then
          ;; done; FEED-DISCARD 1 framing, 2 too large), as a connection feeds it
          (upload :link) (upload-gen :u60) (fstart :u32) (fed :u60) (feed-mode :u8) (feed-discard :u8)
          ;; a register's consumer name, the octets of its request's consumer
          ;; field in the control range (the names row it writes)
          (name-off :u32) (name-len :u8)
          ;; the consume check in progress at :check (AUTHORITY-20261105
          ;; section 4; fn2-cns-authority-allows' step, head and grant)
          (xstep :u8) (xhead :u60) (xgrant :u60)
          ;; a page's items (e-surface.md 4.1): IPOS the position through
          ;; which the walk is complete, the items' octets [IOFF, IOFF+ILEN)
          ;; of the control range; the entry in hand (its position, article,
          ;; type, stored length and location) and the read lease its octets
          ;; and Message-ID are read into, with the block read's result
          (ipos :u60) (ioff :u32) (ilen :u32)
          (npos :u60) (art :u60) (istream :u60) (itype :u8) (alen :u60) (lunit :u60) (lepoch :u60) (lalloc :u60)
          (lslot :link) (lgen :u60) (lease (:enum fn2-cns-lease (:none :held)))
          (revent :u8) (routcome :u8) (rcount :u32) (rready :bool)
          ;; block reads in flight (the terminal of each completion consumes one)
          (pending :u32)
          ;; the pool class a row parked for its lease waits on (:park :pool's field)
          (cursor :u32)
          ;; the row's read row (fn2-cns-read-row)
          (xrow :u32)
          (stopped :bool) (next-free :link))
 :holds ((:decode :wait-row (:storage-window :while (lease :held))) (:check :wait-row (:storage-window :while (lease :held))) (:lookup :wait-row (:storage-window :while (lease :held)))
         (:read :wait-row (:storage-window :while (lease :held))) (:page :wait-row (:storage-window :while (lease :held)))
         (:fetch :wait-row (:storage-window :while (lease :held))) (:park :wait-row (:storage-window :while (lease :held)))
         (:commit :wait-row (:storage-window :while (lease :held))) (:append :wait-row (:storage-window :while (lease :held))) (:draining :wait-row (:storage-window :while (lease :held))))
 :budget (:bytes 16384 :steps 32 :descriptors 4)
 :capacity (fn2-cns-capacity profile)
 :taken (:phase :decode :rows :wait-row :ranges ()
         :copy (ctl ctl-gen request fpos flen fkind tx-slot tx-gen)
         :clear (verb consumer epoch op to cstart page-limit wait-ms deadline cpos version pub-frontier count more outcome
                 reason posted posted-word txn-gen upload-gen fstart fed feed-mode feed-discard name-off name-len
                 ipos ioff ilen npos art istream itype alen lunit lepoch lalloc lgen lease revent routcome rcount rready cursor xrow xstep xhead xgrant stopped))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (ctl *fn2-none*) (edge *fn2-none*) (txn *fn2-none*) (tx-slot *fn2-none*) (upload *fn2-none*)
           (lslot *fn2-none*) (next-free fn2-machine-initial-next-free))
 :arms ((:free) (:decode) (:check) (:lookup) (:read) (:page) (:fetch) (:park) (:commit) (:append) (:draining) (:retired))
 :observes ((:read-result)))

(defmachine-registry fn2-cns)
