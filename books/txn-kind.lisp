;; Schema, core child, and partition registration for fn2-txn (layer D, quest D5).
;; Arm bodies and helper operations live in books/txn.lisp (a leaf book).
(in-package "ACL2")
(include-book "upload-kind")
(include-book "claims")
(include-book "machines-c-bind")
(include-book "machine-arms")
(fn2-book-layer :d)

(defconst *fn2-txn-evidence-sid* 1)
(defconst *fn2-txn-history-sid* 11)
(defconst *fn2-txn-candidates-sid* 12)
(defconst *fn2-txn-summary-sid* 13)
(defconst *fn2-txn-index-sid* 14)
(defconst *fn2-txn-article-sid* 2)
;; fn2-article's LOCATION-KIND: the reference names the raw source.
(defconst *fn2-txn-location-raw-source* 0)
(defconst *fn2-txn-location-source-manifest* 1)
(defconst *fn2-txn-counts-sid* 5)
(defconst *fn2-txn-outcome-sid* 9)

;; Successor write-slot geometry in C-S3 (*fn2-succ-slots*):
;; 0..7 are fixed per-POST slots, *fn2-txn-slot-depend* (20) holds the authority
;; head read dependency (matching authority.lisp's *fn2-auth-depend-slot*), and
;; every remaining pair of slots carries one group's count accept + overview entry.
(defconst *fn2-txn-slot-accepts* 8)
(defconst *fn2-txn-slot-depend* 20)
(defconst *fn2-txn-groups-max*
  (floor (- *fn2-succ-slots* (+ 1 *fn2-txn-slot-accepts*)) 2))
(assert-event (and (posp *fn2-txn-groups-max*)
                   (< *fn2-txn-slot-depend* *fn2-succ-slots*)))

;; Profile-configured cross-post group limit (:max-groups-per-article, D27):
;; a D core child read by fn2-txn instead of a compile-time literal.
(defcolumns fn2-txn-config ((groups-max :u8)))
(defun fn2-txn-config-profilep (profile)
  (declare (xargs :guard t))
  (let ((g (fn2-profile-get :max-groups-per-article profile)))
    (or (null g)
        (and (posp g) (<= g *fn2-txn-groups-max*)))))
(defun fn2-txn-config-from (profile fn2-txn-config)
  (declare (xargs :stobjs fn2-txn-config :guard (fn2-txn-config-profilep profile)))
  (let* ((fn2-txn-config (fn2-txn-config-init 1 fn2-txn-config))
         (g (fn2-profile-get :max-groups-per-article profile)))
    (fn2-txn-config-put 0
      (groups-max (if (and (posp g) (<= g *fn2-txn-groups-max*) (unsigned-byte-p 8 g))
                      g
                    *fn2-txn-groups-max*)))))
(defthm fn2-txn-config-from-type
  (implies (fn2-txn-configp fn2-txn-config)
           (fn2-txn-configp (fn2-txn-config-from profile fn2-txn-config))))
(defthm fn2-txn-config-from-wfp
  (fn2-txn-config-wfp (fn2-txn-config-from profile fn2-txn-config)))
(in-theory (disable fn2-txn-config-from fn2-txn-config-profilep))
(defcorechild fn2-core-txn-config fn2-txn-config
 :init (fn2-txn-config-from profile fn2-txn-config) :profilep (fn2-txn-config-profilep profile)
 :why "Profile-configured cross-post group limit (:max-groups-per-article) read by fn2-txn (D27).")

;; The claim table (a D core child, one row per transaction slot).
(fn2-claims-preserves fn2-claims-init-buckets (left fn2-claims)
  :hyps ((fn2-claimsp fn2-claims) (fn2-claims-wfp fn2-claims) (<= (nfix left) (fn2-claims-rows fn2-claims))))
(defthm fn2-claims-init-buckets-rows-equal
  (equal (fn2-claims-rows (fn2-claims-init-buckets left fn2-claims)) (fn2-claims-rows fn2-claims))
  :hints (("Goal" :in-theory (enable fn2-claims-init-buckets))))
(defthm fn2-claims-init-buckets-wfp-alone
  (implies (and (fn2-claims-wfp fn2-claims) (<= (nfix left) (fn2-claims-rows fn2-claims)))
           (fn2-claims-wfp (fn2-claims-init-buckets left fn2-claims)))
  :hints (("Goal" :in-theory (e/d (fn2-claims-init-buckets) (fn2-claimsp)))))
(defun fn2-txn-claims-profilep (profile)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 (fn2-profile-t profile)))
(defun fn2-claims-init-for (profile fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-txn-claims-profilep profile)))
  (fn2-claims-table-init (fn2-profile-t profile) fn2-claims))
(defthm fn2-claims-init-for-type
  (implies (and (fn2-claimsp fn2-claims) (fn2-txn-claims-profilep profile))
           (fn2-claimsp (fn2-claims-init-for profile fn2-claims))))
(defthm fn2-claims-init-for-wfp
  (implies (fn2-txn-claims-profilep profile) (fn2-claims-wfp (fn2-claims-init-for profile fn2-claims)))
  :hints (("Goal" :in-theory (enable fn2-claims-init-for fn2-txn-claims-profilep))))
(in-theory (disable fn2-claims-init-for fn2-txn-claims-profilep))
(defcorechild fn2-core-claims fn2-claims
 :init (fn2-claims-init-for profile fn2-claims) :profilep (fn2-txn-claims-profilep profile)
 :why "The identity reservation: a transaction's claim on its Message-ID's exact octets and the FIFO of its waiters survive the transaction's yields (section 14.4.2).")

;; The T-row shares (fn2-txn-authority-share, -consumer-share, -capacity)
;; are in upload-kind.lisp: posting is served only when fn2-txn has a row.

(defmachine fn2-txn
 :phases (:free :admit :reserve :lookup :prepare :ready :batched :accepted :refused :uncertain :releasing :draining :retired)
 ;; CONN is the upload's owner the outcome goes to: a connection, or a
 ;; consumer request whose append this is (e-surface.md 3.3).
 :fields ((upload :link) (upload-gen :u60) (conn :link) (conn-gen :u60) (request :u32)
          (rule (:enum fn2-txn-rule (:post :ihave :takethis)))
          (tmode (:enum fn2-txn-mode (:article :evidence)))
          (ecommit (:enum fn2-txn-ecommit (:none :committed :uncertain :refused)))
          (batch :u60) (bevent :u60)
          (word :u8) (offered :bool) (prepared :bool) (filed :bool) (counted :u60) (lines :u32)
          (gcur :u32) (gskip :bool) (ngroups :u8)
          ;; the append check in progress for the group at GCUR (its group
          ;; XGROUP; XSTEP 0 the name lookup, K > 0 fn2-authority-allows'
          ;; step K - 1 with the head and grant it carries)
          (xstep :u8) (xgroup :u60) (xhead :u60) (xgrant :u60)
          (stopped :bool) (next-free :link))
 :links ((upload :kind fn2-upload :slot upload :gen upload-gen :back (txn txn-gen)
                 :reads (phase word inj ml mo c0-slot c0-gen c1-slot c1-gen hashed scan-off no nl pext pepoch palloc ilen lslot lgen mfill op)))
 :stops (:txn-uncertain)
 :holds ((:admit :transaction-row) (:reserve :transaction-row)
         (:lookup :transaction-row :identity-reservation) (:prepare :transaction-row :identity-reservation)
         (:ready :transaction-row :identity-reservation)
         (:batched :transaction-row :identity-reservation :batch-membership)
         (:accepted :transaction-row :identity-reservation) (:refused :transaction-row :identity-reservation)
         (:uncertain :transaction-row :identity-reservation) (:releasing :transaction-row :identity-reservation)
         (:draining :transaction-row))
 :budget (:bytes 26624 :steps 32 :descriptors 4)
 :capacity (fn2-txn-capacity profile)
 :taken (:phase :admit :rows :transaction-row :ranges ()
         :copy (upload upload-gen conn conn-gen request rule principal-slot)
         :clear (tmode ecommit batch bevent word offered prepared filed counted lines gcur gskip ngroups
                xstep xgroup xhead xgrant stopped))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (upload *fn2-none*) (conn *fn2-none*) (account-ref *fn2-none*) (next-free fn2-machine-initial-next-free))
 :arms ((:free) (:admit) (:reserve) (:lookup) (:prepare) (:ready) (:batched)
        (:accepted) (:refused) (:uncertain) (:releasing) (:draining) (:retired)))

(defmachine-registry fn2-txn)
