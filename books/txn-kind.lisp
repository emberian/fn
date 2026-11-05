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
(defconst *fn2-txn-counts-sid* 5)
(defconst *fn2-txn-outcome-sid* 9)

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

(defun fn2-txn-capacity (profile)
  (declare (xargs :guard t))
  (if (fn2-profile-get :posting-interim profile) (nfix (fn2-profile-t profile)) 0))
(defthm fn2-txn-capacity-natp (natp (fn2-txn-capacity profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-txn-capacity))

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
          (stopped :bool) (next-free :link))
 :links ((upload :kind fn2-upload :slot upload :gen upload-gen :back (txn txn-gen)
                 :reads (phase word inj ml mo c0-slot c0-gen c1-slot c1-gen hashed scan-off no nl pext pepoch palloc ilen lslot lgen op)))
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
         :clear (tmode ecommit batch bevent word offered prepared filed counted lines gcur gskip ngroups stopped))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (upload *fn2-none*) (conn *fn2-none*) (account-ref *fn2-none*) (next-free fn2-machine-initial-next-free))
 :arms ((:free) (:admit) (:reserve) (:lookup) (:prepare) (:ready) (:batched)
        (:accepted) (:refused) (:uncertain) (:releasing) (:draining) (:retired)))

(defmachine-registry fn2-txn)
