;; The transaction machine fn2-txn (layer D, quest D5; ROUND2 section B.2
;; row 4). The design is docs/d-machines-nntp.md section 14.4. An upload
;; whose header is complete takes a transaction row (A-S7's taken kind); the
;; transaction claims the exact octets of the Message-ID (claims.lisp, D0's
;; :identity-reservation) so same-Message-ID offers on one node serialize,
;; asks C's identity decision (C-S1) once the upload has its digest, writes
;; its records into its batch's private successor (C-S3: :prepare declares
;; the slots, :ready stages, admits and binds in one transition), and posts
;; the one outcome word to its connection, releasing the claim (handing it to
;; the FIFO's head), the successor, the upload and the row.
;; D5 1/n: the batch admission is B-S2's interim (fn2-commit-admit-txn
;; answers :not-served until B lands the transaction member), so every valid
;; article is refused :not-stored after :ready, and no fact is ever bound.
;; Registration book: assembly-index includes it after upload; its operations
;; and continuations are materialized by assembly-callbacks-d-txn.lisp.
(in-package "ACL2")
(include-book "upload")
(include-book "claims")
(include-book "machines-c-bind")
(include-book "machine-arms") ; defmachine-registry (MACHINE-FORM 6.5 P4)
(fn2-book-layer :d)

;; The claim walk's chain steps per run: each step compares at most one
;; Message-ID (250 octets) on an equal hash and length, so 16 steps stay
;; within the 4 KiB comparison bound of ROUND2 B.3.
(defconst *fn2-txn-claim-steps* 16)
;; Body lines counted per :prepare run (one pool read each).
(defconst *fn2-txn-count-bytes* 2048)
;; The schemas a POST writes (identity.lisp, ordered.lisp) and its write
;; slots (C-S3, W = 24): the identity admission (C §4a: the evidence, the
;; history entry, the summary's and the candidate's :admit, the article
;; index), the article row, the operation outcome, then one group-count
;; accept per carried group. A cross-post to more carried groups than
;; *fn2-txn-groups-max* is refused :unaffordable (the overview row and the
;; addr entries of D5 2/n take the other slots).
(defconst *fn2-txn-evidence-sid* 1)
(defconst *fn2-txn-history-sid* 11)
(defconst *fn2-txn-candidates-sid* 12)
(defconst *fn2-txn-summary-sid* 13)
(defconst *fn2-txn-index-sid* 14)
(defconst *fn2-txn-article-sid* 2)
(defconst *fn2-txn-counts-sid* 5)
(defconst *fn2-txn-outcome-sid* 9)
(defconst *fn2-txn-slot-evidence* 0)
(defconst *fn2-txn-slot-history* 1)
(defconst *fn2-txn-slot-summary* 2)
(defconst *fn2-txn-slot-candidate* 3)
(defconst *fn2-txn-slot-index* 4)
(defconst *fn2-txn-slot-article* 5)
(defconst *fn2-txn-slot-outcome* 6)
(defconst *fn2-txn-slot-accepts* 7)
(defconst *fn2-txn-groups-max* 6)
(assert-event (<= (+ *fn2-txn-slot-accepts* (* 2 *fn2-txn-groups-max*)) *fn2-succ-slots*))
;; The article row's values: a born article is live, version 1; the
;; operation outcome recorded with it is accepted (it is bound only into the
;; batch that accepts it).
(defconst *fn2-txn-article-live* 0)
(defconst *fn2-txn-article-version* 1)
(defconst *fn2-txn-outcome-accepted* 1)
;; Newsgroups is scanned at most this many octets per :prepare run.
(defconst *fn2-txn-scan-bytes* 1024)

;; The claim table (a D core child, one row per transaction slot).
(fn2-claims-preserves fn2-claims-init-buckets (left fn2-claims)
  :hyps ((fn2-claimsp fn2-claims) (fn2-claims-wfp fn2-claims) (<= (nfix left) (fn2-claims-rows fn2-claims))))
;; the core's init-wfp theorem has no recognizer hypothesis: wfp from wfp alone
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

;; One row per transaction slot, and none unless the profile serves article
;; input (the upload's rule): a transaction exists only for an upload.
(defun fn2-txn-capacity (profile)
  (declare (xargs :guard t))
  (if (fn2-profile-get :posting-interim profile) (nfix (fn2-profile-t profile)) 0))
(defthm fn2-txn-capacity-natp (natp (fn2-txn-capacity profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-txn-capacity))

;; The :ready transition's byte bound: C-S3's stage and bind and B's
;; admission happen in one run (nothing may stage or bind between a
;; transaction's stage and its bind), so the run's bound is their sum, above
;; ROUND2 B.3's 4 KiB (a departure recorded in the layer doc, 14.4).
(defconst *fn2-txn-admit-bytes* 4096)
(defconst *fn2-txn-ready-bytes* (+ 4096 8192 *fn2-txn-admit-bytes*))
(assert-event (equal *fn2-txn-ready-bytes* 16384))  ; the kind's :budget below

(defconst *fn2-upload-word-accepted* (fn2-upload-word-code :accepted))
(defconst *fn2-upload-word-uncertain* (fn2-upload-word-code :uncertain))
(defconst *fn2-upload-word-duplicate* (fn2-upload-word-code :duplicate))
(defconst *fn2-upload-word-conflict* (fn2-upload-word-code :conflict))
(defconst *fn2-upload-word-group* (fn2-upload-word-code :group))
(defconst *fn2-upload-word-unaffordable* (fn2-upload-word-code :unaffordable))
(defconst *fn2-upload-word-not-stored* (fn2-upload-word-code :not-stored))

(defcost fn2-txn-upload-live-p :doc "Whether the upload still names this transaction.")
(defcost fn2-txn-upload-sealed-p :doc "Whether the upload reached its verdict.")
(defcost fn2-txn-upload-aborting-p :doc "Whether the upload is aborting.")
(defcost fn2-txn-upload-words :doc "The upload's refusal word and injected-field word.")
(defcost fn2-txn-upload-view :doc "The upload's Message-ID, chunks, hashed/scanned offsets and Newsgroups span.")
(defcost fn2-txn-hash :answers t :bytes 256
  :doc "FNV-1a over the Message-ID's octets (at most 250), under the upload's owner.")
(defcost fn2-claim-begin-core :answers (:ok :bounds :state) :tables (fn2-core-claims)
  :doc "Start a claim on a Message-ID's exact octets.")
(defcost fn2-claim-state-core :doc "Read a transaction's claim state.")
(defcost fn2-claim-walk-core :answers (:claimed :wait :more :bounds :state :fault) :bytes 4096
  :tables (fn2-core-claims)
  :effects ((:acquire (:identity-reservation)))
  :doc "Walk the claim's bucket at most 16 chain steps (one Message-ID compared per step on an equal hash): claimed, waiting in the holder's FIFO, or more.")
(defcost fn2-claim-release-core :answers (:ok :bounds :state) :tables (fn2-core-claims fn2-core-machines)
  :effects ((:release (:identity-reservation)))
  :doc "Release a held claim and hand it to its FIFO's head, waking that transaction.")
(defcost fn2-txn-offer :answers (:ok :bounds :state)
  :tables (fn2-core-succ-txns fn2-core-id-decides fn2-core-fields)
  :doc "Start the identity decision for the upload's Message-ID and content digest.")
(defcost fn2-txn-count-next :answers (:ok :bounds) :bytes *fn2-txn-count-bytes*
  :doc "Count LF octets in up to 2,048 octets of the upload's body.")
(defcost fn2-txn-next-name :answers (:name :end :run :fault) :bytes *fn2-txn-scan-bytes*
  :doc "Scan chunk 0 for the next group name of Newsgroups.")
(defcost fn2-txn-put-post-for :answers t :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields)
  :doc "Declare the article's identity, article and outcome slots in the private successor.")
(defcost fn2-txn-put-evidence-for :answers t :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields)
  :doc "Declare the competing binding's evidence slots in the private successor (ruling 6).")
(defcost fn2-txn-wake-upload :tables (fn2-core-machines)
  :doc "Wake the upload this transaction held, if it still names it, so it drains.")

(defmachine fn2-txn
 :phases (:free :admit :reserve :lookup :prepare :ready :batched :accepted :refused :uncertain :releasing :draining :retired)
 :fields ((upload :link) (upload-gen :u60) (conn :link) (conn-gen :u60) (request :u32)
          (rule (:enum fn2-txn-rule (:post :ihave :takethis)))
          (tmode (:enum fn2-txn-mode (:article :evidence)))
          (ecommit (:enum fn2-txn-ecommit (:none :committed :uncertain :refused)))
          (batch :u60) (bevent :u60)
          (word :u8) (offered :bool) (prepared :bool) (counted :u60) (lines :u32)
          (gcur :u32) (gskip :bool) (ngroups :u8)
          (stopped :bool) (next-free :link))
 :stops (:txn-uncertain)
 :holds ((:admit :transaction-row) (:reserve :transaction-row)
         (:lookup :transaction-row :identity-reservation) (:prepare :transaction-row :identity-reservation)
         (:ready :transaction-row :identity-reservation)
         (:batched :transaction-row :identity-reservation :batch-membership)
         (:accepted :transaction-row :identity-reservation) (:refused :transaction-row :identity-reservation)
         (:uncertain :transaction-row :identity-reservation) (:releasing :transaction-row :identity-reservation)
         (:draining :transaction-row))
 :budget (:bytes 16384 :steps 32 :descriptors 0)
 :capacity (fn2-txn-capacity profile)
 ;; An upload takes the row at its :identity (section 14.3).
 :taken (:phase :admit :rows :transaction-row :ranges ()
         :copy (upload upload-gen conn conn-gen request rule principal-slot)
         :clear (tmode ecommit batch bevent word offered prepared counted lines gcur gskip ngroups stopped))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (upload *fn2-none*) (conn *fn2-none*) (account-ref *fn2-none*) (next-free fn2-machine-initial-next-free))
 :subarms
 (;; one Newsgroups name: look it up, declare its group-count accept
  (group :on-refusal ((:stop :machine-phase))
   (:do (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view row-upload))
   (:do (status start len next skip2)
        (fn2-txn-next-name no row-gcur nl (equal row-gskip 1) c0 g0
                           :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen)
    :accept (:run :end :name) :why "the name scan's three continuations; :fault goes to :on-refusal")
   (:cond ((not (unsigned-byte-p 32 next)) (:stop :machine-phase))
          ((eq status :run) (:set (gcur next) (gskip (if skip2 1 0)))
                            (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
          ((eq status :end) (:set (gcur next)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
          (t (:do (code group) (fn2-group-lookup row-slot c0 g0 (+ no start) len
                                                 :budget 4096 :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen)
              :accept ()
              :case (((:more) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                     ((:absent) (:set (gcur next)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                     ((:ok)
                      (:cond ((>= row-ngroups *fn2-txn-groups-max*)
                              (:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                              (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                             (t (:let i (+ *fn2-txn-slot-accepts* row-ngroups))
                                (:do (c1) (fn2-successor-put row-slot i *fn2-txn-counts-sid* ':accept))
                                (:do (c2) (fn2-successor-arg row-slot i 0 ':value group))
                                (:set (ngroups (+ 1 row-ngroups)) (gcur next))
                                (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t)))))))))
  ;; the outcome: the word to the connection (waking it), the successor released
  (reply :on-refusal ((:stop :machine-phase))
   (:if (not (equal row-word 0))
        ((:do (pcode) (fn2-conn-post-word row-conn row-conn-gen row-request row-word)
          :accept (:ok :dropped) :why "a connection that moved on takes no word; its release woke the upload")
         (:do (rcode) (fn2-successor-release row-slot))
         (:next :releasing) (:charge :steps *fn2-work-transition* :runnable t))
        ((:do (rcode) (fn2-successor-release row-slot))
         (:next :releasing) (:charge :steps *fn2-work-transition* :runnable t)))))
 :arms
 ((:free (:idle))
  ;; wait for the verdict when no Message-ID was scanned (posting the upload's
  ;; word, or :not-stored); else hash it and begin the claim
  (:admit :on-refusal ((:stop :machine-phase))
   (:cond ((not (fn2-txn-upload-live-p row-upload row-upload-gen id row-generation))
           (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
          (t (:do (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view row-upload))
             (:cond ((and (equal ml 0) (fn2-txn-upload-sealed-p row-upload))
                     (:do (w inj) (fn2-txn-upload-words row-upload))
                     (:do (pcode) (fn2-conn-post-word row-conn row-conn-gen row-request
                                                      (cond ((not (equal w 0)) w) ((not (equal inj 0)) inj)
                                                            (t *fn2-upload-word-not-stored*)))
                      :accept (:ok :dropped) :why "a connection that moved on takes no word")
                     (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
                    ((and (equal ml 0) (fn2-txn-upload-aborting-p row-upload))
                     (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
                    ((equal ml 0) (:charge :bytes 256 :steps *fn2-work-transition*))
                    (t (:do (hcode hash) (fn2-txn-hash ml c0 g0 mo :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen))
                       (:do (bcode) (fn2-claim-begin-core row-slot hash c0 g0 mo ml
                                                          :ok *fn2-upload-kind* :os row-upload :og row-upload-gen))
                       (:next :reserve) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))))))
  ;; the claim walk: held, waiting in the holder's FIFO, or more
  (:reserve :on-refusal ((:stop :machine-phase))
   (:let s (fn2-claim-state-core row-slot))
   (:cond ((equal s *fn2-claim-state-held*) (:next :lookup) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((equal s *fn2-claim-state-waiting*) (:charge :bytes 4096 :steps *fn2-work-transition*))
          (t (:do (code holder) (fn2-claim-walk-core row-slot *fn2-txn-claim-steps*)
              :accept ()
              :case (((:claimed) (:next :lookup) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                     ((:wait) (:charge :bytes 4096 :steps *fn2-work-transition*))
                     ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))))
  ;; the upload's verdict, then the identity offer (one run) or one decision step,
  ;; routed from C's separate facts (ruling 6, ruling 8)
  (:lookup :on-refusal ((:stop :machine-phase))
   (:cond ((not (and (fn2-txn-upload-live-p row-upload row-upload-gen id row-generation)
                     (not (fn2-txn-upload-aborting-p row-upload))))
           (:set (word 0)) (:next :refused) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((not (fn2-txn-upload-sealed-p row-upload)) (:charge :bytes 4096 :steps *fn2-work-transition*))
          (t (:do (w inj) (fn2-txn-upload-words row-upload))
             (:cond ((not (equal w 0)) (:set (word w)) (:next :refused)
                                       (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                    ((not (equal row-offered 1))
                     (:do (code) (fn2-txn-offer row-slot row-upload row-upload-gen))
                     (:set (offered 1)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                    (t (:do (answer) (fn2-identity-decide row-slot 4096)
                        :accept ()
                        :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                               ((:stored :duplicate :conflict :evidence)
                                (:do (fcode verdict selection h evidence coverage) (fn2-identity-facts row-slot))
                                (:cond ((eq selection :same)
                                        (:set (word *fn2-upload-word-duplicate*)) (:next :refused)
                                        (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                                       ((and (eq verdict :stored) (not (equal row-tmode *fn2-txn-mode-evidence*)))
                                        (:set (tmode *fn2-txn-mode-article*)) (:next :prepare)
                                        (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                                       (t (:set (tmode *fn2-txn-mode-evidence*) (word *fn2-upload-word-conflict*))
                                          (:next :prepare)
                                          (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))))))))
  ;; count the body's lines, look each group up, refuse :group or the injected
  ;; fields, declare the slots (evidence or article); then resolve them
  (:prepare :on-refusal ((:stop :machine-phase))
   (:if (equal row-prepared 1)
        ((:do (answer) (fn2-successor-resolve row-slot 4096)
          :accept ()
          :case (((:ok) (:next :ready) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                 ((:more) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t)))))
        ((:if (equal row-tmode *fn2-txn-mode-evidence*)
              ((:do (fcode verdict selection h evidence coverage) (fn2-identity-facts row-slot))
               (:do (pcode) (fn2-txn-put-evidence-for row-slot row-upload row-upload-gen h row-principal-slot))
               (:set (prepared 1))
               (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
              ((:do (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view row-upload))
               (:let counted (max scanned row-counted))
               (:cond ((< counted hashed)
                       (:do (ccode counted2 lines2) (fn2-txn-count-next row-upload row-upload-gen counted hashed row-lines))
                       (:if (and (unsigned-byte-p 60 counted2) (unsigned-byte-p 32 lines2))
                            ((:set (counted counted2) (lines lines2))
                             (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                            ((:stop :machine-phase))))
                      ((< row-gcur nl) (:goto group))
                      ((equal row-ngroups 0)
                       (:set (word *fn2-upload-word-group*)) (:next :refused)
                       (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                      (t (:do (w inj) (fn2-txn-upload-words row-upload))
                         (:if (not (equal inj 0))
                              ((:set (word inj)) (:next :refused)
                               (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                              ((:do (fcode verdict selection h evidence coverage) (fn2-identity-facts row-slot))
                               (:do (pcode) (fn2-txn-put-post-for row-slot row-upload row-upload-gen h row-principal-slot row-lines))
                               (:set (prepared 1))
                               (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))))))))))
  ;; stage every slot against the tip, admit the member, bind on :ok (one run)
  (:ready :on-refusal ((:stop :machine-phase))
   (:do (scode i) (fn2-successor-stage row-slot)
    :accept ()
    :case (((:ok)
            (:do (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view row-upload))
            (:do (acode b ev) (fn2-commit-admit-txn c0 g0 0
                                                    :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen)
             :effects ((:acquire (:batch-membership)))
             :accept ()
             :case (((:ok)
                     (:if (and (unsigned-byte-p 60 b) (unsigned-byte-p 60 ev))
                          ((:do (bcode) (fn2-successor-bind row-slot b ev))
                           (:set (batch b) (bevent ev))
                           (:next :batched) (:charge :bytes 16384 :steps *fn2-work-transition*))
                          ((:stop :machine-phase))))
                    ((:exhausted) (:park :batch-membership :steps *fn2-work-transition*))
                    ((:admission)
                     (:if (equal row-tmode *fn2-txn-mode-evidence*)
                          ((:set (ecommit *fn2-txn-ecommit-refused*) (word *fn2-upload-word-conflict*))
                           (:next :refused) (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
                          ((:set (word *fn2-upload-word-not-stored*))
                           (:next :refused) (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t)))))))
           ((:full) (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
           ((:stale) (:set (offered 0)) (:next :lookup) (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
           ((:refused :evidence)
            (:do (rcode) (fn2-successor-release row-slot))
            (:set (tmode *fn2-txn-mode-evidence*) (word *fn2-upload-word-conflict*) (offered 0) (prepared 0))
            (:next :lookup) (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
           ((:duplicate) (:set (word *fn2-upload-word-duplicate*)) (:next :refused)
                         (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
           ((:capacity) (:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                        (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t)))))
  (:batched :on-refusal ((:stop :machine-phase))
   (:do (tcode tbatch tevent tout)
        (fn2-commit-take :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen)
    :effects ((:release (:batch-membership)))
    :accept ()
    :case (((:pending) (:charge :steps *fn2-work-empty*))
           ((:ok)
            (:cond ((equal tout *fn2-commit-outcome-accepted*)
                    (:if (equal row-tmode *fn2-txn-mode-evidence*)
                         ((:set (ecommit *fn2-txn-ecommit-committed*) (word *fn2-upload-word-conflict*))
                          (:next :refused) (:charge :steps *fn2-work-transition* :runnable t))
                         ((:set (word *fn2-upload-word-accepted*))
                          (:next :accepted) (:charge :steps *fn2-work-transition* :runnable t))))
                   ((equal tout *fn2-commit-outcome-uncertain*)
                    (:set (ecommit (if (equal row-tmode *fn2-txn-mode-evidence*) *fn2-txn-ecommit-uncertain* row-ecommit))
                          (word *fn2-upload-word-uncertain*))
                    (:next :uncertain) (:charge :steps *fn2-work-transition* :runnable t))
                   ((equal tout *fn2-commit-outcome-refused*)
                    (:if (equal row-tmode *fn2-txn-mode-evidence*)
                         ((:set (ecommit *fn2-txn-ecommit-refused*) (word *fn2-upload-word-conflict*))
                          (:next :refused) (:charge :steps *fn2-work-transition* :runnable t))
                         ((:set (word *fn2-upload-word-not-stored*))
                          (:next :refused) (:charge :steps *fn2-work-transition* :runnable t))))
                   (t (:stop :machine-phase)))))))
  (:accepted (:goto reply))
  (:refused (:goto reply))
  (:uncertain (:stop :txn-uncertain))
  ;; release the claim; its FIFO's head takes it and is woken (the run's one wake)
  (:releasing :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-claim-release-core row-slot))
   (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))
  (:draining
   (:let u row-upload) (:let gen row-generation)
   (:let next (fn2-machine-free-head *fn2-txn-admission-ordinal*))
   (:let retire (>= gen (fn2-machine-gen-limit)))
   (:set (generation (if retire gen (+ 1 gen))) (upload *fn2-none*) (upload-gen 0) (conn *fn2-none*) (conn-gen 0)
         (next-free next) (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free))
   (:do () (fn2-machine-reclaim-fn2-txn id retire))
   (:do () (fn2-txn-wake-upload u id gen))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle))))

;; ------------------------------------------------------------------------
;; The operations, materialized after the core instance (assembly-callbacks-d-txn,
;; after the upload's continuations): wrappers over the claim table and C's seams.
(defmacro fn2-txn-op-events ()
 '(progn
(defun fn2-txn-hash (n slot gen off okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp n) (natp off))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code h1)
    (mv-let (code h1 h2) (fn2-ribbon-hash n slot gen off 0 okind oslot ogen fn2-pool)
      (declare (ignore h2)) (mv code h1))
    (mv code h1)))
(defthm fn2-txn-hash-type
  (unsigned-byte-p 32 (mv-nth 1 (fn2-txn-hash n slot gen off okind oslot ogen fn2-core))))
(defun fn2-claim-begin-core (c hash slot gen off len ok os og fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-claims (fn2-core-claims fn2-core)))
    (code fn2-claims) (fn2-claim-begin c hash slot gen off len ok os og fn2-claims) (mv code fn2-core)))
(fn2-core-preserves fn2-claim-begin-core (c hash slot gen off len ok os og fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-claim-walk-core (c budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp budget))))
  (stobj-let ((fn2-claims (fn2-core-claims fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
    (code holder fn2-claims) (fn2-claim-walk c budget fn2-claims fn2-pool) (mv code holder fn2-core)))
(fn2-core-preserves fn2-claim-walk-core (c budget fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-claim-state-core (c fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-claims (fn2-core-claims fn2-core)))
    (s) (if (fn2-claim-rowp c fn2-claims) (fn2-claims-state c fn2-claims) *fn2-claim-state-free*) s))
;; Release C's claim; the FIFO's head W (a claim row = a transaction slot)
;; takes it in the same step and is woken.
(defun fn2-claim-release-core (c fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv code w fn2-core)
        (stobj-let ((fn2-claims (fn2-core-claims fn2-core)))
          (code w fn2-claims) (fn2-claim-release c fn2-claims) (mv code w fn2-core)))
       ((unless (eq code :ok)) (mv code fn2-core))
       ((when (equal w *fn2-none*)) (mv :ok fn2-core))
       (waiter (+ (fn2-machine-kind-base *fn2-txn-kind* fn2-core) (nfix w)))
       ((unless (and (fn2-machine-idp waiter fn2-core) (eq (fn2-txn-snapshot-read-code waiter fn2-core) :ok)))
        (mv :bounds fn2-core)))
    (let ((fn2-core (fn2-machine-set-wake-id waiter fn2-core))) (mv :ok fn2-core))))
(fn2-core-preserves fn2-claim-release-core (c fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-commit-admit-txn fn2-txn-hash fn2-claim-begin-core fn2-claim-walk-core fn2-claim-state-core
                    fn2-claim-release-core))

;; The upload this transaction serves, read across rows (no cross-row
;; write): live while it keeps its generation and still names this
;; transaction; sealed once its verdict is written (the digest is stored in
;; window right after the source, fn2-upload-digest-at; the source is hashed
;; whole).
(defun fn2-txn-upload-live-p (u ugen id gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
       (equal (fn2-machine-generation u fn2-core) ugen)
       (equal (fn2-upload-row-txn u fn2-core) id)
       (equal (fn2-upload-row-txn-gen u fn2-core) gen)))
(defun fn2-txn-upload-sealed-p (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
       (equal (fn2-upload-row-phase u fn2-core) *fn2-upload-state-sealed*)))
(defun fn2-txn-upload-aborting-p (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
       (equal (fn2-upload-row-phase u fn2-core) *fn2-upload-state-aborting*)))
;; The upload's verdict when it is sealed: its definite refusal word, else
;; its injected-field word (Xref/Injection, checked after identity and group
;; in the model's order), else 0.
(defun fn2-txn-upload-words (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
      (mv (fn2-upload-row-word u fn2-core) (fn2-upload-row-inj u fn2-core))
    (mv 0 0)))
(defun fn2-txn-upload-view (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
      (mv (nfix (fn2-upload-row-ml u fn2-core))
          (nfix (fn2-upload-row-mo u fn2-core))
          (nfix (fn2-upload-row-c0-slot u fn2-core))
          (nfix (fn2-upload-row-c0-gen u fn2-core))
          (nfix (fn2-upload-row-c1-slot u fn2-core))
          (nfix (fn2-upload-row-c1-gen u fn2-core))
          (nfix (fn2-upload-row-hashed u fn2-core))
          (nfix (fn2-upload-row-scan-off u fn2-core))
          (nfix (fn2-upload-row-no u fn2-core))
          (nfix (fn2-upload-row-nl u fn2-core)))
    (mv 0 0 0 0 0 0 0 0 0 0)))
(defthm fn2-txn-upload-view-natp-0 (natp (mv-nth 0 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
(defthm fn2-txn-upload-view-natp-1 (natp (mv-nth 1 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
(defthm fn2-txn-upload-view-natp-2 (natp (mv-nth 2 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
(defthm fn2-txn-upload-view-natp-3 (natp (mv-nth 3 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
(defthm fn2-txn-upload-view-natp-4 (natp (mv-nth 4 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
(defthm fn2-txn-upload-view-natp-5 (natp (mv-nth 5 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
(defthm fn2-txn-upload-view-natp-6 (natp (mv-nth 6 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
(defthm fn2-txn-upload-view-natp-7 (natp (mv-nth 7 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
(defthm fn2-txn-upload-view-natp-8 (natp (mv-nth 8 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
(defthm fn2-txn-upload-view-natp-9 (natp (mv-nth 9 (fn2-txn-upload-view u fn2-core))) :rule-classes :type-prescription)
;; At the drain: wake the upload U if it still names this row (ID of
;; generation GEN), so it sees the row gone and drains.
(defun fn2-txn-wake-upload (u id gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok) (fn2-machine-idp u fn2-core)
           (equal (fn2-upload-row-txn u fn2-core) id) (equal (fn2-upload-row-txn-gen u fn2-core) gen))
      (fn2-machine-set-wake-id u fn2-core)
    fn2-core))
(fn2-core-preserves fn2-txn-wake-upload (u id gen fn2-core) :rows nil)
(in-theory (disable fn2-txn-upload-words fn2-txn-upload-view fn2-txn-wake-upload))

(defun fn2-txn-offer (tx u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view u fn2-core)
    (declare (ignore scanned no nl))
    (mv-let (in1 doff) (fn2-upload-digest-at hashed (fn2-upload-chunk-cap c0 fn2-core))
      (fn2-identity-decide-start tx c0 g0 mo ml (if in1 c1 c0) (if in1 g1 g0) doff *fn2-upload-kind* u ugen fn2-core))))
(fn2-core-preserves fn2-txn-offer (tx u ugen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-offer))

;; :prepare. The body's lines first (the article row's `lines`): LF octets of
;; [body, source) read under the upload's owner, at most
;; *fn2-txn-count-bytes* per run, COUNTED the continuation.
(defun fn2-txn-count-loop (n slot gen off lines okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off) (natp lines))))
  (if (zp n) (mv :ok lines)
    (mv-let (ok byte) (fn2-gram-read slot gen off okind oslot ogen fn2-pool)
      (if (not ok) (mv :bounds lines)
        (fn2-txn-count-loop (- n 1) slot gen (+ 1 off) (if (equal byte 10) (+ 1 (nfix lines)) (nfix lines))
                            okind oslot ogen fn2-pool)))))
(defthm fn2-txn-count-loop-natp
  (implies (natp lines) (natp (mv-nth 1 (fn2-txn-count-loop n slot gen off lines okind oslot ogen fn2-pool))))
  :rule-classes :type-prescription)
(defthm fn2-txn-count-loop-bound
  (implies (natp lines) (<= (mv-nth 1 (fn2-txn-count-loop n slot gen off lines okind oslot ogen fn2-pool))
                            (+ lines (nfix n))))
  :rule-classes :linear)
(in-theory (disable fn2-txn-count-loop))
(defun fn2-txn-count (slot gen off n lines okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp off) (natp n) (natp lines))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code lines2) (fn2-txn-count-loop n slot gen off lines okind oslot ogen fn2-pool) (mv code lines2)))
(defthm fn2-txn-count-natp
  (implies (natp lines) (natp (mv-nth 1 (fn2-txn-count slot gen off n lines okind oslot ogen fn2-core))))
  :rule-classes :type-prescription)
(in-theory (disable fn2-txn-count))
;; One counting run over [from, to) of the source (chunk 0 then chunk 1):
;; (mv code counted lines).
(defun fn2-txn-count-run (from to lines c0 g0 c1 g1 cap0 u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp from) (natp to) (natp lines) (natp cap0))))
  (b* ((in0 (< from cap0))
       (n (min *fn2-txn-count-bytes* (min (nfix (- to from)) (if in0 (- cap0 from) (nfix (- to from))))))
       ((mv code lines2) (fn2-txn-count (if in0 c0 c1) (if in0 g0 g1) (if in0 from (- from cap0)) n lines
                                        *fn2-upload-kind* u ugen fn2-core)))
    (mv code (+ from n) lines2)))
(defthm fn2-txn-count-run-natp
  (implies (and (natp from) (natp lines))
           (and (natp (mv-nth 1 (fn2-txn-count-run from to lines c0 g0 c1 g1 cap0 u ugen fn2-core)))
                (natp (mv-nth 2 (fn2-txn-count-run from to lines c0 g0 c1 g1 cap0 u ugen fn2-core)))))
  :rule-classes :type-prescription)
(in-theory (disable fn2-txn-count-run))
(defun fn2-txn-count-next (u ugen counted to lines fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp counted) (natp to) (natp lines))))
  (mv-let (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view u fn2-core)
    (declare (ignore ml mo hashed scanned no nl))
    (fn2-txn-count-run counted to lines c0 g0 c1 g1 (fn2-upload-chunk-cap c0 fn2-core) u ugen fn2-core)))
(in-theory (disable fn2-txn-count-next))
;; The write slots of an accepted POST (C-S3): the identity admission (C
;; §4a; fn2-txn-put-identity), the article row (key and birth the same event, live, version
;; 1, the source's content identity (appended after the source), the stored
;; length, the source until injection in D5 2/n, and the body's lines) and
;; the operation outcome ((principal, operation) with the operation the
;; member's commit position, fresh per NNTP attempt: NNT-005; the request
;; binding the source's identity; accepted; the event).
(defmacro fn2-txn-chain (&rest calls)
  (if (atom calls) '(mv :ok fn2-core)
    (if (atom (cdr calls)) (car calls)
      `(mv-let (c fn2-core) ,(car calls) (if (eq c :ok) (fn2-txn-chain ,@(cdr calls)) (mv c fn2-core))))))
;; The identity admission (C §4a) for the name [MOFF, MOFF+MLEN) of
;; MSLOT/MGEN and the content digest [DOFF, DOFF+32) of DSLOT/DGEN, both
;; read under OKIND OSLOT OGEN; H the decision's candidate ordinal (0 when
;; the content is new). Always: the evidence of the binding (its occurrence
;; the member's commit position, issued by PRINCIPAL), the summary's :admit
;; and the candidate's :admit (its ordinal the summary's new candidate count
;; when new, else H). For a local acceptance (LOCAL 1) also this domain's
;; history entry (its position and article the member's commit position)
;; and the article index, and the summary establishes the selection; else
;; (LOCAL 0) evidence only, its history and index slots empty.
(defmacro fn2-txn-put-name (i j)
  `(fn2-successor-arg-octets tx ,i ,j mslot mgen moff mlen okind oslot ogen fn2-core))
(defmacro fn2-txn-put-digest (i j)
  `(fn2-successor-arg-octets tx ,i ,j dslot dgen doff *fn2-upload-digest-octets* okind oslot ogen fn2-core))
;; The ordinal arg J of slot I: the summary's new candidate count when the
;; content is new (H 0), else H.
(defun fn2-txn-put-ordinal (tx i j h fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (equal h 0)
      (fn2-successor-arg tx i j :out (+ (* *fn2-txn-slot-summary* 256) *fn2-identity-summary-entry-field-candidates*) fn2-core)
    (fn2-successor-arg tx i j :value h fn2-core)))
(fn2-core-preserves fn2-txn-put-ordinal (tx i j h fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-put-ordinal))
(defun fn2-txn-put-local (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((r *fn2-txn-slot-history*))
    (fn2-txn-chain
     (fn2-successor-put tx r *fn2-txn-history-sid* :insert fn2-core)
     (fn2-successor-arg tx r *fn2-identity-history-entry-field-namespace* :value *fn2-identity-namespace-netnews* fn2-core)
     (fn2-txn-put-name r *fn2-identity-history-entry-field-name*)
     (fn2-successor-arg tx r *fn2-identity-history-entry-field-profile* :value *fn2-identity-profile-source* fn2-core)
     (fn2-successor-arg tx r *fn2-identity-history-entry-field-algorithm* :value *fn2-identity-algorithm-blake3* fn2-core)
     (fn2-txn-put-digest r *fn2-identity-history-entry-field-digest*)
     (fn2-successor-arg tx r *fn2-identity-history-entry-field-lineage* :value *fn2-identity-lineage* fn2-core)
     (fn2-successor-arg tx r *fn2-identity-history-entry-field-domain* :value *fn2-identity-domain* fn2-core)
     (fn2-successor-arg tx r *fn2-identity-history-entry-field-incarnation* :value *fn2-identity-incarnation* fn2-core)
     (fn2-successor-arg tx r *fn2-identity-history-entry-field-position* :event 0 fn2-core)
     (fn2-successor-arg tx r *fn2-identity-history-entry-field-evidence* :event 0 fn2-core)
     (fn2-successor-arg tx r *fn2-identity-history-entry-field-article* :event 0 fn2-core))))
(fn2-core-preserves fn2-txn-put-local (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-put-local))
;; The article index (slot 4), after the summary (its ordinal may be the
;; summary's :out).
(defun fn2-txn-put-index (tx mslot mgen moff mlen okind oslot ogen h fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((x *fn2-txn-slot-index*))
    (fn2-txn-chain
     (fn2-successor-put tx x *fn2-txn-index-sid* :insert fn2-core)
     (fn2-successor-arg tx x *fn2-identity-article-entry-field-namespace* :value *fn2-identity-namespace-netnews* fn2-core)
     (fn2-txn-put-name x *fn2-identity-article-entry-field-name*)
     (fn2-txn-put-ordinal tx x *fn2-identity-article-entry-field-h* h fn2-core)
     (fn2-successor-arg tx x *fn2-identity-article-entry-field-article* :event 0 fn2-core))))
(fn2-core-preserves fn2-txn-put-index (tx mslot mgen moff mlen okind oslot ogen h fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-put-index))
;; Evidence (slot 0) of the binding, its occurrence the commit position.
(defun fn2-txn-put-evidence (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen principal fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((e *fn2-txn-slot-evidence*))
    (fn2-txn-chain
     (fn2-successor-put tx e *fn2-txn-evidence-sid* :insert fn2-core)
     (fn2-successor-arg tx e *fn2-identity-evidence-entry-field-namespace* :value *fn2-identity-namespace-netnews* fn2-core)
     (fn2-txn-put-name e *fn2-identity-evidence-entry-field-name*)
     (fn2-successor-arg tx e *fn2-identity-evidence-entry-field-profile* :value *fn2-identity-profile-source* fn2-core)
     (fn2-successor-arg tx e *fn2-identity-evidence-entry-field-algorithm* :value *fn2-identity-algorithm-blake3* fn2-core)
     (fn2-txn-put-digest e *fn2-identity-evidence-entry-field-digest*)
     (fn2-successor-arg tx e *fn2-identity-evidence-entry-field-lineage* :value *fn2-identity-lineage* fn2-core)
     (fn2-successor-arg tx e *fn2-identity-evidence-entry-field-domain* :value *fn2-identity-domain* fn2-core)
     (fn2-successor-arg tx e *fn2-identity-evidence-entry-field-incarnation* :value *fn2-identity-incarnation* fn2-core)
     (fn2-successor-arg tx e *fn2-identity-evidence-entry-field-occurrence* :event 0 fn2-core)
     (fn2-successor-arg tx e *fn2-identity-evidence-entry-field-kind* :value *fn2-identity-evidence-kind-binding* fn2-core)
     (fn2-successor-arg tx e *fn2-identity-evidence-entry-field-issuer* :value principal fn2-core))))
(fn2-core-preserves fn2-txn-put-evidence (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen principal fn2-core)
  :position 1 :rows nil)
;; The summary's :admit (slot 2; namespace name ne nr est oldh, h assigned).
(defun fn2-txn-put-summary (tx mslot mgen moff mlen okind oslot ogen h l fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((m *fn2-txn-slot-summary*))
    (fn2-txn-chain
     (fn2-successor-put tx m *fn2-txn-summary-sid* :admit fn2-core)
     (fn2-successor-arg tx m 0 :value *fn2-identity-namespace-netnews* fn2-core)
     (fn2-txn-put-name m 1)
     (fn2-successor-arg tx m 2 :new *fn2-txn-slot-evidence* fn2-core)
     (fn2-successor-arg tx m 3 (if (equal l 1) :new :value) (if (equal l 1) *fn2-txn-slot-history* 0) fn2-core)
     (fn2-successor-arg tx m 4 :value l fn2-core)
     (fn2-successor-arg tx m 5 :value h fn2-core))))
(fn2-core-preserves fn2-txn-put-summary (tx mslot mgen moff mlen okind oslot ogen h l fn2-core) :position 1 :rows nil)
;; The candidate's :admit (slot 3; namespace name profile algorithm digest ch ne q l).
(defun fn2-txn-put-candidate (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h l fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((k *fn2-txn-slot-candidate*))
    (fn2-txn-chain
     (fn2-successor-put tx k *fn2-txn-candidates-sid* :admit fn2-core)
     (fn2-successor-arg tx k 0 :value *fn2-identity-namespace-netnews* fn2-core)
     (fn2-txn-put-name k 1)
     (fn2-successor-arg tx k 2 :value *fn2-identity-profile-source* fn2-core)
     (fn2-successor-arg tx k 3 :value *fn2-identity-algorithm-blake3* fn2-core)
     (fn2-txn-put-digest k 4)
     (fn2-txn-put-ordinal tx k 5 h fn2-core)
     (fn2-successor-arg tx k 6 :new *fn2-txn-slot-evidence* fn2-core)
     (fn2-successor-arg tx k 7 :value 1 fn2-core)
     (fn2-successor-arg tx k 8 :value l fn2-core))))
(fn2-core-preserves fn2-txn-put-candidate (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h l fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-txn-put-evidence fn2-txn-put-summary fn2-txn-put-candidate))
(defun fn2-txn-put-identity (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal local fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((l (if (equal local 1) 1 0)))
    (fn2-txn-chain
     (if (equal l 1) (fn2-txn-put-local tx mslot mgen moff mlen dslot dgen doff okind oslot ogen fn2-core) (mv :ok fn2-core))
     (fn2-txn-put-evidence tx mslot mgen moff mlen dslot dgen doff okind oslot ogen principal fn2-core)
     (fn2-txn-put-summary tx mslot mgen moff mlen okind oslot ogen h l fn2-core)
     (fn2-txn-put-candidate tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h l fn2-core)
     (if (equal l 1) (fn2-txn-put-index tx mslot mgen moff mlen okind oslot ogen h fn2-core) (mv :ok fn2-core)))))
(fn2-core-preserves fn2-txn-put-identity (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal local fn2-core)
  :position 1 :rows nil)
(defun fn2-txn-put-article (tx dslot dgen doff bytes lines principal u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((i *fn2-txn-slot-article*))
    (fn2-txn-chain
     (fn2-successor-put tx i *fn2-txn-article-sid* :insert fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-article* :event 0 fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-birth* :event 0 fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-state* :value *fn2-txn-article-live* fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-version* :value *fn2-txn-article-version* fn2-core)
     (fn2-successor-arg-octets tx i *fn2-article-entry-field-source* dslot dgen doff *fn2-upload-digest-octets*
                               *fn2-upload-kind* u ugen fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-bytes* :value bytes fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-lines* :value lines fn2-core)
     (fn2-successor-put tx *fn2-txn-slot-outcome* *fn2-txn-outcome-sid* :insert fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-principal* :value principal fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-operation* :event 0 fn2-core)
     (fn2-successor-arg-octets tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-request* dslot dgen doff
                               *fn2-upload-digest-octets* *fn2-upload-kind* u ugen fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-outcome* :value *fn2-txn-outcome-accepted* fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-event* :event 0 fn2-core))))
(fn2-core-preserves fn2-txn-put-article (tx dslot dgen doff bytes lines principal u ugen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-put-local fn2-txn-put-index fn2-txn-put-identity fn2-txn-put-article))
;; A POST's slots: the identity admission (a local acceptance) and the
;; article row with its outcome, one call for the declaring run.
(defun fn2-txn-put-post (tx mslot mgen moff mlen dslot dgen doff bytes lines u ugen h principal fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-txn-chain
   (fn2-txn-put-identity tx mslot mgen moff mlen dslot dgen doff *fn2-upload-kind* u ugen h principal 1 fn2-core)
   (fn2-txn-put-article tx dslot dgen doff bytes lines principal u ugen fn2-core)))
(fn2-core-preserves fn2-txn-put-post (tx mslot mgen moff mlen dslot dgen doff bytes lines u ugen h principal fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-txn-put-post))
(defun fn2-txn-put-post-for (tx u ugen h principal lines fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view u fn2-core)
    (declare (ignore scanned no nl))
    (mv-let (in1 doff) (fn2-upload-digest-at hashed (fn2-upload-chunk-cap c0 fn2-core))
      (fn2-txn-put-post tx c0 g0 mo ml (if in1 c1 c0) (if in1 g1 g0) doff hashed lines u ugen h principal fn2-core))))
(fn2-core-preserves fn2-txn-put-post-for (tx u ugen h principal lines fn2-core) :position 1 :rows nil)
(defun fn2-txn-put-evidence-for (tx u ugen h principal fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view u fn2-core)
    (declare (ignore scanned no nl))
    (mv-let (in1 doff) (fn2-upload-digest-at hashed (fn2-upload-chunk-cap c0 fn2-core))
      (fn2-txn-put-identity tx c0 g0 mo ml (if in1 c1 c0) (if in1 g1 g0) doff *fn2-upload-kind* u ugen h principal 0 fn2-core))))
(fn2-core-preserves fn2-txn-put-evidence-for (tx u ugen h principal fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-put-post-for fn2-txn-put-evidence-for))

;; Newsgroups, a name at a time: the value's names are separated by commas
;; and white space (the model's split).
(defun fn2-txn-sep-p (b) (declare (xargs :guard t)) (member b '(44 32 9 13 10)))
;; Skip separators from OFF, at most N octets: (mv ok pos).
(defun fn2-txn-skip-loop (n slot gen off okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n) :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off))))
  (if (zp n) (mv t off)
    (mv-let (ok b) (fn2-gram-read slot gen off okind oslot ogen fn2-pool)
      (cond ((not ok) (mv nil off))
            ((fn2-txn-sep-p b) (fn2-txn-skip-loop (- n 1) slot gen (+ 1 off) okind oslot ogen fn2-pool))
            (t (mv t off))))))
;; Advance over a name from OFF, at most N octets: (mv ok pos).
(defun fn2-txn-name-loop (n slot gen off okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n) :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off))))
  (if (zp n) (mv t off)
    (mv-let (ok b) (fn2-gram-read slot gen off okind oslot ogen fn2-pool)
      (cond ((not ok) (mv nil off))
            ((fn2-txn-sep-p b) (mv t off))
            (t (fn2-txn-name-loop (- n 1) slot gen (+ 1 off) okind oslot ogen fn2-pool))))))
(defthm fn2-txn-skip-loop-natp
  (implies (natp off) (natp (mv-nth 1 (fn2-txn-skip-loop n slot gen off okind oslot ogen fn2-pool))))
  :rule-classes :type-prescription)
(defthm fn2-txn-skip-loop-pos
  (implies (natp off) (and (<= off (mv-nth 1 (fn2-txn-skip-loop n slot gen off okind oslot ogen fn2-pool))) (<= (mv-nth 1 (fn2-txn-skip-loop n slot gen off okind oslot ogen fn2-pool)) (+ off (nfix n)))))
  :rule-classes :linear)
(defthm fn2-txn-name-loop-natp
  (implies (natp off) (natp (mv-nth 1 (fn2-txn-name-loop n slot gen off okind oslot ogen fn2-pool))))
  :rule-classes :type-prescription)
(defthm fn2-txn-name-loop-pos
  (implies (natp off) (and (<= off (mv-nth 1 (fn2-txn-name-loop n slot gen off okind oslot ogen fn2-pool))) (<= (mv-nth 1 (fn2-txn-name-loop n slot gen off okind oslot ogen fn2-pool)) (+ off (nfix n)))))
  :rule-classes :linear)
(in-theory (disable fn2-txn-skip-loop fn2-txn-name-loop))
;; The next name of [CUR, END) of the Newsgroups value (offsets relative to
;; its BASE in chunk 0): (mv status start len next skip). STATUS :name
;; (START LEN, NEXT past it), :end, :run (more scanning; NEXT and SKIP the
;; continuation), :fault. A name longer than 250 octets is no group: it is
;; skipped (SKIP) to its end, never looked up in part.
(defun fn2-txn-next-name (base cur end skip slot gen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp base) (natp cur) (natp end))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (status start len next skip2)
    (b* ((lim (max cur (min end (+ cur *fn2-txn-scan-bytes*))))
         ((when skip)
          (mv-let (ok pos) (fn2-txn-name-loop (- lim cur) slot gen (+ base cur) okind oslot ogen fn2-pool)
            (let ((pos (- pos base)))
              (if (not ok) (mv :fault 0 0 cur skip) (mv :run 0 0 pos (and (= pos lim) (< pos end)))))))
         ((mv ok s) (fn2-txn-skip-loop (- lim cur) slot gen (+ base cur) okind oslot ogen fn2-pool))
         (s (- s base))
         ((unless ok) (mv :fault 0 0 cur nil))
         ((when (>= s end)) (mv :end 0 0 end nil))
         ((when (>= s lim)) (mv :run 0 0 s nil))
         (tlim (min end (+ s 251)))
         ((mv ok2 e) (fn2-txn-name-loop (- tlim s) slot gen (+ base s) okind oslot ogen fn2-pool))
         (e (- e base))
         ((unless ok2) (mv :fault 0 0 cur nil))
         ((when (and (= e tlim) (< e end) (= (- e s) 251))) (mv :run 0 0 e t)))
      (mv :name s (- e s) e nil))
    (mv status start len next skip2)))
(defthm fn2-txn-next-name-types
  (implies (and (natp base) (natp cur) (natp end))
           (and (natp (mv-nth 1 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))
                (natp (mv-nth 2 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))
                (natp (mv-nth 3 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core))))))
(in-theory (disable fn2-txn-next-name))
))

;; ------------------------------------------------------------------------
;; The transaction's continuations (materialized after the upload's).
(defmacro fn2-txn-events ()
 '(progn
(defmachine-arms fn2-txn)
(defmachine-run fn2-txn)
))

; MACHINE-FORM 6.5 P4: the kind's take in child form, proved here;
; the admission section (assembly-callbacks-a) makes its core face.
(defmachine-registry fn2-txn)
