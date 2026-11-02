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
(include-book "txn-kind")
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

;; The :ready transition's byte bound: C-S3's stage, emit and bind and B's
;; admission happen in one run (nothing may stage or bind between a
;; transaction's stage and its bind), so the run's bound is their sum, above
;; ROUND2 B.3's 4 KiB (a departure recorded in the layer doc, 14.4).
(defconst *fn2-txn-admit-bytes* 4096)
(defconst *fn2-txn-ready-bytes* (+ 4096 8192 8192 *fn2-txn-admit-bytes*))
(assert-event (equal *fn2-txn-ready-bytes* 24576))  ; the kind's :budget below

(defconst *fn2-upload-word-accepted* (fn2-upload-word-code :accepted))
(defconst *fn2-upload-word-uncertain* (fn2-upload-word-code :uncertain))
(defconst *fn2-upload-word-duplicate* (fn2-upload-word-code :duplicate))
(defconst *fn2-upload-word-conflict* (fn2-upload-word-code :conflict))
(defconst *fn2-upload-word-group* (fn2-upload-word-code :group))
(defconst *fn2-upload-word-unaffordable* (fn2-upload-word-code :unaffordable))
(defconst *fn2-upload-word-not-stored* (fn2-upload-word-code :not-stored))

(defun fn2-txn-hash-pool (n slot gen off okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off))))
  (mv-let (code h1 h2) (fn2-ribbon-hash n slot gen off 0 okind oslot ogen fn2-pool)
    (declare (ignore h2)) (mv code h1)))
(defthm fn2-txn-hash-pool-type
  (unsigned-byte-p 32 (mv-nth 1 (fn2-txn-hash-pool n slot gen off okind oslot ogen fn2-pool))))
(in-theory (disable fn2-txn-hash-pool))

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
(defun fn2-txn-next-name-pool (base cur end skip slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp base) (natp cur) (natp end))))
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
    (mv :name s (- e s) e nil)))
(defthm fn2-txn-next-name-pool-types
  (implies (and (natp base) (natp cur) (natp end))
           (and (natp (mv-nth 1 (fn2-txn-next-name-pool base cur end skip slot gen okind oslot ogen fn2-pool)))
                (natp (mv-nth 2 (fn2-txn-next-name-pool base cur end skip slot gen okind oslot ogen fn2-pool)))
                (natp (mv-nth 3 (fn2-txn-next-name-pool base cur end skip slot gen okind oslot ogen fn2-pool))))))
(in-theory (disable fn2-txn-next-name-pool))

(defcost fn2-txn-hash :child fn2-txn-hash-pool :answers t :bytes 256
  :doc "FNV-1a over the Message-ID's octets (at most 250), under the upload's owner.")
(defcost fn2-claim-begin-core :child fn2-claim-begin :answers (:ok :bounds :state) :tables (fn2-core-claims)
  :doc "Start a claim on a Message-ID's exact octets.")
(defcost fn2-claim-state-core :child fn2-claim-state :effects :per-use :doc "Read a transaction's claim state.")
(defcost fn2-claim-walk-core :child fn2-claim-walk :answers (:claimed :wait :more :bounds :state :fault) :faults (:bounds :state :fault) :bytes 4096
  :tables (fn2-core-claims)
  :effects ((:acquire (:identity-reservation)))
  :doc "Walk the claim's bucket at most 16 chain steps (one Message-ID compared per step on an equal hash): claimed, waiting in the holder's FIFO, or more.")
(defcost fn2-claim-release-core :answers (:ok :bounds :state) :tables (fn2-core-claims fn2-core-machines)
  :effects ((:release (:identity-reservation)))
  :doc "Release a held claim and hand it to its FIFO's head, waking that transaction.")
(defcost fn2-txn-offer :answers (:ok :bounds :state)
  :tables (fn2-core-succ-txns fn2-core-id-decides fn2-core-fields)
  :doc "Start the identity decision for the upload's Message-ID and content digest.")
(defcost fn2-txn-count :child fn2-txn-count-loop :answers (:ok :bounds) :bytes *fn2-txn-count-bytes*
  :doc "Count LF octets in up to 2,048 octets of a pool slot.")
(defcost fn2-txn-count-next :answers (:ok :bounds) :bytes *fn2-txn-count-bytes*
  :doc "Count LF octets in up to 2,048 octets of the upload's body.")
(defcost fn2-txn-next-name :child fn2-txn-next-name-pool :answers (:name :end :run :fault) :faults (:fault) :bytes *fn2-txn-scan-bytes*
  :doc "Scan chunk 0 for the next group name of Newsgroups.")
(defcost fn2-txn-put-post-for :answers t :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields)
  :doc "Declare the article's identity, article and outcome slots in the private successor.")
(defcost fn2-txn-put-evidence-for :answers t :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields)
  :doc "Declare the competing binding's evidence slots in the private successor (ruling 6).")
(defcost fn2-txn-wake-upload :tables (fn2-core-machines)
  :doc "Wake the upload this transaction held, if it still names it, so it drains.")

(defmachine-arms fn2-txn :declare
 :subarms
 (;; one Newsgroups name: look it up, declare its group-count accept
  (group :on-refusal ((:stop :machine-phase))
   (:let gslot row-slot)
   (:let no (:read upload no)) (:let nl (:read upload nl))
   (:let c0 (:read upload c0-slot)) (:let g0 (:read upload c0-gen))
   (:do (status start len next skip2)
        (fn2-txn-next-name no row-gcur nl (equal row-gskip 1) c0 g0 :owner upload)
    :accept (:run :end :name) :why "the name scan's three continuations; :fault goes to :on-refusal")
   (:cond ((not (unsigned-byte-p 32 next)) (:stop :machine-phase))
          ((eq status :run) (:set (gcur next) (gskip (if skip2 1 0)))
                            (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
          ((eq status :end) (:set (gcur next)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
          (t (:do (code group) (fn2-group-lookup gslot c0 g0 (+ no start) len :budget 4096 :owner upload)
              :accept ()
              :case (((:more) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                     ((:absent) (:set (gcur next)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                     ((:ok)
                      (:cond ((>= row-ngroups *fn2-txn-groups-max*)
                              (:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                              (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                             (t (:let i (+ *fn2-txn-slot-accepts* row-ngroups))
                                (:do (pcode) (fn2-group-counts-put-accept gslot i ':value group))
                                (:set (ngroups (+ 1 row-ngroups)) (gcur next))
                                (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t)))))))))
  ;; the outcome: the word to the connection (waking it), the successor released
  (reply :on-refusal ((:stop :machine-phase))
   (:let rslot row-slot)
   (:if (not (equal row-word 0))
        ((:do (pcode) (fn2-conn-post-word row-conn row-conn-gen row-request row-word))
         (:do (rcode) (fn2-successor-release rslot)
          :accept (:ok :state) :why "a committed or bound transaction's successor is already closed")
         (:next :releasing) (:charge :steps *fn2-work-transition* :runnable t))
        ((:do (rcode) (fn2-successor-release rslot)
          :accept (:ok :state) :why "a committed or bound transaction's successor is already closed")
         (:next :releasing) (:charge :steps *fn2-work-transition* :runnable t)))))
 :arms
 ((:free (:idle))
  ;; wait for the verdict when no Message-ID was scanned (posting the upload's
  ;; word, or :not-stored); else hash it and begin the claim
  (:admit :on-refusal ((:stop :machine-phase))
   (:cond ((not (:live upload))
           (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
          (t (:let ml (:read upload ml)) (:let mo (:read upload mo))
             (:let c0 (:read upload c0-slot)) (:let g0 (:read upload c0-gen))
             (:let uphase (:read upload phase))
             (:cond ((and (equal ml 0) (equal uphase *fn2-upload-state-sealed*))
                     (:let w (:read upload word)) (:let inj (:read upload inj))
                     (:do (pcode) (fn2-conn-post-word row-conn row-conn-gen row-request
                                                      (cond ((not (equal w 0)) w) ((not (equal inj 0)) inj)
                                                            (t *fn2-upload-word-not-stored*))))
                     (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
                    ((and (equal ml 0) (equal uphase *fn2-upload-state-aborting*))
                     (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
                    ((equal ml 0) (:charge :bytes 256 :steps *fn2-work-transition*))
                    (t (:do (hcode hash) (fn2-txn-hash ml c0 g0 mo :owner upload))
                       (:do (bcode) (fn2-claim-begin-core row-slot hash c0 g0 mo ml :owner upload))
                       (:next :reserve) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))))))
  ;; the claim walk: held, waiting in the holder's FIFO, or more
  (:reserve :on-refusal ((:stop :machine-phase))
   (:let s (fn2-claim-state-core row-slot))
   (:cond ((equal s *fn2-claim-state-held*)
           (:do (s2) (fn2-claim-state-core row-slot) :effects ((:acquire (:identity-reservation))))
           (:next :lookup) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((equal s *fn2-claim-state-waiting*) (:charge :bytes 4096 :steps *fn2-work-transition*))
          (t (:do (code holder) (fn2-claim-walk-core row-slot *fn2-txn-claim-steps*)
              :accept ()
              :case (((:claimed) (:next :lookup) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                     ((:wait) (:charge :bytes 4096 :steps *fn2-work-transition*))
                     ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))))
  ;; the upload's verdict, then the identity offer (one run) or one decision step,
  ;; routed from C's separate facts (ruling 6, ruling 8)
  (:lookup :on-refusal ((:stop :machine-phase))
   (:let lslot row-slot)
   (:let uphase (:read upload phase))
   (:cond ((not (and (:live upload) (not (equal uphase *fn2-upload-state-aborting*))))
           (:set (word 0)) (:next :refused) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((not (equal uphase *fn2-upload-state-sealed*)) (:charge :bytes 4096 :steps *fn2-work-transition*))
          (t (:let w (:read upload word))
             (:cond ((not (equal w 0)) (:set (word w)) (:next :refused)
                                       (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                    ((not (equal row-offered 1))
                     (:do (code) (fn2-txn-offer lslot (:read upload mo) (:read upload ml)
                                                (:read upload c0-slot) (:read upload c0-gen)
                                                (:read upload c1-slot) (:read upload c1-gen)
                                                (:read upload hashed) :owner upload))
                     (:set (offered 1)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                    (t (:do (answer) (fn2-identity-decide lslot 4096)
                        :accept ()
                        :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                               ((:stored :duplicate :conflict :evidence)
                                (:do (fcode verdict selection h evidence coverage) (fn2-identity-facts lslot))
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
               (:do (pcode) (fn2-txn-put-evidence-for row-slot (:read upload mo) (:read upload ml)
                                                      (:read upload c0-slot) (:read upload c0-gen)
                                                      (:read upload c1-slot) (:read upload c1-gen)
                                                      (:read upload hashed) h row-principal-slot :owner upload))
               (:set (prepared 1))
               (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
              ((:let c0 (:read upload c0-slot)) (:let g0 (:read upload c0-gen))
               (:let c1 (:read upload c1-slot)) (:let g1 (:read upload c1-gen))
               (:let hashed (:read upload hashed)) (:let scanned (:read upload scan-off))
               (:let nl (:read upload nl))
               (:let counted (max scanned row-counted))
               (:cond ((< counted hashed)
                       (:do (ccode counted2 lines2)
                            (fn2-txn-count-next c0 g0 c1 g1 counted hashed row-lines :owner upload))
                       (:if (and (unsigned-byte-p 60 counted2) (unsigned-byte-p 32 lines2))
                            ((:set (counted counted2) (lines lines2))
                             (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                            ((:stop :machine-phase))))
                      ((< row-gcur nl) (:goto group))
                      ((equal row-ngroups 0)
                       (:set (word *fn2-upload-word-group*)) (:next :refused)
                       (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                      (t (:let inj (:read upload inj))
                         (:if (not (equal inj 0))
                              ((:set (word inj)) (:next :refused)
                               (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                              ((:do (fcode verdict selection h evidence coverage) (fn2-identity-facts row-slot))
                               (:do (pcode) (fn2-txn-put-post-for row-slot (:read upload mo) (:read upload ml)
                                                                  c0 g0 c1 g1 hashed h row-principal-slot row-lines
                                                                  :owner upload))
                               (:set (prepared 1))
                               (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))))))))))
  ;; stage every slot against the tip, emit into chunk 1, admit the member, bind on :ok (one run)
  (:ready :on-refusal ((:stop :machine-phase))
   (:let sslot row-slot)
   (:if (eq (fn2-commit-posture) :draining)
        ((:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
         (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t))
        ((:do (scode i) (fn2-successor-stage sslot)
          :accept ()
          :case (((:ok)
                  (:let c0 (:read upload c0-slot))
                  (:let c1 (:read upload c1-slot)) (:let g1 (:read upload c1-gen))
                  (:let hashed (:read upload hashed))
                  (:if (not (<= (+ hashed *fn2-upload-digest-octets*) (fn2-upload-chunk-cap c0)))
                       ((:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                        (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t))
                       ((:do (ecode elen)
                             (fn2-successor-emit sslot c1 g1 0 (fn2-upload-chunk-cap c1) :owner upload)
                         :accept ()
                         :case (((:ok)
                                 (:do (acode b ev)
                                      (fn2-commit-admit-txn c1 g1 elen :owner upload)
                                  :effects ((:acquire (:batch-membership)))
                                  :accept ()
                                  :case (((:ok)
                                          (:if (and (unsigned-byte-p 60 b) (unsigned-byte-p 60 ev))
                                               ((:do (bcode) (fn2-successor-bind sslot b ev))
                                                (:set (batch b) (bevent ev))
                                                (:next :batched) (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t))
                                               ((:stop :machine-phase))))
                                         ((:exhausted) (:park :batch-membership :steps *fn2-work-transition*))
                                         ((:admission)
                                          (:if (equal row-tmode *fn2-txn-mode-evidence*)
                                               ((:set (ecommit *fn2-txn-ecommit-refused*) (word *fn2-upload-word-conflict*))
                                                (:next :refused) (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t))
                                               ((:set (word *fn2-upload-word-not-stored*))
                                                (:next :refused) (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t)))))))
                                ((:room)
                                 (:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                                 (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t)))))))
                 ((:full) (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t))
                 ((:stale)
                  (:do (rcode) (fn2-successor-release sslot))
                  (:set (offered 0) (prepared 0) (gcur 0) (gskip 0) (ngroups 0))
                  (:next :lookup) (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t))
                 ((:refused :evidence)
                  (:do (rcode) (fn2-successor-release sslot))
                  (:set (tmode *fn2-txn-mode-evidence*) (word *fn2-upload-word-conflict*) (offered 0) (prepared 0))
                  (:next :lookup) (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t))
                 ((:duplicate) (:set (word *fn2-upload-word-duplicate*)) (:next :refused)
                               (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t))
                 ((:capacity) (:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                              (:charge :bytes 24576 :steps *fn2-work-transition* :runnable t)))))))
  (:batched :on-refusal ((:stop :machine-phase))
   (:do (tcode tbatch tevent tout)
        (fn2-commit-take :owner upload)
    :effects ((:release (:batch-membership)))
    :accept ()
    :case (((:pending) (:charge :steps *fn2-work-empty* :runnable t))
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
(defcost-faces fn2-txn)
(defthm fn2-txn-hash-type
  (unsigned-byte-p 32 (mv-nth 1 (fn2-txn-hash n slot gen off okind oslot ogen fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-txn-hash) (unsigned-byte-p)))))
(defthm fn2-txn-count-natp
  (implies (natp lines) (natp (mv-nth 1 (fn2-txn-count n slot gen off lines okind oslot ogen fn2-core))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-txn-count))))
(defthm fn2-txn-next-name-types
  (implies (and (natp base) (natp cur) (natp end))
           (and (natp (mv-nth 1 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))
                (natp (mv-nth 2 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))
                (natp (mv-nth 3 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))))
  :hints (("Goal" :in-theory (enable fn2-txn-next-name))))
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
  :hints (("Goal" :in-theory (e/d (fn2-core-wfp) (fn2-txn-snapshot-read-code)))))
(in-theory (disable fn2-commit-admit-txn fn2-claim-release-core))

;; At the drain: wake the upload U if it still names this row (ID of
;; generation GEN), so it sees the row gone and drains.
(defun fn2-txn-wake-upload (u id gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok) (fn2-machine-idp u fn2-core)
           (equal (fn2-upload-row-txn u fn2-core) id) (equal (fn2-upload-row-txn-gen u fn2-core) gen))
      (fn2-machine-set-wake-id u fn2-core)
    fn2-core))
(fn2-core-preserves fn2-txn-wake-upload (u id gen fn2-core) :rows nil
  :hints (("Goal" :in-theory (disable fn2-upload-snapshot-read-code))))
(in-theory (disable fn2-txn-wake-upload))

(defun fn2-txn-offer (tx mo ml c0 g0 c1 g1 hashed okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp hashed))))
  (mv-let (in1 doff) (fn2-upload-digest-at hashed (fn2-upload-chunk-cap c0 fn2-core))
    (fn2-identity-decide-start tx c0 g0 mo ml (if in1 c1 c0) (if in1 g1 g0) doff okind oslot ogen fn2-core)))
(fn2-core-preserves fn2-txn-offer (tx mo ml c0 g0 c1 g1 hashed okind oslot ogen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-offer))

;; One counting run over [from, to) of the source (chunk 0 then chunk 1):
;; (mv code counted lines).
(defun fn2-txn-count-run (from to lines c0 g0 c1 g1 cap0 okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp from) (natp to) (natp lines) (natp cap0))))
  (b* ((in0 (< from cap0))
       (n (nfix (min *fn2-txn-count-bytes* (min (nfix (- to from)) (if in0 (- cap0 from) (nfix (- to from)))))))
       ((mv code lines2) (fn2-txn-count n (if in0 c0 c1) (if in0 g0 g1) (if in0 from (- from cap0)) lines
                                        okind oslot ogen fn2-core)))
    (mv code (+ from n) lines2)))
(defthm fn2-txn-count-run-natp-1
  (implies (natp from)
           (natp (mv-nth 1 (fn2-txn-count-run from to lines c0 g0 c1 g1 cap0 okind oslot ogen fn2-core))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable min nfix))))
(defthm fn2-txn-count-run-natp-2
  (implies (natp lines)
           (natp (mv-nth 2 (fn2-txn-count-run from to lines c0 g0 c1 g1 cap0 okind oslot ogen fn2-core))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable min nfix))))
(in-theory (disable fn2-txn-count-run))
(defun fn2-txn-count-next (c0 g0 c1 g1 counted to lines okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp counted) (natp to) (natp lines))))
  (fn2-txn-count-run counted to lines c0 g0 c1 g1 (fn2-upload-chunk-cap c0 fn2-core) okind oslot ogen fn2-core))
(in-theory (disable fn2-txn-count-next))

;; The write slots of an accepted POST (C-S3): the identity admission (C
;; §4a; fn2-txn-put-identity), the article row, and the operation outcome,
;; written via the generated per-schema put-row writers (<= 4 calls per fn).
(defun fn2-txn-put-identity-core (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal l fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv c fn2-core)
        (if (equal l 1)
            (fn2-identity-history-put tx *fn2-txn-slot-history*
              (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
              (profile *fn2-identity-profile-source*) (algorithm *fn2-identity-algorithm-blake3*)
              (digest dslot dgen doff) (lineage *fn2-identity-lineage*) (domain *fn2-identity-domain*)
              (incarnation *fn2-identity-incarnation*) (position :event 0) (evidence :event 0) (article :event 0)
              :owner (okind oslot ogen) fn2-core)
          (mv :ok fn2-core)))
       ((unless (eq c :ok)) (mv c fn2-core))
       ((mv c fn2-core)
        (fn2-identity-evidence-put tx *fn2-txn-slot-evidence*
          (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
          (profile *fn2-identity-profile-source*) (algorithm *fn2-identity-algorithm-blake3*)
          (digest dslot dgen doff) (lineage *fn2-identity-lineage*) (domain *fn2-identity-domain*)
          (incarnation *fn2-identity-incarnation*) (occurrence :event 0)
          (kind *fn2-identity-evidence-kind-binding*) (issuer principal)
          :owner (okind oslot ogen) fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core))
       ((mv c fn2-core)
        (fn2-identity-summary-admit tx *fn2-txn-slot-summary*
          (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
          (ne :new *fn2-txn-slot-evidence*)
          (nr (if (equal l 1) :new :value) (if (equal l 1) *fn2-txn-slot-history* 0))
          (est l) (oldh h)
          :owner (okind oslot ogen) fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core)))
    (fn2-identity-candidates-admit tx *fn2-txn-slot-candidate*
      (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
      (profile *fn2-identity-profile-source*) (algorithm *fn2-identity-algorithm-blake3*)
      (digest dslot dgen doff)
      (ch (if (equal h 0) :out :value)
          (if (equal h 0) (+ (* *fn2-txn-slot-summary* 256) *fn2-identity-summary-entry-field-candidates*) h))
      (ne :new *fn2-txn-slot-evidence*) (q 1) (l l)
      :owner (okind oslot ogen) fn2-core)))
(fn2-core-preserves fn2-txn-put-identity-core
  (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal l fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-put-identity-core))

(defun fn2-txn-put-identity (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal local fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* ((l (if (equal local 1) 1 0))
       ((mv c fn2-core)
        (fn2-txn-put-identity-core tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal l fn2-core))
       ((unless (and (eq c :ok) (equal l 1))) (mv c fn2-core)))
    (fn2-identity-article-put tx *fn2-txn-slot-index*
      (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
      (h (if (equal h 0) :out :value)
         (if (equal h 0) (+ (* *fn2-txn-slot-summary* 256) *fn2-identity-summary-entry-field-candidates*) h))
      (article :event 0)
      :owner (okind oslot ogen) fn2-core)))
(fn2-core-preserves fn2-txn-put-identity
  (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal local fn2-core) :position 1 :rows nil)

(defun fn2-txn-put-article (tx dslot dgen doff bytes lines principal okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv c fn2-core)
        (fn2-article-put tx *fn2-txn-slot-article*
          (article :event 0) (birth :event 0) (state *fn2-txn-article-live*)
          (version *fn2-txn-article-version*) (source dslot dgen doff)
          (bytes bytes) (lines lines)
          :owner (okind oslot ogen) fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core)))
    (fn2-outcome-put tx *fn2-txn-slot-outcome*
      (principal principal) (operation :event 0) (request dslot dgen doff)
      (outcome *fn2-txn-outcome-accepted*) (event :event 0)
      :owner (okind oslot ogen) fn2-core)))
(fn2-core-preserves fn2-txn-put-article (tx dslot dgen doff bytes lines principal okind oslot ogen fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-txn-put-identity fn2-txn-put-article))

;; A POST's slots: the identity admission (a local acceptance) and the
;; article row with its outcome, one call for the declaring run.
(defun fn2-txn-put-post (tx mslot mgen moff mlen dslot dgen doff bytes lines okind oslot ogen h principal fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv c fn2-core)
        (fn2-txn-put-identity tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal 1 fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core)))
    (fn2-txn-put-article tx dslot dgen doff bytes lines principal okind oslot ogen fn2-core)))
(fn2-core-preserves fn2-txn-put-post (tx mslot mgen moff mlen dslot dgen doff bytes lines okind oslot ogen h principal fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-txn-put-post))
(defun fn2-txn-put-post-for (tx mo ml c0 g0 c1 g1 hashed h principal lines okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp hashed))))
  (mv-let (in1 doff) (fn2-upload-digest-at hashed (fn2-upload-chunk-cap c0 fn2-core))
    (fn2-txn-put-post tx c0 g0 mo ml (if in1 c1 c0) (if in1 g1 g0) doff hashed lines okind oslot ogen h principal fn2-core)))
(fn2-core-preserves fn2-txn-put-post-for (tx mo ml c0 g0 c1 g1 hashed h principal lines okind oslot ogen fn2-core)
  :position 1 :rows nil)
(defun fn2-txn-put-evidence-for (tx mo ml c0 g0 c1 g1 hashed h principal okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp hashed))))
  (mv-let (in1 doff) (fn2-upload-digest-at hashed (fn2-upload-chunk-cap c0 fn2-core))
    (fn2-txn-put-identity tx c0 g0 mo ml (if in1 c1 c0) (if in1 g1 g0) doff okind oslot ogen h principal 0 fn2-core)))
(fn2-core-preserves fn2-txn-put-evidence-for (tx mo ml c0 g0 c1 g1 hashed h principal okind oslot ogen fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-txn-put-post-for fn2-txn-put-evidence-for))
))

;; ------------------------------------------------------------------------
;; The transaction's continuations (materialized after the upload's).
(defmacro fn2-txn-events ()
 '(progn
(defmachine-arms fn2-txn)
(defmachine-run fn2-txn)
))
