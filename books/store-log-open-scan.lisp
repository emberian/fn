; fn: the charged totals of the log past a checkpoint, read before the open
; (Builder L, landing 2, 2026-10-10; prefix `fn-lgo-').
;
; A read-only command sizes its heap from the store's charged totals
; (books/heap-command.lisp fn-mo-observed-totals HDR SUFFIX) before it opens
; the store: HDR from the checkpoint's header run (Builder A,
; books/charged-totals-header.lisp), SUFFIX from this scan of the log's
; records past the header's S.  The scan streams the log one entry at a
; time (books/store-log-stream.lisp fn-lgw-step), expands each record
; (fn-lzr-expand), decodes it (fn-srs-decode) and adds its charged totals
; to a nine-field accumulator; no record is kept past its step.
;
; What the scan can know.  Eight of a row's nine fields are functions of
; the record's wire event: RECORDS, ARENA, HCHARGE, MEMBERSHIPS, EVENTS, LOG,
; CHARGE, RESIDENCY.  HISTORY (fn-ct-row-history, the padded SCC length of
; the interned ROW) also reads the row's arena handle and its statement
; context, which the open decides from the checkpoint's arena and the
; statement epoch at S; neither is in the log past S (seam L-M-A
; 2026-10-10, build/log-runs/l2/SEAM-history-field.md, M's ruling (b)).  The
; scan charges HISTORY at ALLOW + 3 x the row's octets, Builder M's per-row
; HISTORY clause of K-BOUND (books/admission-memory.lisp fn-adm-row-within-p,
; ALLOW = fn-adm-row-allowance PROFILE, memory landing 4b), and is exact in
; the other eight.  So the scan's totals bound the opened store's from above
; (fn-mm-tot-le), and M's fn-mo-read-holds-every-store-within-its-totals
; makes the read decision sound at them.
;
; KEYSTONES
;   L2-1 fn-lgo-run-is-the-fold          the stream's fold over one segment
;                                        is the fold over the recovered
;                                        kernel's committed records
;   L2-2 fn-lgo-chain-is-the-fold        over the open's segments, the fold
;                                        over fn-lgs-chain-records
;   L2-3 fn-lgo-fold-is-the-wire-fold    a fold that does not refuse is the
;                                        header's total plus the wire fold of
;                                        the decoded expansions past the skip
;   L2-4 fn-lgo-wire-fold-covers-the-replay
;                                        the wire fold agrees with the charged
;                                        fold of the rows the suffix replay
;                                        interns (fn-ssr-intern-step) in eight
;                                        fields and bounds its HISTORY, every
;                                        row within the HISTORY clause
;   L2-5 fn-lgo-observed-covers-the-opened-store
;                                        from a valid (K . TOT) cache, the
;                                        scan's total bounds the charged fold
;                                        of every row the open recovers, the
;                                        suffix replayed from the epoch at K

(in-package "ACL2")
(include-book "store-log-segments")
(include-book "store-log-stream")
(include-book "statement-recover-stream")
(include-book "history-totals-carried")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; 1. One record's charged totals, from its wire event.

; The held row the intern builds from wire record A (books/catalog-record.lisp
; fn-cat-intern-list) at handle 0, under the empty keyring and generation 0.
; The handle and the context are the two fields the scan cannot know; no
; total but HISTORY reads them.
(defun fn-lgo-held-of (a)
  (declare (xargs :guard t :verify-guards nil))
  (let ((bytes (fn-record-payload a)))
    (fn-held-make (fn-record-sequence a) (fn-record-txid a)
                  (fn-record-generation a) (fn-record-msgid a) 0
                  (fn-record-groups a) (fn-record-obligation-id a)
                  (fn-record-content-subject a) (fn-record-release-evidence a)
                  (fn-record-charge a) (fn-record-stamp a)
                  (fn-held-facts-of bytes)
                  (fn-held-context-of bytes nil 0)
                  nil nil)))

; The row the intern builds from wire event W, up to handle and context
; (books/store-intern.lisp fn-intern-event); :bad where the intern refuses.
(defun fn-lgo-wire-row (w)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p w) (fn-lgo-held-of w))
        ((fn-stxa-p w)
         (let ((a (fn-replay-composite-record w)))
           (if (fn-record-p a) (fn-hstxa-make w (fn-lgo-held-of a)) :bad)))
        ((fn-wire-event-p w) w)
        (t :bad)))

; The row's charged totals with HISTORY at the clause's ceiling.
(defun fn-lgo-wire-tot (w allow)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((row (fn-lgo-wire-row w))
         (tot (fn-ct-row-tot row :resident)))
    (fn-mm-make-tot 1 (fn-mm-tot-arena tot) (fn-mm-tot-hcharge tot)
                    (fn-mm-tot-memberships tot) (fn-mm-tot-events tot)
                    (fn-mm-tot-log tot)
                    (+ (nfix allow) (* 3 (fn-sbud-row-octets row)))
                    (fn-mm-tot-charge tot) :resident)))

(defun fn-lgo-wire-fold (ws allow)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ws)
      (fn-mm-tot-plus (fn-lgo-wire-tot (car ws) allow)
                      (fn-lgo-wire-fold (cdr ws) allow))
    (fn-ct-zero-tot :resident)))

; One log record Z (as the stream hands it on: a frame of the store's
; dictionaries DICTS, or the record itself), expanded and decoded as the
; open decodes it, then charged; :bad where either refuses.
(defun fn-lgo-record-tot (z dicts allow)
  (declare (xargs :guard t :verify-guards nil))
  (let ((x (fn-lzr-expand dicts z)))
    (if (and (consp x) (eq (car x) :ok))
        (let ((ws (fn-srs-decode (list (cadr x)))))
          (if (consp ws) (fn-lgo-wire-tot (car ws) allow) :bad))
      :bad)))

; -----------------------------------------------------------------------------
; 2. The fold: the first SKIP records pass uncharged (the checkpoint covers
; them), every later one is added to ACC; :bad absorbs.  Answers
; (mv SKIP' ACC').

(defun fn-lgo-add (acc z dicts allow)
  (declare (xargs :guard t :verify-guards nil))
  (if (eq acc :bad)
      :bad
    (let ((r (fn-lgo-record-tot z dicts allow)))
      (if (eq r :bad) :bad (fn-mm-tot-plus acc r)))))

(defun fn-lgo-fold (zs skip acc dicts allow)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom zs) (mv (nfix skip) acc))
        ((posp skip) (fn-lgo-fold (cdr zs) (1- skip) acc dicts allow))
        (t (fn-lgo-fold (cdr zs) 0 (fn-lgo-add acc (car zs) dicts allow) dicts allow))))

; The expansions of the records ZS, or :bad.
(defun fn-lgo-expansions (zs dicts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp zs)
      (let ((x (fn-lzr-expand dicts (car zs)))
            (rest (fn-lgo-expansions (cdr zs) dicts)))
        (if (and (consp x) (eq (car x) :ok) (not (eq rest :bad)))
            (cons (cadr x) rest)
          :bad))
    nil))

; -----------------------------------------------------------------------------
; 3. The stream: fn-lgw-run's loop with each step's records folded at once.
; Answers (mv SKIP' ACC' ST').

(defun fn-lgo-run (c st unit max skip acc dicts allow)
  (declare (xargs :measure (nfix (- (len c) (fn-lgw-pos st)))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-lgw-step fn-lgw-window)))))
  (mv-let (took records st2) (fn-lgw-step (fn-lgw-window c st) st unit max (len c))
    (mv-let (skip2 acc2) (if took (fn-lgo-fold records skip acc dicts allow) (mv (nfix skip) acc))
      (if (and took (not (fn-lgw-stop st2)) (< (fn-lgw-pos st2) (len c)))
          (fn-lgo-run c st2 unit max skip2 acc2 dicts allow)
        (mv skip2 acc2 st2)))))

; The open's segments CS (their durable octets, index order), each streamed
; from the genesis the one before ends on (books/store-log-stream.lisp
; fn-lgw-open-chain-records).  Answers (mv SKIP' ACC').
(defun fn-lgo-chain (cs genesis unit max skip acc dicts allow)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp cs)
      (mv-let (skip2 acc2 st) (fn-lgo-run (car cs) (fn-lgw-start genesis 1) unit max skip acc dicts allow)
        (fn-lgo-chain (cdr cs) (fn-lgc-last (fn-lgw-kernel st)) unit max skip2 acc2 dicts allow))
    (mv (nfix skip) acc)))

; Every row within the HISTORY clause (K-BOUND's, books/admission-memory.lisp
; fn-adm-row-within-p, at ALLOW = fn-adm-row-allowance PROFILE).
(defun fn-lgo-rows-history-within (rows allow)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (and (<= (nfix (fn-ct-row-history (car rows)))
               (+ (nfix allow) (* 3 (fn-sbud-row-octets (car rows)))))
           (fn-lgo-rows-history-within (cdr rows) allow))
    t))

; Two totals equal in every field but HISTORY.
(defun fn-lgo-agree-but-history (a b)
  (declare (xargs :guard t))
  (and (equal (fn-mm-tot-records a) (fn-mm-tot-records b))
       (equal (fn-mm-tot-arena a) (fn-mm-tot-arena b))
       (equal (fn-mm-tot-hcharge a) (fn-mm-tot-hcharge b))
       (equal (fn-mm-tot-memberships a) (fn-mm-tot-memberships b))
       (equal (fn-mm-tot-events a) (fn-mm-tot-events b))
       (equal (fn-mm-tot-log a) (fn-mm-tot-log b))
       (equal (fn-mm-tot-charge a) (fn-mm-tot-charge b))
       (equal (fn-mm-tot-paged-p a) (fn-mm-tot-paged-p b))))

; -----------------------------------------------------------------------------
; 4. The stream is the fold (L2-1, L2-2).

(defthm fn-lgo-fold-of-nfix
  (equal (fn-lgo-fold zs (nfix skip) acc dicts allow)
         (fn-lgo-fold zs skip acc dicts allow))
  :hints (("Goal" :expand ((fn-lgo-fold zs (nfix skip) acc dicts allow)
                           (fn-lgo-fold zs skip acc dicts allow))
           :in-theory (disable fn-lgo-add))))

(defthm fn-lgo-fold-of-append
  (equal (fn-lgo-fold (append a b) skip acc dicts allow)
         (mv-let (s1 a1) (fn-lgo-fold a skip acc dicts allow)
           (fn-lgo-fold b s1 a1 dicts allow)))
  :hints (("Goal" :induct (fn-lgo-fold a skip acc dicts allow)
           :in-theory (disable fn-lgo-add))))

(defthm fn-lgo-fold-of-atom
  (implies (atom zs)
           (equal (fn-lgo-fold zs skip acc dicts allow) (mv (nfix skip) acc))))

(defthm fn-lgo-run-is-the-run-folded
  (let ((run (fn-lgo-run c st unit max skip acc dicts allow))
        (w (fn-lgw-run c st unit max)))
    (and (equal (mv-nth 0 run) (mv-nth 0 (fn-lgo-fold (mv-nth 0 w) skip acc dicts allow)))
         (equal (mv-nth 1 run) (mv-nth 1 (fn-lgo-fold (mv-nth 0 w) skip acc dicts allow)))
         (equal (mv-nth 2 run) (mv-nth 1 w))))
  :hints (("Goal" :induct (fn-lgo-run c st unit max skip acc dicts allow)
           :expand ((fn-lgo-run c st unit max skip acc dicts allow)
                    (fn-lgw-run c st unit max))
           :in-theory (disable fn-lgw-step fn-lgw-window fn-lgo-fold))))

(defthm fn-lgo-run-is-the-fold
  (let* ((run (fn-lgo-run c (fn-lgw-start genesis floor) unit max skip acc dicts allow))
         (ks (fn-lgt-recover c genesis unit max floor))
         (fold (fn-lgo-fold (fn-lgk-committed ks) skip acc dicts allow)))
    (and (equal (mv-nth 0 run) (mv-nth 0 fold))
         (equal (mv-nth 1 run) (mv-nth 1 fold))
         (equal (fn-lgw-kernel (mv-nth 2 run)) (fn-lgc-of ks))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-lgo-run-is-the-run-folded (st (fn-lgw-start genesis floor)))
                 (:instance fn-lgw-run-is-the-open)))))

(local
 (defthm fn-lgo-chain-is-the-open-chain-fold
   (equal (fn-lgo-chain cs genesis unit max skip acc dicts allow)
          (fn-lgo-fold (fn-lgw-open-chain-records cs genesis unit max) skip acc dicts allow))
   :hints (("Goal" :induct (fn-lgo-chain cs genesis unit max skip acc dicts allow)
            :expand ((fn-lgw-open-chain-records cs genesis unit max))
            :in-theory (e/d (fn-lgw-segment-records fn-lgw-segment-last)
                            (fn-lgo-fold fn-lgo-run fn-lgw-run fn-lgw-kernel fn-lgw-start
                             fn-lgw-open-chain-is-the-chain))))))

(defthm fn-lgo-chain-is-the-fold
  (equal (fn-lgo-chain cs genesis unit max skip acc dicts allow)
         (fn-lgo-fold (fn-lgs-chain-records cs genesis unit max) skip acc dicts allow))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgo-chain fn-lgo-fold)
           :use ((:instance fn-lgw-open-chain-is-the-chain)))))


; -----------------------------------------------------------------------------
; 5. The fold is the wire fold (L2-3).

; -----------------------------------------------------------------------------
; The sum's algebra (restated locally: books/charged-totals.lisp keeps its own local).

(local (defthm fn-lgo-nfix-nfix (equal (nfix (nfix a)) (nfix a))))

(local
 (defthm fn-lgo-records-of-make
   (equal (fn-mm-tot-records (fn-mm-make-tot a b c d e f g h r)) (nfix a))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-records fn-mm-nat fn-mm-make-tot) (nfix))))))
(local
 (defthm fn-lgo-natp-records
   (natp (fn-mm-tot-records a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-records fn-mm-nat)))))

(local
 (defthm fn-lgo-arena-of-make
   (equal (fn-mm-tot-arena (fn-mm-make-tot a b c d e f g h r)) (nfix b))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-arena fn-mm-nat fn-mm-make-tot) (nfix))))))
(local
 (defthm fn-lgo-natp-arena
   (natp (fn-mm-tot-arena a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-arena fn-mm-nat)))))

(local
 (defthm fn-lgo-hcharge-of-make
   (equal (fn-mm-tot-hcharge (fn-mm-make-tot a b c d e f g h r)) (nfix c))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-hcharge fn-mm-nat fn-mm-make-tot) (nfix))))))
(local
 (defthm fn-lgo-natp-hcharge
   (natp (fn-mm-tot-hcharge a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-hcharge fn-mm-nat)))))

(local
 (defthm fn-lgo-memberships-of-make
   (equal (fn-mm-tot-memberships (fn-mm-make-tot a b c d e f g h r)) (nfix d))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-memberships fn-mm-nat fn-mm-make-tot) (nfix))))))
(local
 (defthm fn-lgo-natp-memberships
   (natp (fn-mm-tot-memberships a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-memberships fn-mm-nat)))))

(local
 (defthm fn-lgo-events-of-make
   (equal (fn-mm-tot-events (fn-mm-make-tot a b c d e f g h r)) (nfix e))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-events fn-mm-nat fn-mm-make-tot) (nfix))))))
(local
 (defthm fn-lgo-natp-events
   (natp (fn-mm-tot-events a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-events fn-mm-nat)))))

(local
 (defthm fn-lgo-log-of-make
   (equal (fn-mm-tot-log (fn-mm-make-tot a b c d e f g h r)) (nfix f))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-log fn-mm-nat fn-mm-make-tot) (nfix))))))
(local
 (defthm fn-lgo-natp-log
   (natp (fn-mm-tot-log a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-log fn-mm-nat)))))

(local
 (defthm fn-lgo-history-of-make
   (equal (fn-mm-tot-history (fn-mm-make-tot a b c d e f g h r)) (nfix g))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-history fn-mm-nat fn-mm-make-tot) (nfix))))))
(local
 (defthm fn-lgo-natp-history
   (natp (fn-mm-tot-history a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-history fn-mm-nat)))))

(local
 (defthm fn-lgo-charge-of-make
   (equal (fn-mm-tot-charge (fn-mm-make-tot a b c d e f g h r)) (nfix h))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-charge fn-mm-nat fn-mm-make-tot) (nfix))))))
(local
 (defthm fn-lgo-natp-charge
   (natp (fn-mm-tot-charge a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-charge fn-mm-nat)))))

(local
 (defthm fn-lgo-paged-of-make
   (equal (fn-mm-tot-paged-p (fn-mm-make-tot a b c d e f g h r)) (equal r :paged))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-paged-p fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-lgo-plus-assoc
   (equal (fn-mm-tot-plus (fn-mm-tot-plus a b) c) (fn-mm-tot-plus a (fn-mm-tot-plus b c)))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-plus)
                                   (fn-mm-make-tot fn-mm-tot-records fn-mm-tot-arena
                                    fn-mm-tot-hcharge fn-mm-tot-memberships fn-mm-tot-events
                                    fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge
                                    fn-mm-tot-paged-p))))))

(local
 (defthm fn-lgo-take9
   (equal (take 9 x) (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)
                           (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable nth)
            :expand ((take 9 x) (take 8 (cdr x)) (take 7 (cddr x)) (take 6 (cdddr x))
                     (take 5 (cddddr x)) (take 4 (cdr (cddddr x))) (take 3 (cddr (cddddr x)))
                     (take 2 (cdddr (cddddr x))) (take 1 (cddddr (cddddr x)))
                     (take 0 (cdr (cddddr (cddddr x)))))))))

(local
 (defthm fn-lgo-take-len (implies (true-listp x) (equal (take (len x) x) x))))

(local
 (defthm fn-lgo-tot-shape
   (implies (fn-mm-tot-p tot)
            (equal tot (list (nth 0 tot) (nth 1 tot) (nth 2 tot) (nth 3 tot) (nth 4 tot)
                             (nth 5 tot) (nth 6 tot) (nth 7 tot) (nth 8 tot))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-lgo-take-len (x tot)) (:instance fn-lgo-take9 (x tot)))
            :in-theory (e/d (fn-mm-tot-p) (fn-lgo-take-len))))))

(local
 (defthm fn-lgo-plus-zero-list
   (implies (and (natp a) (natp b) (natp c) (natp d) (natp e) (natp f) (natp g) (natp h)
                 (member-equal r '(:resident :paged)))
            (equal (fn-mm-tot-plus (list a b c d e f g h r) (fn-ct-zero-tot res))
                   (list a b c d e f g h r)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus fn-ct-zero-tot fn-mm-make-tot
                             fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships
                             fn-mm-tot-events fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge
                             fn-mm-tot-paged-p fn-mm-nat)))))

(local
 (defthm fn-lgo-plus-zero
   (implies (fn-mm-tot-p tot)
            (equal (fn-mm-tot-plus tot (fn-ct-zero-tot res)) tot))
   :hints (("Goal" :use (fn-lgo-tot-shape
                         (:instance fn-lgo-plus-zero-list (a (nth 0 tot)) (b (nth 1 tot))
                                    (c (nth 2 tot)) (d (nth 3 tot)) (e (nth 4 tot))
                                    (f (nth 5 tot)) (g (nth 6 tot)) (h (nth 7 tot))
                                    (r (nth 8 tot))))
            :in-theory (e/d (fn-mm-tot-p) (fn-lgo-plus-zero-list))))))

(local
 (defthm fn-lgo-tot-p-of-plus (fn-mm-tot-p (fn-mm-tot-plus a b))
   :hints (("Goal" :in-theory (union-theories '(fn-mm-tot-plus fn-mm-make-tot-is-a-tot)
                                            (theory 'minimal-theory))))))

(local (in-theory (disable fn-mm-tot-plus fn-ct-zero-tot (:e fn-ct-zero-tot) fn-mm-tot-p)))

(local
 (defthm fn-lgo-fold-of-bad
   (equal (mv-nth 1 (fn-lgo-fold zs skip :bad dicts allow)) :bad)
   :hints (("Goal" :induct (fn-lgo-fold zs skip :bad dicts allow)))))

(local
 (defthm fn-lgo-fold-past-the-skip
   (equal (mv-nth 1 (fn-lgo-fold zs skip acc dicts allow))
          (mv-nth 1 (fn-lgo-fold (nthcdr skip zs) 0 acc dicts allow)))
   :hints (("Goal" :induct (fn-lgo-fold zs skip acc dicts allow)
            :in-theory (disable fn-lgo-add)))
   :rule-classes nil))


(local
 (defthm fn-lgo-decode-of-cons
   (implies (syntaxp (not (equal xs ''nil)))
   (equal (fn-srs-decode (cons x xs))
          (let ((d (fn-srs-decode (list x))))
            (if (consp d)
                (if (equal (fn-srs-decode xs) :bad) :bad (cons (car d) (fn-srs-decode xs)))
              :bad))))
   :hints (("Goal" :expand ((fn-srs-decode (cons x xs)) (fn-srs-decode (list x)))
            :in-theory (disable fn-srs-decode fn-store-event-decode-exact fn-rcon-wire-event-p)))))


(local
 (defthm fn-lgo-tot-is-not-bad
   (implies (fn-mm-tot-p acc) (not (equal acc :bad)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-mm-tot-p)))))

(local
 (defthm fn-lgo-add-of-tot
   (implies (fn-mm-tot-p acc)
            (equal (fn-lgo-add acc z dicts allow)
                   (let ((x (fn-lzr-expand dicts z)))
                     (if (and (consp x) (eq (car x) :ok) (consp (fn-srs-decode (list (cadr x)))))
                         (fn-mm-tot-plus acc (fn-lgo-wire-tot (car (fn-srs-decode (list (cadr x)))) allow))
                       :bad))))
   :hints (("Goal" :in-theory (disable fn-lgo-wire-tot fn-lzr-expand fn-srs-decode fn-mm-tot-plus)))))

(local
 (defthm fn-lgo-wire-fold-of-atom
   (implies (atom ws) (equal (fn-lgo-wire-fold ws allow) (fn-ct-zero-tot :resident)))))

(local
 (defthm fn-lgo-fold-0-is-the-wire-fold
   (let ((acc2 (mv-nth 1 (fn-lgo-fold zs 0 acc dicts allow)))
         (xs (fn-lgo-expansions zs dicts)))
     (implies (and (fn-mm-tot-p acc) (not (eq acc2 :bad)))
              (and (not (eq xs :bad))
                   (not (eq (fn-srs-decode xs) :bad))
                   (equal acc2 (fn-mm-tot-plus acc (fn-lgo-wire-fold (fn-srs-decode xs) allow))))))
   :hints (("Goal" :induct (fn-lgo-fold zs 0 acc dicts allow)
            :expand ((fn-lgo-fold zs 0 acc dicts allow) (fn-lgo-expansions zs dicts)
                     (fn-lgo-wire-fold (cons (car (fn-srs-decode (list (cadr (fn-lzr-expand dicts (car zs))))))
                                             (fn-srs-decode (fn-lgo-expansions (cdr zs) dicts)))
                                       allow))
            :in-theory (disable fn-lgo-wire-tot fn-lzr-expand fn-lgo-add
                                fn-srs-decode fn-store-event-decode-exact fn-lgo-record-tot
                                fn-lgo-wire-fold)))))

(defthm fn-lgo-fold-is-the-wire-fold
  (let ((acc2 (mv-nth 1 (fn-lgo-fold zs skip acc dicts allow)))
        (xs (fn-lgo-expansions (nthcdr skip zs) dicts)))
    (implies (and (fn-mm-tot-p acc) (not (eq acc2 :bad)))
             (and (not (eq xs :bad))
                  (not (eq (fn-srs-decode xs) :bad))
                  (equal acc2 (fn-mm-tot-plus acc (fn-lgo-wire-fold (fn-srs-decode xs) allow))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-lgo-fold-0-is-the-wire-fold (zs (nthcdr skip zs)))
                 (:instance fn-lgo-fold-past-the-skip)))))


; -----------------------------------------------------------------------------
; 6. The wire fold covers the replay (L2-4): the intern's row and
; fn-lgo-wire-row differ only in the handle and the context, which no
; charged total but HISTORY reads.

(local
 (defthm fn-lgo-held-p-of-held-of
   (implies (fn-record-p a) (fn-held-p (fn-lgo-held-of a)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-held-p fn-record-internals
                                      fn-held-internals fn-hf-p fn-hc-p
                                      fn-hf-startp fn-hc-verdictp)))))

(local
 (defthm fn-lgo-held-of-is-the-intern-up-to-handle-and-context
   (let ((row (mv-nth 0 (fn-cat-intern-list a keyring generation fn-arena)))
         (wr (fn-lgo-held-of a)))
     (and (equal (fn-held-facts row) (fn-held-facts wr))
          (equal (fn-record-msgid row) (fn-record-msgid wr))
          (equal (fn-record-groups row) (fn-record-groups wr))))))

(local
 (defthm fn-lgo-held-not-hstxa
   (implies (fn-held-p x) (not (fn-hstxa-p x)))
   :hints (("Goal" :in-theory (enable fn-held-p fn-held-shapep fn-hstxa-p)))))

(local
 (defthm fn-lgo-hstxa-not-held
   (not (fn-held-p (fn-hstxa-make s h)))
   :hints (("Goal" :in-theory (enable fn-held-p fn-held-shapep fn-hstxa-make)))))

(local
 (defthm fn-lgo-held-row-charges
   (implies (and (fn-held-p row) (fn-held-p wr)
                 (equal (fn-held-facts row) (fn-held-facts wr))
                 (equal (fn-record-msgid row) (fn-record-msgid wr))
                 (equal (fn-record-groups row) (fn-record-groups wr)))
            (and (equal (fn-ct-row row) (fn-ct-row wr))
                 (equal (fn-ct-row-log row) (fn-ct-row-log wr))
                 (equal (fn-sbud-row-octets row) (fn-sbud-row-octets wr))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-sbud-row-octets fn-sbud-held-heap-charge
                                    fn-sbud-held-header-octets fn-sbud-held-msgid-octets)
                                   (fn-store-event-encode))))))

(local
 (defthm fn-lgo-hstxa-row-charges
   (implies (and (fn-stxa-p s) (fn-held-p h1) (fn-held-p h2)
                 (equal (fn-held-facts h1) (fn-held-facts h2))
                 (equal (fn-record-msgid h1) (fn-record-msgid h2))
                 (equal (fn-record-groups h1) (fn-record-groups h2)))
            (and (equal (fn-ct-row (fn-hstxa-make s h1)) (fn-ct-row (fn-hstxa-make s h2)))
                 (equal (fn-ct-row-log (fn-hstxa-make s h1)) (fn-ct-row-log (fn-hstxa-make s h2)))
                 (equal (fn-sbud-row-octets (fn-hstxa-make s h1))
                        (fn-sbud-row-octets (fn-hstxa-make s h2)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-sbud-row-octets fn-sbud-held-heap-charge fn-hstxa-p
                                    fn-sbud-held-header-octets fn-sbud-held-msgid-octets)
                                   (fn-store-event-encode))))))

(local
 (defthm fn-lgo-intern-list-charges
   (let ((row (mv-nth 0 (fn-cat-intern-list a keyring generation fn-arena)))
         (wr (fn-lgo-held-of a)))
     (implies (and (natp generation) (fn-record-p a))
              (and (equal (fn-ct-row row) (fn-ct-row wr))
                   (equal (fn-ct-row-log row) (fn-ct-row-log wr))
                   (equal (fn-sbud-row-octets row) (fn-sbud-row-octets wr))
                   (fn-held-p row) (fn-held-p wr)
                   (equal (fn-held-facts row) (fn-held-facts wr))
                   (equal (fn-record-msgid row) (fn-record-msgid wr))
                   (equal (fn-record-groups row) (fn-record-groups wr)))))
   :hints (("Goal" :in-theory (union-theories '(fn-held-p-of-intern-list fn-lgo-held-p-of-held-of
                                                fn-lgo-held-of-is-the-intern-up-to-handle-and-context)
                                              (theory 'minimal-theory))
            :use ((:instance fn-lgo-held-row-charges
                             (row (mv-nth 0 (fn-cat-intern-list a keyring generation fn-arena)))
                             (wr (fn-lgo-held-of a))))))))


(local (in-theory (disable fn-lgo-held-of fn-cat-intern-list)))

(local
 (defthm fn-lgo-held-not-bad
   (implies (fn-held-p x) (not (equal x :bad)))
   :hints (("Goal" :in-theory (enable fn-held-p fn-held-shapep)))))

(local
 (defthm fn-lgo-intern-row-charges
   (let ((row (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
         (wr (fn-lgo-wire-row w)))
     (implies (and (natp generation) (not (equal row :bad)))
              (and (not (equal wr :bad))
                   (equal (fn-ct-row row) (fn-ct-row wr))
                   (equal (fn-ct-row-log row) (fn-ct-row-log wr))
                   (equal (fn-sbud-row-octets row) (fn-sbud-row-octets wr)))))
   :hints (("Goal" :in-theory (union-theories '(fn-intern-event fn-lgo-wire-row fn-lgo-intern-list-charges
                                                mv-nth zp natp fn-hstxa-make fn-lgo-held-not-bad (:e fn-held-p) car-cons cdr-cons)
                                              (theory 'minimal-theory))
            :use ((:instance fn-lgo-hstxa-row-charges
                             (s w)
                             (h1 (mv-nth 0 (fn-cat-intern-list (fn-replay-composite-record w)
                                                               keyring generation fn-arena)))
                             (h2 (fn-lgo-held-of (fn-replay-composite-record w))))
                  (:instance fn-lgo-intern-list-charges (a (fn-replay-composite-record w)))
                  (:instance fn-lgo-intern-list-charges (a w)))))))

(local (in-theory (disable fn-mm-make-tot fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge
                           fn-mm-tot-memberships fn-mm-tot-events fn-mm-tot-log fn-mm-tot-history
                           fn-mm-tot-charge fn-mm-tot-paged-p)))

(local
 (defthm fn-lgo-records-of-plus
   (equal (fn-mm-tot-records (fn-mm-tot-plus a b)) (+ (fn-mm-tot-records a) (fn-mm-tot-records b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))
(local
 (defthm fn-lgo-records-of-zero
   (equal (fn-mm-tot-records (fn-ct-zero-tot r)) 0)
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-arena-of-plus
   (equal (fn-mm-tot-arena (fn-mm-tot-plus a b)) (+ (fn-mm-tot-arena a) (fn-mm-tot-arena b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))
(local
 (defthm fn-lgo-arena-of-zero
   (equal (fn-mm-tot-arena (fn-ct-zero-tot r)) 0)
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-hcharge-of-plus
   (equal (fn-mm-tot-hcharge (fn-mm-tot-plus a b)) (+ (fn-mm-tot-hcharge a) (fn-mm-tot-hcharge b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))
(local
 (defthm fn-lgo-hcharge-of-zero
   (equal (fn-mm-tot-hcharge (fn-ct-zero-tot r)) 0)
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-memberships-of-plus
   (equal (fn-mm-tot-memberships (fn-mm-tot-plus a b)) (+ (fn-mm-tot-memberships a) (fn-mm-tot-memberships b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))
(local
 (defthm fn-lgo-memberships-of-zero
   (equal (fn-mm-tot-memberships (fn-ct-zero-tot r)) 0)
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-events-of-plus
   (equal (fn-mm-tot-events (fn-mm-tot-plus a b)) (+ (fn-mm-tot-events a) (fn-mm-tot-events b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))
(local
 (defthm fn-lgo-events-of-zero
   (equal (fn-mm-tot-events (fn-ct-zero-tot r)) 0)
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-log-of-plus
   (equal (fn-mm-tot-log (fn-mm-tot-plus a b)) (+ (fn-mm-tot-log a) (fn-mm-tot-log b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))
(local
 (defthm fn-lgo-log-of-zero
   (equal (fn-mm-tot-log (fn-ct-zero-tot r)) 0)
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-history-of-plus
   (equal (fn-mm-tot-history (fn-mm-tot-plus a b)) (+ (fn-mm-tot-history a) (fn-mm-tot-history b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))
(local
 (defthm fn-lgo-history-of-zero
   (equal (fn-mm-tot-history (fn-ct-zero-tot r)) 0)
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-charge-of-plus
   (equal (fn-mm-tot-charge (fn-mm-tot-plus a b)) (+ (fn-mm-tot-charge a) (fn-mm-tot-charge b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))
(local
 (defthm fn-lgo-charge-of-zero
   (equal (fn-mm-tot-charge (fn-ct-zero-tot r)) 0)
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-paged-of-plus
   (equal (fn-mm-tot-paged-p (fn-mm-tot-plus a b)) (fn-mm-tot-paged-p a))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))
(local
 (defthm fn-lgo-paged-of-zero
   (equal (fn-mm-tot-paged-p (fn-ct-zero-tot r)) (equal r :paged))
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-row-tot-is-the-wire-tot-car
   (let ((row (car (fn-intern-event w keyring generation fn-arena))))
     (implies (and (natp generation) (not (equal row :bad)))
              (and
                   (equal (fn-mm-tot-records (fn-ct-row-tot row :resident)) (fn-mm-tot-records (fn-lgo-wire-tot w allow)))
                   (equal (fn-mm-tot-arena (fn-ct-row-tot row :resident)) (fn-mm-tot-arena (fn-lgo-wire-tot w allow)))
                   (equal (fn-mm-tot-hcharge (fn-ct-row-tot row :resident)) (fn-mm-tot-hcharge (fn-lgo-wire-tot w allow)))
                   (equal (fn-mm-tot-memberships (fn-ct-row-tot row :resident)) (fn-mm-tot-memberships (fn-lgo-wire-tot w allow)))
                   (equal (fn-mm-tot-events (fn-ct-row-tot row :resident)) (fn-mm-tot-events (fn-lgo-wire-tot w allow)))
                   (equal (fn-mm-tot-log (fn-ct-row-tot row :resident)) (fn-mm-tot-log (fn-lgo-wire-tot w allow)))
                   (equal (fn-mm-tot-charge (fn-ct-row-tot row :resident)) (fn-mm-tot-charge (fn-lgo-wire-tot w allow)))
                   (equal (fn-mm-tot-paged-p (fn-ct-row-tot row :resident)) nil)
                   (equal (fn-mm-tot-paged-p (fn-lgo-wire-tot w allow)) nil)
                   (equal (fn-mm-tot-history (fn-ct-row-tot row :resident)) (fn-ct-row-history row))
                   (equal (fn-mm-tot-history (fn-lgo-wire-tot w allow))
                          (+ (nfix allow) (* 3 (fn-sbud-row-octets row)))))))
   :hints (("Goal" :in-theory (e/d (fn-ct-row-tot fn-lgo-wire-tot)
                                   (fn-ct-row fn-ct-row-log fn-sbud-row-octets fn-ct-row-history
                                    fn-intern-event fn-lgo-wire-row))
            :use ((:instance fn-lgo-intern-row-charges))))))

(local
 (defthm fn-lgo-rev-onto-append
   (equal (fn-ag-rev-onto x (append a b)) (append (fn-ag-rev-onto x a) b))))

(local
 (defthm fn-lgo-rows-of-publish
   (implies (not (equal acc :bad))
            (equal (fn-ssr-rows (fn-ssr-publish acc row wire identity))
                   (append (fn-ssr-rows acc) (list row))))
   :hints (("Goal" :in-theory (enable fn-ssr-rows fn-ssr-publish fn-ssr-state)
            :use ((:instance fn-lgo-rev-onto-append (x (fn-ssr-at 0 acc)) (a nil) (b (list row))))))))

(local
 (defthm fn-lgo-publish-shape
   (implies (natp (fn-ssr-at 2 acc))
            (and (natp (fn-ssr-at 2 (fn-ssr-publish acc row wire identity)))
                 (not (equal (fn-ssr-publish acc row wire identity) :bad))))
   :hints (("Goal" :in-theory (e/d (fn-ssr-publish fn-ssr-state)
                                   (fn-stxk-p fn-stxk-context-kind fn-stxk-context-current-generation
                                    fn-ssk-apply-snapshot fn-stxk-keyring-generation))))))

(local
 (defthm fn-lgo-within-of-append
   (equal (fn-lgo-rows-history-within (append a b) allow)
          (and (fn-lgo-rows-history-within a allow) (fn-lgo-rows-history-within b allow)))))

(local
 (defthm fn-lgo-statep-generation
   (implies (fn-ssr-statep acc) (natp (fn-ssr-at 2 acc)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-ssr-statep)))))

(local
 (defthm fn-lgo-statep-not-bad
   (implies (fn-ssr-statep acc) (not (equal acc :bad)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-ssr-statep)))))

(local
 (defthm fn-lgo-wire-fold-paged
   (equal (fn-mm-tot-paged-p (fn-lgo-wire-fold ws allow)) nil)
   :hints (("Goal" :in-theory (e/d (fn-lgo-wire-tot) (fn-lgo-wire-row fn-ct-row-tot fn-sbud-row-octets))))))


(local
 (defthm fn-lgo-charged-of-singleton
   (equal (fn-ct-charged (list r) res)
          (fn-mm-tot-plus (fn-ct-row-tot r res) (fn-ct-zero-tot res)))
   :hints (("Goal" :expand ((fn-ct-charged (list r) res))
            :in-theory (union-theories '(car-cons cdr-cons fn-ct-charged (:e fn-ct-charged))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-lgo-records-of-wire-tot
   (equal (fn-mm-tot-records (fn-lgo-wire-tot w allow)) 1)
   :hints (("Goal" :in-theory (union-theories '(fn-lgo-wire-tot fn-lgo-records-of-make (:e nfix))
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-lgo-intern-step-of-atom
   (implies (atom ws)
            (equal (car (fn-ssr-intern-step acc ws rs ps mode dicts fn-arena))
                   (if (and (null ws) (not (equal acc :bad))) acc :bad)))
   :hints (("Goal" :expand ((fn-ssr-intern-step acc ws rs ps mode dicts fn-arena))))))

(local
 (defthm fn-lgo-replay-fields
   (let ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws rs ps :resident dicts fn-arena))))
     (implies (and (natp (fn-ssr-at 2 acc)) (not (equal acc :bad)) (not (equal acc1 :bad)))
              (and
                   (equal (fn-mm-tot-records (fn-ct-charged (fn-ssr-rows acc1) :resident))
                          (+ (fn-mm-tot-records (fn-ct-charged (fn-ssr-rows acc) :resident))
                             (fn-mm-tot-records (fn-lgo-wire-fold ws allow))))
                   (equal (fn-mm-tot-arena (fn-ct-charged (fn-ssr-rows acc1) :resident))
                          (+ (fn-mm-tot-arena (fn-ct-charged (fn-ssr-rows acc) :resident))
                             (fn-mm-tot-arena (fn-lgo-wire-fold ws allow))))
                   (equal (fn-mm-tot-hcharge (fn-ct-charged (fn-ssr-rows acc1) :resident))
                          (+ (fn-mm-tot-hcharge (fn-ct-charged (fn-ssr-rows acc) :resident))
                             (fn-mm-tot-hcharge (fn-lgo-wire-fold ws allow))))
                   (equal (fn-mm-tot-memberships (fn-ct-charged (fn-ssr-rows acc1) :resident))
                          (+ (fn-mm-tot-memberships (fn-ct-charged (fn-ssr-rows acc) :resident))
                             (fn-mm-tot-memberships (fn-lgo-wire-fold ws allow))))
                   (equal (fn-mm-tot-events (fn-ct-charged (fn-ssr-rows acc1) :resident))
                          (+ (fn-mm-tot-events (fn-ct-charged (fn-ssr-rows acc) :resident))
                             (fn-mm-tot-events (fn-lgo-wire-fold ws allow))))
                   (equal (fn-mm-tot-log (fn-ct-charged (fn-ssr-rows acc1) :resident))
                          (+ (fn-mm-tot-log (fn-ct-charged (fn-ssr-rows acc) :resident))
                             (fn-mm-tot-log (fn-lgo-wire-fold ws allow))))
                   (equal (fn-mm-tot-charge (fn-ct-charged (fn-ssr-rows acc1) :resident))
                          (+ (fn-mm-tot-charge (fn-ct-charged (fn-ssr-rows acc) :resident))
                             (fn-mm-tot-charge (fn-lgo-wire-fold ws allow))))
                   (implies (fn-lgo-rows-history-within (fn-ssr-rows acc1) allow)
                            (and (fn-lgo-rows-history-within (fn-ssr-rows acc) allow)
                                 (<= (fn-mm-tot-history (fn-ct-charged (fn-ssr-rows acc1) :resident))
                                     (+ (fn-mm-tot-history (fn-ct-charged (fn-ssr-rows acc) :resident))
                                        (fn-mm-tot-history (fn-lgo-wire-fold ws allow)))))))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ssr-intern-step acc ws rs ps :resident dicts fn-arena)
            :expand ((fn-ssr-intern-step acc ws rs ps :resident dicts fn-arena)
                     (fn-lgo-wire-fold ws allow))
            :in-theory (e/d ((:induction fn-ssr-intern-step)) (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                                fn-replay-identity-step fn-ssr-publish fn-ssr-at fn-ssr-rows
                                fn-stxk-context-kind fn-ct-row-tot fn-lgo-wire-tot fn-ct-row-history
                                fn-sbud-row-octets fn-ct-charged fn-lgo-wire-fold fn-ssr-statep))
            :do-not '(generalize fertilize eliminate-destructors)))))

(local
 (defthm fn-lgo-rows-of-fresh
   (implies (and (not (equal acc :bad)) (null (fn-ssr-at 0 acc)))
            (equal (fn-ssr-rows acc) nil))
   :hints (("Goal" :in-theory (enable fn-ssr-rows)))))

(local
 (defthm fn-lgo-charged-of-nil
   (equal (fn-ct-charged nil res) (fn-ct-zero-tot res))
   :hints (("Goal" :expand ((fn-ct-charged nil res))))))

(local
 (defthm fn-lgo-charged-paged
   (equal (fn-mm-tot-paged-p (fn-ct-charged rows res)) (equal res :paged))
   :hints (("Goal" :induct (len rows) :expand ((fn-ct-charged rows res))
            :in-theory (enable fn-ct-row-tot)))))

; The cover over any replay state with no rows whose generation is a natural
; (L2-5 states the suffix replay's state by construction).
(local
 (defthm fn-lgo-wire-fold-covers-any-replay
   (let* ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)))
          (rows (fn-ssr-rows acc1)))
     (implies (and (natp (fn-ssr-at 2 acc)) (not (equal acc :bad)) (null (fn-ssr-at 0 acc))
                   (not (eq acc1 :bad))
                   (fn-lgo-rows-history-within rows allow))
              (and (fn-lgo-agree-but-history (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow))
                   (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-mm-tot-le) (fn-ct-charged fn-lgo-wire-fold fn-ssr-rows))
            :use ((:instance fn-lgo-replay-fields (rs nil) (ps nil)))))))

; KEYSTONE L2-4.
(defthm fn-lgo-wire-fold-covers-the-replay
  (let* ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)))
         (rows (fn-ssr-rows acc1)))
    (implies (and (fn-ssr-statep acc) (null (fn-ssr-at 0 acc)) (not (eq acc1 :bad))
                  (fn-lgo-rows-history-within rows allow))
             (and (fn-lgo-agree-but-history (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow))
                  (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgo-wire-fold-covers-any-replay fn-ct-charged fn-lgo-wire-fold
                               fn-ssr-rows fn-lgo-agree-but-history fn-mm-tot-le)
           :use ((:instance fn-lgo-wire-fold-covers-any-replay)))))


; -----------------------------------------------------------------------------
; 7. The scan's total bounds the opened store's (L2-5).

(local
 (defthm fn-lgo-le-of-plus
   (implies (fn-mm-tot-le a b)
            (fn-mm-tot-le (fn-mm-tot-plus c a) (fn-mm-tot-plus c b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-le)))))

(local
 (defthm fn-lgo-plus-zero-left
   (implies (and (fn-mm-tot-p tot) (not (fn-mm-tot-paged-p tot)))
            (equal (fn-mm-tot-plus (fn-ct-zero-tot :resident) tot) tot))
   :hints (("Goal" :use (fn-lgo-tot-shape)
            :in-theory (enable fn-mm-tot-plus fn-ct-zero-tot fn-mm-make-tot fn-mm-tot-p
                               fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships
                               fn-mm-tot-events fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge
                               fn-mm-tot-paged-p fn-mm-nat)))))

(local
 (defthm fn-lgo-wire-fold-is-a-tot
   (fn-mm-tot-p (fn-lgo-wire-fold ws allow))
   :hints (("Goal" :expand ((fn-lgo-wire-fold ws allow))
            :in-theory (e/d (fn-ct-zero-tot) (fn-lgo-wire-tot))))))

(local
 (defthm fn-lgo-zero-is-a-tot
   (fn-mm-tot-p (fn-ct-zero-tot r))
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm fn-lgo-append-take-nthcdr
   (implies (and (natp k) (<= k (len x)))
            (equal (append (take k x) (nthcdr k x)) x))))

(local
 (defthm fn-lgo-charged-of-cache
   (implies (fn-ct-totals-cache-validp cache rows :resident)
            (equal (fn-ct-charged rows :resident)
                   (fn-mm-tot-plus (cdr cache) (fn-ct-charged (nthcdr (car cache) rows) :resident))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-ct-totals-cache-validp) (fn-ct-charged fn-lgo-append-take-nthcdr))
            :use ((:instance fn-lgo-append-take-nthcdr (k (car cache)) (x rows))
                  (:instance fn-ct-charged-of-append (a (take (car cache) rows))
                             (b (nthcdr (car cache) rows)) (residency :resident)))))))


(local
 (defthm fn-lgo-suffix-is-the-wire-fold
   (let ((suffix (mv-nth 1 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow)))
         (xs (fn-lgo-expansions (nthcdr j zs) dicts)))
     (implies (not (eq suffix :bad))
              (equal suffix (fn-lgo-wire-fold (fn-srs-decode xs) allow))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-lgo-fold fn-lgo-expansions fn-srs-decode fn-lgo-wire-fold
                                       fn-lgo-fold-is-the-wire-fold)
            :use ((:instance fn-lgo-fold-is-the-wire-fold (skip j) (acc (fn-ct-zero-tot :resident))))))))


(local
 (defthm fn-lgo-state-shape
   (let ((acc (fn-ssr-state nil keyring (nfix generation) identity)))
     (and (natp (fn-ssr-at 2 acc)) (not (equal acc :bad)) (null (fn-ssr-at 0 acc))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-ssr-state fn-ssr-at)))))

(local
 (defthm fn-lgo-observed-covers-when-interned
  (let* ((k (car cache))
         (suffix (mv-nth 1 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow)))
         (acc (fn-ssr-state nil keyring (nfix generation) identity))
         (acc1 (mv-nth 0 (fn-ssr-intern-step
                          acc (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts))
                          nil nil :resident nil fn-arena))))
    (implies (and (fn-ct-totals-cache-validp cache rows :resident)
                  (not (eq acc1 :bad))
                  (equal (nthcdr k rows) (fn-ssr-rows acc1))
                  (fn-lgo-rows-history-within (nthcdr k rows) allow)
                  (not (eq suffix :bad)))
             (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) suffix))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(eq not) (theory 'minimal-theory))
           :use ((:instance fn-lgo-charged-of-cache)
                 (:instance fn-lgo-suffix-is-the-wire-fold)
                 (:instance fn-lgo-state-shape)
                 (:instance fn-lgo-wire-fold-covers-any-replay
                            (acc (fn-ssr-state nil keyring (nfix generation) identity))
                            (ws (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)))
                            (dicts nil))
                 (:instance fn-lgo-le-of-plus
                            (c (cdr cache))
                            (a (fn-ct-charged (nthcdr (car cache) rows) :resident))
                            (b (fn-lgo-wire-fold (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts))
                                                 allow))))))))

(local
 (defthm fn-lgo-fold-0-does-not-refuse
   (implies (and (fn-mm-tot-p acc)
                 (not (eq (fn-lgo-expansions zs dicts) :bad))
                 (not (eq (fn-srs-decode (fn-lgo-expansions zs dicts)) :bad)))
            (not (eq (mv-nth 1 (fn-lgo-fold zs 0 acc dicts allow)) :bad)))
   :hints (("Goal" :induct (fn-lgo-fold zs 0 acc dicts allow)
            :expand ((fn-lgo-fold zs 0 acc dicts allow) (fn-lgo-expansions zs dicts))
            :in-theory (disable fn-lgo-wire-tot fn-lzr-expand fn-lgo-add
                                fn-srs-decode fn-store-event-decode-exact fn-lgo-record-tot
                                fn-lgo-wire-fold)))))

(local
 (defthm fn-lgo-intern-step-of-bad-wires
   (implies (not (consp ws))
            (equal (car (fn-ssr-intern-step acc ws rs ps mode dicts fn-arena))
                   (if (and (null ws) (not (equal acc :bad))) acc :bad)))
   :hints (("Goal" :expand ((fn-ssr-intern-step acc ws rs ps mode dicts fn-arena))))))

(local
 (defthm fn-lgo-decode-of-bad
   (equal (fn-srs-decode :bad) :bad)
   :hints (("Goal" :expand ((fn-srs-decode :bad))))))

(local
 (defthm fn-lgo-charged-of-bad
   (equal (fn-ct-charged :bad res) (fn-ct-zero-tot res))
   :hints (("Goal" :expand ((fn-ct-charged :bad res))))))

(local
 (defthm fn-lgo-le-of-plus-right
   (implies (and (fn-mm-tot-p a) (not (fn-mm-tot-paged-p a)))
            (fn-mm-tot-le a (fn-mm-tot-plus a b)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-le)))))

(local
 (defthm fn-lgo-cache-tot-shape
   (implies (fn-ct-totals-cache-validp cache rows :resident)
            (and (fn-mm-tot-p (cdr cache)) (not (fn-mm-tot-paged-p (cdr cache)))))
   :hints (("Goal" :in-theory (e/d (fn-ct-totals-cache-validp) (fn-ct-charged))))))

(local
 (defthm fn-lgo-plus-zero-constant
   (implies (fn-mm-tot-p tot)
            (equal (fn-mm-tot-plus tot '(0 0 0 0 0 0 0 0 :resident)) tot))
   :hints (("Goal" :use ((:instance fn-lgo-plus-zero (res :resident)))
            :in-theory (e/d ((:e fn-ct-zero-tot)) (fn-lgo-plus-zero))))))

; KEYSTONE L2-5.  The suffix replay starts from the statement epoch at K with
; no rows (ACC, any keyring, any natural generation, any identity context);
; from a valid (K . TOT) cache for the opened ROWS, the rows past K the
; replay's, each within the HISTORY clause, the scan's total from the cache's
; TOT bounds the charged fold of ROWS.  Whether the replay or the scan
; refuses is not a hypothesis: a refused replay leaves no row past K (the
; fold is the cache's TOT), and a replay that does not refuse decoded every
; record past J, so the scan did not refuse.
(defthm fn-lgo-observed-covers-the-opened-store
  (let* ((k (car cache))
         (suffix (mv-nth 1 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow)))
         (acc1 (mv-nth 0 (fn-ssr-intern-step
                          (fn-ssr-state nil keyring (nfix generation) identity)
                          (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts))
                          nil nil :resident nil fn-arena))))
    (implies (and (fn-ct-totals-cache-validp cache rows :resident)
                  (equal (nthcdr k rows) (fn-ssr-rows acc1))
                  (fn-lgo-rows-history-within (nthcdr k rows) allow))
             (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) suffix))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (mv-nth 0 (fn-ssr-intern-step
                                      (fn-ssr-state nil keyring (nfix generation) identity)
                                      (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts))
                                      nil nil :resident nil fn-arena))
                          :bad))
           :in-theory (disable fn-lgo-fold fn-lgo-expansions fn-srs-decode fn-lgo-wire-fold
                               fn-ct-charged fn-ct-totals-cache-validp fn-mm-tot-le
                               fn-lgo-observed-covers-when-interned)
           :use ((:instance fn-lgo-observed-covers-when-interned)
                 (:instance fn-lgo-charged-of-cache)
                 (:instance fn-lgo-fold-0-does-not-refuse (zs (nthcdr j zs)) (acc (fn-ct-zero-tot :resident)))
                 (:instance fn-lgo-fold-past-the-skip (skip j) (acc (fn-ct-zero-tot :resident)))))))
