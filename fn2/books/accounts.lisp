;; The principal ledger (layer D, quest D7; ROUND2 section B.2: "principal
;; accounts are shared ledger rows, not a second executor"). The design is
;; fn2/docs/d-machines-nntp.md section 13. One row per calendar principal
;; slot 0..P-1 (slot 0 is the anonymous principal) and the system row P,
;; which is never in the calendar. Per row and holding dimension: limit,
;; reserve, hold; per charge dimension: a monotone charge. Per dimension:
;; capacity N and committed = sum over rows of max(hold, reserve).
;; The admission rule: an acquisition above a row's own reserve must fit
;; what no row has committed, so no principal can draw another's reserve.
;; This book is a library; the core wrappers the machines call are in
;; fn2-account-events, materialized after the core instance.
(in-package "ACL2")
(include-book "core-children")
(include-book "profile")
(include-book "resources")
(local (include-book "arithmetic/top" :dir :system))
(fn2-book-layer :d)

;; The dimensions are data; every use names a dimension by keyword and the
;; index is resolved at expansion. A holding dimension is a D0 resource kind
;; whose holdings are attributed to principals; :capacity names its profile key.
(defconst *fn2-account-holdings*
  '((:connection-row :capacity :c
     :why "The entitlement to a connection; one RX and one TX range ride with each row for its lifetime.")
    (:principal-reservation :capacity :c
     :why "Concurrent requests of a principal: one per holder, held from the framed line to the reply's last octet.")
    ;; E's consumer surface (fn2/docs/e-surface.md section 11; D7 4/n-a)
    (:durable-octets :capacity :dstore :default 4294967295
     :why "The store's durable quota in 4,096-octet blocks: a principal's appended articles, from the append's transaction to retention's reclaim.")
    (:wait-row :capacity :w
     :why "A principal's parked waits, from admission to reply or cancellation.")
    (:subscription-edge :capacity :esub :default 4096
     :why "A principal's subscription edges, held from register or rebase to unregister.")))
(defconst *fn2-account-charges*
  '((:rx-octets :why "Octets received, settled from Receive completion counts.")
    (:tx-octets :why "Octets sent, settled from Send completion counts.")
    (:requests :why "Replies rendered for framed lines.")
    (:run-steps :why "Steps of scheduled runs (the scheduler's charge, seam S2).")
    (:run-bytes :why "Bytes of scheduled runs (the scheduler's charge, seam S2).")))
(defconst *fn2-account-nh* (len *fn2-account-holdings*))
(defconst *fn2-account-nc* (len *fn2-account-charges*))
(defconst *fn2-account-u32-max* 4294967295)

(defun fn2-account-key-index (key entries i)
  (declare (xargs :verify-guards nil))
  (cond ((atom entries) nil) ((eq key (caar entries)) i)
        (t (fn2-account-key-index key (cdr entries) (+ 1 i)))))
(defmacro fn2-account-holding (key)
  (or (fn2-account-key-index key *fn2-account-holdings* 0)
      (er hard 'fn2-account-holding "~x0 is not a holding dimension of *fn2-account-holdings*." key)))
(defmacro fn2-account-charge-dim (key)
  (or (fn2-account-key-index key *fn2-account-charges* 0)
      (er hard 'fn2-account-charge-dim "~x0 is not a charge dimension of *fn2-account-charges*." key)))

;; Every holding dimension is a D0 kind.
(assert-event (subsetp-eq (strip-cars *fn2-account-holdings*) (strip-cars *fn2-resource-order*)))

(defcolumns fn2-accounts
  ((state (:enum fn2-account-state (:free :anonymous :configured :system)))
   (weight :u8) (wait-head :link) (wait-tail :link)
   ;; the grant service's cursor (D7 4/n-a, layer doc 13.8): read and
   ;; written on the system row only, the row the grant service runs on
   (grant-at :u32)
   ;; the row's incarnation: bumped at each rebinding, never reset, so a
   ;; principal id (slot, incarnation) is never reused within a store
   (incarnation :u32))
  :init-name fn2-accounts-columns-init
  :extra-fields
  ((fn2-accounts-limit :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t
    :why "Per (dimension, row): dimension-major, holding dimensions times rows.")
   (fn2-accounts-reserve :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t
    :why "Per (dimension, row): the protected reservation.")
   (fn2-accounts-hold :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t
    :why "Per (dimension, row): the current holding.")
   (fn2-accounts-charge :type (array (unsigned-byte 60) (0)) :initially 0 :resizable t
    :why "Per (charge dimension, row): monotone work charges.")
   (fn2-accounts-capacity :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t
    :why "Per holding dimension: the capacity N.")
   (fn2-accounts-committed :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t
    :why "Per holding dimension: the sum over rows of max(hold, reserve).")))

;; Element facts for the extra arrays (the generated facts cover the
;; columns; these cover the dimension-major arrays the same way).
(defmacro fn2-account-array-facts (field width)
  (let* ((fp (fn2-columns-sym field "P"))
         (ix (fn2-columns-pre "*" (fn2-columns-sym field "I*")))
         (lemma (fn2-columns-sym field "-ELEMENT")))
    `(progn
       (defthm ,lemma
         (implies (and (,fp x) (natp i) (< i (len x)))
                  (and (natp (nth i x)) (< (nth i x) ,(expt 2 width))))
         :hints (("Goal" :in-theory (enable nth ,fp) :induct (nth i x))))
       (defthm ,(fn2-columns-sym lemma "-ANY")
         (implies (,fp x) (< (nfix (nth i x)) ,(expt 2 width)))
         :hints (("Goal" :in-theory (enable nth ,fp) :induct (nth i x))))
       (defthm ,(fn2-columns-sym lemma "-TYPES")
         (implies (and (fn2-accountsp fn2-accounts) (natp i) (< i (len (nth ,ix fn2-accounts))))
                  (and (natp (nth i (nth ,ix fn2-accounts)))
                       (integerp (nth i (nth ,ix fn2-accounts)))
                       (rationalp (nth i (nth ,ix fn2-accounts)))
                       (acl2-numberp (nth i (nth ,ix fn2-accounts)))))
         :hints (("Goal" :use ((:instance ,lemma (x (nth ,ix fn2-accounts)))))))
       (defthm ,(fn2-columns-sym lemma "-BOUND")
         (implies (and (fn2-accountsp fn2-accounts) (natp i) (< i (len (nth ,ix fn2-accounts))))
                  (and (<= 0 (nth i (nth ,ix fn2-accounts)))
                       (< (nth i (nth ,ix fn2-accounts)) ,(expt 2 width))))
         :rule-classes :linear
         :hints (("Goal" :use ((:instance ,lemma (x (nth ,ix fn2-accounts))))))))))
(fn2-account-array-facts fn2-accounts-limit 32)
(fn2-account-array-facts fn2-accounts-reserve 32)
(fn2-account-array-facts fn2-accounts-hold 32)
(fn2-account-array-facts fn2-accounts-charge 60)
(fn2-account-array-facts fn2-accounts-capacity 32)
(fn2-account-array-facts fn2-accounts-committed 32)

(defun fn2-accounts-shapep (fn2-accounts)
  (declare (xargs :stobjs fn2-accounts))
  (let ((r (fn2-accounts-rows fn2-accounts)))
    (and (natp r)
         (equal (fn2-accounts-limit-length fn2-accounts) (* *fn2-account-nh* r))
         (equal (fn2-accounts-reserve-length fn2-accounts) (* *fn2-account-nh* r))
         (equal (fn2-accounts-hold-length fn2-accounts) (* *fn2-account-nh* r))
         (equal (fn2-accounts-charge-length fn2-accounts) (* *fn2-account-nc* r))
         (equal (fn2-accounts-capacity-length fn2-accounts) *fn2-account-nh*)
         (equal (fn2-accounts-committed-length fn2-accounts) *fn2-account-nh*))))

(defthm fn2-account-ix-bound
  (implies (and (natp d) (natp p) (natp r) (natp n) (< d n) (< p r))
           (< (+ p (* d r)) (* n r)))
  :hints (("Goal" :nonlinearp t)))

(defmacro fn2-account-ix-facts (field n)
  (let ((ix (fn2-columns-pre "*" (fn2-columns-sym field "I*"))))
    `(defthm ,(fn2-columns-sym field "-IX-IN-RANGE")
       (implies (and (fn2-accounts-shapep fn2-accounts) (fn2-accounts-wfp fn2-accounts)
                     (natp d) (< d ,n) (natp p) (< p (nth *fn2-accounts-rows* fn2-accounts)))
                (< (+ p (* d (nth *fn2-accounts-rows* fn2-accounts))) (len (nth ,ix fn2-accounts))))
       :rule-classes (:rewrite :linear)
       :hints (("Goal" :in-theory (disable fn2-account-ix-bound)
                :use ((:instance fn2-account-ix-bound (n ,n) (r (nth *fn2-accounts-rows* fn2-accounts)))))))))
(fn2-account-ix-facts fn2-accounts-limit *fn2-account-nh*)
(fn2-account-ix-facts fn2-accounts-reserve *fn2-account-nh*)
(fn2-account-ix-facts fn2-accounts-hold *fn2-account-nh*)
(fn2-account-ix-facts fn2-accounts-charge *fn2-account-nc*)
(defthm fn2-account-dimension-lengths
  (implies (fn2-accounts-shapep fn2-accounts)
           (and (equal (len (nth *fn2-accounts-capacityi* fn2-accounts)) *fn2-account-nh*)
                (equal (len (nth *fn2-accounts-committedi* fn2-accounts)) *fn2-account-nh*))))
(defthm fn2-account-shape-rows
  (implies (fn2-accounts-shapep fn2-accounts) (natp (nth *fn2-accounts-rows* fn2-accounts)))
  :rule-classes (:rewrite :forward-chaining))
(defmacro fn2-account-shape-update (field)
  (let ((upd (fn2-columns-pre "UPDATE-" (fn2-columns-sym field "I")))
        (ix (fn2-columns-pre "*" (fn2-columns-sym field "I*"))))
    `(defthm ,(fn2-columns-sym upd "-SHAPE")
       (implies (and (fn2-accounts-shapep fn2-accounts) (natp i) (< i (len (nth ,ix fn2-accounts))))
                (fn2-accounts-shapep (,upd i v fn2-accounts)))
       :hints (("Goal" :in-theory (enable fn2-accounts-shapep))))))
(fn2-account-shape-update fn2-accounts-limit)
(fn2-account-shape-update fn2-accounts-reserve)
(fn2-account-shape-update fn2-accounts-hold)
(fn2-account-shape-update fn2-accounts-charge)
(fn2-account-shape-update fn2-accounts-capacity)
(fn2-account-shape-update fn2-accounts-committed)
(defmacro fn2-account-wfp-update (field)
  (let ((upd (fn2-columns-pre "UPDATE-" (fn2-columns-sym field "I"))))
    `(defthm ,(fn2-columns-sym upd "-WFP")
       (equal (fn2-accounts-wfp (,upd i v fn2-accounts)) (fn2-accounts-wfp fn2-accounts))
       :hints (("Goal" :in-theory (enable fn2-accounts-wfp))))))
(fn2-account-wfp-update fn2-accounts-limit)
(fn2-account-wfp-update fn2-accounts-reserve)
(fn2-account-wfp-update fn2-accounts-hold)
(fn2-account-wfp-update fn2-accounts-charge)
(fn2-account-wfp-update fn2-accounts-capacity)
(fn2-account-wfp-update fn2-accounts-committed)
(defmacro fn2-account-shape-column (col)
  (let ((set (fn2-columns-sym 'fn2-accounts- (concatenate 'string "SET-" (symbol-name col)))))
    `(defthm ,(fn2-columns-sym set "-SHAPE")
       (equal (fn2-accounts-shapep (,set i v fn2-accounts)) (fn2-accounts-shapep fn2-accounts))
       :hints (("Goal" :in-theory (enable fn2-accounts-shapep))))))
(fn2-account-shape-column state)
(fn2-account-shape-column weight)
(fn2-account-shape-column wait-head)
(fn2-account-shape-column wait-tail)
(fn2-account-shape-column grant-at)
(fn2-account-shape-column incarnation)
(in-theory (disable fn2-accounts-shapep fn2-account-ix-bound))

;; Element readers over the dimension-major arrays: natural by
;; construction (the array's type makes the nfix the identity), with the
;; width bound as a linear fact, so the operations' guards are linear.
(defmacro fn2-account-reader (name field width)
  (let ((read (fn2-columns-sym field "I")) (len (fn2-columns-sym field "-LENGTH")))
    `(progn
       (defun ,name (i fn2-accounts)
         (declare (xargs :stobjs fn2-accounts
                         :guard (and (fn2-accountsp fn2-accounts) (natp i) (< i (,len fn2-accounts)))))
         (nfix (,read i fn2-accounts)))
       (defthm ,(fn2-columns-sym name "-BOUND")
         (implies (fn2-accountsp fn2-accounts) (< (,name i fn2-accounts) ,(expt 2 width)))
         :rule-classes :linear
         :hints (("Goal" :in-theory (enable ,name)
                  :use ((:instance ,(fn2-columns-sym field "-ELEMENT-ANY")
                                   (x (nth ,(fn2-columns-pre "*" (fn2-columns-sym field "I*")) fn2-accounts)))))))
       (in-theory (disable ,name)))))
(fn2-account-reader fn2-account-limitv fn2-accounts-limit 32)
(fn2-account-reader fn2-account-reservev fn2-accounts-reserve 32)
(fn2-account-reader fn2-account-holdv fn2-accounts-hold 32)
(fn2-account-reader fn2-account-chargev fn2-accounts-charge 60)
(fn2-account-reader fn2-account-capacityv fn2-accounts-capacity 32)
(fn2-account-reader fn2-account-committedv fn2-accounts-committed 32)

(defmacro fn2-account-guard ()
  '(and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts)))

;; ------------------------------------------------------------------------
;; The ledger operations. Codes: :ok; :limit (over the row's own limit);
;; :shared (the part above the row's reserve does not fit the uncommitted
;; remainder); :bounds (a row or dimension outside the ledger: the caller
;; stops); :underflow and :state (a release the ledger does not hold: an
;; invariant broken, the caller stops); :overflow (a charge past u60).

(defun fn2-account-acquire (p d a fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (let ((rows (fn2-accounts-rows fn2-accounts)))
    (if (not (and (natp p) (< p rows) (natp d) (< d *fn2-account-nh*) (natp a)
                  (< (+ p (* d rows)) (* *fn2-account-nh* rows))))
        (mv :bounds fn2-accounts)
      (let* ((ix (+ p (* d rows)))
             (h (fn2-account-holdv ix fn2-accounts))
             (r (fn2-account-reservev ix fn2-accounts))
             (h2 (+ h a))
             (n (fn2-account-capacityv d fn2-accounts))
             (c (fn2-account-committedv d fn2-accounts))
             (extra (- (max h2 r) (max h r))))
        (cond ((> h2 (fn2-account-limitv ix fn2-accounts)) (mv :limit fn2-accounts))
              ((> (+ c extra) n) (mv :shared fn2-accounts))
              (t (let* ((fn2-accounts (update-fn2-accounts-holdi ix h2 fn2-accounts))
                        (fn2-accounts (update-fn2-accounts-committedi d (+ c extra) fn2-accounts)))
                   (mv :ok fn2-accounts))))))))

(defun fn2-account-release (p d a fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (let ((rows (fn2-accounts-rows fn2-accounts)))
    (if (not (and (natp p) (< p rows) (natp d) (< d *fn2-account-nh*) (natp a)
                  (< (+ p (* d rows)) (* *fn2-account-nh* rows))))
        (mv :bounds fn2-accounts)
      (let* ((ix (+ p (* d rows)))
             (h (fn2-account-holdv ix fn2-accounts))
             (r (fn2-account-reservev ix fn2-accounts))
             (c (fn2-account-committedv d fn2-accounts)))
        (if (> a h) (mv :underflow fn2-accounts)
          (let ((less (- (max h r) (max (- h a) r))))
            (if (> less c) (mv :state fn2-accounts)
              (let* ((fn2-accounts (update-fn2-accounts-holdi ix (- h a) fn2-accounts))
                     (fn2-accounts (update-fn2-accounts-committedi d (- c less) fn2-accounts)))
                (mv :ok fn2-accounts)))))))))

(defun fn2-account-charge (p k a fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (let ((rows (fn2-accounts-rows fn2-accounts)))
    (if (not (and (natp p) (< p rows) (natp k) (< k *fn2-account-nc*) (natp a)
                  (< (+ p (* k rows)) (* *fn2-account-nc* rows))))
        (mv :bounds fn2-accounts)
      (let* ((ix (+ p (* k rows)))
             (v (+ a (fn2-account-chargev ix fn2-accounts))))
        (if (not (unsigned-byte-p 60 v)) (mv :overflow fn2-accounts)
          (let ((fn2-accounts (update-fn2-accounts-chargei ix v fn2-accounts))) (mv :ok fn2-accounts)))))))

;; Shape and type preservation (the guards of the next operation).
(defmacro fn2-account-preserves (name args &optional (pos '1))
  `(progn
     (defthm ,(fn2-columns-sym name "-PRESERVES")
       (implies (fn2-account-guard)
                (let ((fn2-accounts (mv-nth ,pos (,name ,@args))))
                  (fn2-account-guard))))
     (defthm ,(fn2-columns-sym name "-ROWS")
       (equal (nth *fn2-accounts-rows* (mv-nth ,pos (,name ,@args))) (nth *fn2-accounts-rows* fn2-accounts)))))
(fn2-account-preserves fn2-account-acquire (p d a fn2-accounts))
(fn2-account-preserves fn2-account-release (p d a fn2-accounts))
(fn2-account-preserves fn2-account-charge (p k a fn2-accounts))
(in-theory (disable fn2-account-acquire fn2-account-release fn2-account-charge))
;; A two-dimension bundle, whole or not at all (a refused second dimension
;; returns the first before the refusal is reported).
(defun fn2-account-acquire2 (p d1 a1 d2 a2 fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (mv-let (code fn2-accounts) (fn2-account-acquire p d1 a1 fn2-accounts)
    (if (not (eq code :ok)) (mv code fn2-accounts)
      (mv-let (code2 fn2-accounts) (fn2-account-acquire p d2 a2 fn2-accounts)
        (if (eq code2 :ok) (mv :ok fn2-accounts)
          (mv-let (back fn2-accounts) (fn2-account-release p d1 a1 fn2-accounts)
            (mv (if (eq back :ok) code2 :state) fn2-accounts)))))))

(defun fn2-account-release2 (p d1 a1 d2 a2 fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (mv-let (code fn2-accounts) (fn2-account-release p d2 a2 fn2-accounts)
    (if (not (eq code :ok)) (mv code fn2-accounts)
      (fn2-account-release p d1 a1 fn2-accounts))))

(fn2-account-preserves fn2-account-acquire2 (p d1 a1 d2 a2 fn2-accounts))
(fn2-account-preserves fn2-account-release2 (p d1 a1 d2 a2 fn2-accounts))
(in-theory (disable fn2-account-acquire2 fn2-account-release2))

;; Authentication's transfer of attribution (rule 5), as one net change:
;; the bundle is released on FROM and acquired on TO; when TO refuses, it is
;; acquired back on FROM, which cannot be refused (FROM held it a moment ago
;; and nothing else ran), so the ledger is unchanged and the refusal is
;; reported. Releasing first means a capacity-neutral transfer is never
;; refused for want of shared room (Astra, D7 review). Charges are not
;; touched: what FROM incurred stays FROM's.
(defun fn2-account-attribute (from to d1 a1 d2 a2 fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (mv-let (code fn2-accounts) (fn2-account-release2 from d1 a1 d2 a2 fn2-accounts)
    (if (not (eq code :ok)) (mv (if (eq code :bounds) :bounds :state) fn2-accounts)
      (mv-let (code fn2-accounts) (fn2-account-acquire2 to d1 a1 d2 a2 fn2-accounts)
        (if (eq code :ok) (mv :ok fn2-accounts)
          (mv-let (back fn2-accounts) (fn2-account-acquire2 from d1 a1 d2 a2 fn2-accounts)
            (mv (if (eq back :ok) code :state) fn2-accounts)))))))
(fn2-account-preserves fn2-account-attribute (from to d1 a1 d2 a2 fn2-accounts))
(in-theory (disable fn2-account-attribute))

;; ------------------------------------------------------------------------
;; Readers for the machines, the checkers and the tests (a row outside the
;; ledger reads as 0; the operations above refuse it by name).
(defun fn2-account-hold (p d fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (let ((rows (fn2-accounts-rows fn2-accounts)))
    (if (and (natp p) (< p rows) (natp d) (< d *fn2-account-nh*) (< (+ p (* d rows)) (* *fn2-account-nh* rows)))
        (fn2-account-holdv (+ p (* d rows)) fn2-accounts) 0)))
(defun fn2-account-reserve (p d fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (let ((rows (fn2-accounts-rows fn2-accounts)))
    (if (and (natp p) (< p rows) (natp d) (< d *fn2-account-nh*) (< (+ p (* d rows)) (* *fn2-account-nh* rows)))
        (fn2-account-reservev (+ p (* d rows)) fn2-accounts) 0)))
(defun fn2-account-limit (p d fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (let ((rows (fn2-accounts-rows fn2-accounts)))
    (if (and (natp p) (< p rows) (natp d) (< d *fn2-account-nh*) (< (+ p (* d rows)) (* *fn2-account-nh* rows)))
        (fn2-account-limitv (+ p (* d rows)) fn2-accounts) 0)))
(defun fn2-account-charged (p k fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (let ((rows (fn2-accounts-rows fn2-accounts)))
    (if (and (natp p) (< p rows) (natp k) (< k *fn2-account-nc*) (< (+ p (* k rows)) (* *fn2-account-nc* rows)))
        (fn2-account-chargev (+ p (* k rows)) fn2-accounts) 0)))
(defun fn2-account-committed (d fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (if (and (natp d) (< d *fn2-account-nh*)) (fn2-account-committedv d fn2-accounts) 0))
(defun fn2-account-capacity (d fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (if (and (natp d) (< d *fn2-account-nh*)) (fn2-account-capacityv d fn2-accounts) 0))

;; ------------------------------------------------------------------------
;; D7 4/n-a (layer doc 13.8): requests of a principal. A request holds one
;; :principal-reservation from its framed line to its reply's last octet.
;; A principal's waiting requests form a FIFO whose ends are the row's
;; wait-head and wait-tail; its links are the parked rows' directory links
;; (the core wrappers, fn2-account-request-events). No request barges: while
;; the FIFO is non-empty, a new request answers :queued even when it fits.
(defconst *fn2-account-request-dim* (fn2-account-holding :principal-reservation))
;; Whether (fn2-account-acquire p d a) would answer :ok.
(defun fn2-account-fits (p d a fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (let ((rows (fn2-accounts-rows fn2-accounts)))
    (and (natp p) (< p rows) (natp d) (< d *fn2-account-nh*) (natp a)
         (< (+ p (* d rows)) (* *fn2-account-nh* rows))
         (let* ((ix (+ p (* d rows)))
                (h (fn2-account-holdv ix fn2-accounts))
                (r (fn2-account-reservev ix fn2-accounts))
                (h2 (+ h a)))
           (and (<= h2 (fn2-account-limitv ix fn2-accounts))
                (<= (+ (fn2-account-committedv d fn2-accounts) (- (max h2 r) (max h r)))
                    (fn2-account-capacityv d fn2-accounts)))))))
(defthm fn2-account-fits-acquire
  (implies (fn2-account-fits p d a fn2-accounts)
           (equal (mv-nth 0 (fn2-account-acquire p d a fn2-accounts)) :ok))
  :hints (("Goal" :in-theory (enable fn2-account-acquire))))
(defun fn2-account-wait-head-of (p fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (if (and (natp p) (< p (fn2-accounts-rows fn2-accounts))) (fn2-accounts-wait-head p fn2-accounts) *fn2-none*))
(defun fn2-account-wait-tail-of (p fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (if (and (natp p) (< p (fn2-accounts-rows fn2-accounts))) (fn2-accounts-wait-tail p fn2-accounts) *fn2-none*))
;; A new request: :ok (acquired), :queued (the FIFO is non-empty), :limit
;; or :shared (it does not fit), :refused (a request limit of 0: refused by
;; name, never parked), :bounds.
(defun fn2-account-request (p fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (cond ((not (and (natp p) (< p (fn2-accounts-rows fn2-accounts)))) (mv :bounds fn2-accounts))
        ((equal (fn2-account-limit p *fn2-account-request-dim* fn2-accounts) 0) (mv :refused fn2-accounts))
        ((not (equal (fn2-accounts-wait-head p fn2-accounts) *fn2-none*)) (mv :queued fn2-accounts))
        (t (fn2-account-acquire p *fn2-account-request-dim* 1 fn2-accounts))))
(fn2-account-preserves fn2-account-request (p fn2-accounts))
;; No barging (layer doc 13.8): while P's FIFO is non-empty a request
;; acquires nothing, whatever it would fit.
(defthm fn2-account-request-no-barging
  (implies (and (natp p) (< p (fn2-accounts-rows fn2-accounts))
                (not (equal (fn2-account-limit p *fn2-account-request-dim* fn2-accounts) 0))
                (not (equal (fn2-accounts-wait-head p fn2-accounts) *fn2-none*)))
           (and (equal (mv-nth 0 (fn2-account-request p fn2-accounts)) :queued)
                (equal (mv-nth 1 (fn2-account-request p fn2-accounts)) fn2-accounts))))
(in-theory (disable fn2-account-request))
;; The grant service's choice: from row I, at most K rows on (cyclic), the
;; first whose FIFO head's request fits; *fn2-none* when none does.
(defun fn2-account-grant-scan (k i fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-account-guard) (natp k) (natp i)) :measure (nfix k)))
  (let ((rows (nfix (fn2-accounts-rows fn2-accounts))))
    (if (or (zp k) (zp rows)) *fn2-none*
      (let ((p (if (< (nfix i) rows) (nfix i) 0)))
        (if (and (not (equal (fn2-accounts-wait-head p fn2-accounts) *fn2-none*))
                 (fn2-account-fits p *fn2-account-request-dim* 1 fn2-accounts))
            p
          (fn2-account-grant-scan (- k 1) (+ 1 p) fn2-accounts))))))
;; The cursor lives on the system row (the last); every row is scanned once.
(defun fn2-account-grant-cursor (fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (let ((rows (fn2-accounts-rows fn2-accounts)))
    (if (zp rows) 0 (fn2-accounts-grant-at (- rows 1) fn2-accounts))))
(defun fn2-account-grant-next (fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (fn2-account-grant-scan (nfix (fn2-accounts-rows fn2-accounts)) (fn2-account-grant-cursor fn2-accounts) fn2-accounts))
(defthm fn2-account-grant-scan-range
  (implies (not (equal (fn2-account-grant-scan k i fn2-accounts) *fn2-none*))
           (and (natp (fn2-account-grant-scan k i fn2-accounts))
                (< (fn2-account-grant-scan k i fn2-accounts) (nfix (fn2-accounts-rows fn2-accounts))))))
(defthm fn2-account-grant-scan-fits
  (implies (not (equal (fn2-account-grant-scan k i fn2-accounts) *fn2-none*))
           (fn2-account-fits (fn2-account-grant-scan k i fn2-accounts) *fn2-account-request-dim* 1 fn2-accounts)))
(in-theory (disable fn2-account-fits fn2-account-grant-scan))

;; The durable principal identity (C's fn2-outcome key, (:id principal)):
;; slot * 2^32 + incarnation, a u60. A slot is rebound (E2's binding, an
;; account deleted and its slot issued again) only through
;; fn2-account-rebind, which bumps the incarnation, so no id names two
;; principals within a store. :exhausted at the u32 limit: the slot is
;; retired, never wrapped.
(defun fn2-account-principal-id (p fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (if (and (natp p) (< p (fn2-accounts-rows fn2-accounts)))
      (+ (* p 4294967296) (fn2-accounts-incarnation p fn2-accounts))
    0))
(defun fn2-account-rebind (p fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (cond ((not (and (natp p) (< p (fn2-accounts-rows fn2-accounts)))) (mv :bounds fn2-accounts))
        ((>= (fn2-accounts-incarnation p fn2-accounts) *fn2-account-u32-max*) (mv :exhausted fn2-accounts))
        (t (let ((fn2-accounts (fn2-accounts-set-incarnation p (+ 1 (fn2-accounts-incarnation p fn2-accounts))
                                                             fn2-accounts)))
             (mv :ok fn2-accounts)))))
(fn2-account-preserves fn2-account-rebind (p fn2-accounts))
;; Ids are unique: two rows, or one row before and after a rebinding, never
;; share an id; and a rebinding never lowers the incarnation.
(defthm fn2-account-principal-id-unique
  (implies (and (fn2-account-guard) (natp p) (natp q) (< p (fn2-accounts-rows fn2-accounts))
                (< q (fn2-accounts-rows fn2-accounts)) (not (equal p q)))
           (not (equal (fn2-account-principal-id p fn2-accounts) (fn2-account-principal-id q fn2-accounts))))
  :hints (("Goal" :nonlinearp t)))
(defthm fn2-account-rebind-fresh
  (implies (and (fn2-account-guard) (equal (mv-nth 0 (fn2-account-rebind p fn2-accounts)) :ok))
           (< (fn2-account-principal-id p fn2-accounts)
              (fn2-account-principal-id p (mv-nth 1 (fn2-account-rebind p fn2-accounts))))))
(in-theory (disable fn2-account-rebind))

;; ------------------------------------------------------------------------
;; The invariant, executable: per dimension committed = sum of
;; max(hold, reserve) <= capacity, and hold <= limit on every row.
(defun fn2-account-sum (d i fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-account-guard) (natp d) (natp i))
                  :measure (nfix (- (nfix (fn2-accounts-rows fn2-accounts)) (nfix i)))))
  (if (or (not (natp i)) (>= i (nfix (fn2-accounts-rows fn2-accounts)))) 0
    (+ (max (fn2-account-hold i d fn2-accounts) (fn2-account-reserve i d fn2-accounts))
       (fn2-account-sum d (+ 1 i) fn2-accounts))))
(defun fn2-account-limits-ok (d i fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-account-guard) (natp d) (natp i))
                  :measure (nfix (- (nfix (fn2-accounts-rows fn2-accounts)) (nfix i)))))
  (if (or (not (natp i)) (>= i (nfix (fn2-accounts-rows fn2-accounts)))) t
    (and (<= (fn2-account-hold i d fn2-accounts) (fn2-account-limit i d fn2-accounts))
         (fn2-account-limits-ok d (+ 1 i) fn2-accounts))))
(defun fn2-account-dims-ok (d fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-account-guard) (natp d))
                  :measure (nfix (- *fn2-account-nh* (nfix d)))))
  (if (or (not (natp d)) (>= d *fn2-account-nh*)) t
    (and (equal (fn2-account-committed d fn2-accounts) (fn2-account-sum d 0 fn2-accounts))
         (<= (fn2-account-committed d fn2-accounts) (fn2-account-capacity d fn2-accounts))
         (fn2-account-limits-ok d 0 fn2-accounts)
         (fn2-account-dims-ok (+ 1 d) fn2-accounts))))
(defun fn2-accounts-conservedp (fn2-accounts)
  (declare (xargs :stobjs fn2-accounts))
  (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts)
       (fn2-account-dims-ok 0 fn2-accounts)))

;; ------------------------------------------------------------------------
;; Keystones local to the ledger.

;; Protected reservations (rule 5): whatever every other row holds, a row
;; acquiring within its own reserve and limit is admitted. The only fact
;; about the rest of the ledger it needs is committed <= capacity, which
;; fn2-accounts-conservedp gives.
(defthm fn2-account-acquire-protected
  (implies (and (fn2-account-guard)
                (natp p) (< p (fn2-accounts-rows fn2-accounts))
                (natp d) (< d *fn2-account-nh*) (natp a)
                (<= (fn2-account-committed d fn2-accounts) (fn2-account-capacity d fn2-accounts))
                (<= (+ (fn2-account-hold p d fn2-accounts) a) (fn2-account-reserve p d fn2-accounts))
                (<= (+ (fn2-account-hold p d fn2-accounts) a) (fn2-account-limit p d fn2-accounts)))
           (equal (mv-nth 0 (fn2-account-acquire p d a fn2-accounts)) :ok))
  :hints (("Goal" :in-theory (e/d (fn2-account-acquire) (fn2-account-ix-bound))
           :use ((:instance fn2-account-ix-bound (n *fn2-account-nh*) (r (fn2-accounts-rows fn2-accounts)))))))

;; Charges are monotone: no holding operation touches a charge, and a
;; charge only adds (disconnecting erases no charge; attribution launders
;; none).
(defthm fn2-account-acquire-charges
  (equal (nth *fn2-accounts-chargei* (mv-nth 1 (fn2-account-acquire p d a fn2-accounts)))
         (nth *fn2-accounts-chargei* fn2-accounts))
  :hints (("Goal" :in-theory (enable fn2-account-acquire))))
(defthm fn2-account-release-charges
  (equal (nth *fn2-accounts-chargei* (mv-nth 1 (fn2-account-release p d a fn2-accounts)))
         (nth *fn2-accounts-chargei* fn2-accounts))
  :hints (("Goal" :in-theory (enable fn2-account-release))))
(defthm fn2-account-attribute-charges
  (equal (nth *fn2-accounts-chargei* (mv-nth 1 (fn2-account-attribute from to d1 a1 d2 a2 fn2-accounts)))
         (nth *fn2-accounts-chargei* fn2-accounts))
  :hints (("Goal" :in-theory (enable fn2-account-attribute fn2-account-acquire2 fn2-account-release2))))
(defthm fn2-account-charge-monotone
  (implies (natp i)
           (<= (fn2-account-chargev i fn2-accounts)
               (fn2-account-chargev i (mv-nth 1 (fn2-account-charge p k a fn2-accounts)))))
  :hints (("Goal" :in-theory (enable fn2-account-charge fn2-account-chargev)))
  :rule-classes :linear)

;; The ledger's operation set (the owner of its owed rows).
(make-event (value (fn2-declare '(:operation-set fn2-accounts) nil nil nil)))

;; Conservation under every ledger operation: owed (the sum over the
;; dimension-major array under one update), with executable teeth.
(defthm-owed fn2-account-ops-conserve (op p q d1 a1 d2 a2 fn2-accounts)
  (implies (fn2-accounts-conservedp fn2-accounts)
           (fn2-accounts-conservedp
            (case op
              (:acquire (mv-nth 1 (fn2-account-acquire p d1 a1 fn2-accounts)))
              (:release (mv-nth 1 (fn2-account-release p d1 a1 fn2-accounts)))
              (:charge (mv-nth 1 (fn2-account-charge p d1 a1 fn2-accounts)))
              (:acquire2 (mv-nth 1 (fn2-account-acquire2 p d1 a1 d2 a2 fn2-accounts)))
              (:release2 (mv-nth 1 (fn2-account-release2 p d1 a1 d2 a2 fn2-accounts)))
              (otherwise (mv-nth 1 (fn2-account-attribute p q d1 a1 d2 a2 fn2-accounts))))))
  :schema :invariant :from (:operation-set fn2-accounts)
  :teeth (fn2-accounts-test-conserve fn2-accounts-test-conserve-negative)
  :doc "Every ledger operation keeps committed = sum of max(hold, reserve) <= capacity and hold <= limit, in every dimension; with fn2-account-acquire-protected this is rule 5's protected reservation over any sequence of operations.")

;; ------------------------------------------------------------------------
;; Configuration and initialization. Profile keys (optional; A's
;; profile.lisp is untouched): :accounts ((SLOT . PLIST) ...) with SLOT a
;; principal slot below P or :system, PLIST (:state S :weight W :limits
;; ((DIM . N) ...) :reserves ((DIM . N) ...)). Unconfigured: slot 0 is the
;; anonymous principal with every limit its dimension's capacity, every
;; other slot :free with limits 0, the system row limits its capacity and
;; reserves 0.

(defun fn2-account-plist-get (key plist)
  (declare (xargs :guard t))
  (cond ((atom plist) nil) ((atom (cdr plist)) nil)
        ((equal (car plist) key) (cadr plist))
        (t (fn2-account-plist-get key (cddr plist)))))
(defun fn2-account-capacity-key (entries d)
  (declare (xargs :guard (natp d)))
  (let ((e (nth d (true-list-fix entries))))
    (if (consp e) (fn2-account-plist-get :capacity (cdr e)) nil)))
;; The profile's value for the dimension's key, else the dimension's
;; :default (ROUND2's: :esub 4,096 edges; :dstore the ledger's u32 range).
(defun fn2-account-profile-capacity (d profile)
  (declare (xargs :guard (natp d)))
  (let ((v (fn2-profile-get (fn2-account-capacity-key *fn2-account-holdings* d) profile)))
    (or v (let ((e (nth d (true-list-fix *fn2-account-holdings*))))
            (if (consp e) (fn2-account-plist-get :default (cdr e)) nil)))))

(defun fn2-account-dim-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist) (null alist)
    (and (consp (car alist))
         (assoc-equal (caar alist) *fn2-account-holdings*)
         (unsigned-byte-p 32 (cdar alist))
         (fn2-account-dim-alistp (cdr alist)))))
(defun fn2-account-dim-get (key alist)
  (declare (xargs :guard t))
  (cond ((atom alist) 0)
        ((and (consp (car alist)) (equal (caar alist) key)) (nfix (cdar alist)))
        (t (fn2-account-dim-get key (cdr alist)))))

(defun fn2-account-entry-dims-ok (keys limits reserves)
  (declare (xargs :guard t))
  (if (atom keys) t
    (and (<= (fn2-account-dim-get (car keys) reserves) (fn2-account-dim-get (car keys) limits))
         (fn2-account-entry-dims-ok (cdr keys) limits reserves))))
(defun fn2-account-entryp (entry p)
  (declare (xargs :guard t))
  (and (consp entry)
       (or (eq (car entry) :system) (and (natp (car entry)) (< (car entry) (nfix p))))
       (true-listp (cdr entry))
       (let ((state (fn2-account-plist-get :state (cdr entry)))
             (weight (fn2-account-plist-get :weight (cdr entry)))
             (limits (fn2-account-plist-get :limits (cdr entry)))
             (reserves (fn2-account-plist-get :reserves (cdr entry))))
         (and (if (eq (car entry) :system) (member-eq state '(nil :system))
                (member-eq state '(:anonymous :configured)))
              (or (null weight) (and (posp weight) (< weight 256)))
              (fn2-account-dim-alistp limits) (fn2-account-dim-alistp reserves)
              (fn2-account-entry-dims-ok (strip-cars *fn2-account-holdings*) limits reserves)))))
(defun fn2-account-entriesp (entries p)
  (declare (xargs :guard t))
  (if (atom entries) (null entries)
    (and (fn2-account-entryp (car entries) p) (fn2-account-entriesp (cdr entries) p))))
(defthm fn2-account-entryp-consp
  (implies (fn2-account-entryp entry p) (consp entry))
  :rule-classes :forward-chaining)
(defthm fn2-account-entriesp-alistp
  (implies (fn2-account-entriesp entries p) (alistp entries))
  :hints (("Goal" :in-theory (disable fn2-account-entryp))))
(defun fn2-account-reserve-total (key entries)
  (declare (xargs :guard t))
  (if (atom entries) 0
    (+ (if (consp (car entries))
           (fn2-account-dim-get key (fn2-account-plist-get :reserves (cdar entries))) 0)
       (fn2-account-reserve-total key (cdr entries)))))
(defun fn2-account-totals-ok (d entries profile)
  (declare (xargs :guard (natp d) :measure (nfix (- *fn2-account-nh* (nfix d)))))
  (if (or (not (natp d)) (>= d *fn2-account-nh*)) t
    (and (unsigned-byte-p 32 (fn2-account-profile-capacity d profile))
         (<= (fn2-account-reserve-total (car (nth d *fn2-account-holdings*)) entries)
             (fn2-account-profile-capacity d profile))
         (fn2-account-totals-ok (+ 1 d) entries profile))))
(defun fn2-accounts-profilep (profile)
  (declare (xargs :guard t))
  (let ((p (fn2-profile-p profile)) (entries (fn2-profile-get :accounts profile)))
    (and (posp p) (< (+ 1 p) 4294967296)
         (unsigned-byte-p 32 (* *fn2-account-nh* (+ 1 p)))
         (unsigned-byte-p 32 (* *fn2-account-nc* (+ 1 p)))
         (fn2-account-entriesp entries p)
         (no-duplicatesp-equal (strip-cars entries))
         (fn2-account-totals-ok 0 entries profile))))

(defun fn2-account-row-of (slot p)
  (declare (xargs :guard t))
  (if (eq slot :system) (nfix p) (nfix slot)))

;; Write one row's limits and reserves for dimensions d.. (defaults when
;; LIMITS is :default: the dimension's capacity).
(defun fn2-account-set-dims (row d limits reserves fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-account-guard) (natp d))
                  :measure (nfix (- *fn2-account-nh* (nfix d)))))
  (if (or (not (natp d)) (>= d *fn2-account-nh*)
          (not (natp row)) (>= row (fn2-accounts-rows fn2-accounts)))
      fn2-accounts
    (let* ((key (car (nth d *fn2-account-holdings*)))
           (ix (+ row (* d (fn2-accounts-rows fn2-accounts))))
           (l (if (eq limits :default) (fn2-account-capacityv d fn2-accounts)
                (fn2-account-dim-get key limits)))
           (r (if (eq limits :default) 0 (fn2-account-dim-get key reserves)))
           (fn2-accounts (update-fn2-accounts-limiti ix (if (unsigned-byte-p 32 l) l 0) fn2-accounts))
           (fn2-accounts (update-fn2-accounts-reservei ix (if (unsigned-byte-p 32 r) r 0) fn2-accounts)))
      (fn2-account-set-dims row (+ 1 d) limits reserves fn2-accounts))))
(defthm fn2-account-set-dims-preserves
  (implies (fn2-account-guard)
           (let ((fn2-accounts (fn2-account-set-dims row d limits reserves fn2-accounts)))
             (fn2-account-guard))))
(defthm fn2-account-set-dims-rows
  (equal (nth *fn2-accounts-rows* (fn2-account-set-dims row d limits reserves fn2-accounts))
         (nth *fn2-accounts-rows* fn2-accounts)))
(defthm fn2-account-set-dims-wfp
  (implies (fn2-accounts-wfp fn2-accounts) (fn2-accounts-wfp (fn2-account-set-dims row d limits reserves fn2-accounts))))
(in-theory (disable fn2-account-set-dims))

(defun fn2-account-configure (entries p fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (fn2-account-guard)))
  (if (atom entries) fn2-accounts
    (let* ((e (car entries))
           (fn2-accounts
            (if (not (consp e)) fn2-accounts
              (let* ((row (fn2-account-row-of (car e) p))
                     (plist (cdr e))
                     (state (fn2-account-plist-get :state plist))
                     (weight (fn2-account-plist-get :weight plist)))
                (if (>= row (fn2-accounts-rows fn2-accounts)) fn2-accounts
                  (let* ((fn2-accounts (fn2-account-set-dims row 0 (fn2-account-plist-get :limits plist)
                                                             (fn2-account-plist-get :reserves plist) fn2-accounts))
                         (fn2-accounts (fn2-accounts-set-state row
                                         (cond ((eq (car e) :system) *fn2-account-state-system*)
                                               ((eq state :anonymous) *fn2-account-state-anonymous*)
                                               (t *fn2-account-state-configured*))
                                         fn2-accounts)))
                    (fn2-accounts-set-weight row (if (and (posp weight) (< weight 256)) weight 1)
                                             fn2-accounts)))))))
      (fn2-account-configure (cdr entries) p fn2-accounts))))
(defthm fn2-account-configure-preserves
  (implies (fn2-account-guard)
           (let ((fn2-accounts (fn2-account-configure entries p fn2-accounts)))
             (fn2-account-guard))))
(defthm fn2-account-configure-rows
  (equal (nth *fn2-accounts-rows* (fn2-account-configure entries p fn2-accounts))
         (nth *fn2-accounts-rows* fn2-accounts)))
(defthm fn2-account-configure-wfp
  (implies (fn2-accounts-wfp fn2-accounts) (fn2-accounts-wfp (fn2-account-configure entries p fn2-accounts))))
(in-theory (disable fn2-account-configure))

(defun fn2-account-set-capacities (d profile fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-account-guard) (natp d))
                  :measure (nfix (- *fn2-account-nh* (nfix d)))))
  (if (or (not (natp d)) (>= d *fn2-account-nh*)) fn2-accounts
    (let* ((n (fn2-account-profile-capacity d profile))
           (fn2-accounts (update-fn2-accounts-capacityi d (if (unsigned-byte-p 32 n) n 0) fn2-accounts)))
      (fn2-account-set-capacities (+ 1 d) profile fn2-accounts))))
(defthm fn2-account-set-capacities-preserves
  (implies (fn2-account-guard)
           (let ((fn2-accounts (fn2-account-set-capacities d profile fn2-accounts))) (fn2-account-guard))))
(defthm fn2-account-set-capacities-rows
  (equal (nth *fn2-accounts-rows* (fn2-account-set-capacities d profile fn2-accounts)) (nth *fn2-accounts-rows* fn2-accounts)))
(defthm fn2-account-set-capacities-wfp
  (implies (fn2-accounts-wfp fn2-accounts) (fn2-accounts-wfp (fn2-account-set-capacities d profile fn2-accounts))))
(in-theory (disable fn2-account-set-capacities))
(defun fn2-account-set-committed (d fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-account-guard) (natp d))
                  :measure (nfix (- *fn2-account-nh* (nfix d)))))
  (if (or (not (natp d)) (>= d *fn2-account-nh*)) fn2-accounts
    (let* ((s (fn2-account-sum d 0 fn2-accounts))
           (fn2-accounts (update-fn2-accounts-committedi d (if (unsigned-byte-p 32 s) s 0) fn2-accounts)))
      (fn2-account-set-committed (+ 1 d) fn2-accounts))))
(defthm fn2-account-set-committed-preserves
  (implies (fn2-account-guard)
           (let ((fn2-accounts (fn2-account-set-committed d fn2-accounts))) (fn2-account-guard))))
(defthm fn2-account-set-committed-rows
  (equal (nth *fn2-accounts-rows* (fn2-account-set-committed d fn2-accounts)) (nth *fn2-accounts-rows* fn2-accounts)))
(defthm fn2-account-set-committed-wfp
  (implies (fn2-accounts-wfp fn2-accounts) (fn2-accounts-wfp (fn2-account-set-committed d fn2-accounts))))
(in-theory (disable fn2-account-set-committed))
(defun fn2-account-default-rows (row fn2-accounts)
  ;; slot 0 anonymous and the system row: every limit its capacity
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-account-guard) (natp row))))
  (let ((fn2-accounts (fn2-account-set-dims row 0 :default nil fn2-accounts)))
    (if (and (natp row) (< row (fn2-accounts-rows fn2-accounts)))
        (fn2-accounts-set-weight row 1 fn2-accounts) fn2-accounts)))
(defthm fn2-account-default-rows-preserves
  (implies (fn2-account-guard)
           (let ((fn2-accounts (fn2-account-default-rows row fn2-accounts))) (fn2-account-guard))))
(defthm fn2-account-default-rows-rows
  (equal (nth *fn2-accounts-rows* (fn2-account-default-rows row fn2-accounts)) (nth *fn2-accounts-rows* fn2-accounts)))
(defthm fn2-account-default-rows-wfp
  (implies (fn2-accounts-wfp fn2-accounts) (fn2-accounts-wfp (fn2-account-default-rows row fn2-accounts))))
(in-theory (disable fn2-account-default-rows))

(defun fn2-accounts-alloc (n fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-accountsp fn2-accounts) (natp n) (< n 4294967296))))
  (let* ((fn2-accounts (fn2-accounts-columns-init n fn2-accounts))
         (fn2-accounts (resize-fn2-accounts-limit (* *fn2-account-nh* n) fn2-accounts))
         (fn2-accounts (resize-fn2-accounts-reserve (* *fn2-account-nh* n) fn2-accounts))
         (fn2-accounts (resize-fn2-accounts-hold (* *fn2-account-nh* n) fn2-accounts))
         (fn2-accounts (resize-fn2-accounts-charge (* *fn2-account-nc* n) fn2-accounts))
         (fn2-accounts (resize-fn2-accounts-capacity *fn2-account-nh* fn2-accounts)))
    (resize-fn2-accounts-committed *fn2-account-nh* fn2-accounts)))
(defthm fn2-accounts-alloc-preserves
  (implies (and (fn2-accountsp fn2-accounts) (natp n) (< n 4294967296))
           (let ((fn2-accounts (fn2-accounts-alloc n fn2-accounts))) (fn2-account-guard)))
  :hints (("Goal" :in-theory (enable fn2-accounts-shapep))))
(defthm fn2-accounts-alloc-wfp
  (implies (and (natp n) (< n 4294967296)) (fn2-accounts-wfp (fn2-accounts-alloc n fn2-accounts))))
(defthm fn2-accounts-alloc-rows
  (implies (natp n) (equal (nth *fn2-accounts-rows* (fn2-accounts-alloc n fn2-accounts)) n)))
(in-theory (disable fn2-accounts-alloc))
(defthm fn2-accounts-profilep-rows
  (implies (fn2-accounts-profilep profile)
           (and (posp (fn2-profile-p profile)) (< (+ 1 (fn2-profile-p profile)) 4294967296)))
  :rule-classes (:rewrite :forward-chaining))
(in-theory (disable fn2-accounts-profilep))

(defun fn2-accounts-init (profile fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :guard (and (fn2-accountsp fn2-accounts) (fn2-accounts-profilep profile))))
  (let* ((p (nfix (fn2-profile-p profile)))
         (fn2-accounts (fn2-accounts-alloc (if (< (+ 1 p) 4294967296) (+ 1 p) 1) fn2-accounts))
         (fn2-accounts (fn2-account-set-capacities 0 profile fn2-accounts))
         (fn2-accounts (fn2-account-default-rows 0 fn2-accounts))
         (fn2-accounts (if (< 0 p) (fn2-accounts-set-state 0 *fn2-account-state-anonymous* fn2-accounts) fn2-accounts))
         (fn2-accounts (fn2-account-default-rows p fn2-accounts))
         (fn2-accounts (if (< p (fn2-accounts-rows fn2-accounts))
                           (fn2-accounts-set-state p *fn2-account-state-system* fn2-accounts) fn2-accounts))
         (fn2-accounts (fn2-account-configure (fn2-profile-get :accounts profile) p fn2-accounts)))
    (fn2-account-set-committed 0 fn2-accounts)))
(defthm fn2-accounts-init-preserves
  (implies (fn2-accountsp fn2-accounts)
           (let ((fn2-accounts (fn2-accounts-init profile fn2-accounts))) (fn2-account-guard))))
(defthm fn2-accounts-init-wfp
  (fn2-accounts-wfp (fn2-accounts-init profile fn2-accounts)))
(in-theory (disable fn2-accounts-init))

(defconst *fn2-account-system* :system)

(assert-event (fn2-assert-compliant-p
 '(fn2-accounts-shapep fn2-account-acquire fn2-account-release fn2-account-charge fn2-account-acquire2
   fn2-account-release2 fn2-account-attribute fn2-account-hold fn2-account-reserve fn2-account-limit
   fn2-account-charged fn2-account-committed fn2-account-capacity fn2-account-sum fn2-account-limits-ok
   fn2-account-dims-ok fn2-accounts-conservedp fn2-accounts-profilep fn2-accounts-init
   fn2-account-fits fn2-account-wait-head-of fn2-account-wait-tail-of fn2-account-request
   fn2-account-grant-scan fn2-account-grant-cursor fn2-account-grant-next fn2-account-principal-id
   fn2-account-rebind)
 (w state)))
