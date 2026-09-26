;; fn: the owner's two other per-POST caches, advanced through the Store's
;; derived event index (PRF-180, lane hot-path-scans-2, 2026-09-26).
;
; host/owner-host.lisp carries three (K . VALUE) caches over the committed
; history and consults each on every POST: the committed record octets
; (books/store-budget.lisp `fn-sbud-bytes-carried'), the completion debt
; (`fn-owner-record-debt', books/store-capacity-vector.lisp
; `fn-cvec-debt-extend') and the peer carriage usage (`fn-owner-carried-usage',
; books/peer-carriage.lisp `fn-pcb-usage-extend').  The reference extensions
; take `len' of the history and step `nthcdr' down it to reach record K: two
; walks of every committed record per query.  The functions below reach the
; records K .. count-1 through the index instead (`fn-cei-get', a fixed-depth
; lookup) and take the count from it (`fn-sbud-count'), so a query costs one
; lookup and one fold step per record committed since the last one.
;
; The maintained relation is `fn-ceis-indexedp' (the index is the index of
; the committed history), established at every host-called open and
; preserved by every owner transition the host installs, with no hypothesis
; (books/owner-store-indexed.lisp `fn-osi-live-owner-store-is-indexed');
; a count past the index's uint32 sequence space (which no well-formed kernel
; reaches) takes the reference fold.  Under the relation each carried figure
; is its reference extension, and so the fold itself.
(in-package "ACL2")
(include-book "store-budget")
(include-book "store-capacity-vector")
(include-book "peer-carriage")

(local (in-theory (disable fn-store-event-encode fn-cei-get
                           fn-cei-correspondencep)))

(local
 (defthm fn-scf-nthcdr-step
   (implies (and (natp k) (< k (len xs)))
            (equal (nthcdr k xs) (cons (nth k xs) (nthcdr (1+ k) xs))))
   :hints (("Goal" :induct (nthcdr k xs) :in-theory (enable nthcdr nth)))))

(local
 (defthm fn-scf-nthcdr-of-len-is-an-atom
   (implies (and (natp k) (<= (len xs) k))
            (not (consp (nthcdr k xs))))
   :hints (("Goal" :induct (nthcdr k xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-scf-debt-from-of-atom
   (implies (not (consp x))
            (equal (fn-cvec-debt-from d x) (nfix d)))
   :hints (("Goal" :in-theory (enable fn-cvec-debt-from)))))

(local
 (defthm fn-scf-tally-records-of-atom
   (implies (not (consp x))
            (equal (fn-pcb-tally-records x tally) tally))
   :hints (("Goal" :in-theory (enable fn-pcb-tally-records)))))

; -----------------------------------------------------------------------------
; The completion debt

(defun fn-scf-debt-advance (k count debt index)
  (declare (xargs :guard (and (natp k) (natp count))
                  :measure (nfix (- (nfix count) (nfix k)))))
  (if (and (natp k) (natp count) (< k count))
      (fn-scf-debt-advance
       (1+ k) count
       (fn-cvec-debt-step (fn-store-event-kind (fn-cei-get k index)) debt)
       index)
    (nfix debt)))

(defthm fn-scf-debt-advance-is-the-suffix-fold
  (implies (and (fn-cei-correspondencep index events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (natp k) (<= k (len events)))
           (equal (fn-scf-debt-advance k (len events) debt index)
                  (fn-cvec-debt-from debt (nthcdr k events))))
  :hints (("Goal" :induct (fn-scf-debt-advance k (len events) debt index)
           :in-theory (e/d (fn-scf-debt-advance)
                           (fn-cvec-debt-step fn-store-event-kind)))))

; The completion debt of S from the carried CACHE = (K . DEBT).
(defun fn-scf-debt-carried (cache s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((count (fn-sbud-count s)))
    (if (and (consp cache) (natp (car cache)) (natp (cdr cache))
             (<= (car cache) count)
             (<= count (1+ *fn-cbor-max-uint*)))
        (fn-scf-debt-advance (car cache) count (cdr cache)
                             (fn-sn-event-index s))
      (fn-cvec-record-debt (fn-sf-records (fn-sn-files s))))))

; KEYSTONE (the carried debt).  Under the maintained relation, from a cache that is the debt of a prefix of the
; committed records, the carried debt is the history's completion debt.
(defthm fn-scf-debt-carried-is-the-record-debt
  (implies (and (fn-ceis-indexedp s)
                (fn-cvec-debt-cache-validp cache (fn-sf-records (fn-sn-files s))))
           (equal (fn-scf-debt-carried cache s)
                  (fn-cvec-record-debt (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :use (fn-sbud-count-is-used
                        (:instance fn-scf-debt-advance-is-the-suffix-fold
                                   (index (fn-sn-event-index s))
                                   (events (fn-sf-records (fn-sn-files s)))
                                   (k (car cache)) (debt (cdr cache)))
                        (:instance fn-cvec-debt-extend-is-the-record-debt
                                   (records (fn-sf-records (fn-sn-files s)))))
           :in-theory (e/d (fn-scf-debt-carried fn-cvec-debt-cache-validp
                            fn-cvec-debt-extend fn-ceis-indexedp fn-sbud-used)
                           (fn-scf-debt-advance fn-cvec-debt-from
                            fn-cvec-record-debt fn-sbud-count fn-sbud-count-is-used
                            fn-scf-debt-advance-is-the-suffix-fold
                            fn-cvec-debt-extend-is-the-record-debt
                            take nthcdr)))))

; -----------------------------------------------------------------------------
; The peer carriage usage

(defun fn-scf-tally-step (record tally)
  (declare (xargs :guard t))
  (let ((c (fn-pcb-event-carriage record)))
    (if (consp c)
        (fn-pcb-tally-put (car c)
                          (fn-pcb-usage-plus (fn-pcb-tally-get (car c) tally)
                                             (cdr c))
                          tally)
      tally)))

(local
 (defthm fn-scf-tally-records-of-cons
   (equal (fn-pcb-tally-records (cons record rest) tally)
          (fn-pcb-tally-records rest (fn-scf-tally-step record tally)))
   :hints (("Goal" :in-theory (enable fn-pcb-tally-records)))))

(defun fn-scf-tally-advance (k count tally index)
  (declare (xargs :guard (and (natp k) (natp count))
                  :measure (nfix (- (nfix count) (nfix k)))))
  (if (and (natp k) (natp count) (< k count))
      (fn-scf-tally-advance (1+ k) count
                            (fn-scf-tally-step (fn-cei-get k index) tally)
                            index)
    tally))

(defthm fn-scf-tally-advance-is-the-suffix-fold
  (implies (and (fn-cei-correspondencep index events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (natp k) (<= k (len events)))
           (equal (fn-scf-tally-advance k (len events) tally index)
                  (fn-pcb-tally-records (nthcdr k events) tally)))
  :hints (("Goal" :induct (fn-scf-tally-advance k (len events) tally index)
           :in-theory (e/d (fn-scf-tally-advance)
                           (fn-scf-tally-step fn-pcb-tally-records)))))

(local
 (defthm fn-scf-pcb-drop-is-nthcdr
   (implies (natp k) (equal (fn-pcb-drop k records) (nthcdr k records)))
   :hints (("Goal" :in-theory (enable fn-pcb-drop nthcdr)))))

; The peer carriage tally of S from the carried CACHE = (K . TALLY).
(defun fn-scf-usage-carried (cache s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((count (fn-sbud-count s)))
    (if (and (consp cache) (natp (car cache)) (<= (car cache) count)
             (<= count (1+ *fn-cbor-max-uint*)))
        (fn-scf-tally-advance (car cache) count (cdr cache)
                              (fn-sn-event-index s))
      (fn-pcb-tally-records (fn-sf-records (fn-sn-files s)) nil))))

; Within the index's sequence space the carried tally is the reference
; extension itself.
(defthm fn-scf-usage-carried-is-usage-extend
  (implies (and (fn-ceis-indexedp s)
                (<= (len (fn-sf-records (fn-sn-files s))) (1+ *fn-cbor-max-uint*))
                (fn-pcb-cache-validp cache (fn-sf-records (fn-sn-files s))))
           (equal (fn-scf-usage-carried cache s)
                  (fn-pcb-usage-extend cache (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :use (fn-sbud-count-is-used
                        (:instance fn-scf-tally-advance-is-the-suffix-fold
                                   (index (fn-sn-event-index s))
                                   (events (fn-sf-records (fn-sn-files s)))
                                   (k (car cache)) (tally (cdr cache))))
           :in-theory (e/d (fn-scf-usage-carried fn-pcb-cache-validp
                            fn-pcb-usage-extend fn-ceis-indexedp fn-sbud-used)
                           (fn-scf-tally-advance fn-pcb-tally-records
                            fn-sbud-count fn-sbud-count-is-used
                            fn-scf-tally-advance-is-the-suffix-fold
                            take nthcdr)))))

(local
 (defthm fn-scf-usage-is-a-pair
   (equal (cons (car (fn-pcb-usage records evidence))
                (cdr (fn-pcb-usage records evidence)))
          (fn-pcb-usage records evidence))))

; KEYSTONE (the carried usage).  Under the maintained relation, from a cache
; that is the tally of a prefix of the committed records, the carried usage
; read at EVIDENCE is the replay projection `fn-pcb-usage' of the history.
(defthm fn-scf-usage-carried-is-the-projection
  (implies (and (fn-ceis-indexedp s)
                (fn-pcb-cache-validp cache (fn-sf-records (fn-sn-files s))))
           (equal (fn-pcb-tally-get evidence (fn-scf-usage-carried cache s))
                  (fn-pcb-usage (fn-sf-records (fn-sn-files s)) evidence)))
  :hints (("Goal" :cases ((<= (len (fn-sf-records (fn-sn-files s)))
                              (1+ *fn-cbor-max-uint*))))
          ("Subgoal 2"
           :use (fn-sbud-count-is-used
                 (:instance fn-pcb-tally-records-get
                            (records (fn-sf-records (fn-sn-files s)))
                            (tally nil)))
           :in-theory (e/d (fn-scf-usage-carried fn-sbud-used)
                           (fn-pcb-tally-records fn-pcb-usage fn-sbud-count
                            fn-sbud-count-is-used fn-pcb-tally-records-get
                            fn-pcb-cache-validp fn-ceis-indexedp)))
          ("Subgoal 1"
           :use (fn-scf-usage-carried-is-usage-extend
                 (:instance fn-pcb-carried-usage-is-the-projection
                            (records (fn-sf-records (fn-sn-files s)))))
           :in-theory (disable fn-scf-usage-carried fn-pcb-usage-extend
                               fn-pcb-cache-validp fn-ceis-indexedp
                               fn-pcb-tally-get fn-pcb-usage
                               fn-scf-usage-carried-is-usage-extend
                               fn-pcb-carried-usage-is-the-projection))))

(in-theory (disable fn-scf-debt-advance fn-scf-debt-carried fn-scf-tally-step
                    fn-scf-tally-advance fn-scf-usage-carried))
