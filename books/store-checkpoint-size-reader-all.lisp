; Additive same-parse consumer-wrapper provenance.
; R=(configured-fold ORIGINALctx consumer-result topic).
; Fourth result is R child2 info, NOT configured-fold child0.
; Existing MV3 API remains unchanged. No allocation/cold authority is inferred.
(in-package "ACL2")
(include-book "store-checkpoint-size-reader")

(defun fn-sctsr-decode-programs-all (fa fb pa pb ea eb ra rb fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :guard (and (natp fa) (natp fb) (<= fa fb) (<= fb (fn-octets-len fn-octets))
                              (natp pa) (natp pb) (<= pa pb) (<= pb (fn-octets-len fn-octets))
                              (natp ea) (natp eb) (<= ea eb) (<= eb (fn-octets-len fn-octets))
                              (natp ra) (natp rb) (<= ra rb) (<= rb (fn-octets-len fn-octets)))))
  (let ((f (fn-sctr-decode-rows fa fb nil fn-octets)))
    (if (not (eq (car f) :ok)) (mv f nil nil nil)
      (let ((frows (cadr f)))
        (if (not (and (consp frows) (null (cdr frows)) (fn-sct-f-rowp (car frows))))
            (mv (list :refused :f-row) nil nil nil)
          (let* ((frow (car frows)) (s (cadr frow)))
            (mv-let (p pinfos) (fn-sctsr-decode-rows pa pb nil nil fn-octets)
              (if (not (eq (car p) :ok)) (mv p nil nil nil)
                (if (not (equal (len (cadr p)) s)) (mv (list :refused :close) nil nil nil)
                  (let* ((table (fn-cei-build (cadr p)))
                         (info-table (fn-scsr-info-index pinfos))
                         (e (fn-sctr-decode-rows ea eb table fn-octets)))
                    (if (not (eq (car e) :ok)) (mv e nil nil nil)
                      (if (not (equal (len (cadr e)) s)) (mv (list :refused :close) nil nil nil)
                        (mv-let (r rinfos) (fn-sctsr-decode-rows ra rb table info-table fn-octets)
                          (if (not (eq (car r) :ok)) (mv r nil nil nil)
                            (if (not (equal (len (cadr r)) 4)) (mv (list :refused :close) nil nil nil)
                              (mv (list :ok (list frow (cadr p) (cadr e) (cadr r)))
                                  (fn-scsr-car (fn-scsr-cdr rinfos))
                                  (list :summary-region ra rb :R 1)
                                  (fn-scsr-car (fn-scsr-cdr (fn-scsr-cdr rinfos)))))))))))))))))))

(local (defthm fn-sctsr-all-decode-rows-shape
 (and (true-listp (car (fn-sctsr-decode-rows start end table info-table fn-octets)))
      (implies (equal (car (car (fn-sctsr-decode-rows start end table info-table fn-octets))) :ok)
               (true-listp (cadr (car (fn-sctsr-decode-rows start end table info-table fn-octets))))))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (e/d (fn-sctsr-decode-rows)
                                (fn-sctsr-run fn-sctr-run))))))
(verify-guards fn-sctsr-decode-programs-all
 :hints (("Goal" :in-theory (disable fn-sctsr-decode-rows fn-sctr-decode-rows fn-cei-build))))


(defthm fn-sctsr-decode-programs-all-original-three-by-definition
 (and
   (equal (mv-nth 0 (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets))
          (mv-nth 0 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets)))
   (equal (mv-nth 1 (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets))
          (mv-nth 1 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets)))
   (equal (mv-nth 2 (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets))
          (mv-nth 2 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))))
 :hints (("Goal" :in-theory (e/d (fn-sctsr-decode-programs-all fn-sctsr-decode-programs)
                                (fn-sctsr-decode-rows fn-sctr-decode-rows fn-cei-build
                                 fn-scsr-info-index fn-sct-f-rowp)))))

(defun fn-sctsr-load-all (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let ((start (if (consp plan) (fn-sccr-at 1 (car plan)) 0)))
    (if (not (fn-sccr-planp plan start fn-octets))
        (mv (list :refused :layout) nil nil nil)
      (let ((h (and (consp plan) (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
        (if (not h) (mv (list :refused :header) nil nil nil)
          (let* ((s (nth 3 h)) (f (fn-sctr-next-run plan s fn-octets)))
            (if (not (eq (car f) :ok)) (mv f nil nil nil)
              (let ((p (fn-sctr-next-run (nth 3 f) s fn-octets)))
                (if (not (eq (car p) :ok)) (mv p nil nil nil)
                  (let ((e (fn-sctr-next-run (nth 3 p) s fn-octets)))
                    (if (not (eq (car e) :ok)) (mv e nil nil nil)
                      (let ((r (fn-sctr-next-run (nth 3 e) s fn-octets)))
                        (if (not (eq (car r) :ok)) (mv r nil nil nil)
                          (if (consp (nth 3 r)) (mv (list :refused :trailing) nil nil nil)
                            (mv-let (tables info region consumer-info)
                              (fn-sctsr-decode-programs-all
                               (nth 1 f) (nth 2 f) (nth 1 p) (nth 2 p)
                               (nth 1 e) (nth 2 e) (nth 1 r) (nth 2 r) fn-octets)
                              (if (not (eq (car tables) :ok)) (mv tables nil nil nil)
                                (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr tables))) s))
                                    (mv (list :refused :close) nil nil nil)
                                  (mv tables info region consumer-info)))))))))))))))))

)

(local (defthm fn-sctsr-all-planp-first-frame-for-guards
 (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
          (and (true-listp (car plan)) (consp (car plan))
               (fn-scc-octet-listp (car (car plan)))
               (fn-scc-octet-listp (fn-sccr-at 0 (car plan)))))
 :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))
          :in-theory (enable fn-sccr-framep)))))
(local (defthm fn-sctsr-all-programs-result-shape
 (and (true-listp (car (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets)))
      (implies (equal (car (car (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets))) :ok)
               (true-listp (cadr (car (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets))))))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (e/d (fn-sctsr-decode-programs-all fn-sctr-decode-rows)
                                (fn-sctsr-decode-rows fn-sctr-run fn-cei-build
                                 fn-scsr-info-index fn-sct-f-rowp))))))
(verify-guards fn-sctsr-load-all
 :hints (("Goal" :in-theory (disable fn-sctsr-decode-programs-all-original-three-by-definition fn-sctsr-decode-programs-all fn-sctr-next-run fn-sctr-restp
                                    fn-scc-parse-header fn-sccr-planp fn-sccr-framep))))

(defthm fn-sctsr-load-all-original-three-by-definition
 (and
   (equal (mv-nth 0 (fn-sctsr-load-all plan fn-octets))
          (mv-nth 0 (fn-sctsr-load plan fn-octets)))
   (equal (mv-nth 1 (fn-sctsr-load-all plan fn-octets))
          (mv-nth 1 (fn-sctsr-load plan fn-octets)))
   (equal (mv-nth 2 (fn-sctsr-load-all plan fn-octets))
          (mv-nth 2 (fn-sctsr-load plan fn-octets))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-sctsr-load-all fn-sctsr-load)
                                (fn-sctsr-decode-programs-all fn-sctsr-decode-programs
                                 fn-sctr-next-run fn-sccr-planp fn-scc-parse-header
                                 fn-sct-tables-f fn-sco-at)))))

(local (defthm fn-sctsr-all-nth-two-is-caddr
 (equal (nth 2 x) (car (cdr (cdr x))))
 :hints (("Goal" :expand ((nth 2 x) (nth 1 (cdr x)) (nth 0 (cdr (cdr x))))))))

(local (defun fn-sctsr-all-nth-provenance-ind (n infos rows)
 (declare (xargs :measure (nfix n)))
 (if (zp n) (list infos rows)
  (fn-sctsr-all-nth-provenance-ind (1- n) (cdr infos) (cdr rows)))))
(local (defthm fn-sctsr-all-stack-provenance-nth
 (implies (and (natp n) (fn-scsr-stack-provenancep infos rows))
          (fn-scsr-info-provenancep (nth n infos) (nth n rows)))
 :hints (("Goal" :induct (fn-sctsr-all-nth-provenance-ind n infos rows)
          :in-theory (e/d (fn-scsr-stack-provenancep fn-scsr-info-provenancep
                           fn-scsr-info-root nth)
                          (fn-scs-summary fn-scs-carryp))))) )

(defthm fn-sctsr-decode-programs-all-consumer-provenance
 (implies
  (and (fn-octets-p fn-octets)
       (natp fa) (natp fb) (<= fa fb) (<= fb (len fn-octets))
       (natp pa) (natp pb) (<= pa pb) (<= pb (len fn-octets))
       (natp ea) (natp eb) (<= ea eb) (<= eb (len fn-octets))
       (natp ra) (natp rb) (<= ra rb) (<= rb (len fn-octets))
       (equal (car (mv-nth 0 (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets))) :ok)
       (<= (fn-sco-at 1 (fn-sct-tables-f
            (cadr (mv-nth 0 (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets)))))
           (1+ *fn-cbor-max-uint*)))
  (fn-scsr-info-provenancep
   (mv-nth 3 (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets))
   (nth 2 (nth 3 (cadr (mv-nth 0 (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-sctsr-all-decode-rows-shape
                   (start pa) (end pb) (table nil) (info-table nil))
                (:instance fn-sctsr-decode-rows-preserves-partial-provenance
                  (start pa) (end pb) (rows nil) (row-infos nil) (table nil) (info-table nil))
                (:instance fn-sctsr-decode-rows-preserves-partial-provenance
                  (start ra) (end rb)
                  (rows (cadr (mv-nth 0 (fn-sctsr-decode-rows pa pb nil nil fn-octets))))
                  (row-infos (mv-nth 1 (fn-sctsr-decode-rows pa pb nil nil fn-octets)))
                  (table (fn-cei-build (cadr (mv-nth 0 (fn-sctsr-decode-rows pa pb nil nil fn-octets)))))
                  (info-table (fn-scsr-info-index (mv-nth 1 (fn-sctsr-decode-rows pa pb nil nil fn-octets)))))
                (:instance fn-sctsr-all-stack-provenance-nth
                  (n 2)
                  (infos (mv-nth 1
                    (fn-sctsr-decode-rows ra rb
                     (fn-cei-build (cadr (mv-nth 0 (fn-sctsr-decode-rows pa pb nil nil fn-octets))))
                     (fn-scsr-info-index (mv-nth 1 (fn-sctsr-decode-rows pa pb nil nil fn-octets))) fn-octets)))
                  (rows (cadr (mv-nth 0
                    (fn-sctsr-decode-rows ra rb
                     (fn-cei-build (cadr (mv-nth 0 (fn-sctsr-decode-rows pa pb nil nil fn-octets))))
                     (fn-scsr-info-index (mv-nth 1 (fn-sctsr-decode-rows pa pb nil nil fn-octets))) fn-octets))))))
          :in-theory (e/d (fn-sctsr-decode-programs-all fn-scsr-car fn-scsr-cdr fn-sco-at fn-sct-tables-f)
                          (fn-sctsr-decode-programs-all-original-three-by-definition fn-sctsr-decode-rows fn-sctr-decode-rows fn-cei-build
                           fn-sct-log-positionp fn-sctsr-all-decode-rows-shape
                           fn-scsr-info-index fn-scsr-stack-provenancep
                           fn-scsr-info-provenancep fn-sctsr-all-stack-provenance-nth
                            fn-cei-sequence-trie

                           )))))
