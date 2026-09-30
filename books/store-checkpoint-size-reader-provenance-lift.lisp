; Proof-only outer lift over the actual paired checkpoint loader.
(in-package "ACL2")
(include-book "store-checkpoint-size-reader-all")

(local (defthm fn-sctsr-program-mixed-provenance-rewrite
 (implies
  (and (fn-octets-p fn-octets)
       (natp fa) (natp fb) (<= fa fb) (<= fb (len fn-octets))
       (natp pa) (natp pb) (<= pa pb) (<= pb (len fn-octets))
       (natp ea) (natp eb) (<= ea eb) (<= eb (len fn-octets))
       (natp ra) (natp rb) (<= ra rb) (<= rb (len fn-octets))
       (equal (car (car (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))) :ok)
       (<= (fn-sco-at 1 (fn-sct-tables-f
            (cadr (car (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets)))))
           (1+ *fn-cbor-max-uint*)))
  (fn-scsr-info-provenancep
   (mv-nth 1 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))
   (cadr (nth 3 (cadr (car (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets)))))))

 :hints (("Goal" :use fn-sctsr-decode-programs-original-context-provenance))))

(defthm fn-sctsr-load-original-context-provenance
 (implies (and (fn-octets-p fn-octets)
               (equal (car (mv-nth 0 (fn-sctsr-load plan fn-octets))) :ok)
               (<= (fn-sco-at 1 (fn-sct-tables-f (cadr (mv-nth 0 (fn-sctsr-load plan fn-octets)))))
                   (1+ *fn-cbor-max-uint*)))
          (fn-scsr-info-provenancep
           (mv-nth 1 (fn-sctsr-load plan fn-octets))
           (cadr (nth 3 (cadr (mv-nth 0 (fn-sctsr-load plan fn-octets)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-sctsr-load fn-sctsr-program-mixed-provenance-rewrite
                           fn-sctr-next-run-ok-shape fn-sctr-restp-of-plan)
                          (fn-sctsr-decode-programs fn-sctr-decode-programs
                           fn-sctr-next-run fn-sctr-restp fn-sccr-planp fn-sccr-framep
                           fn-scc-parse-header fn-sco-at fn-sct-tables-f
                           fn-scsr-info-provenancep
)))))

(local (defthm fn-sctsr-all-program-mixed-consumer-provenance-rewrite
 (implies
  (and (fn-octets-p fn-octets)
       (natp fa) (natp fb) (<= fa fb) (<= fb (len fn-octets))
       (natp pa) (natp pb) (<= pa pb) (<= pb (len fn-octets))
       (natp ea) (natp eb) (<= ea eb) (<= eb (len fn-octets))
       (natp ra) (natp rb) (<= ra rb) (<= rb (len fn-octets))
       (equal (car (car (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets))) :ok)
       (<= (fn-sco-at 1 (fn-sct-tables-f
            (cadr (car (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets)))))
           (1+ *fn-cbor-max-uint*)))
  (fn-scsr-info-provenancep
   (mv-nth 3 (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets))
   (nth 2 (nth 3 (cadr (car (fn-sctsr-decode-programs-all fa fb pa pb ea eb ra rb fn-octets)))))))

 :hints (("Goal" :use fn-sctsr-decode-programs-all-consumer-provenance
 :in-theory (disable fn-sctsr-decode-programs-all-original-three-by-definition fn-sctsr-decode-programs-all fn-scsr-info-provenancep fn-sco-at fn-sct-tables-f)))))

(defthm fn-sctsr-load-all-consumer-provenance
 (implies (and (fn-octets-p fn-octets)
               (equal (car (mv-nth 0 (fn-sctsr-load-all plan fn-octets))) :ok)
               (<= (fn-sco-at 1 (fn-sct-tables-f (cadr (mv-nth 0 (fn-sctsr-load-all plan fn-octets)))))
                   (1+ *fn-cbor-max-uint*)))
          (fn-scsr-info-provenancep
           (mv-nth 3 (fn-sctsr-load-all plan fn-octets))
           (nth 2 (nth 3 (cadr (mv-nth 0 (fn-sctsr-load-all plan fn-octets)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-sctsr-load-all fn-sctsr-all-program-mixed-consumer-provenance-rewrite
                           fn-sctr-next-run-ok-shape fn-sctr-restp-of-plan)
                          (fn-sctsr-decode-programs-all-original-three-by-definition fn-sctsr-decode-programs-all fn-sctsr-decode-programs fn-sctr-decode-programs
                           fn-sctr-next-run fn-sctr-restp fn-sccr-planp fn-sccr-framep
                           fn-scc-parse-header fn-sco-at fn-sct-tables-f
                           fn-scsr-info-provenancep
)))))
