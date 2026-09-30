; Actual canonical image controller capture/authority/effect safety.
; Whole canonical byte-trace fidelity and productive progress remain open.
; Pure proof observers below model captured fields; host calls fn-hpi-tick/offer.
(in-package "ACL2")
(include-book "history-image-producer")
(include-book "history-cold-runtime-status")

(defun fn-hpiv-capture (c)
 (declare (xargs :guard t))
 (list (fn-omk-at 1 c) (fn-omk-at 2 c) (fn-omk-at 3 c)
       (fn-omk-at 6 c) (fn-omk-at 7 c) (fn-omk-at 8 c)
       (fn-omk-at 9 c) (fn-omk-at 10 c) (fn-omk-at 11 c)
       (fn-omk-at 12 c) (fn-omk-at 13 c)))

(local
 (defun fn-hpiv-field-ind (j k c)
  (if (or (zp j) (zp k)) (list j k c)
    (fn-hpiv-field-ind (1- j) (1- k) (if (consp c) (cdr c) nil)))))

(local
 (defthm fn-hpiv-set-field
  (implies (and (natp k) (< k 25) (natp j) (< j 25))
   (equal (fn-omk-at j (fn-hpi-set k value c))
          (if (equal j k) value (fn-omk-at j c))))
  :hints (("Goal" :induct (fn-hpiv-field-ind j k c)
           :expand ((fn-hpi-set k value c)
                    (fn-omk-at j c)
                    (fn-omk-at j (fn-hpi-set k value c))
                    (:free (a d) (fn-omk-at j (cons a d))))
           :in-theory (e/d (fn-omk-at fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))

(local
 (defthm fn-hpiv-update-preserves-capture
  (implies (member-equal index '(0 4 5 14 15 16 17 18 19 20 21 22 23 24))
   (equal (fn-hpiv-capture (fn-hpi-set index value c)) (fn-hpiv-capture c)))
  :hints (("Goal" :in-theory (e/d (fn-hpiv-capture) (fn-hpi-set-is-update-by-definition))))))

(in-theory (disable fn-hpiv-capture))

(local (defthm fn-hpi-await-page-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 2 (fn-hpi-await-page region logical physical buffer resume c))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-page) (fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-await-region-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 2 (fn-hpi-await-region region resume c))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-region) (fn-hpi-await-page fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-offer-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 1 (fn-hpi-offer c ordinal source token key))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-offer) (fn-hpi-await-page fn-hpi-await-region fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-written-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 1 (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-written) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-supply-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 1 (fn-hpi-supply c position byte fn-hpb))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-supply) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-issue-io-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 2 (fn-hpi-issue-io tag kind ordinal offset length bytes wait c))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-issue-io) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-digest-begin-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 1 (fn-hpi-digest-begin kind index c pgs-digest-state))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-digest-begin) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-meta-begin-capture-frame-by-definition
 (equal (fn-hpiv-capture (fn-hpi-meta-begin kind page c)) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-meta-begin) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-after-spool-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 1 (fn-hpi-after-spool c pgs-digest-state))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-after-spool) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-metadata-step-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 2 (fn-hpi-metadata-step c fn-hpb))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-metadata-step) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-stream-step-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 2 (fn-hpi-stream-step c observation fn-hpb pgs-digest-state))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-stream-step) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-buffer-step-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 2 (fn-hpi-buffer-step c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-buffer-step) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(defthm fn-hpi-tick-capture-frame-by-definition
 (equal (fn-hpiv-capture (mv-nth 2 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))) (fn-hpiv-capture c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-tick) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpiv-capture fn-hpi-set fn-hpi-set-is-update-by-definition)))))

(local (defthm fn-hpi-await-page-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 2 (fn-hpi-await-page region logical physical buffer resume c))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-page) (fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-await-region-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 2 (fn-hpi-await-region region resume c))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-region) (fn-hpi-await-page fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-offer-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 1 (fn-hpi-offer c ordinal source token key))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-offer) (fn-hpi-await-page fn-hpi-await-region fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-written-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 1 (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-written) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-supply-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 1 (fn-hpi-supply c position byte fn-hpb))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-supply) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-issue-io-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 2 (fn-hpi-issue-io tag kind ordinal offset length bytes wait c))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-issue-io) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-digest-begin-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 1 (fn-hpi-digest-begin kind index c pgs-digest-state))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-digest-begin) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-meta-begin-receipt-frame
 (equal (fn-omk-at 22 (fn-hpi-meta-begin kind page c)) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-meta-begin) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-after-spool-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 1 (fn-hpi-after-spool c pgs-digest-state))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-after-spool) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-metadata-step-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 2 (fn-hpi-metadata-step c fn-hpb))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-metadata-step) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-stream-step-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 2 (fn-hpi-stream-step c observation fn-hpb pgs-digest-state))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-stream-step) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-buffer-step-receipt-frame
 (equal (fn-omk-at 22 (mv-nth 2 (fn-hpi-buffer-step c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-omk-at 22 c))
 :hints (("Goal" :in-theory (e/d (fn-hpi-buffer-step) (fn-hpi-await-page fn-hpi-await-region fn-hpi-offer fn-hpi-written fn-hpi-supply fn-hpi-issue-io fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-metadata-step fn-hpi-stream-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local
 (defthm fn-hpiv-same-capture-and-receipt-live
  (implies (and (equal (fn-hpiv-capture a) (fn-hpiv-capture b))
                (equal (fn-omk-at 22 a) (fn-omk-at 22 b)))
   (equal (fn-hpi-grant-matchesp a ledger) (fn-hpi-grant-matchesp b ledger)))
  :hints (("Goal" :in-theory (e/d (fn-hpiv-capture fn-hpi-grant-matchesp fn-hpi-growth-request)
                                 (fn-osj-native-grant-livep fn-omk-at))))))

(local
 (defthm fn-hpi-nongrowth-retains-receipt-and-ledger
  (implies (not (equal (fn-omk-at 0 c) :need-growth))
   (and (equal (fn-omk-at 22 (mv-nth 2 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
               (fn-omk-at 22 c))
        (equal (mv-nth 3 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)) ledger)))
  :hints (("Goal" :in-theory (e/d (fn-hpi-tick)
   (fn-hpi-written fn-hpi-buffer-step fn-hpi-supply fn-hpi-stream-step fn-hpi-grant-matchesp fn-osj-native-grow fn-hpi-reset-buffer fn-hpi-growth-request fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

(defthm fn-hpi-nongrowth-step-keeps-live-write-authority
 (implies (and (fn-hpi-grant-matchesp c ledger)
               (not (equal (fn-omk-at 0 c) :need-growth)))
  (let* ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
         (next (mv-nth 2 r)) (next-ledger (mv-nth 3 r)))
   (and (equal (fn-hpiv-capture next) (fn-hpiv-capture c))
        (equal next-ledger ledger)
        (equal (fn-omk-at 22 next) (fn-omk-at 22 c))
        (fn-hpi-grant-matchesp next next-ledger))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-hpiv-same-capture-and-receipt-live
                 (a (mv-nth 2 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
                 (b c)))
           :in-theory (disable fn-hpi-tick fn-hpi-grant-matchesp fn-hpiv-capture fn-omk-at))))

(local
 (defthm fn-hpiv-at-zero-by-definition
  (equal (fn-omk-at 0 x) (car x))
  :hints (("Goal" :in-theory (enable fn-omk-at)))))

(local
 (defthm fn-hpiv-native-growth-exact-request
  (implies (equal (fn-omk-at 0 (mv-nth 0 (fn-osj-native-grow ledger maintenance source stage request))) :checkpoint-funded)
   (and (consp request)
        (equal (mv-nth 0 (fn-osj-native-grow ledger maintenance source stage request))
               (cons :checkpoint-funded (cdr request)))))
  :rule-classes nil
  :hints (("Goal" :use fn-osj-grown-authority-matches-exact-request
           :in-theory (e/d (fn-osj-native-grow fn-omk-at fn-osj-growth-requestp)
                        (fn-osj-grow fn-osj-native-backingp))))))

(local
 (defthm fn-hpiv-native-growth-is-tagged
  (consp (mv-nth 0 (fn-osj-native-grow ledger maintenance source stage request)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-osj-native-grow fn-osj-grow)
    (fn-osj-native-backingp fn-osj-growth-requestp fn-pmn-grow fn-osj-growth-disk fn-osj-keep-grant fn-prl-binding fn-prl-nth fn-prs-vectorp))))))

(local
 (defthm fn-hpi-growth-success-establishes-live-authority
  (let* ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
         (next (mv-nth 2 r)) (next-ledger (mv-nth 3 r)))
   (implies (and (equal (fn-omk-at 0 c) :need-growth) (equal (mv-nth 0 r) :funded))
     (fn-hpi-grant-matchesp next next-ledger)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hpiv-native-growth-is-tagged
                (maintenance (fn-omk-at 2 c)) (source (fn-omk-at 1 c))
                (stage (fn-omk-at 3 c)) (request (fn-hpi-growth-request c)))
               (:instance fn-osj-native-grown-authority-is-live
                (maintenance (fn-omk-at 2 c)) (source (fn-omk-at 1 c))
                (stage (fn-omk-at 3 c)) (request (fn-hpi-growth-request c)))
               (:instance fn-hpiv-native-growth-exact-request
                (maintenance (fn-omk-at 2 c)) (source (fn-omk-at 1 c))
                (stage (fn-omk-at 3 c)) (request (fn-hpi-growth-request c))))
           :in-theory (e/d (fn-hpi-tick fn-hpi-grant-matchesp fn-hpi-growth-request)
             (fn-hpi-written fn-hpi-buffer-step fn-hpi-supply fn-hpi-stream-step
              fn-osj-native-grow fn-osj-native-grant-livep fn-hpi-reset-buffer
              fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

; Initial growth and every admitted retained step share ONE actual authority
; boundary. An unsuccessful initial allocation supplies no write authority.
(defthm fn-hpi-step-carries-captured-stage-authority
 (let* ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
        (next (mv-nth 2 r)) (next-ledger (mv-nth 3 r)))
  (implies (or (and (fn-hpi-grant-matchesp c ledger)
                    (not (equal (fn-omk-at 0 c) :need-growth)))
               (and (equal (fn-omk-at 0 c) :need-growth)
                    (equal (mv-nth 0 r) :funded)))
   (and (equal (fn-hpiv-capture next) (fn-hpiv-capture c))
        (fn-hpi-grant-matchesp next next-ledger)
        (implies (not (equal (fn-omk-at 0 c) :need-growth))
         (and (equal next-ledger ledger)
              (equal (fn-omk-at 22 next) (fn-omk-at 22 c)))))))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpi-nongrowth-step-keeps-live-write-authority
                       fn-hpi-growth-success-establishes-live-authority)
          :in-theory (disable fn-hpi-tick fn-hpi-grant-matchesp fn-hpiv-capture fn-omk-at))))

; A matching uncertain write cannot reset a selected buffer or clear its
; outstanding effect. This is the whole controller's actual ten-output MV.
(defthm fn-hpi-uncertain-page-write-retains-all-state
 (implies (and (fn-omk-widthp c 25)
               (equal (fn-omk-at 0 c) :wait-write)
               (fn-hpi-grant-matchesp c ledger)
               (equal (fn-hpi-written-status (fn-omk-at 5 c) observation) :recovery-required))
  (equal (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
         (list :recovery-required nil (fn-hpi-set 0 :recovery-required c) ledger
               fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-hpi-tick fn-hpi-written)
                 (fn-hpi-grant-matchesp fn-hpi-written-status fn-hpi-reset-buffer
                  fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition)))))

(defun fn-hpiv-io-effectp (effect)
 (declare (xargs :guard t))
 (member-eq (fn-omk-at 0 effect) '(:write-page :read-stage :write-spool :read-spool)))

(defun fn-hpiv-issued-effectp (next effect)
 (declare (xargs :guard t))
 (and (fn-omk-widthp effect 10)
      (equal (fn-omk-at 5 next) effect)
      (equal (fn-omk-at 1 effect) (fn-omk-at 1 next))
      (equal (fn-omk-at 2 effect) (fn-omk-at 3 next))
      (natp (fn-omk-at 3 effect))
      (equal (fn-omk-at 4 next) (+ 1 (fn-omk-at 3 effect)))))

(local (defthm fn-hpi-await-page-output-is-exact-issued-effect
 (let ((r (fn-hpi-await-page region logical physical buffer resume c)))
  (implies (and (member-eq (mv-nth 0 r) (quote (:write :io)))
                (fn-hpiv-io-effectp (mv-nth 1 r)))
   (fn-hpiv-issued-effectp (mv-nth 2 r) (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-page fn-omk-at fn-omk-widthp fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-write-effect) (fn-hpi-await-region fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-written fn-hpi-supply fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-await-region-output-is-exact-issued-effect
 (let ((r (fn-hpi-await-region region resume c)))
  (implies (and (member-eq (mv-nth 0 r) (quote (:write :io)))
                (fn-hpiv-io-effectp (mv-nth 1 r)))
   (fn-hpiv-issued-effectp (mv-nth 2 r) (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-region) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-issue-io-output-is-exact-issued-effect
 (let ((r (fn-hpi-issue-io tag kind ordinal offset length bytes wait c)))
  (implies (and (member-eq (mv-nth 0 r) (quote (:write :io)))
                (fn-hpiv-io-effectp (mv-nth 1 r)))
   (fn-hpiv-issued-effectp (mv-nth 2 r) (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-issue-io fn-omk-at fn-omk-widthp fn-hpiv-io-effectp fn-hpiv-issued-effectp) (fn-hpi-await-page fn-hpi-await-region fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-metadata-step-output-is-exact-issued-effect
 (let ((r (fn-hpi-metadata-step c fn-hpb)))
  (implies (and (member-eq (mv-nth 0 r) (quote (:write :io)))
                (fn-hpiv-io-effectp (mv-nth 1 r)))
   (fn-hpiv-issued-effectp (mv-nth 2 r) (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-metadata-step) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-await-region fn-hpi-issue-io fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-stream-step-output-is-exact-issued-effect
 (let ((r (fn-hpi-stream-step c observation fn-hpb pgs-digest-state)))
  (implies (and (member-eq (mv-nth 0 r) (quote (:write :io)))
                (fn-hpiv-io-effectp (mv-nth 1 r)))
   (fn-hpiv-issued-effectp (mv-nth 2 r) (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-stream-step) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-await-region fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-buffer-step-output-is-exact-issued-effect
 (let ((r (fn-hpi-buffer-step c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (member-eq (mv-nth 0 r) (quote (:write :io)))
                (fn-hpiv-io-effectp (mv-nth 1 r)))
   (fn-hpiv-issued-effectp (mv-nth 2 r) (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-buffer-step) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-await-region fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-tick-io-output-is-exact-issued-effect
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (member-eq (mv-nth 0 r) (quote (:write :io)))
                (fn-hpiv-io-effectp (mv-nth 1 r)))
   (fn-hpiv-issued-effectp (mv-nth 2 r) (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-tick) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-await-region fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition)))))
)

(local (defthm fn-hpi-await-page-output-has-io-tag
 (let ((r (fn-hpi-await-page region logical physical buffer resume c)))
  (implies (member-eq (mv-nth 0 r) (quote (:write :io)))
   (fn-hpiv-io-effectp (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-page fn-omk-at fn-omk-widthp fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-write-effect) (fn-hpi-await-region fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-written fn-hpi-supply fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-await-region-output-has-io-tag
 (let ((r (fn-hpi-await-region region resume c)))
  (implies (member-eq (mv-nth 0 r) (quote (:write :io)))
   (fn-hpiv-io-effectp (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-region) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-issue-io-output-has-io-tag
 (let ((r (fn-hpi-issue-io tag kind ordinal offset length bytes wait c)))
  (implies (and (member-eq (mv-nth 0 r) (quote (:write :io)))
                (fn-hpiv-io-effectp (list tag)))
   (fn-hpiv-io-effectp (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-issue-io fn-omk-at fn-omk-widthp fn-hpiv-io-effectp fn-hpiv-issued-effectp) (fn-hpi-await-page fn-hpi-await-region fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-metadata-step-output-has-io-tag
 (let ((r (fn-hpi-metadata-step c fn-hpb)))
  (implies (member-eq (mv-nth 0 r) (quote (:write :io)))
   (fn-hpiv-io-effectp (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-metadata-step) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-await-region fn-hpi-issue-io fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-digest-begin-never-issues-io
 (and (not (equal (car (fn-hpi-digest-begin kind index c pgs-digest-state)) :write))
      (not (equal (car (fn-hpi-digest-begin kind index c pgs-digest-state)) :io)))
 :hints (("Goal" :in-theory (e/d (fn-hpi-digest-begin) (pgs-dcb-begin fn-hpi-set fn-omk-at))))))

(local (defthm fn-hpi-after-spool-never-issues-io
 (and (not (equal (car (fn-hpi-after-spool c pgs-digest-state)) :write))
      (not (equal (car (fn-hpi-after-spool c pgs-digest-state)) :io)))
 :hints (("Goal" :in-theory (e/d (fn-hpi-after-spool) (fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-set fn-omk-at))))))

(local (defthm fn-hpi-io-matchp-never-operation-word
 (implies (fn-hpi-io-matchp c observation tag width)
  (and (not (equal (fn-omk-at 7 observation) :write))
       (not (equal (fn-omk-at 7 observation) :io))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-io-matchp)
                     (fn-omk-at fn-omk-widthp fn-omk-token-matchp))))))

(local (defthm fn-hpi-stream-step-output-has-io-tag
 (let ((r (fn-hpi-stream-step c observation fn-hpb pgs-digest-state)))
  (implies (member-eq (mv-nth 0 r) (quote (:write :io)))
   (fn-hpiv-io-effectp (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-stream-step) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-await-region fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-buffer-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpcx-tick-never-issues-image-io
 (and (not (equal (car (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :write))
      (not (equal (car (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :io)))
 :hints (("Goal" :in-theory (e/d (fn-hpcx-tick fn-hsrcb-demandp)
   (fn-hpcx-shapep fn-hpcx-with fn-hpe-tick fn-hcc-row fn-hcl-cell fn-hpq-put
    fn-hrcur-widthp fn-hrcur-field))))))

(local (defthm fn-hpi-buffer-step-output-has-io-tag
 (let ((r (fn-hpi-buffer-step c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (member-eq (mv-nth 0 r) (quote (:write :io)))
   (fn-hpiv-io-effectp (mv-nth 1 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-buffer-step) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-await-region fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-tick fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpi-written-never-issues-io
 (and (not (equal (car (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :write))
      (not (equal (car (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :io)))
 :hints (("Goal" :in-theory (e/d (fn-hpi-written fn-hpi-written-status)
    (fn-hpi-reset-buffer fn-hpi-set fn-omk-at fn-omk-widthp fn-omk-token-matchp
     fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hsrcb-supply-never-issues-image-io
 (and (not (equal (car (fn-hsrcb-supply c position byte)) :write))
      (not (equal (car (fn-hsrcb-supply c position byte)) :io)))
 :hints (("Goal" :in-theory (e/d (fn-hsrcb-supply) (fn-hsrcb-coldp fn-hsrcb-tick fn-hsrcb-demandp fn-hrcur-cold-supply fn-hrcur-field))))))

(local (defthm fn-hpe-supply-never-issues-image-io
 (and (not (equal (car (fn-hpe-supply c position byte fn-hpb)) :write))
      (not (equal (car (fn-hpe-supply c position byte fn-hpb)) :io)))
 :hints (("Goal" :in-theory (e/d (fn-hpe-supply) (fn-hpe-shapep fn-hpb-ready fn-hsrcb-supply fn-hrcur-word-push fn-hpb-put fn-hrcur-field fn-scc-octetp))))))

(local (defthm fn-hpcx-supply-never-issues-image-io
 (and (not (equal (car (fn-hpcx-supply c position byte fn-hpb)) :write))
      (not (equal (car (fn-hpcx-supply c position byte fn-hpb)) :io)))
 :hints (("Goal" :in-theory (e/d (fn-hpcx-supply) (fn-hpcx-shapep fn-hpcx-with fn-hpe-supply fn-hrcur-field))))))

(local (defthm fn-hpi-supply-never-issues-image-io
 (and (not (equal (car (fn-hpi-supply c position byte fn-hpb)) :write))
      (not (equal (car (fn-hpi-supply c position byte fn-hpb)) :io)))
 :hints (("Goal" :in-theory (e/d (fn-hpi-supply) (fn-hpcx-supply fn-hpi-set fn-omk-at))))))

(local (defthm fn-hpi-tick-output-has-io-tag
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (member-eq (mv-nth 0 r) (quote (:write :io)))
   (fn-hpiv-io-effectp (mv-nth 1 r))))
 :hints (("Goal" :use ((:instance fn-hpiv-native-growth-is-tagged
                (maintenance (fn-omk-at 2 c)) (source (fn-omk-at 1 c))
                (stage (fn-omk-at 3 c)) (request (fn-hpi-growth-request c))))
          :in-theory (e/d (fn-hpi-tick) (fn-hpiv-io-effectp fn-hpiv-issued-effectp fn-hpi-await-page fn-hpi-await-region fn-hpi-issue-io fn-hpi-metadata-step fn-hpi-stream-step fn-hpi-buffer-step fn-hpcx-tick fn-hpcx-supply fn-hpcx-offer fn-hpq-put fn-hpb-put fn-hpi-reset-buffer fn-hch-tick fn-hpm-tick pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets fn-hpir-root fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-io-matchp fn-hpi-octets-p fn-hpi-digest-validp fn-osj-native-grow fn-hpi-written-status fn-hpi-region-cap fn-hpi-region-start fn-hpi-region-used fn-hpi-digest-begin fn-hpi-meta-begin fn-hpi-after-spool fn-hpi-write-effect fn-hpi-written fn-hpi-supply fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition)))))
)

; Operation status itself establishes the effect tag; no caller premise
; about a returned effect's type is needed.
(defthm fn-hpi-tick-output-is-exact-issued-effect
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (member-eq (mv-nth 0 r) '(:write :io))
   (and (fn-hpiv-io-effectp (mv-nth 1 r))
        (fn-hpiv-issued-effectp (mv-nth 2 r) (mv-nth 1 r)))))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpi-tick-output-has-io-tag fn-hpi-tick-io-output-is-exact-issued-effect)
                 :in-theory (disable fn-hpi-tick fn-hpiv-io-effectp fn-hpiv-issued-effectp))))

(defthm fn-hpi-uncertain-stream-io-retains-all-state
 (implies (and (fn-omk-widthp c 25)
               (member-eq (fn-omk-at 0 c) '(:wait-stage-read :wait-spool-read :wait-spool-write))
               (fn-hpi-grant-matchesp c ledger)
               (fn-hpi-io-matchp c observation
                 (case (fn-omk-at 0 c) (:wait-stage-read :image-read)
                                      (:wait-spool-read :spool-read)
                                      (otherwise :spool-written))
                 (if (equal (fn-omk-at 0 c) :wait-spool-write) 8 9))
               (equal (fn-omk-at 7 observation) :uncertain))
  (equal (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
         (list :uncertain nil (fn-hpi-set 0 :recovery-required c) ledger
               fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-hpi-tick fn-hpi-stream-step)
                 (fn-hpi-grant-matchesp fn-hpi-io-matchp fn-hpi-reset-buffer
                  fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition
                  fn-hpi-digest-validp fn-hpi-octets-p fn-hpi-metadata-step
                  fn-hpi-after-spool fn-hpi-digest-begin fn-hpi-meta-begin
                  pgs-dcb-step pgs-dcb-result-octets fn-hpir-root)))))
