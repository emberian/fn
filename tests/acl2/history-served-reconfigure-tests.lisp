; Full publication refinement: a durable configuration, corrupted carried
; configuration, and a cancel whose resident history was replaced mid-run.
(in-package "ACL2")
(include-book "../../books/history-served-reconfigure")
(include-book "../../books/defkeystone")
(include-book "config-observed-tests")
(include-book "held-rows-tests")

(defconst *hcrt-config*
  (fn-cnode-config (fn-oclc-replayed *cpo-t-ready*)))
(defconst *hcrt-owner*
  (fn-ocfg-make (fn-own-start *cpo-t-ready* 4) *hcrt-config* nil *cpo-t-increase*))
(defconst *hcrt-history* (fn-sf-records (fn-sn-files *cpo-t-ready*)))
(defconst *hcrt-forged*
  (fn-ocfg-make (fn-ocfg-owner *hcrt-owner*) (fn-cfg-initial) nil *cpo-t-increase*))

(defthm fn-hcrt-publication-positive
  (and (fn-ocl-relation *hcrt-owner*)
       (fn-hist-of-storep *hcrt-history* (fn-own-store (fn-ocfg-owner *hcrt-owner*)))
       (equal (fn-hcr-publish *hcrt-owner* 3 32768 *hcrt-history*)
              (fn-ocl-publish *hcrt-owner* 3 32768))
       (equal (mv-nth 0 (fn-hcr-publish *hcrt-owner* 3 32768 *hcrt-history*)) :durable)))

(defthm fn-hcrt-missing-owner-relation
  (and (not (fn-ocl-relation *hcrt-forged*))
       (fn-hist-of-storep *hcrt-history* (fn-own-store (fn-ocfg-owner *hcrt-forged*)))
       (not (equal (fn-hcr-publish *hcrt-forged* 3 32768 *hcrt-history*)
                   (fn-ocl-publish *hcrt-forged* 3 32768))))
  :hints (("Goal" :in-theory (enable fn-hcr-publish fn-hcr-complete))))

; Two ordinary persisted held rows: T has a Cancel-Lock, C supplies its key.
; Open the configured store through the real recovery barriers. The owner
; retains the prefix view at T while its store has both rows, a legal carried
; view that configuration completion must refresh.
(defun fn-hcrt-lines (lines)
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) '(13 10) (fn-hcrt-lines (cdr lines)))
    '(13 10)))
(defconst *hcrt-key* "b2NyLWtleS1mb3ItdGhlLXRhcmdldA==")
(defconst *hcrt-lock*
  (fn-record-octets-string (fn-ctl-lock-of-key (fn-record-string-octets *hcrt-key*))))
(defun fn-hcrt-row (sequence msgid lines)
  (fn-hrt-row-at
   (fn-record-make sequence sequence sequence msgid (fn-hcrt-lines lines) '("fn.letters")
                  (concatenate 'string "pin:" msgid)
                  (concatenate 'string "content:" msgid)
                  (concatenate 'string "release:" msgid) 2 841000000)
   sequence))
(defconst *hcrt-target*
  (fn-hcrt-row 0 "<lt@example>"
   (list "From: friend <friend@example.invalid>" "Newsgroups: fn.letters"
         "Subject: mine" "Message-ID: <lt@example>"
         (concatenate 'string "Cancel-Lock: sha256:" *hcrt-lock*))))
(defconst *hcrt-cancel*
  (fn-hcrt-row 1 "<lc@example>"
   (list "From: friend <friend@example.invalid>" "Newsgroups: fn.letters"
         "Subject: cancel" "Message-ID: <lc@example>" "Control: cancel <lt@example>"
         (concatenate 'string "Cancel-Key: sha256:" *hcrt-key*))))
(defconst *hcrt-plain*
  (fn-hcrt-row 1 "<lc@example>"
   '("From: friend <friend@example.invalid>" "Newsgroups: fn.letters"
     "Subject: plain" "Message-ID: <lc@example>")))
(defun fn-hcrt-ready (rows frontier)
  (fn-sn-io (fn-sn-io (fn-sn-io
   (fn-sn-open-state (fn-cpo-open-observed (list *fn-cfg-default-record*) frontier rows))
   :recovery-barrier :ok) :recovery-barrier :ok) :recovery-barrier :ok))
(defconst *hcrt-cancel-history* (list *hcrt-target* *hcrt-cancel*))
(defconst *hcrt-wrong-history* (list *hcrt-target* *hcrt-plain*))
(defconst *hcrt-prefix-owner* (fn-own-start (fn-hcrt-ready (list *hcrt-target*) 1) 4))
(defconst *hcrt-cancel-store* (fn-hcrt-ready *hcrt-cancel-history* 2))
(defconst *hcrt-stage*
  (fn-cfg-record-make 1 2 2
    (list (fn-cfg-create-group "fn.hist-tooth" *fn-cfg-default-policy-id*))
    *fn-cfg-default-stamp*))
(defconst *hcrt-cancel-owner*
 (fn-ocfg-make
  (let ((o *hcrt-prefix-owner*))
   (fn-own-make *hcrt-cancel-store* (fn-own-view o) (fn-own-conns o)
    (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
    (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
    (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))
  (fn-cnode-config (fn-oclc-replayed *hcrt-cancel-store*)) nil *hcrt-stage*))

(defthm fn-hcrt-cancel-positive
 (and (fn-ocl-relation *hcrt-cancel-owner*)
      (fn-hist-of-storep *hcrt-cancel-history* *hcrt-cancel-store*)
      (equal (mv-nth 0 (fn-hcr-publish *hcrt-cancel-owner* 2 32768 *hcrt-cancel-history*)) :durable)
      (equal (fn-hcr-publish *hcrt-cancel-owner* 2 32768 *hcrt-cancel-history*)
             (fn-ocl-publish *hcrt-cancel-owner* 2 32768))))

(defthm fn-hcrt-missing-history-relation
 (and (fn-ocl-relation *hcrt-cancel-owner*)
      (not (fn-hist-of-storep *hcrt-wrong-history* *hcrt-cancel-store*))
      (not (equal (fn-hcr-publish *hcrt-cancel-owner* 2 32768 *hcrt-wrong-history*)
                  (fn-ocl-publish *hcrt-cancel-owner* 2 32768))))
 :hints (("Goal" :in-theory (enable fn-hcr-publish fn-hcr-complete fn-hcr-owner-with-store fn-own-refresh-ix))))

(defthm fn-hcrt-skipped-publication
 (and (fn-ocl-relation *hcrt-owner*)
      (fn-hist-of-storep *hcrt-history* (fn-own-store (fn-ocfg-owner *hcrt-owner*)))
      (equal (fn-hcr-publish *hcrt-owner* 3 32768 *hcrt-history*)
             (fn-ocl-publish *hcrt-owner* 3 32768))
      (not (equal (mv :durable *hcrt-owner*) (fn-ocl-publish *hcrt-owner* 3 32768)))))

; Exact conjunctions consumed by defteeth; the positive fact above also
; checks that this is a durable publication, not a refusal witness.
(defthm fn-hcrt-publication-witness
 (and (fn-ocl-relation *hcrt-owner*)
      (fn-hist-of-storep *hcrt-history* (fn-own-store (fn-ocfg-owner *hcrt-owner*)))
      (equal (fn-hcr-publish *hcrt-owner* 3 32768 *hcrt-history*)
             (fn-ocl-publish *hcrt-owner* 3 32768))))
(defthm fn-hcrt-owner-break
 (and (fn-hist-of-storep *hcrt-history* (fn-own-store (fn-ocfg-owner *hcrt-forged*)))
      (not (fn-ocl-relation *hcrt-forged*))
      (not (equal (fn-hcr-publish *hcrt-forged* 3 32768 *hcrt-history*)
                  (fn-ocl-publish *hcrt-forged* 3 32768))))
 :hints (("Goal" :use fn-hcrt-missing-owner-relation)))
(defthm fn-hcrt-history-break
 (and (fn-ocl-relation *hcrt-cancel-owner*)
      (not (fn-hist-of-storep *hcrt-wrong-history* (fn-own-store (fn-ocfg-owner *hcrt-cancel-owner*))))
      (not (equal (fn-hcr-publish *hcrt-cancel-owner* 2 32768 *hcrt-wrong-history*)
                  (fn-ocl-publish *hcrt-cancel-owner* 2 32768))))
 :hints (("Goal" :use fn-hcrt-missing-history-relation)))

(defteeth fn-hcr-publish-is-publish
 :claim (((owner (fn-ocl-relation oc))
          (history (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc)))))
         (equal (fn-hcr-publish oc generation max-octets hist)
                (fn-ocl-publish oc generation max-octets)))
 :subject fn-owner-reconfigure-complete
 :witness ((oc *hcrt-owner*) (generation 3) (max-octets 32768) (hist *hcrt-history*))
 :witness-lemma fn-hcrt-publication-witness
 :breaks ((owner ((oc *hcrt-forged*) (generation 3) (max-octets 32768) (hist *hcrt-history*))
                 :lemma fn-hcrt-owner-break)
          (history ((oc *hcrt-cancel-owner*) (generation 2) (max-octets 32768) (hist *hcrt-wrong-history*))
                   :lemma fn-hcrt-history-break))
 :mutations ((skipped-publication
              (:conclusion (equal (mv :durable oc) (fn-ocl-publish oc generation max-octets)))
              ((oc *hcrt-owner*) (generation 3) (max-octets 32768) (hist *hcrt-history*))
              :fault "returning durable without installing the staged configuration loses publication"
              :lemma fn-hcrt-skipped-publication)))
