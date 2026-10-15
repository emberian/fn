; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-pool-types")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm
    fn-lbcrt-mod-u64
    (implies (integerp x) (unsigned-byte-p 64 (mod x 18446744073709551616)))
    :hints
    (("Goal"
       :use
       ((:instance mod-bounds-1 (y 18446744073709551616)))
       :in-theory
       '(unsigned-byte-p integer-range-p (:type-prescription integerp-mod-1) (:executable-counterpart <) (:executable-counterpart expt) (:executable-counterpart binary-*) (:executable-counterpart binary-+) (:executable-counterpart not))))))

(local (defthm
    fn-lbcrt-msgid-hash-word
    (implies
      (unsigned-byte-p 64 hash)
      (unsigned-byte-p 64 (fn-lbc-msgid-hash-octets bytes hash)))
    :hints
    (("Goal"
       :induct
       (fn-lbc-msgid-hash-octets bytes hash)
       :in-theory
       '(fn-lbc-msgid-hash-octets fn-lbcrt-mod-u64 nfix natp unsigned-byte-p integer-range-p (:type-prescription integerp-mod-1) (:executable-counterpart <) (:executable-counterpart not) (:executable-counterpart expt))))))

(defthm
    fn-lbc-msgid-hash-has-native-type
    (unsigned-byte-p 64 (fn-lbc-msgid-hash msgid))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-msgid-hash) (fn-lbc-msgid-hash-octets unsigned-byte-p)))))

(local (defthm
    fn-lbcrt-framed-boolean
    (booleanp (fn-nntp-framed-of-bytes payload))
    :hints
    (("Goal"
       :in-theory
       (e/d (fn-nntp-framed-of-bytes fn-nntp-split-okp) (fn-nntp-split-article))))))

(local (defthm
    fn-lbcrt-locator-make-types
    (implies
      (and (unsigned-byte-p 64 seg) (unsigned-byte-p 32 off) (unsigned-byte-p 32 len))
      (fn-locp (mv-nth 0 (fn-loc-make seg off len)) (mv-nth 1 (fn-loc-make seg off len))))
    :hints
    (("Goal"
       :use
       fn-loc-accessors-of-make
       :in-theory
       (disable fn-loc-make fn-locp fn-loc-segment fn-loc-offset fn-loc-len unsigned-byte-p)))))

(local (defthm fn-lbcrt-flags-fit-u64
 (unsigned-byte-p 64 (+ (if a 1 0) (if b 2 0) (if c 4 0) (if d 8 0) (if e 16 0) (if f 32 0)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(unsigned-byte-p integer-range-p))))))

(defthm fn-lbc-row-flags-have-native-type
 (unsigned-byte-p 64 (fn-lbc-row-flags nov withdrawn escaped verified reclaimed))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbcrt-flags-fit-u64
    (a (and (fn-hnov-p nov) (fn-hnov-ok nov)))
    (b (and (fn-hnov-p nov) (fn-hnov-tomb nov)))
    (c withdrawn) (d escaped) (e verified) (f reclaimed)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-flags)))))

(defthm
    fn-lbc-rowwords-cell-has-native-type
    (implies
      (and (fn-locp loc0 loc1) (unsigned-byte-p 64 flags))
      (adt-rec-p
        *fn-lbc-rowwords-schema*
        (list
          (fn-lbc-u64 x0)
          loc0
          loc1
          (fn-lbc-u64 x3)
          (fn-lbc-u64 x4)
          (fn-lbc-u64 x5)
          (fn-lbc-u64 x6)
          (fn-lbc-u64 x7)
          (fn-lbc-u64 x8)
          (fn-lbc-msgid-hash msgid)
          (fn-lbc-u64 x10)
          (fn-lbc-u64 x11)
          (fn-lbc-u64 x12)
          (fn-lbc-u64 x13)
          (fn-lbc-u64 x14)
          flags)))
    :hints
    (("Goal"
       :in-theory
       (e/d (adt-rec-p adt-val-okp fn-locp) (fn-lbc-u64 fn-lbc-msgid-hash unsigned-byte-p)))))

(defthm
    fn-lbc-directory-cell-has-native-type
    (implies
      (and (booleanp b3) (booleanp b14) (booleanp b15) (booleanp b16) (booleanp b18))
      (adt-rec-p
        *fn-lbc-directory-schema*
        (list
          (fn-lbc-u64 x0)
          (fn-lbc-u64 x1)
          (fn-lbc-u64 x2)
          b3
          (fn-lbc-u64 x4)
          (fn-lbc-u64 x5)
          (if q6 1 0)
          (fn-lbc-u64 x7)
          (if q8 1 0)
          (fn-lbc-u64 x9)
          (fn-lbc-u64 x10)
          (fn-lbc-u64 x11)
          (fn-lbc-u64 x12)
          b14
          b15
          b16
          (fn-lbc-u64 x17)
          b18)))
    :hints
    (("Goal" :in-theory (e/d (adt-rec-p adt-val-okp) (fn-lbc-u64 unsigned-byte-p)))))

(local (defthm fn-lbcrt-true-listp-update
 (implies (true-listp xs) (true-listp (update-nth i value xs)))
 :hints (("Goal" :induct (update-nth i value xs) :in-theory (enable update-nth true-listp)))))

(defthm fn-lbc-p-of-escape-store-clear
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-escape-store-clear fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-escape-store-clear fn-lbc-escape-storep fn-dm-nth-update-nth
 fn-dm-len-update-nth fn-lbcrt-true-listp-update length)))))

(local (defthm fn-lbcrt-empty-rowwords
 (fn-lbc-rowwordsp nil)
 :hints (("Goal" :in-theory (enable fn-lbc-rowwordsp fn-lbc-rowwords$ap adt-seq-p)))))

(local (defthm fn-lbcrt-empty-msgid-octets
 (fn-lbc-msgid-octetsp nil)
 :hints (("Goal" :in-theory (enable fn-lbc-msgid-octetsp fn-lbc-msgid-octets$ap adt-seq-p)))))

(local (defthm fn-lbcrt-empty-overview-octets
 (fn-lbc-overview-octetsp nil)
 :hints (("Goal" :in-theory (enable fn-lbc-overview-octetsp fn-lbc-overview-octets$ap adt-seq-p)))))

(local (defthm fn-lbcrt-empty-msgid-slots
 (fn-lbc-msgid-slotsp nil)
 :hints (("Goal" :in-theory (enable fn-lbc-msgid-slotsp fn-lbc-msgid-slots$ap adt-seq-p)))))

(local (defthm fn-lbcrt-empty-directory
 (fn-lbc-directoryp nil)
 :hints (("Goal" :in-theory (enable fn-lbc-directoryp fn-lbc-directory$ap adt-seq-p)))))

(local (defthm fn-lbcrt-empty-memberships
 (fn-lbc-membershipsp nil)
 :hints (("Goal" :in-theory (enable fn-lbc-membershipsp fn-lbc-memberships$ap adt-seq-p)))))

(local (defthm fn-lbcrt-empty-nov
 (fn-lbc-novp nil)
 :hints (("Goal" :in-theory (enable fn-lbc-novp fn-lbc-nov$ap adt-seq-p)))))

(local (defthm fn-lbcrt-empty-number-map (fn-dmapp '(nil nil nil))
 :hints (("Goal" :in-theory (enable fn-dmapp fn-dmap$ap)))))

(defthm fn-lbc-p-of-clear-columns
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-clear-columns fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbcrt-empty-rowwords fn-lbcrt-empty-msgid-octets fn-lbcrt-empty-overview-octets fn-lbcrt-empty-msgid-slots fn-lbcrt-empty-directory fn-lbcrt-empty-memberships fn-lbcrt-empty-nov fn-lbcrt-empty-number-map fn-lbc-clear-columns fn-lbc-p-of-escape-store-clear fn-lbc-p-of-update-summary-groups fn-lbc-p-of-update-slot-escape-keys fn-lbc-p-of-update-row-store fn-lbc-row-store-has-native-type fn-lbc-rowwordsp-of-clear fn-lbc-p-of-update-msgid-store fn-lbc-msgid-store-has-native-type fn-lbc-msgid-octetsp-of-clear fn-lbc-p-of-update-overview-store fn-lbc-overview-store-has-native-type fn-lbc-overview-octetsp-of-clear fn-lbc-p-of-update-number-store fn-lbc-number-store-has-native-type fn-dmapp-of-clear fn-lbc-p-of-update-slot-store fn-lbc-slot-store-has-native-type fn-lbc-msgid-slotsp-of-clear fn-lbc-p-of-update-directory-store fn-lbc-directory-store-has-native-type fn-lbc-directoryp-of-clear fn-lbc-p-of-update-membership-store fn-lbc-membership-store-has-native-type fn-lbc-membershipsp-of-clear fn-lbc-p-of-update-nov-store fn-lbc-nov-store-has-native-type fn-lbc-novp-of-clear)))))

(defthm fn-lbc-p-of-row-store-append
 (implies (and (fn-lbc-p fn-lbc) (adt-rec-p *fn-lbc-rowwords-schema* record))
 (fn-lbc-p (update-fn-lbc-row-store
    (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-p-of-update-row-store fn-lbc-rowwordsp-of-append fn-lbc-row-store-has-native-type)))))

(defthm fn-lbc-p-of-directory-store-append
 (implies (and (fn-lbc-p fn-lbc) (adt-rec-p *fn-lbc-directory-schema* record))
 (fn-lbc-p (update-fn-lbc-directory-store
    (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-p-of-update-directory-store fn-lbc-directoryp-of-append fn-lbc-directory-store-has-native-type)))))

(defthm fn-lbc-p-of-record-pair-and-escape
 (implies (and (fn-lbc-p fn-lbc) (adt-rec-p *fn-lbc-rowwords-schema* words)
               (adt-rec-p *fn-lbc-directory-schema* directory))
 (fn-lbc-p (fn-lbc-escape-store-put key escape
  (let ((fn-lbc (update-fn-lbc-row-store (fn-lbc-rowwords-append words (fn-lbc-row-store fn-lbc)) fn-lbc)))
   (update-fn-lbc-directory-store (fn-lbc-directory-append directory (fn-lbc-directory-store fn-lbc)) fn-lbc)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-p-of-row-store-append fn-lbc-p-of-directory-store-append fn-lbc-p-of-escape-store-put)))))

(local (defthm fn-lbcrt-prefix-keeps-native-type
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (let* ((entry (fn-lb-log-model-row-entry row log)) (payload (nth 6 entry)) (facts (fn-held-facts row)) (nov (fn-hf-nov facts)) (nov-small (fn-lbc-nov-pool-fitp nov (fn-lbc-overview-pool-count fn-lbc))) (render-nov (fn-hnov-of payload)) (fn-lbc (if nov-small (fn-lbc-append-nov nov fn-lbc) fn-lbc)) (render-small (fn-lbc-nov-pool-fitp render-nov (fn-lbc-overview-pool-count fn-lbc))) (fn-lbc (if render-small (fn-lbc-append-nov render-nov fn-lbc) fn-lbc)) (groups-small (fn-lbc-pool-spans-fitp (fn-record-groups row) nil (fn-lbc-overview-pool-count fn-lbc))) (fn-lbc (if groups-small (fn-lbc-append-memberships (fn-record-groups row) nil fn-lbc) fn-lbc)) (numbers-small (and (fn-lbc-numbers-smallp (fn-held-numbers row)) (fn-lbc-pool-spans-fitp (fn-held-numbers row) t (fn-lbc-overview-pool-count fn-lbc)))) (fn-lbc (if numbers-small (fn-lbc-append-memberships (fn-held-numbers row) t fn-lbc) fn-lbc)) (msgid-bytes (fn-record-string-octets (fn-record-msgid row))) (fn-lbc (fn-lbc-msgid-pool-append msgid-bytes fn-lbc))) fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-nov-pool-fitp fn-lbc-p-of-append-nov fn-lbc-p-of-append-memberships
 fn-lbc-p-of-msgid-pool-append fn-lbc-string-octets-are-octets))))))

(local (defthm fn-lbcrt-actual-words-have-native-type
 (implies (fn-lbc-row-log-guardp row log) (adt-rec-p *fn-lbc-rowwords-schema* (let* ((i (fn-lbc-count fn-lbc)) (entry (fn-lb-log-model-row-entry row log)) (segment (fn-lb-log-model-row-segment row log)) (payload (nth 6 entry)) (facts (fn-held-facts row)) (nov (fn-hf-nov facts)) (nov-small (fn-lbc-nov-pool-fitp nov (fn-lbc-overview-pool-count fn-lbc))) (render-nov (fn-hnov-of payload)) (nov-start (fn-lbc-nov-record-count fn-lbc)) (fn-lbc (if nov-small (fn-lbc-append-nov nov fn-lbc) fn-lbc)) (render-small (fn-lbc-nov-pool-fitp render-nov (fn-lbc-overview-pool-count fn-lbc))) (render-start (fn-lbc-nov-record-count fn-lbc)) (fn-lbc (if render-small (fn-lbc-append-nov render-nov fn-lbc) fn-lbc)) (groups-small (fn-lbc-pool-spans-fitp (fn-record-groups row) nil (fn-lbc-overview-pool-count fn-lbc))) (groups-start (fn-lbc-membership-record-count fn-lbc)) (fn-lbc (if groups-small (fn-lbc-append-memberships (fn-record-groups row) nil fn-lbc) fn-lbc)) (numbers-small (and (fn-lbc-numbers-smallp (fn-held-numbers row)) (fn-lbc-pool-spans-fitp (fn-held-numbers row) t (fn-lbc-overview-pool-count fn-lbc)))) (numbers-start (fn-lbc-membership-record-count fn-lbc)) (fn-lbc (if numbers-small (fn-lbc-append-memberships (fn-held-numbers row) t fn-lbc) fn-lbc)) (msgid-offset (fn-lbc-msgid-pool-count fn-lbc)) (msgid-bytes (fn-record-string-octets (fn-record-msgid row))) (fn-lbc (fn-lbc-msgid-pool-append msgid-bytes fn-lbc)) (head-length (len (fn-nntp-stuffed-section :head payload))) (raw-head-length (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload))))) (previous-max (if (zp i) 0 (fn-lbc-value (- i 1) :prefix-max fn-lbc))) (max-stamp (max (nfix previous-max) (nfix (fn-record-stamp row)))) (w (fn-held-withdrawn row)) (escape (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset (len msgid-bytes) i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small)) (flags (fn-lbc-row-flags nov w escape (fn-arx-entry-ok (fn-lb-entry-octets segment (nth 3 entry) log) (fn-lb-entry-protected-len segment (nth 3 entry) log)) (fn-rcl-tombstonep payload)))) (let* ((loc0 (mv-nth 0 (fn-loc-make segment (nth 3 entry) (nth 4 entry)))) (loc1 (mv-nth 1 (fn-loc-make segment (nth 3 entry) (nth 4 entry))))) (let* ((words (list (fn-lbc-u64 (fn-record-payload row)) loc0 loc1 (fn-lbc-u64 head-length) (fn-lbc-u64 (fn-record-stamp row)) (fn-lbc-u64 max-stamp) (fn-lbc-u64 (fn-record-txid row)) (fn-lbc-u64 (fn-record-generation row)) (fn-lbc-u64 (fn-record-charge row)) (fn-lbc-msgid-hash (fn-record-msgid row)) (fn-lbc-u64 msgid-offset) (fn-lbc-u64 (len msgid-bytes)) (fn-lbc-u64 (car w)) (fn-lbc-u64 (cdr w)) (fn-lbc-u64 i) flags))) words)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbcrt-locator-make-types (seg (fn-lb-log-model-row-segment row log)) (off (nth 3 (fn-lb-log-model-row-entry row log))) (len (nth 4 (fn-lb-log-model-row-entry row log))))) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-row-log-guardp fn-lbc-rowwords-cell-has-native-type fn-lbc-directory-cell-has-native-type
 fn-lbc-row-flags-have-native-type fn-lbcrt-framed-boolean))))))

(local (defthm fn-lbcrt-actual-directory-have-native-type
 (adt-rec-p *fn-lbc-directory-schema* (let* ((entry (fn-lb-log-model-row-entry row log)) (payload (nth 6 entry)) (facts (fn-held-facts row)) (nov (fn-hf-nov facts)) (nov-small (fn-lbc-nov-pool-fitp nov (fn-lbc-overview-pool-count fn-lbc))) (render-nov (fn-hnov-of payload)) (nov-start (fn-lbc-nov-record-count fn-lbc)) (fn-lbc (if nov-small (fn-lbc-append-nov nov fn-lbc) fn-lbc)) (render-small (fn-lbc-nov-pool-fitp render-nov (fn-lbc-overview-pool-count fn-lbc))) (render-start (fn-lbc-nov-record-count fn-lbc)) (fn-lbc (if render-small (fn-lbc-append-nov render-nov fn-lbc) fn-lbc)) (groups-small (fn-lbc-pool-spans-fitp (fn-record-groups row) nil (fn-lbc-overview-pool-count fn-lbc))) (groups-start (fn-lbc-membership-record-count fn-lbc)) (fn-lbc (if groups-small (fn-lbc-append-memberships (fn-record-groups row) nil fn-lbc) fn-lbc)) (numbers-start (fn-lbc-membership-record-count fn-lbc)) (raw-head-length (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))))) (let* ((directory (list (fn-lbc-u64 (fn-record-sequence row)) (fn-lbc-u64 (fn-hf-octets facts)) (fn-lbc-u64 (fn-hf-body-start facts)) (natp (fn-hf-body-start facts)) (fn-lbc-u64 (fn-hf-body-lines facts)) (fn-lbc-u64 nov-start) (if nov-small 1 0) (fn-lbc-u64 render-start) (if render-small 1 0) (fn-lbc-u64 groups-start) (fn-lbc-u64 (len (fn-record-groups row))) (fn-lbc-u64 numbers-start) (fn-lbc-u64 (len (fn-held-numbers row))) (equal (car (fn-nntp-section-of-bytes payload :article)) :ok) (equal (car (fn-nntp-section-of-bytes payload :head)) :ok) (equal (car (fn-nntp-section-of-bytes payload :body)) :ok) (fn-lbc-u64 raw-head-length) (fn-nntp-framed-of-bytes payload)))) directory)))
 :hints (("Goal" :do-not-induct t  :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(adt-rec-p adt-val-okp fn-lbc-u64-has-native-type fn-lbcrt-framed-boolean (:executable-counterpart unsigned-byte-p))) '(unsigned-byte-p))))))

(defthm fn-lbc-p-of-append-row
 (implies (and (fn-lbc-p fn-lbc) (fn-cat-rowp row) (fn-lbc-row-log-guardp row log))
 (fn-lbc-p (fn-lbc-append-row row log fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbcrt-prefix-keeps-native-type)
       (:instance fn-lbcrt-actual-words-have-native-type)
       (:instance fn-lbcrt-actual-directory-have-native-type))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-append-row fn-lbc-p-of-record-pair-and-escape
 fn-lbc-p-of-row-store-append fn-lbc-p-of-directory-store-append fn-lbc-p-of-escape-store-put
 fn-lbc-p-of-update-row-store fn-lbc-p-of-update-directory-store
 fn-lbc-row-store-has-native-type fn-lbc-directory-store-has-native-type
 fn-lbc-rowwordsp-of-append fn-lbc-directoryp-of-append)))))

(defthm fn-lbc-p-of-rebuild-rows
 (implies (and (fn-lbc-p fn-lbc) (fn-cat-rowsp rows) (fn-lbc-rows-log-guardp rows log))
 (fn-lbc-p (fn-lbc-rebuild-rows rows log fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-rebuild-rows fn-cat-rowsp fn-lbc-rows-log-guardp fn-lbc-p-of-append-row fn-lbc-p-of-number-put-row)))))

(defthm fn-lbc-p-of-open-rebuild
 (implies (and (fn-lbc-p fn-lbc) (fn-cat-rowsp rows) (fn-lbc-rows-log-guardp rows log))
 (fn-lbc-p (fn-lbc-open-rebuild rows log fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-open-rebuild fn-lbc-p-of-clear-columns fn-lbc-p-of-rebuild-rows
 fn-lbc-p-of-rebuild-summaries fn-lbc-p-of-update-summary-groups
 fn-lbc-p-of-reserve-slots fn-lbc-p-of-index-slots)))))
