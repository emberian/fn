; LB served reads.  The references stay unchanged and provide the logical
; target; the resident selector and stored-range worker own execution.
(in-package "ACL2")
(include-book "nntp-reader-compat")
(include-book "nntp-newnews")
(include-book "nntp-effects")
(include-book "served-columns")
(include-book "catalog-number-index")
(include-book "log-locator-resolves")
(include-book "log-verified-map")
(include-book "catalog-columns-guards")

; Carried logical invariant; its two component invariants are non-executable.
(defun fn-lb-served-log-invp (log fn-lb-vmap fn-lbc rows)
  (declare (xargs :stobjs (fn-lb-vmap fn-lbc) :verify-guards nil))
  (and (fn-lbc-corr fn-lbc rows log)
       (fn-lb-verified-invp log fn-lb-vmap)
       (fn-lc-locators-resolve fn-lbc log)))

; Guard-only shape for APPEND's section argument. Establishment from
; section correspondence is owed with the carried invariant; no served scan.
(defun fn-lbc-section-values-guardp (i fn-lbc log)
 (declare (xargs :stobjs fn-lbc
  :guard (and (fn-lb-log-read-guardp log) (fn-lbc-escape-cellsp 0 fn-lbc))
  :measure (nfix (- (fn-lbc-count fn-lbc) (nfix i)))
  :hints (("Goal" :in-theory (disable fn-lbc-stored-range fn-lbc-count fn-lbc-p true-listp)))
  :verify-guards nil))
 (if (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (and (true-listp (fn-lbc-stored-range i :article fn-lbc log))
       (true-listp (fn-lbc-stored-range i :head fn-lbc log))
       (true-listp (fn-lbc-stored-range i :body fn-lbc log))
       (fn-lbc-section-values-guardp (+ 1 i) fn-lbc log))
  t))

(defun fn-lbc-article (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (fn-make-article (fn-lbc-msgid i fn-lbc) (fn-lbc-value i :handle fn-lbc)
                  (fn-lbc-groups i fn-lbc) (fn-lbc-numbers i fn-lbc)
                  t (fn-lbc-value i :stamp fn-lbc)))

(defun fn-lbc-id-article (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (fn-make-article (fn-lbc-msgid i fn-lbc) 0 nil nil t 0))

(defun fn-lbc-msgid-visible-last (seqs v fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-escape-cellsp 0 fn-lbc) :verify-guards nil))
  (if (consp seqs)
      (let ((later (fn-lbc-msgid-visible-last (cdr seqs) v fn-lbc)))
        (if later later
          (if (fn-lbc-visiblep (car seqs) v fn-lbc) (car seqs) nil)))
    nil))

; Selection returns (:ROW I NUMBER UPDATEP GROUP), or (:REFUSAL TEXT).
; Neither the archive's article list nor payload bytes are traversed here.
(defun fn-lbc-select (session kind args v fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (fn-lbc-escape-cellsp 0 fn-lbc) (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc)) :verify-guards nil)
           (ignore kind))
  (if (null args)
      (let ((group (fn-nntp-session-group session))
            (number (fn-nntp-session-current session)))
        (cond ((null group) (list :refusal (fn-proto-text * :no-group-selected)))
              ((null number) (list :refusal (fn-proto-text * :no-current)))
              (t (let ((i (fn-lbc-number-get group number fn-lbc)))
                   (if (and (natp i) (fn-lbc-visiblep i v fn-lbc)
                            (posp number)
                            (<= number *fn-nntp-max-article-number*)
                            (fn-nntp-article-idp (fn-lbc-id-article i fn-lbc)))
                       (list :row i number t group)
                     (list :refusal (fn-proto-text * :no-current)))))))
    (let ((token (and (consp args) (car args))))
      (if (fn-nntp-number-tokenp token)
          (let ((group (fn-nntp-session-group session))
                (number (fn-nntp-decimal-value token)))
            (if (null group) (list :refusal (fn-proto-text * :no-group-selected))
              (let ((i (fn-lbc-number-get group number fn-lbc)))
                (if (and (natp i) (fn-lbc-visiblep i v fn-lbc))
                    (list :row i number t group)
                  (list :refusal (fn-proto-text * :no-number))))))
        (if (not (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token)))
            (list :refusal (fn-proto-text * :syntax))
          (let ((i (fn-lbc-msgid-visible-last
                     (fn-lbc-msgid-seqs (fn-nntp-token-string token) fn-lbc) v fn-lbc)))
            (if (natp i)
                (list :row i
                      (fn-nntp-msgid-local-number session (fn-lbc-article i fn-lbc)) nil nil)
              (list :refusal (fn-proto-text * :no-msgid)))))))))

(defun fn-lb-unverified-target (session args)
  (declare (xargs :guard t :verify-guards nil))
  (let ((token (and (consp args) (car args))))
    (if (and (consp args) (fn-nntp-message-id-tokenp token) (fn-octet-listp token))
        token
      (append (fn-nntp-string-octets (fn-nntp-session-group session)) '(58)
              (if (and (consp args) (fn-nntp-number-tokenp token)) token
                (fn-nntp-decimal-field (fn-nntp-session-current session)))))))

; Existing extent resource-refusal text (owner-resource-line), with the
; requested article named.  Authentication failure does not claim absence.
(defun fn-lb-unverified-refusal (session kind args)
  (declare (xargs :guard (or (atom args) (true-listp (car args))) :verify-guards nil) (ignore kind))
  (fn-nntp-make-result session
    (list (fn-nntp-reply-effect
      (append
        (fn-nntp-string-octets
          "403 article temporarily unavailable; cold read resources unavailable; try again later")
        '(32 40) (fn-lb-unverified-target session args) '(41 13 10))))))

(defun fn-lbc-selected-reads-entry-p (selected kind server v fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (true-listp selected) (fn-lbc-escape-cellsp 0 fn-lbc)) :verify-guards nil))
  (let ((i (cadr selected)))
    (and (equal (car selected) :row)
         (fn-lbc-visiblep i v fn-lbc)
         (fn-nntp-article-idp (fn-lbc-id-article i fn-lbc))
         (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc))
         (not (equal kind :stat))
         (or (fn-lbc-directory-value i :framed fn-lbc)
             (not (or (null server) (fn-xref-serverp server)))))))

(defun fn-lbc-retrieval-reads-entry-p
    (session archive arts kind args server v fn-lbc seg entry)
  (declare (xargs :stobjs fn-lbc :guard (and (fn-lbc-escape-cellsp 0 fn-lbc) (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc)) :verify-guards nil)
           (ignore archive arts))
  (let* ((selected (fn-lbc-select session kind args v fn-lbc))
         (i (cadr selected)))
    (and (fn-lbc-selected-reads-entry-p selected kind server v fn-lbc)
         (equal seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
         (equal entry (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))))))

(defun fn-lb-log-model-unwire (bytes startp)
  (declare (xargs :guard (or (true-listp bytes) (equal bytes :bad)) :verify-guards nil))
  (if (consp bytes)
      (if (and startp (eql (car bytes) 46) (eql (cadr bytes) 46))
          (cons 46 (fn-lb-log-model-unwire (cddr bytes) nil))
        (cons (car bytes) (fn-lb-log-model-unwire (cdr bytes) (eql (car bytes) 10))))
    nil))

; The full API also gives a logical answer for an arbitrary server value.
; Such a prefix can contain a separator or malformed framing.  Keep that
; case explicit; the typed served server uses the resident section arm.
(defun fn-lbc-arbitrary-prefix-reply (session article number kind updatep group server i fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (and (natp i) (< i (fn-lbc-count fn-lbc)) (alistp (fn-lbc-escape-store-get i fn-lbc)) (fn-lb-log-read-guardp log)) :verify-guards nil))
  (let* ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
         (wire (fn-lb-log-model-read-range (fn-loc-segment a b)
                   (fn-loc-offset a b) (fn-loc-len a b) log))
         (payload (fn-lb-log-model-unwire wire t))
         (served (fn-nntp-article-response-of-bytes session article
                     (fn-rcompat-served-payload-of-bytes server article payload)
                     number kind updatep group)))
    (if (equal (fn-nntp-result-session served)
               (if (fn-nntp-response-okp-of-bytes article payload kind)
                   (if updatep (fn-nntp-set-cursor session group number) session) session))
        served
      (fn-nntp-article-response-of-bytes session article payload number kind updatep group))))

(defun fn-lbc-resident-reply (session selected kind server fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (and (true-listp selected) (natp (nth 1 selected)) (< (nth 1 selected) (fn-lbc-count fn-lbc)) (alistp (fn-lbc-escape-store-get (nth 1 selected) fn-lbc)) (fn-lb-log-read-guardp log) (fn-lbc-escape-cellsp 0 fn-lbc) (fn-lbc-section-values-guardp 0 fn-lbc log)) :verify-guards nil))
  (let* ((i (nth 1 selected)) (number (nth 2 selected))
         (updatep (nth 3 selected)) (group (nth 4 selected))
         (id (fn-lbc-id-article i fn-lbc)))
    (cond ((not (fn-nntp-article-idp id))
           (fn-nntp-single session "503 stored article identifier unavailable"))
          ((fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)
           (fn-nntp-single session (if updatep "423 article reclaimed" "430 article reclaimed")))
          ((equal kind :stat)
           (fn-nntp-make-result
             (if updatep (fn-nntp-set-cursor session group number) session)
             (list (fn-nntp-reply-effect
                     (fn-nntp-crlf (fn-nntp-retrieval-initial kind number id))))))
          ((not (or (null server) (fn-xref-serverp server)))
           (fn-lbc-arbitrary-prefix-reply session (fn-lbc-article i fn-lbc)
              number kind updatep group server i fn-lbc log))
          ((not (fn-lbc-directory-value i :framed fn-lbc))
           (fn-nntp-single session "503 stored article framing unavailable"))
          (t (let* ((article (fn-lbc-article i fn-lbc))
                    (section-kind (if (member-equal kind '(:article :head)) kind :body))
                    (section (fn-lbc-stored-range i section-kind fn-lbc log))
                    (prefix (if (and (not (equal section-kind :body))
                                     (consp (fn-xref-pairs article)))
                                (append (fn-xref-field server (fn-xref-pairs article)) '(13 10)) nil)))
               (fn-nntp-make-result
                 (if updatep (fn-nntp-set-cursor session group number) session)
                 (list (fn-nntp-reply-effect
                         (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
                                 prefix section '(46 13 10))))))))))

(defun fn-lbc-retrieval
    (session archive arts kind args server v log fn-lb-vmap fn-arena fn-lbc)
  (declare (xargs :stobjs (fn-lb-vmap fn-arena fn-lbc) :guard (and (fn-lbc-escape-cellsp 0 fn-lbc) (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc) (fn-lb-log-read-guardp log) (or (atom args) (true-listp (car args))) (fn-lbc-section-values-guardp 0 fn-lbc log)) :verify-guards nil)
           (ignore archive arts fn-arena))
  (let* ((selected (fn-lbc-select session kind args v fn-lbc))
         (i (cadr selected)))
    (if (equal (car selected) :refusal)
        (fn-nntp-single session (cadr selected))
      (let ((seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
            (entry (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))))
        (if (and (fn-lbc-selected-reads-entry-p selected kind server v fn-lbc)
                 (not (fn-lb-verified-bit seg entry fn-lb-vmap))
                 (not (fn-arx-entry-ok (fn-lb-entry-octets seg entry log)
                                       (fn-lb-entry-protected-len seg entry log))))
            (fn-lb-unverified-refusal session kind args)
          (fn-lbc-resident-reply session selected kind server fn-lbc log))))))


; Every row's locator lies inside one committed entry of LOG.
(defun fn-lb-locators-in-log-from (i fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (fn-lb-log-read-guardp log)
                  :measure (nfix (- (fn-lbc-count fn-lbc) (nfix i)))
                  :verify-guards nil))
  (if (and (natp i) (< i (fn-lbc-count fn-lbc)))
      (let* ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
             (seg (fn-lb-log-model-segment (fn-loc-segment a b) log)))
        (and seg (fn-locp a b)
             (fn-lb-log-model-range-in-entries (fn-loc-offset a b)
                                               (fn-loc-len a b) (caddr seg))
             (not (equal (fn-lb-log-model-read-range (fn-loc-segment a b)
                           (fn-loc-offset a b) (fn-loc-len a b) log) :bad))
             (fn-lb-locators-in-log-from (+ 1 i) fn-lbc log)))
    t))

(defun fn-lb-locators-in-log (fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (fn-lb-log-read-guardp log) :verify-guards nil))
  (fn-lb-locators-in-log-from 0 fn-lbc log))

; The bytes at every row's locator equal its expected stored range:
; article wire octets, or raw reclaimed tombstone octets.
(defun fn-lb-log-binds-payloads-from (i rows fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (and (natp i) (<= (+ i (len rows)) (fn-lbc-count fn-lbc)) (fn-lb-log-read-guardp log)) :measure (acl2-count rows)
                  :verify-guards nil))
  (if (consp rows)
      (let ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)))
        (and (equal (fn-lb-log-model-read-range (fn-loc-segment a b)
                      (fn-loc-offset a b) (fn-loc-len a b) log)
                    (fn-lc-expected-range (fn-lb-log-payload (car rows) log)))
             (fn-lb-log-binds-payloads-from (+ 1 (nfix i)) (cdr rows) fn-lbc log)))
    t))

(defun fn-lb-log-binds-payloads (fn-lbc rows log)
  (declare (xargs :stobjs fn-lbc :guard (and (<= (len rows) (fn-lbc-count fn-lbc)) (fn-lb-log-read-guardp log)) :verify-guards nil))
  (fn-lb-log-binds-payloads-from 0 rows fn-lbc log))

; Served guard proofs. Guard-only domains leave the logical outputs unchanged.
(verify-guards fn-lb-log-model-unwire :guard-debug t)
(verify-guards fn-lb-unverified-target :guard-debug t)
(verify-guards fn-lbc-article
 :hints (("Goal" :in-theory (disable fn-lbc-msgid fn-lbc-value fn-lbc-groups fn-lbc-numbers fn-lbc-p fn-lbc-escape-store-get))))
(verify-guards fn-lbc-id-article
 :hints (("Goal" :in-theory (disable fn-lbc-msgid fn-lbc-p fn-lbc-escape-store-get))))
(local (defthm fn-lbsg-octets-true-list
 (implies (fn-octet-listp bytes) (true-listp bytes))
 :hints (("Goal" :induct (fn-octet-listp bytes) :in-theory (enable fn-octet-listp)))))
(local (defthm fn-lbsg-unverified-target-true-list
 (implies (or (atom args) (true-listp (car args)))
  (true-listp (fn-lb-unverified-target session args)))
 :hints (("Goal" :in-theory
  (e/d (fn-lb-unverified-target)
       (fn-nntp-message-id-tokenp fn-nntp-number-tokenp fn-octet-listp
        fn-nntp-string-octets fn-nntp-decimal-field fn-nntp-session-current fn-nntp-session-group))))))
(verify-guards fn-lb-unverified-refusal
 :hints (("Goal" :in-theory (disable fn-lb-unverified-target fn-nntp-string-octets))))

; BEGIN LB resume9 generated served domain proofs
(local (defthm fn-lbsg-escape-select
 (implies (and (natp start) (natp i) (<= start i) (< i (fn-lbc-count fn-lbc))
               (fn-lbc-escape-cellsp start fn-lbc))
  (alistp (fn-lbc-escape-store-get i fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-escape-cellsp start fn-lbc)
 :in-theory (e/d (fn-lbc-escape-cellsp) (fn-lbc-p fn-lbc-count fn-lbc-escape-store-get))))))
(local (defthm fn-lbsg-escape-select-zero
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lbc-escape-cellsp 0 fn-lbc))
  (alistp (fn-lbc-escape-store-get i fn-lbc)))
 :hints (("Goal" :use ((:instance fn-lbsg-escape-select (start 0)))
 :in-theory (disable fn-lbsg-escape-select fn-lbc-p fn-lbc-count fn-lbc-escape-cellsp fn-lbc-escape-store-get)))))
(local (defthm fn-lbsg-visiblep-index-domain
 (implies (fn-lbc-visiblep i v fn-lbc) (and (natp i) (< i (fn-lbc-count fn-lbc))))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (e/d (fn-lbc-visiblep) (fn-lbc-withdrawn fn-lbc-count fn-lbc-p))))))
(local (defthm fn-lbsg-msgid-visible-last-domain
 (implies (fn-lbc-msgid-visible-last seqs v fn-lbc)
  (and (natp (fn-lbc-msgid-visible-last seqs v fn-lbc))
       (< (fn-lbc-msgid-visible-last seqs v fn-lbc) (fn-lbc-count fn-lbc))))
 :rule-classes :forward-chaining
 :hints (("Goal" :induct (fn-lbc-msgid-visible-last seqs v fn-lbc)
 :in-theory (e/d (fn-lbc-msgid-visible-last fn-lbc-visiblep) (fn-lbc-withdrawn fn-lbc-count fn-lbc-p))))))
(local (defthm fn-lbsg-select-true-list
 (true-listp (fn-lbc-select session kind args v fn-lbc))
 :hints (("Goal" :in-theory (e/d (fn-lbc-select)
  (fn-lbc-number-get fn-lbc-visiblep fn-nntp-session-group fn-nntp-session-current
   fn-nntp-article-idp fn-lbc-id-article fn-nntp-number-tokenp fn-nntp-decimal-value
   fn-nntp-message-id-tokenp fn-octet-listp fn-nntp-token-string fn-lbc-msgid-seqs
   fn-lbc-msgid-visible-last fn-nntp-msgid-local-number fn-lbc-article fn-lbc-count fn-lbc-p))))))
(local (defthm fn-lbsg-select-row-domain
 (implies (equal (car (fn-lbc-select session kind args v fn-lbc)) :row)
  (and (natp (cadr (fn-lbc-select session kind args v fn-lbc)))
       (< (cadr (fn-lbc-select session kind args v fn-lbc)) (fn-lbc-count fn-lbc))))
 :hints (("Goal" :use ((:instance fn-lbsg-msgid-visible-last-domain
 (seqs (fn-lbc-msgid-seqs (fn-nntp-token-string (and (consp args) (car args))) fn-lbc))))
 :in-theory (e/d (fn-lbc-select fn-lbc-visiblep)
  (fn-lbc-number-get fn-lbc-withdrawn fn-nntp-session-group fn-nntp-session-current
   fn-nntp-article-idp fn-lbc-id-article fn-nntp-number-tokenp fn-nntp-decimal-value
   fn-nntp-message-id-tokenp fn-octet-listp fn-nntp-token-string fn-lbc-msgid-seqs
   fn-lbc-msgid-visible-last fn-nntp-msgid-local-number fn-lbc-article fn-lbc-count fn-lbc-p))))))
(local (defthm
    fn-lbsg-rowwords-loc-fields
    (implies
      (and (adt-seq-p *fn-lbc-rowwords-schema* rows) (natp i) (< i (len rows)))
      (and (unsigned-byte-p 64 (nth 1 (nth i rows))) (unsigned-byte-p 64 (nth 2 (nth i rows)))))
    :hints
    (("Goal"
       :use
       ((:instance adt-tp-rec-p-nth (s *fn-lbc-rowwords-schema*) (a rows)))
       :in-theory
       (enable adt-rec-p adt-val-okp)))))
(local (defthm
    fn-lbsg-locator-words
    (implies
      (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
      (fn-locp (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
    :hints
    (("Goal" :in-theory (enable fn-lbc-loc0 fn-lbc-loc1 fn-lbc-count fn-locp)))))
(local (defthm fn-lbsg-selected-reads-row-domain
 (implies (fn-lbc-selected-reads-entry-p selected kind server v fn-lbc)
  (and (equal (car selected) :row) (natp (cadr selected))
       (< (cadr selected) (fn-lbc-count fn-lbc))))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (e/d (fn-lbc-selected-reads-entry-p fn-lbc-visiblep)
  (fn-lbc-withdrawn fn-lbc-id-article fn-lbc-flag fn-lbc-directory-value fn-lbc-count fn-lbc-p))))))
(local (defthm fn-lbsg-select-tag
 (or (equal (car (fn-lbc-select session kind args v fn-lbc)) :row)
     (equal (car (fn-lbc-select session kind args v fn-lbc)) :refusal))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-lbc-select)
  (fn-lbc-number-get fn-lbc-visiblep fn-nntp-session-group fn-nntp-session-current
   fn-nntp-article-idp fn-lbc-id-article fn-nntp-number-tokenp fn-nntp-decimal-value
   fn-nntp-message-id-tokenp fn-octet-listp fn-nntp-token-string fn-lbc-msgid-seqs
   fn-lbc-msgid-visible-last fn-nntp-msgid-local-number fn-lbc-article fn-lbc-count fn-lbc-p))))))
(local (defthm fn-lbsg-log-read-shape
 (implies (fn-lb-log-read-guardp log)
  (and (fn-lb-log-entries-guardp log)
       (alistp (remove-equal nil (true-list-fix log)))
       (true-listp (fn-lb-log-model-segment seg log))
       (true-listp (cadr (fn-lb-log-model-segment seg log)))
       (true-list-listp (true-list-fix (caddr (fn-lb-log-model-segment seg log))))))
 :hints (("Goal" :induct (fn-lb-log-read-guardp log)
  :in-theory (enable fn-lb-log-read-guardp fn-lb-log-entries-guardp fn-lb-log-model-segment)))))
(local (defthm fn-lbsg-true-listp-take
 (true-listp (take n x))
 :hints (("Goal" :induct (take n x) :in-theory (enable take)))))
(local (defthm fn-lbsg-read-range-result-domain
 (or (true-listp (fn-lb-log-model-read-range seg off n log))
     (equal (fn-lb-log-model-read-range seg off n log) :bad))
 :rule-classes :rewrite
 :hints (("Goal" :in-theory (e/d (fn-lb-log-model-read-range)
   (fn-lb-log-model-segment fn-lb-log-model-range-in-entries))))))
(local (defthm fn-lbsg-log-read-raw-alist
 (implies (fn-lb-log-read-guardp log) (alistp (remove-equal nil log)))
 :hints (("Goal" :induct (fn-lb-log-read-guardp log)
  :in-theory (enable fn-lb-log-read-guardp remove-equal alistp)))))
(local (defthm fn-lbsg-nth-one-by-definition
 (equal (nth 1 x) (cadr x))
 :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-lbsg-segment-true-listp
 (implies (fn-lb-log-read-guardp log)
  (true-listp (fn-lb-log-model-segment seg log)))
 :rule-classes :type-prescription
 :hints (("Goal" :use fn-lbsg-log-read-shape
  :in-theory (disable fn-lbsg-log-read-shape fn-lb-log-read-guardp fn-lb-log-model-segment true-listp)))))
(local (defthm fn-lbsg-section-values-select
 (implies (and (fn-lbc-section-values-guardp start fn-lbc log)
               (natp start) (natp i) (<= start i) (< i (fn-lbc-count fn-lbc))
               (member-equal kind '(:article :head :body)))
  (true-listp (fn-lbc-stored-range i kind fn-lbc log)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lbc-section-values-guardp start fn-lbc log)
  :in-theory (e/d (fn-lbc-section-values-guardp member-equal)
    (fn-lbc-stored-range fn-lbc-count fn-lbc-p))))))
(local (defthm fn-lbsg-section-values-select-zero
 (implies (and (fn-lbc-section-values-guardp 0 fn-lbc log)
               (natp i) (< i (fn-lbc-count fn-lbc))
               (member-equal kind '(:article :head :body)))
  (true-listp (fn-lbc-stored-range i kind fn-lbc log)))
 :hints (("Goal" :use ((:instance fn-lbsg-section-values-select (start 0)))
  :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-lbc-count fn-lbc-p)))))
(verify-guards fn-lbc-section-values-guardp :guard-debug t
 :hints (("Goal" :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lbc-msgid-visible-last :guard-debug t
 :hints (("Goal" :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lbc-select :guard-debug t
 :hints (("Goal" :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lbc-selected-reads-entry-p :guard-debug t
 :hints (("Goal" :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lbc-retrieval-reads-entry-p :guard-debug t
 :hints (("Goal" :use ((:instance fn-lbsg-selected-reads-row-domain (selected (fn-lbc-select session kind args v fn-lbc))))
 :in-theory (disable fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lbc-arbitrary-prefix-reply :guard-debug t
 :hints (("Goal" :use ((:instance fn-lbsg-read-range-result-domain
 (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
 (off (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
 (n (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))))
 :in-theory (disable fn-lbsg-read-range-result-domain fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lbc-resident-reply :guard-debug t
 :hints (("Goal" :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lbc-retrieval :guard-debug t
 :hints (("Goal" :use ((:instance fn-lbsg-select-tag)) :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lb-locators-in-log-from :guard-debug t
 :hints (("Goal" :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lb-locators-in-log :guard-debug t
 :hints (("Goal" :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lb-log-binds-payloads-from :guard-debug t
 :hints (("Goal" :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
(verify-guards fn-lb-log-binds-payloads :guard-debug t
 :hints (("Goal" :in-theory (disable fn-lbc-section-values-guardp fn-lbc-stored-range fn-loc-segment fn-loc-offset fn-loc-len fn-locp fn-lbc-p fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp
 fn-lbc-slot-owners-guardp fn-lbc-slot-escape-keys fn-lbc-visiblep fn-lbc-msgid-seqs
 fn-lbc-article fn-lbc-id-article fn-lbc-select fn-lbc-msgid-visible-last
 fn-lbc-selected-reads-entry-p fn-lbc-arbitrary-prefix-reply fn-lbc-resident-reply
 fn-lb-unverified-refusal fn-lb-log-read-guardp fn-lb-log-entries-guardp
 fn-lb-log-model-read-range fn-lb-log-payload fn-lc-expected-range fn-lbc-loc0 fn-lbc-loc1))))
; END LB resume9 generated served domain proofs
