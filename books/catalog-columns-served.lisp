; LB served reads.  The references stay unchanged and provide the logical
; target; the resident selector and stored-range worker own execution.
(in-package "ACL2")
(include-book "nntp-reader-compat")
(include-book "nntp-newnews")
(include-book "served-columns")
(include-book "catalog-number-index")
(include-book "log-locator-resolves")
(include-book "log-verified-map")

(defun fn-lb-served-log-invp (log fn-lb-vmap fn-lbc rows)
  (declare (xargs :stobjs (fn-lb-vmap fn-lbc) :verify-guards nil))
  (and (fn-lbc-corr fn-lbc rows log)
       (fn-lb-verified-invp log fn-lb-vmap)
       (fn-lc-locators-resolve fn-lbc log)))

(defun fn-lbc-article (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (fn-make-article (fn-lbc-msgid i fn-lbc) (fn-lbc-value i :handle fn-lbc)
                  (fn-lbc-groups i fn-lbc) (fn-lbc-numbers i fn-lbc)
                  t (fn-lbc-value i :stamp fn-lbc)))

(defun fn-lbc-id-article (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (fn-make-article (fn-lbc-msgid i fn-lbc) 0 nil nil t 0))

(defun fn-lbc-msgid-visible-last (seqs v fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (if (consp seqs)
      (let ((later (fn-lbc-msgid-visible-last (cdr seqs) v fn-lbc)))
        (if later later
          (if (fn-lbc-visiblep (car seqs) v fn-lbc) (car seqs) nil)))
    nil))

; Selection returns (:ROW I NUMBER UPDATEP GROUP), or (:REFUSAL TEXT).
; Neither the archive's article list nor payload bytes are traversed here.
(defun fn-lbc-select (session kind args v fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil)
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
  (declare (xargs :guard t :verify-guards nil) (ignore kind))
  (fn-nntp-make-result session
    (list (fn-nntp-reply-effect
      (append
        (fn-nntp-string-octets
          "403 article temporarily unavailable; cold read resources unavailable; try again later")
        '(32 40) (fn-lb-unverified-target session args) '(41 13 10))))))

(defun fn-lbc-selected-reads-entry-p (selected kind server v fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
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
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil)
           (ignore archive arts))
  (let* ((selected (fn-lbc-select session kind args v fn-lbc))
         (i (cadr selected)))
    (and (fn-lbc-selected-reads-entry-p selected kind server v fn-lbc)
         (equal seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
         (equal entry (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))))))

(defun fn-lb-log-model-unwire (bytes startp)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp bytes)
      (if (and startp (eql (car bytes) 46) (eql (cadr bytes) 46))
          (cons 46 (fn-lb-log-model-unwire (cddr bytes) nil))
        (cons (car bytes) (fn-lb-log-model-unwire (cdr bytes) (eql (car bytes) 10))))
    nil))

; The full API also gives a logical answer for an arbitrary server value.
; Such a prefix can contain a separator or malformed framing.  Keep that
; case explicit; the typed served server uses the resident section arm.
(defun fn-lbc-arbitrary-prefix-reply (session article number kind updatep group server i fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
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
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
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
  (declare (xargs :stobjs (fn-lb-vmap fn-arena fn-lbc) :guard t :verify-guards nil)
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
  (declare (xargs :stobjs fn-lbc :guard t
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
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (fn-lb-locators-in-log-from 0 fn-lbc log))

; The bytes at every row's locator equal its expected stored range:
; article wire octets, or raw reclaimed tombstone octets.
(defun fn-lb-log-binds-payloads-from (i rows fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard t :measure (acl2-count rows)
                  :verify-guards nil))
  (if (consp rows)
      (let ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)))
        (and (equal (fn-lb-log-model-read-range (fn-loc-segment a b)
                      (fn-loc-offset a b) (fn-loc-len a b) log)
                    (fn-lc-expected-range (fn-lb-log-payload (car rows) log)))
             (fn-lb-log-binds-payloads-from (+ 1 (nfix i)) (cdr rows) fn-lbc log)))
    t))

(defun fn-lb-log-binds-payloads (fn-lbc rows log)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (fn-lb-log-binds-payloads-from 0 rows fn-lbc log))
