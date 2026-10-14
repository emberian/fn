; Full API retrieval refinement. Frozen LB5 hypotheses remain unchanged.
(in-package "ACL2")
(include-book "catalog-columns-framing")
(include-book "catalog-columns-range")

(local (defthm fn-lbr11-id-article-is-full-identifier
 (and (equal (fn-nntp-article-idp (fn-lbc-id-article i fn-lbc)) (fn-nntp-article-idp (fn-lbc-article i fn-lbc)))
      (equal (fn-nntp-retrieval-initial kind number (fn-lbc-id-article i fn-lbc))
             (fn-nntp-retrieval-initial kind number (fn-lbc-article i fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-id-article fn-lbc-article fn-nntp-article-idp fn-nntp-retrieval-initial fn-article-msgid-of-fn-make-article))))))

(local (defthm fn-lbr11-row-corr-reply-metadata
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
 (and (equal (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc) (fn-rcl-tombstonep (fn-lb-log-payload row log)))
      (equal (fn-lbc-directory-value i :framed fn-lbc) (fn-nntp-framed-of-bytes (fn-lb-log-payload row log)))
      (equal (fn-lbc-xref-shift-prefix i fn-lbc) (fn-lb-xref-shift-prefix (fn-lb-log-payload row log)))
      (equal (fn-lb-log-model-read-range (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))
                    (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))
                    (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)) log)
             (if (fn-rcl-tombstonep (fn-lb-log-payload row log))
                 (fn-la-tombstone-raw (fn-lb-log-payload row log)) (fn-la-payload-wire (fn-lb-log-payload row log))))))
 :hints (("Goal" :in-theory '(fn-lbc-row-corr)))))

(local (defthm fn-lbr11-log-payload-octets
 (implies (and (fn-cat$ap rows) (fn-arena-p fn-arena) (fn-lb-arena-is-log fn-arena rows log) (natp i) (< i (len rows)))
 (fn-octet-listp (fn-lb-log-payload (nth i rows) log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-cat-rowp-of-nth-of-rowsp (xs rows))
       (:instance fn-cat-rowp-fields (h (nth i rows)))
       (:instance fn-scol-handle-bytes-octets (article (fn-cat-row-article i fn-arena rows)))
       (:instance fn-lbc-row-article-bytes-are-log-payload))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat$ap fn-lbc-row-article-fields))))))

(local (defthm fn-lbr11-octets-proper
 (implies (fn-octet-listp bytes) (true-listp bytes))
 :hints (("Goal" :induct (len bytes) :in-theory (union-theories (theory 'ground-zero) '(fn-octet-listp true-listp))))))

(local (defthm fn-lbr11-proper-fix
 (implies (true-listp bytes) (equal (true-list-fix bytes) bytes))
 :hints (("Goal" :induct (len bytes) :in-theory (union-theories (theory 'ground-zero) '(true-list-fix true-listp))))))

(local (defthm fn-lbr11-arbitrary-prefix-reply-is-reference
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
 (fn-arena-p fn-arena) (fn-lb-arena-is-log fn-arena rows log) (natp i) (< i (len rows))
 (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)))
 (equal (fn-lbc-arbitrary-prefix-reply session (fn-lbc-article i fn-lbc) number kind updatep group server i fn-lbc log)
        (fn-rcompat-article-reply-exec session (fn-lbc-article i fn-lbc) number kind updatep group server fn-arena)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-corresponding-row-at-index)
       (:instance fn-lbr11-row-corr-reply-metadata (row (nth i rows)) (pm (fn-lbc-value i :prefix-max fn-lbc)))
       (:instance fn-lbc-article-is-row-article)
       (:instance fn-lbc-row-article-bytes-are-log-payload)
       (:instance fn-lbr11-log-payload-octets)
       (:instance fn-lb-log-model-unwire-is-wire-inverse (payload (fn-lb-log-payload (nth i rows) log)) (startp t)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-arbitrary-prefix-reply fn-rcompat-article-reply-exec fn-la-payload-wire fn-lbr11-octets-proper fn-lbr11-proper-fix))))))

(local (defthm fn-lbr11-typed-resident-reply-is-reference
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
 (fn-arena-p fn-arena) (fn-lb-arena-is-log fn-arena rows log)
 (natp (nth 1 selected)) (< (nth 1 selected) (len rows))
 (or (null server) (fn-xref-serverp server)))
 (equal (fn-lbc-resident-reply session selected kind server fn-lbc log)
 (fn-rcompat-article-reply-exec session (fn-lbc-article (nth 1 selected) fn-lbc)
 (nth 2 selected) kind (nth 3 selected) (nth 4 selected) server fn-arena)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-corresponding-row-at-index (i (nth 1 selected)))
       (:instance fn-lbr11-row-corr-reply-metadata (i (nth 1 selected)) (row (nth (nth 1 selected) rows)) (pm (fn-lbc-value (nth 1 selected) :prefix-max fn-lbc)))
       (:instance fn-lbr11-id-article-is-full-identifier (i (nth 1 selected)) (number (nth 2 selected)))
       (:instance fn-lbc-article-is-row-article (i (nth 1 selected)))
       (:instance fn-lbc-row-article-bytes-are-log-payload (i (nth 1 selected)))
       (:instance fn-lbc-stored-range-is-wire-section (i (nth 1 selected)) (kind (if (member-equal kind '(:article :head)) kind :body)))
       (:instance fn-lb-rcompat-typed-reply-is-prefixed-response (article (fn-lbc-article (nth 1 selected) fn-lbc))
        (number (nth 2 selected)) (updatep (nth 3 selected)) (group (nth 4 selected)))
       (:instance fn-lb-rcompat-prefixed-response-is-resident-construction
        (article (fn-lbc-article (nth 1 selected) fn-lbc)) (payload (fn-lb-log-payload (nth (nth 1 selected) rows) log))
        (number (nth 2 selected)) (updatep (nth 3 selected)) (group (nth 4 selected))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-resident-reply nth member-equal))))))

(local (defthm fn-lbr11-reference-base-cases
 (and
 (implies (not (fn-nntp-article-idp article))
 (equal (fn-rcompat-article-reply-exec session article number kind updatep group server fn-arena)
 (fn-nntp-single session "503 stored article identifier unavailable")))
 (implies (and (fn-nntp-article-idp article) (fn-rcl-tombstonep (fn-nntp-article-bytes article fn-arena)))
 (equal (fn-rcompat-article-reply-exec session article number kind updatep group server fn-arena)
 (fn-nntp-single session (if updatep "423 article reclaimed" "430 article reclaimed"))))
 (implies (and (fn-nntp-article-idp article) (not (fn-rcl-tombstonep (fn-nntp-article-bytes article fn-arena))) (equal kind :stat))
 (equal (fn-rcompat-article-reply-exec session article number kind updatep group server fn-arena)
 (fn-nntp-make-result (if updatep (fn-nntp-set-cursor session group number) session)
 (list (fn-nntp-reply-effect (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-rcompat-served-payload-preserves-tombstone (payload (fn-nntp-article-bytes article fn-arena))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-rcompat-article-reply-exec fn-nntp-article-response-of-bytes fn-nntp-response-okp-of-bytes fn-nntp-result-session fn-nntp-make-result fn-nntp-single))))))

(defthm fn-lbc-resident-reply-is-rcompat-article-reply
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
 (fn-arena-p fn-arena) (fn-lb-arena-is-log fn-arena rows log)
 (natp (nth 1 selected)) (< (nth 1 selected) (len rows)))
 (equal (fn-lbc-resident-reply session selected kind server fn-lbc log)
 (fn-rcompat-article-reply session (fn-lbc-article (nth 1 selected) fn-lbc)
 (nth 2 selected) kind (nth 3 selected) (nth 4 selected) server fn-arena)))
 :hints (("Goal" :do-not-induct t :cases ((or (null server) (fn-xref-serverp server)))
 :use ((:instance fn-lbr11-typed-resident-reply-is-reference)
       (:instance fn-lbc-corresponding-row-at-index (i (nth 1 selected)))
       (:instance fn-lbr11-row-corr-reply-metadata (i (nth 1 selected)) (row (nth (nth 1 selected) rows)) (pm (fn-lbc-value (nth 1 selected) :prefix-max fn-lbc)))
       (:instance fn-lbr11-id-article-is-full-identifier (i (nth 1 selected)) (number (nth 2 selected)))
       (:instance fn-lbc-article-is-row-article (i (nth 1 selected)))
       (:instance fn-lbc-row-article-bytes-are-log-payload (i (nth 1 selected)))
       (:instance fn-lbr11-arbitrary-prefix-reply-is-reference
        (i (nth 1 selected)) (number (nth 2 selected)) (updatep (nth 3 selected)) (group (nth 4 selected)))
       (:instance fn-lbr11-reference-base-cases (article (fn-lbc-article (nth 1 selected) fn-lbc))
        (number (nth 2 selected)) (updatep (nth 3 selected)) (group (nth 4 selected)))
       (:instance fn-rcompat-article-reply-exec-is-the-reply (article (fn-lbc-article (nth 1 selected) fn-lbc))
        (number (nth 2 selected)) (updatep (nth 3 selected)) (group (nth 4 selected))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-resident-reply nth member-equal)))))

(local (defthm fn-lbr11-select-has-result-tag
 (let ((selected (fn-lbc-select session kind args v fn-lbc)))
 (or (equal (car selected) :refusal) (equal (car selected) :row)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-select))))))

(local (defthm fn-lbc-corresponding-entry-trailer-is-valid
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log) (natp i) (< i (len rows)))
 (fn-arx-entry-ok (fn-lb-entry-octets (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))
                                   (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)) log)
                  (fn-lb-entry-protected-len (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))
                                   (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)) log)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-corresponding-row-at-index))
 :in-theory '(fn-lbc-row-corr)))))

(defthm fn-lbc-retrieval-is-rcompat-retrieval
  (implies (and (fn-lbc-p fn-lbc) (fn-lb-vmap-p fn-lb-vmap) (fn-cat$ap rows)
                (fn-arena-p fn-arena) (fn-scol-okp fn-arena rows)
                (fn-lb-arena-is-log fn-arena rows log)
                (fn-lb-served-log-invp log fn-lb-vmap fn-lbc rows)
                (fn-cnx-freshp rows)
                (equal arts (fn-state-articles archive))
                (equal arts (fn-cat-view-articles v fn-arena rows)))
           (equal (fn-lbc-retrieval session archive arts kind args server v log fn-lb-vmap fn-arena fn-lbc)
                  (fn-rcompat-retrieval session archive arts kind args server fn-arena)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-select-has-result-tag)
       (:instance fn-lbc-select-row-is-in-range)
       (:instance fn-lbc-corr-count-is-length)
       (:instance fn-lbc-corresponding-entry-trailer-is-valid (i (cadr (fn-lbc-select session kind args v fn-lbc))))
       (:instance fn-lbc-resident-reply-is-rcompat-article-reply (selected (fn-lbc-select session kind args v fn-lbc)))
       (:instance fn-lbc-selector-reference-dispatch))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-served-log-invp fn-lbc-retrieval nth)))))
