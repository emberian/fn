; Counts derived from the actual executed served reader bodies.
(in-package "ACL2")
(include-book "catalog-columns-served")
(include-book "def-cost")

(def-cost fn-lbc-stored-range
 :unaccounted (fn-lb-log-model-read-range fn-lbc-directory-value fn-lbc-flag fn-lbc-value fn-nntp-stuffed-section)
 :calls ((range-requests (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets))
         (entry-reads (fn-lb-entry-octets))
         (range-bytes (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets) :argument 2)
         (range-offsets (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets) :argument 1)))

(def-cost fn-lbc-arbitrary-prefix-reply
 :unaccounted (fn-lb-log-model-read-range fn-lb-log-model-unwire fn-nntp-article-response-of-bytes fn-nntp-response-okp-of-bytes fn-rcompat-served-payload-of-bytes)
 :calls ((range-requests (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets))
         (entry-reads (fn-lb-entry-octets))
         (range-bytes (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets) :argument 2)
         (range-offsets (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets) :argument 1)))

(def-cost fn-lbc-resident-reply
 :unaccounted (fn-lb-log-model-read-range fn-lb-log-model-unwire fn-lbc-article fn-lbc-directory-value fn-lbc-flag fn-lbc-id-article fn-lbc-value fn-lbc-xref-shift-prefix fn-nntp-article-idp fn-nntp-article-response-of-bytes fn-nntp-crlf fn-nntp-response-okp-of-bytes fn-nntp-retrieval-initial fn-nntp-single fn-nntp-stuffed-section fn-rcompat-served-payload-of-bytes fn-xref-field fn-xref-pairs fn-xref-serverp)
 :calls ((range-requests (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets))
         (entry-reads (fn-lb-entry-octets))
         (range-bytes (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets) :argument 2)
         (range-offsets (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets) :argument 1)))

(def-cost fn-lbc-retrieval
 :unaccounted (fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len fn-lb-log-model-read-range fn-lb-log-model-unwire fn-lb-unverified-refusal fn-lbc-article fn-lbc-directory-value fn-lbc-flag fn-lbc-id-article fn-lbc-select fn-lbc-selected-reads-entry-p fn-lbc-value fn-lbc-xref-shift-prefix fn-nntp-article-idp fn-nntp-article-response-of-bytes fn-nntp-crlf fn-nntp-response-okp-of-bytes fn-nntp-retrieval-initial fn-nntp-single fn-nntp-stuffed-section fn-rcompat-served-payload-of-bytes fn-xref-field fn-xref-pairs fn-xref-serverp)
 :calls ((range-requests (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets))
         (entry-reads (fn-lb-entry-octets))
         (range-bytes (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets) :argument 2)
         (range-offsets (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets) :argument 1)))

(defthm fn-lbc-stored-range-at-most-one-request
 (<= (fn-lbc-stored-range-range-requests i kind fn-lbc-v log) 1)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-stored-range-range-requests)))))

(defthm fn-lbc-arbitrary-prefix-one-request
 (equal (fn-lbc-arbitrary-prefix-reply-range-requests session article number kind updatep group server i fn-lbc-v log) 1)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-arbitrary-prefix-reply-range-requests)))))

(defthm fn-lbc-resident-reply-at-most-one-request
 (<= (fn-lbc-resident-reply-range-requests session selected kind server fn-lbc-v log) 1)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-resident-reply-range-requests fn-lbc-arbitrary-prefix-one-request fn-lbc-stored-range-at-most-one-request)))))

(defthm fn-lbc-retrieval-at-most-one-range-request
 (<= (fn-lbc-retrieval-range-requests session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 1)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-retrieval-range-requests fn-lbc-resident-reply-at-most-one-request)))))

(defthm fn-lbc-selected-stat-never-reads-entry
 (not (fn-lbc-selected-reads-entry-p selected :stat server v fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-selected-reads-entry-p)))))

(defthm fn-lbc-resident-stat-no-range-request
 (equal (fn-lbc-resident-reply-range-requests session selected :stat server fn-lbc-v log) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-resident-reply-range-requests)))))

(defthm fn-lbc-stat-no-range-request
 (equal (fn-lbc-retrieval-range-requests session archive arts :stat args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-retrieval-range-requests fn-lbc-resident-stat-no-range-request fn-lbc-selected-stat-never-reads-entry)))))

(defthm fn-lbc-stored-range-no-entry-read
 (equal (fn-lbc-stored-range-entry-reads i kind fn-lbc-v log) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-stored-range-entry-reads)))))

(defthm fn-lbc-arbitrary-prefix-reply-no-entry-read
 (equal (fn-lbc-arbitrary-prefix-reply-entry-reads session article number kind updatep group server i fn-lbc-v log) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-arbitrary-prefix-reply-entry-reads)))))

(defthm fn-lbc-resident-reply-no-entry-read
 (equal (fn-lbc-resident-reply-entry-reads session selected kind server fn-lbc-v log) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-resident-reply-entry-reads)))))

(defthm fn-lbc-retrieval-at-most-one-entry-read
 (<= (fn-lbc-retrieval-entry-reads session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 1)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-retrieval-entry-reads fn-lbc-resident-reply-no-entry-read)))))

(defthm fn-lbc-stat-no-entry-read
 (equal (fn-lbc-retrieval-entry-reads session archive arts :stat args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-retrieval-entry-reads fn-lbc-selected-stat-never-reads-entry fn-lbc-resident-reply-no-entry-read)))))


(def-cost-check fn-lbc-stored-range)
(def-cost-check fn-lbc-arbitrary-prefix-reply)
(def-cost-check fn-lbc-resident-reply)
(def-cost-check fn-lbc-retrieval)
(defthm fn-lbc-stored-range-exact-request-length
 (equal (fn-lbc-stored-range-range-bytes i kind fn-lbc-v log)
 (cond ((fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc-v) (nfix (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))))
       ((equal kind :article) (if (fn-lbc-directory-value i :article-ok fn-lbc-v) (nfix (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))) 0))
       ((equal kind :head) (if (fn-lbc-directory-value i :head-ok fn-lbc-v) (nfix (fn-lbc-value i :head-length fn-lbc-v)) 0))
       (t (if (fn-lbc-directory-value i :body-ok fn-lbc-v) (nfix (- (- (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (nfix (fn-lbc-directory-value i :raw-head-length fn-lbc-v))) 2)) 0))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-stored-range-range-bytes nfix)))))

(defthm fn-lbc-stored-range-exact-request-offset
 (equal (fn-lbc-stored-range-range-offsets i kind fn-lbc-v log)
 (cond ((fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc-v) (nfix (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))))
       ((equal kind :article) (if (fn-lbc-directory-value i :article-ok fn-lbc-v) (nfix (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))) 0))
       ((equal kind :head) (if (fn-lbc-directory-value i :head-ok fn-lbc-v) (nfix (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))) 0))
       (t (if (fn-lbc-directory-value i :body-ok fn-lbc-v) (nfix (+ (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (nfix (fn-lbc-directory-value i :raw-head-length fn-lbc-v)) 2)) 0))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-stored-range-range-offsets nfix)))))

(defthm fn-lbc-head-exact-request-length
 (implies (and (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc-v)) (fn-lbc-directory-value i :head-ok fn-lbc-v))
 (equal (fn-lbc-stored-range-range-bytes i :head fn-lbc-v log) (nfix (fn-lbc-value i :head-length fn-lbc-v))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-stored-range-exact-request-length)))))

(defthm fn-lbc-body-exact-request-length
 (implies (and (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc-v)) (fn-lbc-directory-value i :body-ok fn-lbc-v))
 (equal (fn-lbc-stored-range-range-bytes i :body fn-lbc-v log) (nfix (- (- (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (nfix (fn-lbc-directory-value i :raw-head-length fn-lbc-v))) 2))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-stored-range-exact-request-length)))))

(defthm fn-lbc-resident-stat-zero-range-bytes
 (equal (fn-lbc-resident-reply-range-bytes session selected :stat server fn-lbc-v log) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-resident-reply-range-bytes)))))

(defthm fn-lbc-stat-zero-range-bytes
 (equal (fn-lbc-retrieval-range-bytes session archive arts :stat args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-retrieval-range-bytes fn-lbc-resident-stat-zero-range-bytes fn-lbc-selected-stat-never-reads-entry)))))

(defthm fn-lbc-resident-stat-zero-range-offsets
 (equal (fn-lbc-resident-reply-range-offsets session selected :stat server fn-lbc-v log) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-resident-reply-range-offsets)))))

(defthm fn-lbc-stat-zero-range-offsets
 (equal (fn-lbc-retrieval-range-offsets session archive arts :stat args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-retrieval-range-offsets fn-lbc-resident-stat-zero-range-offsets fn-lbc-selected-stat-never-reads-entry)))))


; A refusal, a reclaimed row, and a withdrawn current article never ask for bytes.
(defthm fn-lbc-retrieval-refusal-reads-nothing
 (implies (equal (car (fn-lbc-select session kind args v fn-lbc-v)) :refusal)
  (and (equal (fn-lbc-retrieval-range-requests session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)
       (equal (fn-lbc-retrieval-entry-reads session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-retrieval-range-requests fn-lbc-retrieval-entry-reads)))))

(defthm fn-lbc-retrieval-reclaimed-reads-nothing
 (implies (fn-lbc-flag (cadr (fn-lbc-select session kind args v fn-lbc-v)) *fn-lbc-reclaimed-bit* fn-lbc-v)
  (and (equal (fn-lbc-retrieval-range-requests session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)
       (equal (fn-lbc-retrieval-entry-reads session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-retrieval-range-requests fn-lbc-retrieval-entry-reads
    fn-lbc-selected-reads-entry-p fn-lbc-resident-reply-range-requests fn-lbc-resident-reply-no-entry-read)))))

(defthm fn-lbc-retrieval-withdrawn-reads-nothing
 (implies (not (fn-lbc-visiblep
   (fn-lbc-number-get (fn-nntp-session-group session) (fn-nntp-session-current session) fn-lbc-v) v fn-lbc-v))
  (and (equal (fn-lbc-retrieval-range-requests session archive arts kind nil server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)
       (equal (fn-lbc-retrieval-entry-reads session archive arts kind nil server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-select fn-lbc-retrieval-range-requests fn-lbc-retrieval-entry-reads)))))

(defthm fn-lbc-retrieval-warm-no-entry-read
 (implies (fn-lb-verified-bit
   (fn-loc-segment (fn-lbc-loc0 (cadr (fn-lbc-select session kind args v fn-lbc-v)) fn-lbc-v)
                   (fn-lbc-loc1 (cadr (fn-lbc-select session kind args v fn-lbc-v)) fn-lbc-v))
   (fn-loc-offset (fn-lbc-loc0 (cadr (fn-lbc-select session kind args v fn-lbc-v)) fn-lbc-v)
                  (fn-lbc-loc1 (cadr (fn-lbc-select session kind args v fn-lbc-v)) fn-lbc-v)) fn-lb-vmap-v)
  (equal (fn-lbc-retrieval-entry-reads session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-retrieval-entry-reads fn-lbc-resident-reply-no-entry-read)))))
