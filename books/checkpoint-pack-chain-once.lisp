; fn: each pack-chain link decoded once per open (lane open-by-index,
; 2026-09-26; PKT-168 (3); PRF-219).
;
; An open walked and decoded every link of the selected chain several times:
; `fnn-pack-lower-bound' (host/native/checkpoint.lisp) walks the chain with
; `fn-ccc-entry-step' (a full decode of each link, its events decoded in
; `fn-ccc-linkp') and then asks `fn-ccc-coverage-chain', which decodes every
; link again and re-runs `fn-ccc-linkp' on each in `fn-ccc-links-okp'; a full
; replay calls the lower bound twice and then `fnn-pack-recover-records',
; which walks, covers and observes (`fn-ccc-observe-chain', a fourth decode).
; Every decode of a link is a full decode of the Store events it packs, as
; octet lists (planning/evidence/pack-chain-open-2026-09-26.md item 3;
; served-path-scale-2's reading of the 20,000-article open: 30 percent).
;
; Here the decode of a link is MEMOIZED by content: MEMO is a list of
; (FRAMED DIGEST MAX RESULT) with RESULT = (fn-ccc-framed-link FRAMED DIGEST
; MAX), the invariant `fn-ccco-memo-soundp'.  The host keeps MEMO in the
; ACL2 global `fn-store-pack-memo' (host/checkpoint-host.lisp): the walk's
; step adds the link it decodes, the coverage and the observation read it,
; and the open clears it when it ends.  A lookup is `equal' on the link's
; octets, which on the host is EQ on the list the walk read (the same list is
; passed to the step and kept in the chain), and otherwise a comparison, never
; a decode.  And the chain check re-runs no event decode: every link a
; decode produced is a link (`fn-ccc-decode-link-is-a-link'), so over decoded
; entries `fn-ccc-links-okp' is its chaining conditions alone
; (`fn-ccco-links-okp-of-decoded').
;
; KEYSTONES (each the reference, for every input, under a sound memo; the
; memo starts empty and every step keeps it sound):
;   fn-ccco-entry-step-is-entry-step      the walk's step
;   fn-ccco-coverage-chain-is-coverage-chain
;   fn-ccco-observe-chain-is-observe-chain
; so the walk the host performs, its coverage and the open's reconstruction
; are the reference's decisions on every chain, corrupt ones included, and
; `fn-ccc-chain-reconstructs-the-history' (PRF-073's chain form) and the
; publication crash theorem over `fn-ccc-walk' transfer unchanged.

(in-package "ACL2")
(include-book "checkpoint-pack-chain")

(local
 (defthm fn-ccco-nth-0-of-cons
   (equal (fn-cc-nth 0 (cons a b)) a)
   :hints (("Goal" :in-theory (enable fn-cc-nth)))))

(local
 (defthm fn-ccco-nth-of-cons
   (implies (not (zp n))
            (equal (fn-cc-nth n (cons a b)) (fn-cc-nth (1- n) b)))
   :hints (("Goal" :in-theory (enable fn-cc-nth)))))

; -----------------------------------------------------------------------------
; The memo.

(defun fn-ccco-memo-soundp (memo)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp memo)
      (let ((e (car memo)))
        (and (equal (fn-cc-nth 3 e)
                    (fn-ccc-framed-link (fn-cc-nth 0 e) (fn-cc-nth 1 e) (fn-cc-nth 2 e)))
             (fn-ccco-memo-soundp (cdr memo))))
    t))

; The remembered result for (FRAMED DIGEST MAX), or NIL (every result of
; `fn-ccc-framed-link' is a cons, so NIL is never a remembered result).
(defun fn-ccco-lookup (framed digest max memo)
  (declare (xargs :guard t))
  (if (consp memo)
      (let ((e (car memo)))
        (if (and (equal (fn-cc-nth 0 e) framed)
                 (equal (fn-cc-nth 1 e) digest)
                 (equal (fn-cc-nth 2 e) max))
            (fn-cc-nth 3 e)
          (fn-ccco-lookup framed digest max (cdr memo))))
    nil))

(defthm fn-ccc-framed-link-consp
  (consp (fn-ccc-framed-link framed digest max))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-ccc-framed-link fn-ccc-decode-link))))

(defthm fn-ccco-lookup-of-sound
  (implies (and (fn-ccco-memo-soundp memo)
                (fn-ccco-lookup framed digest max memo))
           (equal (fn-ccco-lookup framed digest max memo)
                  (fn-ccc-framed-link framed digest max))))

(in-theory (disable fn-ccc-framed-link))

; -----------------------------------------------------------------------------
; A link's decode, recognizing each packed event once.  `fn-cc-octet-event-listp'
; (books/checkpoint-compaction.lisp), inside `fn-ccc-linkp', reads each
; decoded event's sequence, txid (three times) and generation through the
; kind dispatchers of books/store-events.lisp, each of which re-runs the
; event recognizers from the first (`fn-record-p' walks the payload): six
; recognitions per event, 25 percent of the 20,000-article open
; (planning/evidence/open-by-index-2026-09-26.md).  The twin reads the three
; fields in one dispatch.

(defun fn-ccco-event-fields (x)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p x)
         (list t (fn-record-sequence x) (fn-record-txid x) (fn-record-generation x)))
        ((fn-store-retention-event-p x)
         (list t (fn-store-event-nth 2 x) (fn-store-event-nth 3 x) (fn-store-event-nth 4 x)))
        ((fn-stxe-p x) (list t (fn-stxe-sequence x) (fn-stxe-txid x) (fn-stxe-generation x)))
        ((fn-stxk-p x) (list t (fn-stxk-sequence x) (fn-stxk-txid x) (fn-stxk-generation x)))
        ((fn-stxa-p x) (list t (fn-stxa-sequence x) (fn-stxa-txid x) (fn-stxa-generation x)))
        ((fn-cpe-eventp x) (list t (fn-cpe-sequence x) (fn-cpe-txid x) (fn-cpe-generation x)))
        ((fn-th-topic-eventp x) (list t (fn-th-at 1 x) (fn-th-at 2 x) (fn-th-at 3 x)))
        (t (list nil nil nil nil))))

(defthm fn-ccco-event-fields-are-the-dispatchers
  (equal (fn-ccco-event-fields x)
         (list (if (fn-store-event-p x) t nil) (fn-store-event-sequence x)
               (fn-store-event-txid x) (fn-store-event-generation x)))
  :hints (("Goal" :in-theory (e/d (fn-store-event-p fn-store-event-sequence
                                   fn-store-event-txid fn-store-event-generation)
                                  (fn-record-p fn-store-retention-event-p fn-stxe-p
                                   fn-stxk-p fn-stxa-p fn-cpe-eventp fn-th-topic-eventp)))))

(in-theory (disable fn-ccco-event-fields))

(defun fn-ccco-octet-event-listp (octet-events sequence lower-frontier upper-frontier)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp octet-events)
      (let* ((decoded (fn-store-event-decode-exact (car octet-events)))
             (f (fn-ccco-event-fields (fn-cc-nth 1 decoded)))
             (txid (fn-cc-nth 2 f)))
        (and (fn-cbor-octet-listp (car octet-events))
             (equal (car decoded) :ok)
             (fn-cc-nth 0 f)
             (equal (fn-cc-nth 1 f) sequence)
             (equal txid (fn-cc-nth 3 f))
             (<= lower-frontier txid)
             (< txid upper-frontier)
             (fn-ccco-octet-event-listp (cdr octet-events) (+ 1 sequence)
                                        (+ 1 txid) upper-frontier)))
    (null octet-events)))

(defthm fn-ccco-octet-event-listp-is-octet-event-listp
  (equal (fn-ccco-octet-event-listp evs sequence lf uf)
         (fn-cc-octet-event-listp evs sequence lf uf))
  :hints (("Goal" :induct (fn-cc-octet-event-listp evs sequence lf uf)
           :in-theory (e/d (fn-cc-octet-event-listp)
                           (fn-store-event-decode-exact fn-store-event-p
                            fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation)))))

(defun fn-ccco-linkp (l)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp l) (equal (len l) 9)
       (equal (fn-cc-nth 0 l) :fn-pack-link)
       (equal (fn-cc-nth 1 l) 1)
       (fn-record-uint32p (fn-ccc-lower l))
       (fn-record-uint32p (fn-ccc-boundary l))
       (fn-record-uint32p (fn-ccc-lower-frontier l))
       (fn-record-uint32p (fn-ccc-frontier l))
       (fn-record-uint32p (fn-ccc-pred-generation l))
       (fn-cbor-octet-listp (fn-ccc-pred-digest l))
       (< (fn-ccc-lower l) (fn-ccc-boundary l))
       (<= (fn-ccc-lower-frontier l) (fn-ccc-frontier l))
       (equal (len (fn-ccc-events l))
              (- (fn-ccc-boundary l) (fn-ccc-lower l)))
       (fn-ccco-octet-event-listp (fn-ccc-events l) (fn-ccc-lower l)
                                  (fn-ccc-lower-frontier l) (fn-ccc-frontier l))))

(defthm fn-ccco-linkp-is-linkp
  (equal (fn-ccco-linkp l) (fn-ccc-linkp l))
  :hints (("Goal" :in-theory (e/d (fn-ccc-linkp) (fn-cc-octet-event-listp)))))

(in-theory (disable fn-ccco-linkp))

(defun fn-ccco-decode-link (octets max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp octets)) (not (natp max-octets))
          (< max-octets (len octets)))
      (list :error :octets)
    (let ((v0 (fn-cc-decode-exact octets)))
      (if (equal (car v0) :ok)
          (let ((l (fn-ccc-link-of-summary (fn-cc-nth 1 v0))))
            (if (fn-ccco-linkp l) (list :ok l) (list :error :summary)))
        (let ((header (fn-stmt-decode-prefix-items-bounded
                       9 octets max-octets max-octets)))
          (if (not (equal (car header) :ok))
              (list :error :header)
            (let ((v (fn-cc-nth 1 header)))
              (if (or (not (equal (fn-cc-nth 0 v) (cons :bytes *fn-cc-magic*)))
                      (not (equal (fn-cc-nth 1 v) (cons :uint *fn-ccc-version*)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 2 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 3 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 4 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 5 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 6 v)))
                      (not (fn-ccc-bytes-itemp (fn-cc-nth 7 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 8 v)))
                      (< *fn-cc-max-events* (cdr (fn-cc-nth 8 v))))
                  (list :error :header)
                (let* ((body (fn-stmt-decode-prefix-items-bounded
                              (cdr (fn-cc-nth 8 v)) (fn-cc-nth 2 header)
                              max-octets max-octets))
                       (events (if (equal (car body) :ok)
                                   (fn-cc-values-event-octets (fn-cc-nth 1 body))
                                 :bad))
                       (l (fn-ccc-make (cdr (fn-cc-nth 2 v)) (cdr (fn-cc-nth 3 v))
                                       (cdr (fn-cc-nth 4 v)) (cdr (fn-cc-nth 5 v))
                                       (cdr (fn-cc-nth 6 v)) (cdr (fn-cc-nth 7 v))
                                       events)))
                  (if (or (not (equal (car body) :ok))
                          (consp (fn-cc-nth 2 body))
                          (equal events :bad)
                          (not (fn-ccco-linkp l)))
                      (list :error :link)
                    (list :ok l)))))))))))

(defthm fn-ccco-decode-link-is-decode-link
  (equal (fn-ccco-decode-link octets max-octets)
         (fn-ccc-decode-link octets max-octets))
  :hints (("Goal" :in-theory (e/d (fn-ccc-decode-link)
                                  (fn-ccc-linkp fn-cc-decode-exact)))))

(defun fn-ccco-framed-link-fast (framed digest max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp framed))
          (< (len framed) *fn-frame-trailer-octets*))
      (list :error :frame)
    (let ((n (- (len framed) *fn-frame-trailer-octets*)))
      (if (not (equal (nthcdr n framed) digest))
          (list :error :integrity)
        (fn-ccco-decode-link (take n framed) max-octets)))))

(defthm fn-ccco-framed-link-fast-is-framed-link
  (equal (fn-ccco-framed-link-fast framed digest max)
         (fn-ccc-framed-link framed digest max))
  :hints (("Goal" :in-theory (e/d (fn-ccc-framed-link) (fn-ccco-decode-link fn-ccc-decode-link)))))

(in-theory (disable fn-ccco-framed-link-fast fn-ccco-decode-link))

; A link's decode, from the memo when it holds it.
(defun fn-ccco-framed-link (framed digest max memo)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-ccco-lookup framed digest max memo)
      (fn-ccco-framed-link-fast framed digest max)))

(defthm fn-ccco-framed-link-is-framed-link
  (implies (fn-ccco-memo-soundp memo)
           (equal (fn-ccco-framed-link framed digest max memo)
                  (fn-ccc-framed-link framed digest max))))

; The memo after the walk decoded FRAMED: unchanged on a hit.
(defun fn-ccco-remember (framed digest max memo)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-ccco-lookup framed digest max memo)
      memo
    (cons (list framed digest max (fn-ccco-framed-link-fast framed digest max)) memo)))

(defthm fn-ccco-remember-keeps-sound
  (implies (fn-ccco-memo-soundp memo)
           (fn-ccco-memo-soundp (fn-ccco-remember framed digest max memo)))
  :hints (("Goal" :do-not-induct t :expand ((:free (e m) (fn-ccco-memo-soundp (cons e m)))))))

(defthm fn-ccco-memo-soundp-of-nil
  (fn-ccco-memo-soundp nil))

; Every link of a walked chain (newest first, (GENERATION FRAMED DIGEST)
; each), remembered: the coverage's form (host `fn-store-checkpoint-chain-
; coverage'), so a chain extended by a compaction is decoded once too.
(defun fn-ccco-remember-all (chain max memo)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp chain)
      (fn-ccco-remember-all
       (cdr chain) max
       (fn-ccco-remember (fn-cc-nth 1 (car chain)) (fn-cc-nth 2 (car chain)) max memo))
    memo))

(defthm fn-ccco-remember-all-keeps-sound
  (implies (fn-ccco-memo-soundp memo)
           (fn-ccco-memo-soundp (fn-ccco-remember-all chain max memo)))
  :hints (("Goal" :in-theory (disable fn-ccco-remember))))

(in-theory (disable fn-ccco-framed-link fn-ccco-remember fn-ccco-lookup))

; -----------------------------------------------------------------------------
; The walk's step (host: `fn-store-checkpoint-chain-step').

(defun fn-ccco-entry-step (framed digest max memo)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-ccco-framed-link framed digest max memo)))
    (if (not (equal (car d) :ok)) d
      (list :ok (fn-ccc-lower (cadr d)) (fn-ccc-pred-generation (cadr d))))))

(defthm fn-ccco-entry-step-is-entry-step
  (implies (fn-ccco-memo-soundp memo)
           (equal (fn-ccco-entry-step framed digest max memo)
                  (fn-ccc-entry-step framed digest max)))
  :hints (("Goal" :in-theory (enable fn-ccc-entry-step))))

; -----------------------------------------------------------------------------
; The entries, from the memo.

(defun fn-ccco-decode-entries (framed max memo)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp framed)
      (let* ((e (car framed))
             (d (fn-ccco-framed-link (fn-cc-nth 1 e) (fn-cc-nth 2 e) max memo))
             (rest (fn-ccco-decode-entries (cdr framed) max memo)))
        (if (or (not (equal (car d) :ok)) (equal rest :bad))
            :bad
          (cons (list (fn-cc-nth 0 e) (cadr d) (fn-cc-nth 2 e)) rest)))
    (if (null framed) nil :bad)))

(defthm fn-ccco-decode-entries-is-decode-entries
  (implies (fn-ccco-memo-soundp memo)
           (equal (fn-ccco-decode-entries framed max memo)
                  (fn-ccc-decode-entries framed max)))
  :hints (("Goal" :in-theory (enable fn-ccc-decode-entries))))

; -----------------------------------------------------------------------------
; The chain check over decoded entries: the chaining conditions alone.

(defun fn-ccco-links-chainedp (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (let ((l (fn-ccc-entry-link (car entries))))
        (if (zp (fn-ccc-lower l))
            (and (equal (fn-ccc-lower-frontier l) 0)
                 (null (cdr entries)))
          (and (consp (cdr entries))
               (let ((p (cadr entries)))
                 (and (equal (fn-ccc-lower l)
                             (fn-ccc-boundary (fn-ccc-entry-link p)))
                      (equal (fn-ccc-lower-frontier l)
                             (fn-ccc-frontier (fn-ccc-entry-link p)))
                      (equal (fn-ccc-pred-generation l)
                             (fn-ccc-entry-generation p))
                      (equal (fn-ccc-pred-digest l)
                             (fn-ccc-entry-digest p))))
               (fn-ccco-links-chainedp (cdr entries)))))
    nil))

(defun fn-ccco-all-linksp (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (and (fn-ccc-linkp (fn-ccc-entry-link (car entries)))
           (fn-ccco-all-linksp (cdr entries)))
    t))

(defthm fn-ccc-framed-link-ok-is-a-link
  (implies (equal (car (fn-ccc-framed-link framed digest max)) :ok)
           (fn-ccc-linkp (cadr (fn-ccc-framed-link framed digest max))))
  :hints (("Goal" :in-theory (enable fn-ccc-framed-link))))

(defthm fn-ccco-decoded-entries-are-links
  (implies (not (equal (fn-ccc-decode-entries framed max) :bad))
           (fn-ccco-all-linksp (fn-ccc-decode-entries framed max)))
  :hints (("Goal" :in-theory (e/d (fn-ccc-decode-entries fn-ccc-entry-link)
                                  (fn-ccc-linkp)))))

(defthm fn-ccco-links-okp-of-all-links
  (implies (fn-ccco-all-linksp entries)
           (equal (fn-ccc-links-okp entries)
                  (fn-ccco-links-chainedp entries)))
  :hints (("Goal" :induct (fn-ccco-links-chainedp entries)
           :expand ((fn-ccc-links-okp entries) (fn-ccco-all-linksp entries)
                    (fn-ccco-links-chainedp entries))
           :in-theory (disable fn-ccc-linkp))))

(defthm fn-ccco-links-okp-of-decoded
  (implies (not (equal (fn-ccc-decode-entries framed max) :bad))
           (equal (fn-ccc-links-okp (fn-ccc-decode-entries framed max))
                  (fn-ccco-links-chainedp (fn-ccc-decode-entries framed max))))
  :hints (("Goal" :in-theory (disable fn-ccc-linkp fn-ccc-links-okp
                                      fn-ccco-links-chainedp fn-ccc-decode-entries))))

(in-theory (disable fn-ccco-all-linksp fn-ccco-links-okp-of-all-links))

; -----------------------------------------------------------------------------
; The coverage (host: `fn-store-checkpoint-chain-coverage') and the open's
; observation (`fn-store-checkpoint-chain-observe').

(defun fn-ccco-coverage-chain (framed observed-count frontier max memo)
  (declare (xargs :guard t :verify-guards nil))
  (let ((entries (fn-ccco-decode-entries framed max memo)))
    (cond ((equal entries :bad) '(:error :integrity))
          ((not (fn-ccco-links-chainedp entries)) '(:error :chain))
          (t (let ((summary (fn-ccc-chain-summary entries)))
               (if (or (< observed-count (fn-cc-sequence summary))
                       (< frontier (fn-cc-frontier summary)))
                   '(:error :coverage)
                 (list :ok (fn-cc-sequence summary) (fn-cc-frontier summary))))))))

(defthm fn-ccco-coverage-chain-is-coverage-chain
  (implies (fn-ccco-memo-soundp memo)
           (equal (fn-ccco-coverage-chain framed observed-count frontier max memo)
                  (fn-ccc-coverage-chain framed observed-count frontier max)))
  :hints (("Goal" :in-theory (e/d (fn-ccc-coverage-chain)
                                  (fn-ccc-decode-entries fn-ccc-links-okp
                                   fn-ccco-links-chainedp fn-ccco-decode-entries)))))

(defun fn-ccco-observe-chain (framed observed frontier max memo)
  (declare (xargs :guard t :verify-guards nil))
  (let ((entries (fn-ccco-decode-entries framed max memo)))
    (cond ((equal entries :bad) '(:error :integrity))
          ((not (fn-ccco-links-chainedp entries)) '(:error :chain))
          (t (fn-cc-recover-observation (fn-ccc-chain-summary entries)
                                        observed frontier)))))

(defthm fn-ccco-observe-chain-is-observe-chain
  (implies (fn-ccco-memo-soundp memo)
           (equal (fn-ccco-observe-chain framed observed frontier max memo)
                  (fn-ccc-observe-chain framed observed frontier max)))
  :hints (("Goal" :in-theory (e/d (fn-ccc-observe-chain)
                                  (fn-ccc-decode-entries fn-ccc-links-okp
                                   fn-ccco-links-chainedp fn-ccco-decode-entries
                                   fn-cc-recover-observation)))))
