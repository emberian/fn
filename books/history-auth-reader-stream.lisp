; Proof-only combined reader trajectory. No ghost predicate is a runtime guard.
(in-package "ACL2")
(include-book "pagestore-digest-cursor-semantics")
(include-book "history-auth-reader")
(include-book "history-auth-reader-frontier")
(local (include-book "arithmetic/top" :dir :system))

(local
 (defun fn-hsr-stream-put-ind (i j c)
   (declare (xargs :measure (nfix i) :verify-guards nil))
   (if (or (zp i) (zp j)) c
     (fn-hsr-stream-put-ind (1- i) (1- j) (if (consp c) (cdr c) nil)))))
(local
 (defthm fn-hsr-stream-field-of-put
   (implies (and (natp i) (natp j))
            (equal (fn-hsr-field j (fn-hsr-put i value c))
                   (if (equal i j) value (fn-hsr-field j c))))
   :hints (("Goal" :induct (fn-hsr-stream-put-ind i j c)
            :expand ((fn-hsr-put i value c) (fn-hsr-field j c)
                     (:free (a b) (fn-hsr-field j (cons a b))))
            :in-theory (enable fn-hsr-put fn-hsr-field)))))

(defun fn-hsr-auth-carryp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hsr-auth-lifetimep c)
       (fn-b3-word-listp (fn-hsr-field 9 c))
       (equal (mod (len (fn-hsr-field 9 c)) 2) 0)
       (<= (fn-hsr-field 6 c) (fn-hsr-field 5 c))
       (or (equal (fn-hsr-field 5 c) 0)
           (and (equal (fn-hsr-field 16 c) :data) (not (fn-hsr-field 10 c)))
           (let ((scan (fn-hsr-field 10 c)))
             (and (fn-hsr-scan-invariantp scan)
                  (equal (fn-hsr-field 0 scan) (fn-hsr-field 6 c))
                  (equal (fn-hsr-field 1 scan) (fn-hsr-field 5 c))
                  (equal (fn-hsr-field 4 scan) (fn-hsr-field 1 (fn-hsr-field 2 c)))
                  (equal (fn-hsr-field 7 scan) (fn-hsr-field 18 c))
                  (equal (fn-hsr-field 8 scan) (fn-hsr-field 1 (fn-hsr-field 1 c))))))))

(defthm fn-hsr-auth-begin-establishes-carry
  (implies (equal (mv-nth 0 (fn-hsr-auth-begin root ticket epoch capture lease)) :idle)
           (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-begin root ticket epoch capture lease))))
  :hints (("Goal" :use fn-hsr-auth-begin-establishes-lifetime
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-begin fn-hsr-field)
                           (fn-hsr-auth-begin-establishes-lifetime fn-hsr-auth-lifetimep fn-hsr-io-begin
                            fn-hsr-rootp fn-hsr-scan-invariantp fn-b3-word-listp)))))

(local
 (defthm fn-hsr-stream-root-txid-domain
   (implies (fn-hsr-auth-shapep c)
            (unsigned-byte-p 64 (fn-hsr-field 1 (fn-hsr-field 2 c))))
   :hints (("Goal" :in-theory (e/d (fn-hsr-auth-shapep fn-hsr-rootp)
                                   (fn-hsr-field unsigned-byte-p fn-hsr-io-shapep fn-hsr-prefixp fn-hsr-tagp fn-hsr-widthp fn-hrcur-wordp fn-hsr-scan-shapep))))))
(local
 (defthm fn-hsr-stream-lifetime-shape
   (implies (fn-hsr-auth-lifetimep c) (fn-hsr-auth-shapep c))
   :hints (("Goal" :in-theory (e/d (fn-hsr-auth-lifetimep)
                                   (fn-hsr-auth-shapep fn-hsr-field fn-hsr-io-invariantp))))))

(local
 (defthm fn-hsr-stream-field-of-cons
   (equal (fn-hsr-field i (cons a b))
          (if (zp i) a (fn-hsr-field (1- i) b)))
   :hints (("Goal" :expand ((fn-hsr-field i (cons a b)))
                   :in-theory (disable fn-hsr-field)))))

(defthm fn-hsr-auth-open-phase-preserves-carry
  (implies (and (fn-hsr-auth-carryp c)
                (member-eq (fn-hsr-field 0 (fn-hsr-field 1 c)) '(:idle :observed)))
           (fn-hsr-auth-carryp
            (mv-nth 1 (fn-hsr-auth-open-phase phase physical total count selected expected c pgs-digest-state))))
  :hints (("Goal"
           :use ((:instance fn-hsr-auth-open-phase-preserves-lifetime)
                 (:instance fn-hsr-stream-root-txid-domain)
                 (:instance fn-hsr-scan-begin-establishes-invariant
                            (txid (fn-hsr-field 1 (fn-hsr-field 2 c)))
                            (capture (list (fn-hsr-field 1 (fn-hsr-field 1 c))
                                           (fn-hsr-field 2 (fn-hsr-field 1 c))
                                           (fn-hsr-field 3 (fn-hsr-field 1 c)) phase))
                            (lease (fn-hsr-field 1 (fn-hsr-field 1 c)))))
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-open-phase fn-hsr-scan-begin)
                            (fn-hsr-auth-open-phase-preserves-lifetime fn-hsr-scan-begin-establishes-invariant
                             fn-hsr-auth-lifetimep fn-hsr-auth-shapep fn-hsr-rootp unsigned-byte-p
                             fn-hsr-stream-root-txid-domain fn-hsr-put fn-hsr-field fn-hsr-scan-invariantp fn-b3-word-listp
                             fn-hsr-io-shapep fn-hsr-widthp fn-hsr-prefixp fn-hsr-tagp fn-hrcur-wordp
                             pgs-dc-begin floor mod)))))

(local
 (defthm fn-hsr-stream-put-width
   (implies (and (natp i) (natp k) (< i k) (fn-hsr-widthp c k))
            (fn-hsr-widthp (fn-hsr-put i value c) k))
   :hints (("Goal" :induct (fn-hsr-stream-put-ind i k c)
                   :in-theory (enable fn-hsr-put fn-hsr-widthp)))))
(local
 (defthm fn-hsr-stream-selection-seed-carry
   (implies (and (fn-hsr-auth-carryp c) (natp logical) (natp tp) (natp count))
            (fn-hsr-auth-carryp (fn-hsr-put 3 logical (fn-hsr-put 13 tp (fn-hsr-put 14 count c)))))
   :hints (("Goal" :in-theory
            (e/d (fn-hsr-auth-carryp fn-hsr-auth-lifetimep fn-hsr-auth-shapep)
                 (fn-hsr-put fn-hsr-field fn-hsr-rootp fn-hsr-io-shapep fn-hsr-io-invariantp
                  fn-hsr-scan-invariantp fn-hsr-scan-shapep fn-hsr-widthp fn-hsr-prefixp
                  fn-hsr-tagp fn-hrcur-wordp fn-b3-word-listp floor mod))))))

(defthm fn-hsr-auth-select-page-preserves-carry
  (implies (fn-hsr-auth-carryp c)
           (fn-hsr-auth-carryp
            (mv-nth 1 (fn-hsr-auth-select-page logical c pgs-digest-state))))
  :hints (("Goal"
           :use ((:instance pgs-tq-tr-facts (i logical))
                 (:instance fn-hsr-stream-selection-seed-carry
                            (tp (pgs-tq logical))
                            (count (nfix (min 341 (- (fn-hsr-field 3 (fn-hsr-field 2 c)) (* 341 (pgs-tq logical)))))))
                 (:instance fn-hsr-auth-select-page-preserves-lifetime)
                 (:instance fn-hsr-auth-open-phase-preserves-carry
                            (phase :directory)
                            (physical (fn-hsr-field 2 (fn-hsr-field 2 c)))
                            (total (* 2048 (fn-hsr-field 12 c)))
                            (count (pgs-x-ntables (fn-hsr-field 3 (fn-hsr-field 2 c))))
                            (selected (pgs-tq logical))
                            (expected (fn-hsr-field 4 (fn-hsr-field 2 c)))
                            (c (fn-hsr-put 3 logical
                                  (fn-hsr-put 13 (pgs-tq logical)
                                    (fn-hsr-put 14 (nfix (min 341 (- (fn-hsr-field 3 (fn-hsr-field 2 c)) (* 341 (pgs-tq logical))))) c))))))
           :in-theory (e/d (fn-hsr-auth-select-page)
                            (fn-hsr-auth-carryp pgs-tq fn-hsr-stream-selection-seed-carry fn-hsr-auth-open-phase fn-hsr-auth-open-phase-preserves-carry fn-hsr-auth-select-page-preserves-lifetime
                             fn-hsr-auth-lifetimep fn-hsr-auth-shapep fn-hsr-put fn-hsr-field
                             fn-b3-word-listp fn-hsr-scan-invariantp fn-hsr-rootp
                             pgs-dc-begin floor mod pgs-x-ntables)))))

(local
 (defthm fn-hsr-stream-io-ticket
   (and (equal (fn-hsr-field 1 (mv-nth 2 (fn-hsr-io-request phase physical logical c))) (fn-hsr-field 1 c))
        (equal (fn-hsr-field 1 (mv-nth 1 (fn-hsr-io-complete request discovery-id count status c))) (fn-hsr-field 1 c))
        (equal (fn-hsr-field 1 (mv-nth 1 (fn-hsr-io-release discovery-id c))) (fn-hsr-field 1 c))
        (equal (fn-hsr-field 1 (mv-nth 1 (fn-hsr-io-cancel c))) (fn-hsr-field 1 c))
        (equal (fn-hsr-field 1 (mv-nth 1 (fn-hsr-io-joined-failure request outcome c))) (fn-hsr-field 1 c)))
   :hints (("Goal" :use fn-hsr-io-transitions-preserve-identities
                   :in-theory (e/d (fn-hsr-io-identities)
                                    (fn-hsr-io-transitions-preserve-identities fn-hsr-field
                                     fn-hsr-io-request fn-hsr-io-complete fn-hsr-io-release fn-hsr-io-cancel fn-hsr-io-joined-failure))))))

(defthm fn-hsr-auth-request-preserves-carry
  (implies (fn-hsr-auth-carryp c)
           (fn-hsr-auth-carryp (mv-nth 2 (fn-hsr-auth-request c))))
  :hints (("Goal" :use fn-hsr-auth-request-preserves-lifetime
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-request)
                            (fn-hsr-auth-request-preserves-lifetime fn-hsr-auth-lifetimep fn-hsr-auth-shapep
                             fn-hsr-field fn-hsr-put fn-hsr-io-request fn-hsr-scan-invariantp fn-b3-word-listp floor mod)))))

(defthm fn-hsr-auth-complete-preserves-carry
  (implies (fn-hsr-auth-carryp c)
           (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-complete request discovery-id count status c))))
  :hints (("Goal" :use fn-hsr-auth-complete-preserves-lifetime
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-complete)
                            (fn-hsr-auth-complete-preserves-lifetime fn-hsr-auth-lifetimep fn-hsr-auth-shapep
                             fn-hsr-field fn-hsr-put fn-hsr-io-complete fn-hsr-scan-invariantp fn-b3-word-listp floor mod)))))

(defthm fn-hsr-auth-release-preserves-carry
  (implies (fn-hsr-auth-carryp c)
           (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-release discovery-id c))))
  :hints (("Goal" :use fn-hsr-auth-release-preserves-lifetime
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-release)
                            (fn-hsr-auth-release-preserves-lifetime fn-hsr-auth-lifetimep fn-hsr-auth-shapep
                             fn-hsr-field fn-hsr-put fn-hsr-io-release fn-hsr-scan-invariantp fn-b3-word-listp floor mod)))))

(defthm fn-hsr-auth-cancel-preserves-carry
  (implies (fn-hsr-auth-carryp c)
           (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-cancel c))))
  :hints (("Goal" :use fn-hsr-auth-cancel-preserves-lifetime
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-cancel)
                            (fn-hsr-auth-cancel-preserves-lifetime fn-hsr-auth-lifetimep fn-hsr-auth-shapep
                             fn-hsr-field fn-hsr-put fn-hsr-io-cancel fn-hsr-scan-invariantp fn-b3-word-listp floor mod)))))

(defthm fn-hsr-auth-joined-failure-preserves-carry
  (implies (fn-hsr-auth-carryp c)
           (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-joined-failure request outcome c))))
  :hints (("Goal" :use fn-hsr-auth-joined-failure-preserves-lifetime
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-joined-failure)
                            (fn-hsr-auth-joined-failure-preserves-lifetime fn-hsr-auth-lifetimep fn-hsr-auth-shapep
                             fn-hsr-field fn-hsr-put fn-hsr-io-joined-failure fn-hsr-scan-invariantp fn-b3-word-listp floor mod)))))


(local
 (defthm fn-hsr-stream-carry-naturals
   (implies (fn-hsr-auth-carryp c)
            (and (natp (fn-hsr-field 5 c)) (natp (fn-hsr-field 6 c))))
   :hints (("Goal" :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-lifetimep fn-hsr-auth-shapep)
                (fn-hsr-field fn-hsr-io-shapep fn-hsr-rootp fn-hsr-prefixp fn-hsr-tagp fn-hsr-widthp
                 fn-hsr-scan-shapep fn-hsr-scan-invariantp fn-b3-word-listp fn-hrcur-wordp fn-hsr-io-invariantp))))))
(local
 (defthm fn-hsr-stream-u32-append-halves
   (implies (fn-b3-word-listp block)
            (fn-b3-word-listp (append block (list (pgs-lo32 word) (pgs-hi32 word)))))
   :hints (("Goal" :induct (fn-b3-word-listp block)
                   :in-theory (e/d (fn-b3-word-listp) (pgs-lo32 pgs-hi32 unsigned-byte-p))))))
(local
 (defthm fn-hsr-stream-append-halves-length
   (equal (len (append block (list a b))) (+ 2 (len block)))
   :hints (("Goal" :induct (len block)))))

(local
 (encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-hsr-stream-even-plus-two
    (implies (natp n) (equal (mod (+ 2 n) 2) (mod n 2)))
    :hints (("Goal" :in-theory (disable mod floor))))))

(defthm fn-hsr-auth-feed-byte-preserves-carry
  (implies (fn-hsr-auth-carryp c)
           (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-feed-byte discovery-id offset byte c))))
  :hints (("Goal"
           :use ((:instance fn-hsr-stream-carry-naturals)
                 (:instance fn-hsr-auth-feed-byte-preserves-lifetime)
                 (:instance fn-hsr-scan-word-progress-and-invariant
                            (c (fn-hsr-field 10 c))
                            (word (mv-nth 1 (fn-hrcur-word-push byte (fn-hsr-field 7 c) (fn-hsr-field 8 c))))))
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-feed-byte fn-hsr-auth-refuse)
                            (fn-hsr-stream-carry-naturals fn-hsr-auth-feed-byte-preserves-lifetime fn-hsr-auth-lifetimep fn-hsr-auth-shapep
                             fn-hsr-field fn-hsr-put fn-hsr-scan-invariantp fn-b3-word-listp
                             fn-hsr-scan-word fn-hrcur-word-push fn-hsr-scan-word-progress-and-invariant
                             pgs-lo32 pgs-hi32 floor mod)))))

(local
 (defthm fn-hsr-stream-digest-observed
   (implies (and (fn-hsr-auth-lifetimep c) (equal (fn-hsr-field 0 c) :digest))
            (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :observed))
   :hints (("Goal" :in-theory (e/d (fn-hsr-auth-lifetimep)
                                   (fn-hsr-auth-shapep fn-hsr-io-invariantp fn-hsr-field))))))

(defthm fn-hsr-auth-finish-phase-preserves-carry
  (implies (fn-hsr-auth-carryp c)
           (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-finish-phase c pgs-digest-state))))
  :hints (("Goal"
           :use ((:instance fn-hsr-auth-finish-phase-preserves-lifetime)
                 (:instance fn-hsr-stream-digest-observed)
                 (:instance fn-hsr-auth-open-phase-preserves-carry
                   (phase :table) (physical (fn-hsr-field 0 (fn-hsr-scan-entry (fn-hsr-field 10 c))))
                   (total 2048) (count (fn-hsr-field 14 c)) (selected (pgs-tr (fn-hsr-field 3 c)))
                   (expected (fn-hsr-field 2 (fn-hsr-scan-entry (fn-hsr-field 10 c)))))
                 (:instance fn-hsr-auth-open-phase-preserves-carry
                   (phase :data) (physical (fn-hsr-field 0 (fn-hsr-scan-entry (fn-hsr-field 10 c))))
                   (total 2048) (count 0) (selected 0)
                   (expected (fn-hsr-field 2 (fn-hsr-scan-entry (fn-hsr-field 10 c))))))
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-finish-phase fn-hsr-auth-refuse)
                            (fn-hsr-auth-finish-phase-preserves-lifetime fn-hsr-stream-digest-observed
                             fn-hsr-auth-lifetimep fn-hsr-auth-shapep fn-hsr-auth-open-phase fn-hsr-auth-open-phase-preserves-carry
                             fn-hsr-field fn-hsr-put fn-hsr-scan-invariantp fn-b3-word-listp fn-hsr-scan-entry
                             fn-hsr-page-verdict pgs-dc-result pgs-tr floor mod)))))

(local
 (defthm fn-hsr-stream-clear-block-carry
   (implies (fn-hsr-auth-carryp c) (fn-hsr-auth-carryp (fn-hsr-put 9 nil c)))
   :hints (("Goal" :in-theory
            (e/d (fn-hsr-auth-carryp fn-hsr-auth-lifetimep fn-hsr-auth-shapep)
                 (fn-hsr-put fn-hsr-field fn-hsr-rootp fn-hsr-io-shapep fn-hsr-io-invariantp
                  fn-hsr-scan-invariantp fn-hsr-scan-shapep fn-hsr-widthp fn-hsr-prefixp
                  fn-hsr-tagp fn-hrcur-wordp fn-b3-word-listp floor mod))))))

(defthm fn-hsr-auth-digest-tick-preserves-carry
  (implies (fn-hsr-auth-carryp c)
           (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-digest-tick c pgs-digest-state))))
  :hints (("Goal"
           :use ((:instance fn-hsr-auth-digest-tick-preserves-lifetime)
                 (:instance fn-hsr-stream-clear-block-carry)
                 (:instance fn-hsr-auth-finish-phase-preserves-carry
                   (c (fn-hsr-put 9 nil c))
                   (pgs-digest-state
                    (mv-nth 1 (pgs-dc-step (if (pgs-dc-needs-block pgs-digest-state) (fn-hsr-field 9 c) nil) pgs-digest-state)))))
           :in-theory (e/d (fn-hsr-auth-carryp fn-hsr-auth-digest-tick fn-hsr-auth-refuse)
                            (fn-hsr-auth-digest-tick-preserves-lifetime fn-hsr-stream-clear-block-carry
                             fn-hsr-auth-finish-phase-preserves-carry fn-hsr-auth-finish-phase
                             fn-hsr-auth-lifetimep fn-hsr-auth-shapep
                             fn-hsr-field fn-hsr-put fn-hsr-scan-invariantp fn-b3-word-listp
                             pgs-dc-step pgs-dc-needs-block pgs-dc-next-word-offset pgs-dc-read-demand floor mod)))))
