; The reply codes of the reader dispatcher's response builders (lane
; defprotocol): the lemmas books/protocol-codes.lisp assembles, per row of
; books/protocol-table.lisp, into its keystone.  Split from that book at the
; seam between the builders and the table (D26: under 10 s at two jobs).
;
; A reply's code is the natural number its first three octets spell
; (fn-proto-octets-code).  One lemma per response builder, bottom up, says the
; codes of its replies are among a set -- stated as member-equal hypotheses so
; that a caller whose set is a ground list discharges them by evaluation, and
; parametric where the builder's code is (fn-proto-retrieval-code KIND for
; ARTICLE/HEAD/BODY/STAT, fn-proto-hdr-code LEGACYP for HDR/XHDR, the
; direction for NEXT/LAST, UPDATEP for 423 against 430).

(in-package "ACL2")
(include-book "nntp")

(local (in-theory (enable fn-nntp-syntax-vocabulary)))

; -----------------------------------------------------------------------------
; A reply's status code

(defun fn-proto-digitp (b)
  (declare (xargs :guard t))
  (and (integerp b) (<= 48 b) (<= b 57)))

(defun fn-proto-octets-code (octets)
  (declare (xargs :guard t))
  (if (and (consp octets) (consp (cdr octets)) (consp (cddr octets))
           (fn-proto-digitp (car octets)) (fn-proto-digitp (cadr octets))
           (fn-proto-digitp (caddr octets)))
      (+ (* 100 (- (car octets) 48)) (* 10 (- (cadr octets) 48))
         (- (caddr octets) 48))
    nil))

; Every :reply effect's code is a member of CODES.
(defun fn-proto-within (effects codes)
  (declare (xargs :guard (true-listp codes)))
  (if (consp effects)
      (and (or (not (and (consp (car effects)) (equal (car (car effects)) :reply)
                         (consp (cdr (car effects)))))
               (member-equal (fn-proto-octets-code (cadr (car effects))) codes))
           (fn-proto-within (cdr effects) codes))
    t))

; The codes of the :reply effects, in order (for witnesses).
(defun fn-proto-effect-codes (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (if (and (consp (car effects)) (equal (car (car effects)) :reply)
               (consp (cdr (car effects))))
          (cons (fn-proto-octets-code (cadr (car effects)))
                (fn-proto-effect-codes (cdr effects)))
        (fn-proto-effect-codes (cdr effects)))
    nil))

(defthm fn-proto-within-is-subset-of-effect-codes
  (equal (fn-proto-within effects codes)
         (subsetp-equal (fn-proto-effect-codes effects) codes)))

(in-theory (disable fn-proto-within-is-subset-of-effect-codes))

(defun fn-proto-retrieval-code (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :article) 220)
        ((equal kind :head) 221)
        ((equal kind :body) 222)
        (t 223)))

(defun fn-proto-hdr-code (legacyp)
  (declare (xargs :guard t))
  (if legacyp 221 225))

; -----------------------------------------------------------------------------
; The reply constructors

; Exported: the row theorems of books/protocol-codes.lisp meet the same
; nested appends when they open an arm.
(defthm fn-proto-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm fn-proto-within-of-cons
  (equal (fn-proto-within (cons e rest) codes)
         (and (or (not (and (consp e) (equal (car e) :reply) (consp (cdr e))))
                  (member-equal (fn-proto-octets-code (cadr e)) codes))
              (fn-proto-within rest codes))))

(defthm fn-proto-within-of-atom
  (implies (not (consp effects)) (fn-proto-within effects codes)))

(defthm fn-proto-reply-effect-parts
  (and (consp (fn-nntp-reply-effect x))
       (equal (car (fn-nntp-reply-effect x)) :reply)
       (consp (cdr (fn-nntp-reply-effect x)))
       (equal (cadr (fn-nntp-reply-effect x)) x))
  :hints (("Goal" :in-theory (enable fn-nntp-reply-effect))))

(defthm fn-proto-close-effect-is-not-a-reply
  (not (equal (car (fn-nntp-close-effect)) :reply))
  :hints (("Goal" :in-theory (enable fn-nntp-close-effect))))

(defthm fn-proto-effects-of-make-result
  (equal (fn-nntp-result-effects (fn-nntp-make-result session effects)) effects)
  :hints (("Goal" :in-theory (enable fn-nntp-make-result fn-nntp-result-effects))))

(defthm fn-proto-crlf-is-append
  (equal (fn-nntp-crlf x) (append x '(13 10)))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf))))

(defthm fn-proto-append-pieces-of-cons
  (equal (fn-nntp-append-pieces (cons x rest))
         (append x (fn-nntp-append-pieces rest)))
  :hints (("Goal" :in-theory (enable fn-nntp-append-pieces))))

; The octets after a multi-line reply's initial line, left closed.
(defun fn-proto-block-tail (lines)
  (declare (xargs :guard t :verify-guards nil))
  (cons 13 (cons 10 (append (fn-nntp-stuff-lines lines) '(46 13 10)))))

(defthm fn-proto-within-of-single
  (equal (fn-proto-within (fn-nntp-result-effects (fn-nntp-single session text)) codes)
         (if (member-equal (fn-proto-octets-code
                            (append (fn-nntp-string-octets text) '(13 10)))
                           codes)
             t nil))
  :hints (("Goal" :in-theory (enable fn-nntp-single))))

(defthm fn-proto-within-of-multi
  (equal (fn-proto-within (fn-nntp-result-effects (fn-nntp-multi session initial lines)) codes)
         (if (member-equal (fn-proto-octets-code
                            (append (fn-nntp-string-octets initial)
                                    (fn-proto-block-tail lines)))
                           codes)
             t nil))
  :hints (("Goal" :in-theory (e/d (fn-nntp-multi fn-proto-block-tail)
                                  (fn-proto-octets-code fn-nntp-stuff-lines)))))

(defthm fn-proto-within-of-multi-octets
  (equal (fn-proto-within (fn-nntp-result-effects
                           (fn-nntp-multi-octets session initial lines)) codes)
         (if (member-equal (fn-proto-octets-code
                            (append initial (fn-proto-block-tail lines)))
                           codes)
             t nil))
  :hints (("Goal" :in-theory (e/d (fn-nntp-multi-octets fn-proto-block-tail)
                                  (fn-proto-octets-code fn-nntp-stuff-lines)))))

(in-theory (disable fn-proto-block-tail fn-proto-within))

; -----------------------------------------------------------------------------
; The computed initial lines: the code is their first three octets

(defmacro fn-proto-initial-code (name call code &key enable disable)
  `(defthm ,name
     (and (equal (fn-proto-octets-code (append ,call rest)) ,code)
          (equal (fn-proto-octets-code ,call) ,code))
     :hints (("Goal" :in-theory (e/d (,(car call) ,@enable) ,disable)))))

(fn-proto-initial-code fn-proto-code-of-group-initial
  (fn-nntp-group-initial archive group) 211
  :disable (fn-nntp-decimal-field fn-nntp-group-summary))
(fn-proto-initial-code fn-proto-code-of-listgroup-initial
  (fn-nntp-listgroup-initial archive group) 211
  :enable (fn-nntp-group-initial)
  :disable (fn-nntp-decimal-field fn-nntp-group-summary))
(fn-proto-initial-code fn-proto-code-of-gidx-group-initial
  (fn-gidx-group-initial archive buckets group) 211
  :disable (fn-nntp-decimal-field fn-gidx-group-summary))
(fn-proto-initial-code fn-proto-code-of-date-octets
  (fn-nntp-date-octets civil) 111
  :disable (fn-nntp-pad4 fn-nntp-pad2))
(fn-proto-initial-code fn-proto-code-of-cu-initial-line
  (fn-cu-initial-line next end chain) 291
  :disable (fn-cu-u64-hex fn-cu-hex))
(fn-proto-initial-code fn-proto-code-of-retrieval-initial
  (fn-nntp-retrieval-initial kind number article) (fn-proto-retrieval-code kind)
  :enable (fn-proto-retrieval-code)
  :disable (fn-nntp-decimal-field fn-article-msgid))
(fn-proto-initial-code fn-proto-code-of-hdr-initial
  (fn-nntp-string-octets (fn-nntp-hdr-initial legacyp)) (fn-proto-hdr-code legacyp)
  :enable (fn-nntp-hdr-initial fn-proto-hdr-code))

(in-theory (disable fn-nntp-group-initial fn-nntp-listgroup-initial
                    fn-gidx-group-initial fn-nntp-date-octets fn-cu-initial-line
                    fn-nntp-retrieval-initial fn-nntp-hdr-initial
                    fn-proto-retrieval-code fn-proto-hdr-code))

; -----------------------------------------------------------------------------
; The response builders, bottom up
;; fn-cu-serve-reply (books/peer-catchup-serve.lisp)
(defthm fn-proto-codes-of-cu-serve-reply
  (implies (and (member-equal 291 codes) (member-equal 423 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-cu-serve-reply session archive index args fn-arena)) codes))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cu-serve-reply)
                           (fn-cu-select fn-cu-render-lines fn-cu-chain-over
                            fn-cu-parse-request fn-nntp-filter-groups-by-wildmat
                            fn-cu-list)))))

;; fn-gidx-list-counts-command (books/nntp.lisp)
(defthm fn-proto-codes-of-gidx-list-counts-command
  (implies (and (member-equal 215 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-gidx-list-counts-command session archive buckets closed args)) codes))
  :hints (("Goal" :in-theory (enable fn-gidx-list-counts-command))))

;; fn-gidx-listgroup-result (books/group-bucket-index.lisp)
(defthm fn-proto-codes-of-gidx-listgroup-result
  (implies (and (member-equal 211 codes) (member-equal 411 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-gidx-listgroup-result session archive buckets group range)) codes))
  :hints (("Goal" :in-theory (enable fn-gidx-listgroup-result))))

;; fn-gidx-listgroup-command (books/group-bucket-index.lisp)
(defthm fn-proto-codes-of-gidx-listgroup-command
  (implies (and (member-equal 211 codes) (member-equal 411 codes) (member-equal 412 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-gidx-listgroup-command session archive buckets args)) codes))
  :hints (("Goal" :in-theory (enable fn-gidx-listgroup-command))))

;; fn-nntp-article-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-article-response
  (implies (and (member-equal (fn-proto-retrieval-code kind) codes)
                (member-equal (if updatep 423 430) codes)
                (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-article-response session article number kind updatep group fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-article-response))))

;; fn-nntp-article-response-of-bytes (books/nntp-article-block.lisp)
(defthm fn-proto-codes-of-nntp-article-response-of-bytes
  (implies (and (member-equal (fn-proto-retrieval-code kind) codes)
                (member-equal (if updatep 423 430) codes)
                (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-article-response-of-bytes session article bytes number kind updatep group)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-article-response-of-bytes))))

;; fn-nntp-capabilities (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-capabilities
  (implies (and (member-equal 101 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-capabilities session postingp)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-capabilities))))

;; fn-nntp-control-hdr-response (books/nntp.lisp)
(defthm fn-proto-codes-of-nntp-control-hdr-response
  (implies (and (member-equal 225 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-control-hdr-response session archive index verdicts args fn-arena)) codes))
  :hints (("Goal" :in-theory (e/d (fn-nntp-control-hdr-response)
                                  (fn-ctl-control-item fn-ctl-served-status
                                   fn-ctl-served-held fn-nntp-string-octets
                                   fn-nntp-control-cleanp fn-nntp-hdr-line
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-ctl-pin-withdrawn fn-ctl-pin-ws
                                   fn-nntp-token-string fn-ctl-target-octets
                                   fn-octet-listp fn-nntp-article-bytes)))))

;; fn-nntp-current-retrieval (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-current-retrieval
  (implies (and (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 503 codes) (member-equal (fn-proto-retrieval-code kind) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-current-retrieval session archive kind fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-current-retrieval))))

;; fn-nntp-date-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-date-response
  (implies (and (member-equal 111 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-date-response session env)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-date-response))))

;; fn-nntp-enrollment-hdr-response (books/nntp-enrollment.lisp)
(defthm fn-proto-codes-of-nntp-enrollment-hdr-response
  (implies (and (member-equal 225 codes) (member-equal 430 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-enrollment-hdr-response session archive index verdicts args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-enrollment-hdr-response))))

;; fn-nntp-group-result (books/nntp-projection.lisp)
(defthm fn-proto-codes-of-nntp-group-result
  (implies (and (member-equal 211 codes) (member-equal 411 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-group-result session archive group)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-group-result))))

;; fn-nntp-hdr-current (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-hdr-current
  (implies (and (member-equal 412 codes) (member-equal 420 codes) (member-equal 503 codes) (member-equal (fn-proto-hdr-code legacyp) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-hdr-current session archive field legacyp fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-hdr-current))))

;; fn-nntp-hdr-msgid (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-hdr-msgid
  (implies (and (member-equal 430 codes) (member-equal 503 codes) (member-equal (fn-proto-hdr-code legacyp) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-hdr-msgid session archive field token legacyp fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-hdr-msgid))))

;; fn-nntp-hdr-range (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-hdr-range
  (implies (and (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal (fn-proto-hdr-code legacyp) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-hdr-range session archive field token legacyp fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-hdr-range))))

;; fn-nntp-hdr-command (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-hdr-command
  (implies (and (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes) (member-equal (fn-proto-hdr-code legacyp) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-hdr-command session archive args legacyp fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-hdr-command))))

;; fn-nntp-hdr-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-hdr-response
  (implies (and (member-equal 225 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-hdr-response session archive args fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-hdr-response))))

;; fn-nntp-help (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-help
  (implies (and (member-equal 100 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-help session)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-help))))

;; fn-nntp-list-active (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-active
  (implies (and (member-equal 215 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-active session archive groups)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-active))))

;; fn-nntp-list-newsgroups (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-newsgroups
  (implies (and (member-equal 215 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-newsgroups session groups)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-newsgroups))))

;; fn-nntp-list-filtered-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-filtered-response
  (implies (and (member-equal 215 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-filtered-response session archive kind wildmat)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-filtered-response))))

;; fn-nntp-list-active-or-newsgroups (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-active-or-newsgroups
  (implies (and (member-equal 215 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-active-or-newsgroups session archive kind args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-active-or-newsgroups))))

;; fn-nntp-list-active-status (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-active-status
  (implies (and (member-equal 215 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-active-status session archive groups closed)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-active-status))))

;; fn-nntp-list-active-times (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-active-times
  (implies (and (member-equal 215 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-active-times session env args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-active-times))))

;; fn-nntp-list-counts (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-counts
  (implies (and (member-equal 215 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-counts session archive groups closed)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-counts))))

;; fn-nntp-list-counts-command (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-counts-command
  (implies (and (member-equal 215 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-counts-command session archive closed args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-counts-command))))

;; fn-nntp-list-motd (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-motd
  (implies (and (member-equal 215 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-motd session env args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-motd))))

;; fn-nntp-list-newsgroups-described (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-newsgroups-described
  (implies (and (member-equal 215 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-newsgroups-described session archive descs args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-newsgroups-described))))

;; fn-nntp-list-headers (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-headers
  (implies (and (member-equal 215 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-headers session)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-headers))))

;; fn-nntp-list-overview-fmt (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-overview-fmt
  (implies (and (member-equal 215 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-overview-fmt session)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-overview-fmt))))

;; fn-nntp-list-unmaintained-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-unmaintained-response
  (implies (and (member-equal 215 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-unmaintained-response session keyword args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-unmaintained-response))))

;; fn-nntp-list-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-response
  (implies (and (member-equal 215 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-response session archive args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-response))))

;; fn-nntp-list-status-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-status-response
  (implies (and (member-equal 215 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-status-response session archive closed args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-status-response))))

;; fn-nntp-list-command (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-list-command
  (implies (and (member-equal 215 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-command session archive env args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-command))))

;; fn-nntp-list-overview-fmt-served (books/nntp-xref.lisp)
(defthm fn-proto-codes-of-nntp-list-overview-fmt-served
  (implies (and (member-equal 215 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-list-overview-fmt-served session)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-list-overview-fmt-served))))

;; fn-nntp-listgroup-result (books/nntp-projection.lisp)
(defthm fn-proto-codes-of-nntp-listgroup-result
  (implies (and (member-equal 211 codes) (member-equal 411 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-listgroup-result session archive group range)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-listgroup-result))))

;; fn-nntp-listgroup-command (books/nntp-projection.lisp)
(defthm fn-proto-codes-of-nntp-listgroup-command
  (implies (and (member-equal 211 codes) (member-equal 411 codes) (member-equal 412 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-listgroup-command session archive args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-listgroup-command))))

;; fn-nntp-mode-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-mode-response
  (implies (and (member-equal 200 codes) (member-equal 201 codes) (member-equal 501 codes) (member-equal 502 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-mode-response session env args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-mode-response))))

;; fn-nntp-msgid-retrieval (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-msgid-retrieval
  (implies (and (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes) (member-equal (fn-proto-retrieval-code kind) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-msgid-retrieval session archive kind token fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-msgid-retrieval))))

;; fn-nntp-msgid-retrieval-indexed (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-msgid-retrieval-indexed
  (implies (and (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes) (member-equal (fn-proto-retrieval-code kind) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-msgid-retrieval-indexed session archive index kind token fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-msgid-retrieval-indexed))))

;; fn-nntp-newgroups-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-newgroups-response
  (implies (and (member-equal 231 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-newgroups-response session archive env args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-newgroups-response))))

;; fn-nntp-newnews-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-newnews-response
  (implies (and (member-equal 230 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-newnews-response session archive env args fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-newnews-response))))

;; fn-nntp-next-or-last (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-next-or-last
  (implies (and (member-equal 223 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal (if (equal direction :next) 421 422) codes) (member-equal 423 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-next-or-last session archive direction fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-next-or-last))))

;; fn-nntp-number-retrieval (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-number-retrieval
  (implies (and (member-equal 412 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes) (member-equal (fn-proto-retrieval-code kind) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-number-retrieval session archive kind token fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-number-retrieval))))

;; fn-nntp-over-current (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-over-current
  (implies (and (member-equal 224 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-over-current session archive fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-over-current))))

;; fn-nntp-over-current-served (books/nntp-xref.lisp)
(defthm fn-proto-codes-of-nntp-over-current-served
  (implies (and (member-equal 224 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-over-current-served session archive server fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-over-current-served))))

;; fn-nntp-over-msgid (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-over-msgid
  (implies (and (member-equal 224 codes) (member-equal 430 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-over-msgid session archive token fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-over-msgid))))

;; fn-nntp-over-msgid-served (books/nntp-xref.lisp)
(defthm fn-proto-codes-of-nntp-over-msgid-served
  (implies (and (member-equal 224 codes) (member-equal 430 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-over-msgid-served session archive token server fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-over-msgid-served))))

;; fn-nntp-over-range (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-over-range
  (implies (and (member-equal 224 codes) (member-equal 412 codes) (member-equal 423 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-over-range session archive token fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-over-range))))

;; fn-nntp-over-range-indexed (books/nntp-range-indexed.lisp)
(defthm fn-proto-codes-of-nntp-over-range-indexed
  (implies (and (member-equal 224 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-over-range-indexed session buckets trie token legacyp fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-over-range-indexed))))

;; fn-nntp-over-range-served (books/nntp-xref.lisp)
(defthm fn-proto-codes-of-nntp-over-range-served
  (implies (and (member-equal 224 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-over-range-served session buckets trie token legacyp server fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-over-range-served))))

;; fn-nntp-over-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-over-response
  (implies (and (member-equal 224 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-over-response session archive args fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-over-response))))

;; fn-nntp-post-offer (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-post-offer
  (implies (and (member-equal 340 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-post-offer session)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-post-offer))))

;; fn-nntp-retrieval (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-retrieval
  (implies (and (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes) (member-equal (fn-proto-retrieval-code kind) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-retrieval session archive kind args fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-retrieval))))

;; fn-nntp-verdict-hdr-current (books/nntp-verdict.lisp)
(defthm fn-proto-codes-of-nntp-verdict-hdr-current
  (implies (and (member-equal 225 codes) (member-equal 412 codes) (member-equal 420 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-verdict-hdr-current session archive verdicts)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-verdict-hdr-current))))

;; fn-nntp-verdict-hdr-msgid (books/nntp-verdict.lisp)
(defthm fn-proto-codes-of-nntp-verdict-hdr-msgid
  (implies (and (member-equal 225 codes) (member-equal 430 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-verdict-hdr-msgid session archive verdicts token)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-verdict-hdr-msgid))))

;; fn-nntp-verdict-hdr-range (books/nntp-verdict.lisp)
(defthm fn-proto-codes-of-nntp-verdict-hdr-range
  (implies (and (member-equal 225 codes) (member-equal 412 codes) (member-equal 423 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-verdict-hdr-range session archive verdicts token)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-verdict-hdr-range))))

;; fn-nntp-verdict-hdr-response (books/nntp-verdict.lisp)
(defthm fn-proto-codes-of-nntp-verdict-hdr-response
  (implies (and (member-equal 225 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-verdict-hdr-response session archive verdicts args)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-verdict-hdr-response))))

;; fn-nntp-withdrawn-reply (books/nntp.lisp)
(defthm fn-proto-codes-of-nntp-withdrawn-reply
  (implies (and (member-equal 423 codes) (member-equal 430 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-withdrawn-reply session msgidp)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-withdrawn-reply))))

;; fn-nntp-xhdr-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-xhdr-response
  (implies (and (member-equal 221 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-xhdr-response session archive args fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-xhdr-response))))

;; fn-nntp-xover-range (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-xover-range
  (implies (and (member-equal 224 codes) (member-equal 412 codes) (member-equal 420 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-xover-range session archive token fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-xover-range))))

;; fn-nntp-xover-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-xover-response
  (implies (and (member-equal 224 codes) (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-xover-response session archive args fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-xover-response))))

;; fn-nntp-xpat-msgid (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-xpat-msgid
  (implies (and (member-equal 221 codes) (member-equal 430 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-xpat-msgid session archive field patterns token fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-xpat-msgid))))

;; fn-nntp-xpat-range (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-xpat-range
  (implies (and (member-equal 221 codes) (member-equal 412 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-xpat-range session archive field patterns token fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-xpat-range))))

;; fn-nntp-xpat-response (books/nntp-responses.lisp)
(defthm fn-proto-codes-of-nntp-xpat-response
  (implies (and (member-equal 221 codes) (member-equal 412 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-nntp-xpat-response session archive args fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-nntp-xpat-response))))

;; fn-rcompat-article-reply (books/nntp-reader-compat.lisp)
(defthm fn-proto-codes-of-rcompat-article-reply
  (implies (and (member-equal (fn-proto-retrieval-code kind) codes)
                (member-equal (if updatep 423 430) codes)
                (member-equal 503 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-rcompat-article-reply session article number kind updatep group server fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-rcompat-article-reply))))

;; fn-rcompat-hdr (books/nntp-reader-compat.lisp)
(defthm fn-proto-codes-of-rcompat-hdr
  (implies (and (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal (fn-proto-hdr-code legacyp) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-rcompat-hdr session archive trie args legacyp server fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-rcompat-hdr))))

;; fn-rcompat-retrieval (books/nntp-reader-compat.lisp)
(defthm fn-proto-codes-of-rcompat-retrieval
  (implies (and (member-equal 412 codes) (member-equal 420 codes) (member-equal 423 codes) (member-equal 430 codes) (member-equal 501 codes) (member-equal 503 codes) (member-equal (fn-proto-retrieval-code kind) codes))
           (fn-proto-within (fn-nntp-result-effects (fn-rcompat-retrieval session archive trie kind args server fn-arena)) codes))
  :hints (("Goal" :in-theory (enable fn-rcompat-retrieval))))

;; fn-rcompat-subscriptions (books/nntp-reader-compat.lisp)
(defthm fn-proto-codes-of-rcompat-subscriptions
  (implies (and (member-equal 215 codes) (member-equal 501 codes))
           (fn-proto-within (fn-nntp-result-effects (fn-rcompat-subscriptions session archive env args)) codes))
  :hints (("Goal" :in-theory (e/d (fn-rcompat-subscriptions)
                                  (fn-wildmat-parse fn-rcompat-name-lines
                                   fn-nntp-filter-groups-by-wildmat
                                   fn-rcompat-subscription-names)))))
