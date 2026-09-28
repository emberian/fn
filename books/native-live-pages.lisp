; fn: the operator's `obligations' report sent page by page with a version
; token (lane obligations-paged, 2026-09-28; PKT-470's bounded render).
; Prefix `fn-nlp-'.
;
; The FNLS exchange of books/native-live-status.lisp carries, on every page,
; the report's total length and a digest over the whole report
; (`fn-nls-reply'), so the owner renders the whole report before its first
; page (`fn-nls-buffer').  The retention ledger has one obligation per held
; article: at 1,000,000 articles the `obligations' report is 244,000,037
; octets, built as an octet list under the owner mutex, and a second request
; exhausted the 32 GB heap and killed the owner (lanes scale-reads-status and
; serve-depth, syn1m-2k).
;
; This exchange renders one page per request.  A page is the next W octets
; of the report (W = `*fn-nls-chunk-octets*' on the served path), cut from a
; cursor: the unsent rest of the current line and the obligations not yet
; rendered (`fn-nlp-take').  The first request (version 0, page 0) starts a
; report over the ledger the owner holds then and answers with a VERSION
; token; the owner keeps the cursor under that token (`fn-nlp-answer'), and
; each later request names the token and the page it wants.  A token the
; owner no longer holds (it keeps `*fn-nlp-max-versions*' cursors, a report
; read to the end drops its own, a restarted owner holds none), or a page
; that is not the one the cursor stands at, is answered `version-gone' BY
; NAME; the client restarts from page 0, at most `*fn-nls-max-restarts*'
; times, then answers uncertain.  The ledger is an applicative value: the
; cursor holds the rest of the ledger the report started from, so a POST
; between two pages does not change the report a version names (the
; report is the ledger at its first page).  No total, no digest over the
; whole report; each frame's trailer covers its page.
;
; Work per request: one page, at most W octets and at most W obligation lines
; (a line is never empty), plus the ledger's length on the first page (the
; header's count, one walk, no rendering).  Allocation per request: one page.
; The page counter wraps modulo 2^32 and the version counter skips 0, so no
; report length is refused: a report past 4 GB is more pages, not a refusal
; (the old exchange's u32 total refused it by name, PRF-178).
;
; KEYSTONES (the subjects are `fn-nlp-answer', which
; host/native-live-status-host.lisp `fn-native-live-pages-host-answer' calls
; under the owner mutex (host/native/control.lisp
; `fnn-control-live-pages-answer'), and `fn-nlp-client-step', which
; host/native/control.lisp `fnn-control-live-pages' folds every page
; through):
;   fn-nlp-live-report-is-the-report           the old whole report of kind
;       :obligations (`fn-nls-live-report') is `fn-nlp-report' of the
;       owner's retention, no hypothesis;
;   fn-nlp-pages-join-to-the-report            the pages a client reads at
;       one version, concatenated, are that report of the ledger the owner
;       held at the first page, whenever the client reaches :done;
;   fn-nlp-pages-reach-the-report              and it does reach :done within
;       (the report's length / W) + 2 requests when nothing else intervenes;
;   fn-nlp-answer-keeps-other-versions         another client's request
;       leaves a version's cursor as it was or drops it (then version-gone),
;       never moves it;
;   fn-nlp-offline-pages-join-to-the-report    the offline command's pages
;       (`fn-nlp-take' from the report's start, host/native/io.lisp
;       `fnn-command-live-pages') concatenate to the report.

(in-package "ACL2")
(include-book "native-live-status")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The report, and its cursor

(defun fn-nlp-header (ret)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nls-text "obligations=")
          (fn-nls-nat (len (fn-retain-pins ret)))
          (fn-nls-field "reserved" (fn-retain-reserved ret))
          *fn-nls-lf*))

(defun fn-nlp-report (ret)
  "The `obligations' report of the retention value RET."
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nlp-header ret) (fn-nls-obligation-lines (fn-retain-pins ret))))

(local
 (defthm fn-nlp-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-nlp-report-is-the-obligations-report
  (equal (fn-nls-report :obligations profile s bytes cfg pins obs fn-arena)
         (fn-nlp-report (fn-nls-retention s)))
  :hints (("Goal" :in-theory '(fn-nls-report fn-nlp-report fn-nlp-header
                               fn-nlp-append-assoc))))

; The retention the running owner carries.
(defun fn-nlp-live-retention (oc)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nls-retention (fn-own-store (fn-ocfg-owner oc))))

; KEYSTONE (the paged report is the old report).  The subject is
; `fn-nlp-live-retention', which host/native-live-status-host.lisp
; `fn-native-live-pages-host-answer' reads for the first page; the report
; of it is, with no hypothesis, the whole report the owner rendered before
; (`fn-nls-live-report' of kind :obligations), and so the offline report
; (`fn-nls-live-report-is-the-offline-report').
(defthm fn-nlp-live-report-is-the-report
  (equal (fn-nls-live-report :obligations profile oc cache obs fn-arena)
         (fn-nlp-report (fn-nlp-live-retention oc)))
  :hints (("Goal" :in-theory '(fn-nls-live-report fn-nlp-live-retention
                               fn-nlp-report-is-the-obligations-report))))

; A cursor (PEND . ITEMS): the unsent octets of the current line, and the
; obligations not yet rendered.  What is left of the report:
(defun fn-nlp-stream (pend items)
  (declare (xargs :guard t :verify-guards nil))
  (append (true-list-fix pend) (fn-nls-obligation-lines items)))

; Fill: render whole lines while they fit in NEED octets, and the head of the
; line that does not.  ACC is the page so far, reversed.  (ACC' PEND' ITEMS').
(defun fn-nlp-fill (items need acc)
  (declare (xargs :guard (natp need) :measure (len items) :verify-guards nil))
  (if (or (zp need) (atom items))
      (mv acc nil items)
    (let ((line (fn-nls-obligation-line (car items))))
      (if (< (len line) need)
          (fn-nlp-fill (cdr items) (- need (len line)) (revappend line acc))
        (mv (revappend (take need line) acc) (nthcdr need line) (cdr items))))))

; One page of at most W octets from the cursor: (CHUNK PEND' ITEMS').
(defun fn-nlp-take (pend items w)
  (declare (xargs :guard t :verify-guards nil))
  (let ((pend (true-list-fix pend)) (w (nfix w)))
    (if (<= w (len pend))
        (list (take w pend) (nthcdr w pend) items)
      (mv-let (acc p i)
        (fn-nlp-fill items (- w (len pend)) (revappend pend nil))
        (list (reverse acc) p i)))))

(defun fn-nlp-donep (pend items)
  (declare (xargs :guard t))
  (and (atom pend) (atom items)))

; -----------------------------------------------------------------------------
; The cut, proved

(local
 (defthm fn-nlp-lines-of-cons
   (equal (fn-nls-obligation-lines (cons o items))
          (append (fn-nls-obligation-line o) (fn-nls-obligation-lines items)))
   :hints (("Goal" :expand ((fn-nls-obligation-lines (cons o items)))
            :in-theory '(car-cons cdr-cons)))))

(local
 (defthm fn-nlp-lines-of-atom
   (implies (atom items) (equal (fn-nls-obligation-lines items) nil))))

(local (in-theory (disable fn-nls-obligation-lines fn-nls-obligation-line)))

(local
 (defthm fn-nlp-true-listp-of-line
   (true-listp (fn-nls-obligation-line o))
   :hints (("Goal" :in-theory (enable fn-nls-obligation-line)))))

(local
 (defthm fn-nlp-true-listp-of-lines
   (true-listp (fn-nls-obligation-lines items))
   :hints (("Goal" :induct (len items)))))

(local
 (defthm fn-nlp-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-nlp-take-of-append
   (implies (natp n)
            (equal (take n (append a b))
                   (if (<= n (len a))
                       (take n a)
                     (append (true-list-fix a) (take (- n (len a)) b)))))
   :hints (("Goal" :induct (nthcdr n a) :in-theory (enable take nthcdr)))))

(local
 (defthm fn-nlp-nthcdr-of-append
   (implies (natp n)
            (equal (nthcdr n (append a b))
                   (if (<= n (len a))
                       (append (nthcdr n a) b)
                     (nthcdr (- n (len a)) b))))
   :hints (("Goal" :induct (nthcdr n a) :in-theory (enable nthcdr)))))

(local
 (defthm fn-nlp-take-of-true-list-fix
   (equal (take n (true-list-fix x)) (take n x))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-nlp-true-listp-take
   (true-listp (take n x))))

(local
 (defthm fn-nlp-len-take
   (equal (len (take n x)) (nfix n))))

(local
 (defthm fn-nlp-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr n x)))))

(local
 (defthm fn-nlp-take-len
   (implies (true-listp x) (equal (take (len x) x) x))))

(local
 (defthm fn-nlp-nthcdr-len
   (implies (true-listp x) (equal (nthcdr (len x) x) nil))))

(local
 (defthm fn-nlp-take-past-len
   (implies (and (true-listp x) (<= (len x) (nfix n)))
            (equal (take (min n (len x)) x) x))))

(local
 (defthm fn-nlp-len-zero-of-true-list
   (implies (true-listp x)
            (equal (equal (len x) 0) (equal x nil)))))

(local
 (defthm fn-nlp-take-of-len-of-true-list
   (implies (true-listp x) (equal (take (len x) x) x))))

; What one fill takes: the first min(NEED, |lines|) octets of the lines, onto
; ACC reversed; the cursor it leaves is the rest.
(defthm fn-nlp-fill-cuts-the-lines
  (implies (natp need)
           (let* ((r (fn-nlp-fill items need acc))
                  (l (fn-nls-obligation-lines items))
                  (m (min need (len l))))
             (and (equal (mv-nth 0 r) (revappend (take m l) acc))
                  (equal (fn-nlp-stream (mv-nth 1 r) (mv-nth 2 r)) (nthcdr m l))
                  (true-listp (mv-nth 1 r)))))
  :hints (("Goal" :induct (fn-nlp-fill items need acc))))

(local
 (defthm fn-nlp-take-cuts-a-true-list
   (implies (true-listp pend)
            (let* ((r (fn-nlp-take pend items w))
                   (st (fn-nlp-stream pend items))
                   (m (min (nfix w) (len st))))
              (and (equal (car r) (take m st))
                   (equal (fn-nlp-stream (cadr r) (caddr r)) (nthcdr m st)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-nlp-fill-cuts-the-lines
                             (need (- (nfix w) (len pend)))
                             (acc (revappend pend nil))))))))

(local
 (defthm fn-nlp-true-list-fix-idempotent
   (equal (true-list-fix (true-list-fix x)) (true-list-fix x))))

; The page is the next min(W, |rest|) octets of the rest, and the cursor it
; leaves is what follows them.
(defthm fn-nlp-take-cuts-the-stream
  (let* ((r (fn-nlp-take pend items w))
         (st (fn-nlp-stream pend items))
         (m (min (nfix w) (len st))))
    (and (equal (car r) (take m st))
         (equal (fn-nlp-stream (cadr r) (caddr r)) (nthcdr m st))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nlp-take-cuts-a-true-list (pend (true-list-fix pend))))
           :in-theory (e/d (fn-nlp-stream fn-nlp-take)
                           (fn-nlp-take-cuts-a-true-list fn-nlp-fill)))))

(defthm fn-nlp-stream-of-done
  (implies (fn-nlp-donep pend items)
           (equal (fn-nlp-stream pend items) nil)))

; -----------------------------------------------------------------------------
; The exchange: FNLS frames kind 4 (request) and 5 (reply)
;
; Request: uint KIND-CODE (`fn-nls-kind-code'), uint VERSION (0 starts a
; report), uint PAGE.  Reply: uint STATUS (1 accepted, 2 refused, 3
; version-gone), uint VERSION, uint PAGE, uint DONE (1 on the report's last
; page), bytes CHUNK (at most W octets of the report).

(defconst *fn-nlp-request-kind* 4)
(defconst *fn-nlp-reply-kind* 5)
(defconst *fn-nlp-kinds* '(:obligations))
; Work bound: the report cursors the owner keeps at once (the oldest is
; dropped; its client is answered version-gone and restarts).
(defconst *fn-nlp-max-versions* 4)

(defun fn-nlp-pagedp (kind)
  "KIND is sent page by page with a version token, never rendered whole."
  (declare (xargs :guard t))
  (if (member-equal kind *fn-nlp-kinds*) t nil))

(defun fn-nlp-request-encode (kind version page)
  (declare (xargs :guard t))
  (if (not (and (fn-nlp-pagedp kind)
                (fn-record-uint32p version)
                (fn-record-uint32p page)))
      :bad
    (fn-nls-seal *fn-nlp-request-kind*
                 (append (fn-cbor-encode (cons :uint (fn-nls-kind-code kind)))
                         (fn-cbor-encode (cons :uint version))
                         (fn-cbor-encode (cons :uint page))))))

(defun fn-nlp-request-decode (octets)
  "(:page KIND VERSION PAGE), or (:refused REASON)."
  (declare (xargs :guard t :verify-guards nil))
  (let ((opened (fn-nls-open octets *fn-nlp-request-kind*)))
    (if (not (fn-frame-result-okp opened))
        (list :refused :frame)
      (let* ((r1 (fn-record-read-uint (fn-frame-result-payload opened)))
             (r2 (fn-record-read-uint (fn-record-parse-rest r1)))
             (r3 (fn-record-read-uint (fn-record-parse-rest r2))))
        (if (not (and (fn-record-parse-okp r1) (fn-record-parse-okp r2)
                      (fn-record-parse-okp r3)
                      (fn-nlp-pagedp (fn-nls-code-kind (fn-record-parse-value r1)))
                      (fn-record-uint32p (fn-record-parse-value r2))
                      (fn-record-uint32p (fn-record-parse-value r3))
                      (null (fn-record-parse-rest r3))))
            (list :refused :fields)
          (list :page (fn-nls-code-kind (fn-record-parse-value r1))
                (fn-record-parse-value r2) (fn-record-parse-value r3)))))))

(defun fn-nlp-status-code (status)
  (declare (xargs :guard t))
  (cond ((equal status :accepted) 1) ((equal status :version-gone) 3) (t 2)))

(defun fn-nlp-code-status (code)
  (declare (xargs :guard t))
  (cond ((equal code 1) :accepted) ((equal code 3) :version-gone) (t :refused)))

(defun fn-nlp-reply-payload (status version page donep chunk)
  (declare (xargs :guard t))
  (append (fn-cbor-encode (cons :uint (fn-nlp-status-code status)))
          (fn-cbor-encode (cons :uint version))
          (fn-cbor-encode (cons :uint page))
          (fn-cbor-encode (cons :uint (if donep 1 0)))
          (fn-record-item-encode (cons :bytes chunk))))

(defun fn-nlp-reply-encode (status version page donep chunk)
  (declare (xargs :guard t))
  (fn-nls-seal *fn-nlp-reply-kind*
               (fn-nlp-reply-payload status version page donep chunk)))

(defun fn-nlp-reply-decode (octets)
  "(:page-reply STATUS VERSION PAGE DONEP CHUNK), or :bad."
  (declare (xargs :guard t :verify-guards nil))
  (let ((opened (fn-nls-open octets *fn-nlp-reply-kind*)))
    (if (not (fn-frame-result-okp opened))
        :bad
      (let* ((r1 (fn-record-read-uint (fn-frame-result-payload opened)))
             (r2 (fn-record-read-uint (fn-record-parse-rest r1)))
             (r3 (fn-record-read-uint (fn-record-parse-rest r2)))
             (r4 (fn-record-read-uint (fn-record-parse-rest r3)))
             (r5 (fn-record-read-bytes (fn-record-parse-rest r4))))
        (if (not (and (fn-record-parse-okp r1) (fn-record-parse-okp r2)
                      (fn-record-parse-okp r3) (fn-record-parse-okp r4)
                      (fn-record-parse-okp r5)
                      (null (fn-record-parse-rest r5))))
            :bad
          (list :page-reply
                (fn-nlp-code-status (fn-record-parse-value r1))
                (fn-record-parse-value r2)
                (fn-record-parse-value r3)
                (equal (fn-record-parse-value r4) 1)
                (fn-record-parse-value r5)))))))

; -----------------------------------------------------------------------------
; The owner's cursors
;
; CACHE is (LAST . ENTRIES): LAST the last version issued, ENTRIES the
; cursors newest first, each (VERSION PAGE PEND ITEMS): the page the next
; request of VERSION must name, and the cursor it is answered from.  The
; host carries CACHE; ACL2 chooses it.

(defun fn-nlp-cache-last (cache)
  (declare (xargs :guard t))
  (if (consp cache) (car cache) 0))

(defun fn-nlp-cache-entries (cache)
  (declare (xargs :guard t))
  (if (consp cache) (cdr cache) nil))

(defun fn-nlp-find (v entries)
  (declare (xargs :guard t))
  (cond ((atom entries) nil)
        ((and (consp (car entries)) (equal (car (car entries)) v)) (car entries))
        (t (fn-nlp-find v (cdr entries)))))

(defun fn-nlp-drop (v entries)
  (declare (xargs :guard t))
  (cond ((atom entries) nil)
        ((and (consp (car entries)) (equal (car (car entries)) v))
         (fn-nlp-drop v (cdr entries)))
        (t (cons (car entries) (fn-nlp-drop v (cdr entries))))))

(defun fn-nlp-prefix (n entries)
  "The first N ENTRIES (fewer when there are fewer)."
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom entries))
      nil
    (cons (car entries) (fn-nlp-prefix (1- n) (cdr entries)))))

(defun fn-nlp-next-version (last)
  (declare (xargs :guard t))
  (if (and (natp last) (< last *fn-cbor-max-uint*)) (+ 1 last) 1))

(defun fn-nlp-next-page (page)
  (declare (xargs :guard t))
  (if (and (natp page) (< page *fn-cbor-max-uint*)) (+ 1 page) 0))

(defun fn-nlp-keep (v page pend items entries)
  (declare (xargs :guard t))
  (cons (list v page pend items)
        (fn-nlp-prefix (- *fn-nlp-max-versions* 1) (fn-nlp-drop v entries))))

; One page of version V from the cursor (PEND . ITEMS): (REPLY CACHE').  The
; cursor of a report read to its end is dropped.  A page that is not octets
; or wider than the frame carries (only a width W past the chunk) is
; refused, and its cursor dropped.
(defun fn-nlp-serve (v page pend items last entries w)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((r (fn-nlp-take pend items w))
         (chunk (car r))
         (donep (fn-nlp-donep (cadr r) (caddr r))))
    (if (not (and (fn-cbor-octet-listp chunk)
                  (<= (len chunk) *fn-nls-chunk-octets*)))
        (list (fn-nlp-reply-encode :refused 0 0 nil nil)
              (cons last (fn-nlp-drop v entries)))
      (list (fn-nlp-reply-encode :accepted v page donep chunk)
            (cons last
                  (if donep
                      (fn-nlp-drop v entries)
                    (fn-nlp-keep v (fn-nlp-next-page page) (cadr r) (caddr r)
                                 entries)))))))

(defun fn-nlp-answer (request cache ret w)
  "The owner's page for one request: (REPLY CACHE').  RET is the retention
the owner holds now; it is read only by a request that starts a report."
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-nlp-request-decode request))
        (last (fn-nlp-cache-last cache))
        (entries (fn-nlp-cache-entries cache)))
    (cond ((not (equal (car d) :page))
           (list (fn-nlp-reply-encode :refused 0 0 nil nil) cache))
          ((equal (nth 2 d) 0)
           (if (equal (nth 3 d) 0)
               (let ((v (fn-nlp-next-version last)))
                 (fn-nlp-serve v 0 (fn-nlp-header ret) (fn-retain-pins ret)
                               v entries w))
             (list (fn-nlp-reply-encode :refused 0 0 nil nil) cache)))
          (t (let ((e (fn-nlp-find (nth 2 d) entries)))
               (if (and (consp e) (equal (nth 1 e) (nth 3 d)))
                   (fn-nlp-serve (nth 2 d) (nth 3 d) (nth 2 e) (nth 3 e)
                                 last entries w)
                 (list (fn-nlp-reply-encode :version-gone 0 0 nil nil) cache)))))))

; The client's word on one page, asked as (VERSION PAGE): (:done CHUNK),
; (:next CHUNK VERSION' PAGE'), (:restart) for version-gone, (:refused),
; (:transport) for a malformed or mismatched page.
(defun fn-nlp-client-step (version page reply)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-nlp-reply-decode reply)))
    (cond ((not (and (consp d) (equal (car d) :page-reply))) (list :transport))
          ((equal (nth 1 d) :version-gone) (list :restart))
          ((not (equal (nth 1 d) :accepted)) (list :refused))
          ((not (and (posp (nth 2 d))
                     (equal (nth 3 d) page)
                     (or (equal version 0) (equal (nth 2 d) version))))
           (list :transport))
          ((nth 4 d) (list :done (nth 5 d)))
          ((not (consp (nth 5 d))) (list :transport))
          (t (list :next (nth 5 d) (nth 2 d) (fn-nlp-next-page page))))))

; The composition the host runs (host/native/control.lisp
; `fnn-control-live-pages' asks, the owner answers each request under its
; mutex): FUEL requests from (VERSION PAGE), the chunks joined.
(defun fn-nlp-run (fuel cache ret w version page)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel)
      (list :fuel)
    (let* ((a (fn-nlp-answer (fn-nlp-request-encode :obligations version page)
                             cache ret w))
           (st (fn-nlp-client-step version page (car a))))
      (if (equal (car st) :next)
          (let ((rest (fn-nlp-run (- fuel 1) (cadr a) ret w (caddr st) (cadddr st))))
            (if (equal (car rest) :done)
                (list :done (append (cadr st) (cadr rest)))
              rest))
        st))))

; What is left of the report version V stands at when PAGE is asked.
(defun fn-nlp-entry-stream (v page cache)
  (declare (xargs :guard t :verify-guards nil))
  (let ((e (fn-nlp-find v (fn-nlp-cache-entries cache))))
    (if (and (consp e) (equal (nth 1 e) page))
        (fn-nlp-stream (nth 2 e) (nth 3 e))
      :none)))

; -----------------------------------------------------------------------------
; The frames, proved

(encapsulate ()
(local
 (defthm fn-nlp-octets-of-append
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))))
(local
 (defthm fn-nlp-read-uint-alone
   (implies (fn-record-uint32p n)
            (equal (fn-record-read-uint (fn-cbor-encode (cons :uint n)))
                   (fn-record-parse-ok n nil)))
   :hints (("Goal" :use ((:instance fn-record-read-uint-of-encoding (rest nil))
                         (:instance fn-record-cbor-encode-octets (value (cons :uint n))))
            :in-theory (disable fn-record-cbor-encode-octets fn-record-read-uint-of-encoding
                                fn-record-read-uint fn-cbor-encode)))))
(local
 (defthm fn-nlp-read-bytes-alone
   (implies (and (fn-cbor-octet-listp xs) (<= (len xs) *fn-record-max-octets*))
            (equal (fn-record-read-bytes (fn-record-item-encode (cons :bytes xs)))
                   (fn-record-parse-ok xs nil)))
   :hints (("Goal" :use ((:instance fn-record-read-bytes-of-item-encoding (rest nil))
                         (:instance fn-record-item-encode-true-list (value (cons :bytes xs))))
            :in-theory (disable fn-record-read-bytes-of-item-encoding
                                fn-record-item-encode-true-list
                                fn-record-read-bytes fn-record-item-encode)))))
(local
 (defthm fn-nlp-len-append-c
   (equal (len (append a b)) (+ (len a) (len b)))))
(local
 (defthm fn-nlp-request-payload-octets
   (and (fn-cbor-octet-listp
         (append (fn-cbor-encode (cons :uint a)) (fn-cbor-encode (cons :uint b))
                 (fn-cbor-encode (cons :uint c))))
        (<= (len (append (fn-cbor-encode (cons :uint a)) (fn-cbor-encode (cons :uint b))
                         (fn-cbor-encode (cons :uint c))))
            15))
   :hints (("Goal" :in-theory (e/d (fn-record-cbor-encode-octets
                                    fn-record-cbor-uint-encoding-bound)
                                   (fn-cbor-encode (:e fn-cbor-encode)))))))
(local
 (defthm fn-nlp-open-of-request-encode
   (implies (and (fn-nlp-pagedp kind)
                 (fn-record-uint32p version)
                 (fn-record-uint32p page))
            (equal (fn-nls-open (fn-nlp-request-encode kind version page) 4)
                   (fn-frame-ok *fn-nls-magic* *fn-nls-version* 4
                                (append (fn-cbor-encode (cons :uint (fn-nls-kind-code kind)))
                                        (fn-cbor-encode (cons :uint version))
                                        (fn-cbor-encode (cons :uint page))))))
   :hints (("Goal" :use ((:instance fn-nls-open-of-seal
                                    (kind 4)
                                    (payload (append (fn-cbor-encode (cons :uint (fn-nls-kind-code kind)))
                                                     (fn-cbor-encode (cons :uint version))
                                                     (fn-cbor-encode (cons :uint page)))))
                         (:instance fn-nlp-request-payload-octets
                                    (a (fn-nls-kind-code kind)) (b version) (c page)))
            :in-theory (e/d (fn-nlp-request-encode)
                            (fn-nls-open-of-seal fn-nlp-request-payload-octets
                             fn-nls-open fn-nls-seal fn-nls-kind-code
                             fn-cbor-encode (:e fn-cbor-encode)))))))
; The owner reads back the kind, version and page the client framed.
(defthm fn-nlp-request-decode-of-encode
  (implies (and (fn-nlp-pagedp kind)
                (fn-record-uint32p version)
                (fn-record-uint32p page))
           (equal (fn-nlp-request-decode (fn-nlp-request-encode kind version page))
                  (list :page kind version page)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nlp-request-decode fn-nlp-pagedp
                            fn-nls-kind-code fn-nls-code-kind
                            fn-record-read-uint-of-encoding
                            fn-record-cbor-encode-octets
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload)
                           (fn-nlp-request-encode fn-nls-open fn-nls-seal fn-record-read-uint
                            fn-cbor-encode (:e fn-cbor-encode))))))

(local
 (defthm fn-nlp-reply-payload-facts
   (and (fn-cbor-octet-listp (fn-nlp-reply-payload status version page donep chunk))
        (<= (len (fn-nlp-reply-payload status version page donep chunk))
            (+ 25 (len chunk))))
   :hints (("Goal" :in-theory (e/d (fn-nlp-reply-payload fn-record-cbor-encode-octets
                                    fn-record-item-encode-octets
                                    fn-record-cbor-uint-encoding-bound
                                    fn-nls-bytes-item-length)
                                   (fn-cbor-encode fn-record-item-encode
                                    (:e fn-cbor-encode)))))))
(local
 (defthm fn-nlp-open-of-reply-encode
   (implies (<= (len chunk) *fn-nls-chunk-octets*)
            (equal (fn-nls-open (fn-nlp-reply-encode status version page donep chunk) 5)
                   (fn-frame-ok *fn-nls-magic* *fn-nls-version* 5
                                (fn-nlp-reply-payload status version page donep chunk))))
   :hints (("Goal" :use ((:instance fn-nls-open-of-seal
                                    (kind 5)
                                    (payload (fn-nlp-reply-payload status version page donep chunk)))
                         fn-nlp-reply-payload-facts)
            :in-theory (e/d (fn-nlp-reply-encode)
                            (fn-nls-open-of-seal fn-nlp-reply-payload-facts
                             fn-nlp-reply-payload fn-nls-open fn-nls-seal))))))
; The client reads back the status, version, page, last-page flag and chunk
; the owner framed.
(defthm fn-nlp-reply-decode-of-encode
  (implies (and (member-equal status '(:accepted :refused :version-gone))
                (fn-record-uint32p version)
                (fn-record-uint32p page)
                (fn-cbor-octet-listp chunk)
                (<= (len chunk) *fn-nls-chunk-octets*))
           (equal (fn-nlp-reply-decode (fn-nlp-reply-encode status version page donep chunk))
                  (list :page-reply status version page (if donep t nil) chunk)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nlp-reply-decode fn-nlp-reply-payload
                            fn-nlp-status-code fn-nlp-code-status
                            fn-record-read-uint-of-encoding
                            fn-record-read-bytes-of-item-encoding
                            fn-record-cbor-encode-octets fn-record-item-encode-octets
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload)
                           (fn-nlp-reply-encode fn-nls-open fn-nls-seal fn-record-read-uint
                            fn-record-read-bytes fn-cbor-encode fn-record-item-encode
                            (:e fn-cbor-encode))))))
)

; -----------------------------------------------------------------------------
; The join, proved

(local (in-theory (disable (:e fn-nlp-reply-encode) (:e fn-nlp-request-encode))))

(local
 (defthm fn-nlp-next-page-u32
   (fn-record-uint32p (fn-nlp-next-page page))
   :hints (("Goal" :in-theory (enable fn-record-uint32p)))))

(local
 (defthm fn-nlp-next-version-u32
   (and (fn-record-uint32p (fn-nlp-next-version last))
        (posp (fn-nlp-next-version last)))
   :hints (("Goal" :in-theory (enable fn-record-uint32p)))))

(local
 (defthm fn-nlp-find-of-keep
   (equal (fn-nlp-find v (fn-nlp-keep v page pend items entries))
          (list v page pend items))))

(local
 (defthm fn-nlp-true-listp-stream
   (true-listp (fn-nlp-stream pend items))))

(local
 (defthm fn-nlp-len-of-page
   (<= (len (car (fn-nlp-take pend items w))) (nfix w))
   :rule-classes :linear
   :hints (("Goal" :use fn-nlp-take-cuts-the-stream
            :in-theory (disable fn-nlp-take-cuts-the-stream fn-nlp-take fn-nlp-stream)))))

(local
 (defthm fn-nlp-append-take-nthcdr
   (implies (and (true-listp st) (natp m) (<= m (len st)))
            (equal (append (take m st) (nthcdr m st)) st))
   :hints (("Goal" :induct (nthcdr m st) :in-theory (enable take nthcdr)))))

(local
 (defthm fn-nlp-take-when-nthcdr-empty
   (implies (and (true-listp st) (natp m) (<= m (len st))
                 (not (consp (nthcdr m st))))
            (equal (take m st) st))
   :hints (("Goal" :induct (nthcdr m st) :in-theory (enable take nthcdr)))))

; A last page is all that was left.
(local
 (defthm fn-nlp-last-page-is-the-rest
   (implies (fn-nlp-donep (cadr (fn-nlp-take pend items w))
                          (caddr (fn-nlp-take pend items w)))
            (equal (car (fn-nlp-take pend items w))
                   (fn-nlp-stream pend items)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-nlp-take-cuts-the-stream
                  (:instance fn-nlp-stream-of-done
                             (pend (cadr (fn-nlp-take pend items w)))
                             (items (caddr (fn-nlp-take pend items w))))
                  (:instance fn-nlp-take-when-nthcdr-empty
                             (st (fn-nlp-stream pend items))
                             (m (min (nfix w) (len (fn-nlp-stream pend items))))))
            :in-theory (disable fn-nlp-take-cuts-the-stream fn-nlp-stream-of-done
                                fn-nlp-take-when-nthcdr-empty
                                fn-nlp-take fn-nlp-stream fn-nlp-donep)))))

; The owner's answer to a request that names a version.
(local
 (defthm fn-nlp-answer-of-a-version
   (implies (and (posp v) (fn-record-uint32p v) (fn-record-uint32p page))
            (equal (fn-nlp-answer (fn-nlp-request-encode :obligations v page) cache ret w)
                   (let ((e (fn-nlp-find v (fn-nlp-cache-entries cache))))
                     (if (and (consp e) (equal (nth 1 e) page))
                         (fn-nlp-serve v page (nth 2 e) (nth 3 e)
                                       (fn-nlp-cache-last cache)
                                       (fn-nlp-cache-entries cache) w)
                       (list (fn-nlp-reply-encode :version-gone 0 0 nil nil) cache)))))
   :hints (("Goal" :in-theory (e/d (fn-nlp-answer) (fn-nlp-serve fn-nlp-request-encode
                                                     fn-nlp-request-decode
                                                     fn-nlp-reply-encode fn-nlp-find))))))

; The owner's answer to a request that starts a report.
(local
 (defthm fn-nlp-answer-of-a-start
   (equal (fn-nlp-answer (fn-nlp-request-encode :obligations 0 0) cache ret w)
          (let ((v (fn-nlp-next-version (fn-nlp-cache-last cache))))
            (fn-nlp-serve v 0 (fn-nlp-header ret) (fn-retain-pins ret) v
                          (fn-nlp-cache-entries cache) w)))
   :hints (("Goal" :in-theory (e/d (fn-nlp-answer) (fn-nlp-serve fn-nlp-request-encode
                                                     (:e fn-nlp-request-encode)
                                                     fn-nlp-request-decode
                                                     fn-nlp-reply-encode fn-nlp-header))))))

(local
 (defthm fn-nlp-client-step-of-gone
   (equal (fn-nlp-client-step version page (fn-nlp-reply-encode :version-gone 0 0 nil nil))
          (list :restart))
   :hints (("Goal" :in-theory (e/d (fn-nlp-client-step) (fn-nlp-reply-encode
                                                          (:e fn-nlp-reply-encode)
                                                          fn-nlp-reply-decode))))))

; The client's word on a served page.
(local
 (defthm fn-nlp-client-step-of-serve
   (implies (and (posp w) (<= w *fn-nls-chunk-octets*)
                 (posp v) (fn-record-uint32p v) (fn-record-uint32p page)
                 (or (equal version 0) (equal version v)))
            (equal (fn-nlp-client-step version page
                                       (car (fn-nlp-serve v page pend items last entries w)))
                   (let ((r (fn-nlp-take pend items w)))
                     (cond ((not (and (fn-cbor-octet-listp (car r))
                                      (<= (len (car r)) *fn-nls-chunk-octets*)))
                            (list :refused))
                           ((fn-nlp-donep (cadr r) (caddr r)) (list :done (car r)))
                           ((not (consp (car r))) (list :transport))
                           (t (list :next (car r) v (fn-nlp-next-page page)))))))
   :hints (("Goal" :in-theory (e/d (fn-nlp-client-step fn-nlp-serve)
                                   (fn-nlp-reply-encode (:e fn-nlp-reply-encode)
                                    fn-nlp-reply-decode fn-nlp-take-cuts-the-stream
                                    fn-nlp-take fn-nlp-donep fn-nlp-keep fn-nlp-drop))))))

; What the client can take from a served page, for any width: a :done
; carries the page and the cursor was finished; a :next carries the page, the
; version and the next page, and the cursor was not finished.
(local
 (defthm fn-nlp-client-step-of-serve-any-width
   (implies (and (posp v) (fn-record-uint32p v) (fn-record-uint32p page)
                 (or (equal version 0) (equal version v)))
            (let ((st (fn-nlp-client-step version page
                                          (car (fn-nlp-serve v page pend items last
                                                             entries w))))
                  (r (fn-nlp-take pend items w)))
              (and (implies (equal (car st) :done)
                            (and (fn-nlp-donep (cadr r) (caddr r))
                                 (equal (cadr st) (car r))))
                   (implies (equal (car st) :next)
                            (and (not (fn-nlp-donep (cadr r) (caddr r)))
                                 (fn-cbor-octet-listp (car r))
                                 (<= (len (car r)) *fn-nls-chunk-octets*)
                                 (equal (cadr st) (car r))
                                 (equal (caddr st) v)
                                 (equal (cadddr st) (fn-nlp-next-page page)))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-nlp-client-step fn-nlp-serve)
                            (fn-nlp-reply-encode (:e fn-nlp-reply-encode)
                             fn-nlp-reply-decode fn-nlp-take-cuts-the-stream
                             fn-nlp-take fn-nlp-donep fn-nlp-keep fn-nlp-drop))))))

(local
 (defthm fn-nlp-cache-of-serve
   (implies (and (fn-cbor-octet-listp (car (fn-nlp-take pend items w)))
                 (<= (len (car (fn-nlp-take pend items w))) *fn-nls-chunk-octets*)
                 (not (fn-nlp-donep (cadr (fn-nlp-take pend items w))
                                    (caddr (fn-nlp-take pend items w)))))
            (equal (cadr (fn-nlp-serve v page pend items last entries w))
                   (cons last (fn-nlp-keep v (fn-nlp-next-page page)
                                           (cadr (fn-nlp-take pend items w))
                                           (caddr (fn-nlp-take pend items w))
                                           entries))))
   :hints (("Goal" :in-theory '(fn-nlp-serve car-cons cdr-cons)))))

; A served page: a last page is what was left of the cursor, and a page
; before the last is followed, at the next page, by the rest.
(local
 (defthm fn-nlp-step-of-serve
   (implies (and (posp v) (fn-record-uint32p v) (fn-record-uint32p page)
                 (or (equal version 0) (equal version v)))
            (let* ((a (fn-nlp-serve v page pend items last entries w))
                   (st (fn-nlp-client-step version page (car a))))
              (and (implies (equal (car st) :done)
                            (equal (cadr st) (fn-nlp-stream pend items)))
                   (implies (equal (car st) :next)
                            (and (equal (caddr st) v)
                                 (equal (cadddr st) (fn-nlp-next-page page))
                                 (equal (append (cadr st)
                                                (fn-nlp-entry-stream v (fn-nlp-next-page page)
                                                                     (cadr a)))
                                        (fn-nlp-stream pend items)))))))
   :hints (("Goal" :do-not-induct t
            :use (fn-nlp-take-cuts-the-stream
                  fn-nlp-last-page-is-the-rest
                  fn-nlp-client-step-of-serve-any-width
                  (:instance fn-nlp-append-take-nthcdr
                             (st (fn-nlp-stream pend items))
                             (m (min (nfix w) (len (fn-nlp-stream pend items))))))
            :in-theory (union-theories
                        '(fn-nlp-cache-of-serve fn-nlp-entry-stream fn-nlp-find-of-keep
                          fn-nlp-cache-entries fn-nlp-true-listp-stream
                          car-cons cdr-cons nth-0-cons nth-add1 (:e zp) (:e nfix)
                          min nfix natp posp fix (:type-prescription len)
                          (:compound-recognizer natp-compound-recognizer)
                          (:compound-recognizer posp-compound-recognizer))
                        (theory 'minimal-theory))))))

; One request of a named version: a last page is what was left of the report,
; and a page before the last is followed, at the next page, by the rest.
(local
 (defthm fn-nlp-step-of-a-version
   (implies (and (posp v) (fn-record-uint32p v) (fn-record-uint32p page))
            (let* ((a (fn-nlp-answer (fn-nlp-request-encode :obligations v page)
                                     cache ret w))
                   (st (fn-nlp-client-step v page (car a))))
              (and (implies (equal (car st) :done)
                            (equal (cadr st) (fn-nlp-entry-stream v page cache)))
                   (implies (equal (car st) :next)
                            (and (equal (caddr st) v)
                                 (equal (cadddr st) (fn-nlp-next-page page))
                                 (equal (append (cadr st)
                                                (fn-nlp-entry-stream v (fn-nlp-next-page page)
                                                                     (cadr a)))
                                        (fn-nlp-entry-stream v page cache)))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-nlp-step-of-serve
                             (version v)
                             (pend (nth 2 (fn-nlp-find v (fn-nlp-cache-entries cache))))
                             (items (nth 3 (fn-nlp-find v (fn-nlp-cache-entries cache))))
                             (last (fn-nlp-cache-last cache))
                             (entries (fn-nlp-cache-entries cache))))
            :in-theory (union-theories
                        '(fn-nlp-answer-of-a-version fn-nlp-client-step-of-gone
                          fn-nlp-entry-stream car-cons cdr-cons)
                        (theory 'minimal-theory))))))

; The pages from a named version, joined: what was left of its report.
(local
 (defthm fn-nlp-run-joins-the-entry
   (implies (and (posp v) (fn-record-uint32p v) (fn-record-uint32p page)
                 (equal (car (fn-nlp-run fuel cache ret w v page)) :done))
            (equal (cadr (fn-nlp-run fuel cache ret w v page))
                   (fn-nlp-entry-stream v page cache)))
   :hints (("Goal" :induct (fn-nlp-run fuel cache ret w v page)
            :in-theory '(fn-nlp-run fn-nlp-step-of-a-version fn-nlp-next-page-u32
                         car-cons cdr-cons zp natp posp
                         (:e zp))))))

(local
 (defthm fn-nlp-stream-of-the-start
   (equal (fn-nlp-stream (fn-nlp-header ret) (fn-retain-pins ret))
          (fn-nlp-report ret))))

; A request that starts a report: a last page is the whole report, and a page
; before the last is followed, at page 1 of the version it names, by the rest.
(local
 (defthm fn-nlp-step-of-a-start
   (implies t
            (let* ((a (fn-nlp-answer (fn-nlp-request-encode :obligations 0 0)
                                     cache ret w))
                   (st (fn-nlp-client-step 0 0 (car a))))
              (and (implies (equal (car st) :done)
                            (equal (cadr st) (fn-nlp-report ret)))
                   (implies (equal (car st) :next)
                            (and (posp (caddr st))
                                 (fn-record-uint32p (caddr st))
                                 (equal (cadddr st) 1)
                                 (equal (append (cadr st)
                                                (fn-nlp-entry-stream (caddr st) 1 (cadr a)))
                                        (fn-nlp-report ret)))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-nlp-take-cuts-the-stream
                             (pend (fn-nlp-header ret))
                             (items (fn-retain-pins ret)))
                  (:instance fn-nlp-last-page-is-the-rest
                             (pend (fn-nlp-header ret))
                             (items (fn-retain-pins ret)))
                  (:instance fn-nlp-client-step-of-serve-any-width
                             (version 0) (page 0)
                             (v (fn-nlp-next-version (fn-nlp-cache-last cache)))
                             (pend (fn-nlp-header ret))
                             (items (fn-retain-pins ret))
                             (last (fn-nlp-next-version (fn-nlp-cache-last cache)))
                             (entries (fn-nlp-cache-entries cache))))
            :in-theory (e/d (fn-nlp-entry-stream)
                            (fn-nlp-answer fn-nlp-serve fn-nlp-client-step
                             fn-nlp-client-step-of-serve
                             fn-nlp-take-cuts-the-stream fn-nlp-header fn-nlp-report
                             fn-nlp-next-version fn-nlp-request-encode fn-nlp-reply-encode
                             fn-nlp-take fn-nlp-stream fn-nlp-keep fn-nlp-find
                             fn-nlp-donep))))))

; KEYSTONE (the pages at one version join to the report).  The subjects are
; `fn-nlp-answer' (the owner, host/native-live-status-host.lisp
; `fn-native-live-pages-host-answer', called under the owner mutex by
; host/native/control.lisp `fnn-control-live-pages-answer') and
; `fn-nlp-client-step' (the client, host/native/control.lisp
; `fnn-control-live-pages'), composed as the host composes them
; (`fn-nlp-run').  A client that starts a report and reaches :done has
; joined exactly the report of the retention RET the owner held at the
; first page, whatever the owner's cursors were before: no hypothesis on
; the cache, the ledger, the page width or the fuel.
(defthm fn-nlp-pages-join-to-the-report
  (implies (equal (car (fn-nlp-run fuel cache ret w 0 0)) :done)
           (equal (cadr (fn-nlp-run fuel cache ret w 0 0))
                  (fn-nlp-report ret)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-nlp-run fuel cache ret w 0 0))
           :use ((:instance fn-nlp-step-of-a-start)
                 (:instance fn-nlp-run-joins-the-entry
                            (fuel (- fuel 1))
                            (cache (cadr (fn-nlp-answer (fn-nlp-request-encode :obligations 0 0)
                                                        cache ret w)))
                            (v (caddr (fn-nlp-client-step
                                       0 0 (car (fn-nlp-answer
                                                 (fn-nlp-request-encode :obligations 0 0)
                                                 cache ret w)))))
                            (page 1)))
           :in-theory '(car-cons cdr-cons (:e fn-record-uint32p) (:e posp)))))

; -----------------------------------------------------------------------------
; Progress: with nothing else between its requests, a client reaches :done

(local
 (defthm fn-nlp-octets-of-append-p
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))))

(local
 (defthm fn-nlp-string-octets-aux-octets
   (implies (character-listp chars)
            (fn-cbor-octet-listp (fn-record-string-octets-aux chars)))
   :hints (("Goal" :in-theory (enable fn-record-string-octets-aux fn-cbor-octet-listp
                                      fn-cbor-octetp)))))

(local
 (defthm fn-nlp-string-octets-octets
   (fn-cbor-octet-listp (fn-record-string-octets x))
   :hints (("Goal" :in-theory (enable fn-record-string-octets)))))

(local
 (defthm fn-nlp-digits-octets
   (implies (fn-cbor-octet-listp acc)
            (fn-cbor-octet-listp (fn-nls-digits n acc)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-nlp-nat-octets
   (fn-cbor-octet-listp (fn-nls-nat n))
   :hints (("Goal" :in-theory (enable fn-nls-nat)))))

(local
 (defthm fn-nlp-value-octets
   (fn-cbor-octet-listp (fn-nls-value v))
   :hints (("Goal" :in-theory (e/d (fn-nls-value fn-nls-text) (fn-record-string-octets))))))

(local
 (defthm fn-nlp-line-octets
   (and (fn-cbor-octet-listp (fn-nls-obligation-line o))
        (consp (fn-nls-obligation-line o)))
   :hints (("Goal" :in-theory (e/d (fn-nls-obligation-line fn-nls-text fn-nls-field
                                    fn-nls-kind-words)
                                   (fn-record-string-octets))))))

(local
 (defthm fn-nlp-lines-octets
   (fn-cbor-octet-listp (fn-nls-obligation-lines items))
   :hints (("Goal" :induct (len items)))))

(local
 (defthm fn-nlp-lines-empty
   (iff (consp (fn-nls-obligation-lines items)) (consp items))
   :hints (("Goal" :induct (len items)))))

(defthm fn-nlp-report-is-octets
  (fn-cbor-octet-listp (fn-nlp-report ret))
  :hints (("Goal" :in-theory (e/d (fn-nlp-report fn-nlp-header fn-nls-text fn-nls-field)
                                  (fn-record-string-octets)))))

; An empty rest is a finished cursor, and a finished cursor an empty rest.
(local
 (defthm fn-nlp-donep-is-empty-stream
   (iff (fn-nlp-donep pend items)
        (not (consp (fn-nlp-stream pend items))))
   :hints (("Goal" :in-theory (enable fn-nlp-stream fn-nlp-donep)))))

(local
 (defthm fn-nlp-octets-of-take
   (implies (and (fn-cbor-octet-listp x) (<= (nfix m) (len x)))
            (fn-cbor-octet-listp (take m x)))
   :hints (("Goal" :in-theory (enable take fn-cbor-octet-listp)))))

(local
 (defthm fn-nlp-octets-of-nthcdr
   (implies (fn-cbor-octet-listp x)
            (fn-cbor-octet-listp (nthcdr m x)))
   :hints (("Goal" :in-theory (enable nthcdr fn-cbor-octet-listp)))))

(local
 (defthm fn-nlp-len-nthcdr
   (equal (len (nthcdr m x)) (nfix (- (len x) (nfix m))))
   :hints (("Goal" :induct (nthcdr m x) :in-theory (enable nthcdr)))))

(local
 (defthm fn-nlp-consp-nthcdr
   (iff (consp (nthcdr m x)) (< (nfix m) (len x)))
   :hints (("Goal" :induct (nthcdr m x) :in-theory (enable nthcdr)))))

(local
 (defthm fn-nlp-nthcdr-nonnil
   (implies (true-listp x)
            (iff (nthcdr m x) (< (nfix m) (len x))))
   :hints (("Goal" :induct (nthcdr m x) :in-theory (enable nthcdr)))))

(local
 (defthm fn-nlp-consp-take
   (implies (posp m) (consp (take m x)))))

(local
 (defthm fn-nlp-step-of-a-version-progress
   (implies (and (posp w) (<= w *fn-nls-chunk-octets*)
                 (posp v) (fn-record-uint32p v) (fn-record-uint32p page)
                 (not (equal (fn-nlp-entry-stream v page cache) :none))
                 (fn-cbor-octet-listp (fn-nlp-entry-stream v page cache)))
            (let* ((s (fn-nlp-entry-stream v page cache))
                   (a (fn-nlp-answer (fn-nlp-request-encode :obligations v page)
                                     cache ret w))
                   (st (fn-nlp-client-step v page (car a))))
              (if (<= (len s) w)
                  (equal st (list :done s))
                (and (equal (car st) :next)
                     (equal (cadr st) (take w s))
                     (equal (caddr st) v)
                     (equal (cadddr st) (fn-nlp-next-page page))
                     (equal (fn-nlp-entry-stream v (fn-nlp-next-page page) (cadr a))
                            (nthcdr w s))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-nlp-take-cuts-the-stream
                             (pend (nth 2 (fn-nlp-find v (fn-nlp-cache-entries cache))))
                             (items (nth 3 (fn-nlp-find v (fn-nlp-cache-entries cache)))))
                  (:instance fn-nlp-donep-is-empty-stream
                             (pend (cadr (fn-nlp-take
                                          (nth 2 (fn-nlp-find v (fn-nlp-cache-entries cache)))
                                          (nth 3 (fn-nlp-find v (fn-nlp-cache-entries cache)))
                                          w)))
                             (items (caddr (fn-nlp-take
                                            (nth 2 (fn-nlp-find v (fn-nlp-cache-entries cache)))
                                            (nth 3 (fn-nlp-find v (fn-nlp-cache-entries cache)))
                                            w)))))
            :in-theory (e/d (fn-nlp-entry-stream)
                            (fn-nlp-answer fn-nlp-serve fn-nlp-client-step
                             fn-nlp-take-cuts-the-stream fn-nlp-donep-is-empty-stream
                             fn-nlp-request-encode fn-nlp-reply-encode
                             fn-nlp-take fn-nlp-stream fn-nlp-keep fn-nlp-find
                             fn-nlp-donep))))))

(local
 (defthm fn-nlp-fuel-arith
   (implies (and (natp l) (posp w) (posp fuel) (< w l) (<= l (* w fuel)))
            (and (<= (- l w) (* w (- fuel 1)))
                 (posp (- fuel 1))))
   :hints (("Goal" :cases ((equal fuel 1) (< 1 fuel)) :nonlinearp t))))

(local
 (defthm fn-nlp-entry-stream-is-a-list
   (implies (not (equal (fn-nlp-entry-stream v page cache) :none))
            (true-listp (fn-nlp-entry-stream v page cache)))
   :hints (("Goal" :in-theory (enable fn-nlp-entry-stream)))))

(local
 (defthm fn-nlp-nthcdr-is-not-none
   (implies (true-listp x) (not (equal (nthcdr m x) :none)))))

(local
 (defthm fn-nlp-run-reaches-the-entry
   (implies (and (posp w) (<= w *fn-nls-chunk-octets*)
                 (posp v) (fn-record-uint32p v) (fn-record-uint32p page)
                 (not (equal (fn-nlp-entry-stream v page cache) :none))
                 (fn-cbor-octet-listp (fn-nlp-entry-stream v page cache))
                 (posp fuel)
                 (<= (len (fn-nlp-entry-stream v page cache)) (* w fuel)))
            (equal (fn-nlp-run fuel cache ret w v page)
                   (list :done (fn-nlp-entry-stream v page cache))))
   :hints (("Goal" :induct (fn-nlp-run fuel cache ret w v page)
            :in-theory (union-theories
                        '(fn-nlp-run fn-nlp-step-of-a-version-progress fn-nlp-next-page-u32
                          fn-nlp-octets-of-nthcdr fn-nlp-len-nthcdr fn-nlp-fuel-arith
                          fn-nlp-append-take-nthcdr fn-nlp-entry-stream-is-a-list
                          fn-nlp-nthcdr-is-not-none
                          posp natp nfix zp car-cons cdr-cons (:e zp)
                          (:type-prescription len) unicity-of-1 commutativity-of-* fix
                          (:compound-recognizer zp-compound-recognizer)
                          (:compound-recognizer posp-compound-recognizer)
                          (:compound-recognizer natp-compound-recognizer))
                        (theory 'minimal-theory)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-nlp-fuel-arith
                                   (l (len (fn-nlp-entry-stream v page cache))))
                        fn-nlp-step-of-a-version-progress))))))

(local
 (defthm fn-nlp-report-is-a-list
   (true-listp (fn-nlp-report ret))))

(local
 (defthm fn-nlp-take-done-iff
   (iff (fn-nlp-donep (cadr (fn-nlp-take pend items w))
                      (caddr (fn-nlp-take pend items w)))
        (<= (len (fn-nlp-stream pend items)) (nfix w)))
   :hints (("Goal" :do-not-induct t
            :use (fn-nlp-take-cuts-the-stream
                  (:instance fn-nlp-donep-is-empty-stream
                             (pend (cadr (fn-nlp-take pend items w)))
                             (items (caddr (fn-nlp-take pend items w)))))
            :in-theory (disable fn-nlp-take-cuts-the-stream fn-nlp-donep-is-empty-stream
                                fn-nlp-take fn-nlp-stream fn-nlp-donep)))))

(local
 (defthm fn-nlp-step-of-a-start-progress
   (implies (and (posp w) (<= w *fn-nls-chunk-octets*))
            (let* ((s (fn-nlp-report ret))
                   (a (fn-nlp-answer (fn-nlp-request-encode :obligations 0 0)
                                     cache ret w))
                   (st (fn-nlp-client-step 0 0 (car a))))
              (if (<= (len s) w)
                  (equal st (list :done s))
                (and (equal (car st) :next)
                     (equal (cadr st) (take w s))
                     (posp (caddr st))
                     (fn-record-uint32p (caddr st))
                     (equal (cadddr st) 1)
                     (equal (fn-nlp-entry-stream (caddr st) 1 (cadr a))
                            (nthcdr w s))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-nlp-take-cuts-the-stream
                             (pend (fn-nlp-header ret))
                             (items (fn-retain-pins ret)))
                  (:instance fn-nlp-take-done-iff
                             (pend (fn-nlp-header ret))
                             (items (fn-retain-pins ret))))
            :in-theory (e/d (fn-nlp-entry-stream)
                            (fn-nlp-answer fn-nlp-serve fn-nlp-client-step
                             fn-nlp-take-cuts-the-stream fn-nlp-donep-is-empty-stream
                             fn-nlp-take-done-iff
                             fn-nlp-header fn-nlp-report fn-nlp-next-version
                             fn-nlp-request-encode fn-nlp-reply-encode
                             fn-nlp-take fn-nlp-stream fn-nlp-keep fn-nlp-find
                             fn-nlp-donep))))))

; KEYSTONE (a client reaches the report).  With nothing else between its
; requests, a client that starts a report of L octets reaches :done with the
; report within ceiling(L / W) requests (FUEL requests with L <= W * FUEL),
; whatever cursors the owner held before.  With other clients between them,
; `fn-nlp-answer-keeps-other-versions' says what can change: its cursor is
; dropped (version-gone, and the client restarts) or kept, never moved.
(defthm fn-nlp-pages-reach-the-report
  (implies (and (posp w) (<= w *fn-nls-chunk-octets*)
                (posp fuel)
                (<= (len (fn-nlp-report ret)) (* w fuel)))
           (equal (fn-nlp-run fuel cache ret w 0 0)
                  (list :done (fn-nlp-report ret))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-nlp-run fuel cache ret w 0 0))
           :use ((:instance fn-nlp-step-of-a-start-progress)
                 (:instance fn-nlp-fuel-arith (l (len (fn-nlp-report ret))))
                 (:instance fn-nlp-run-reaches-the-entry
                            (fuel (- fuel 1))
                            (cache (cadr (fn-nlp-answer (fn-nlp-request-encode :obligations 0 0)
                                                        cache ret w)))
                            (v (caddr (fn-nlp-client-step
                                       0 0 (car (fn-nlp-answer
                                                 (fn-nlp-request-encode :obligations 0 0)
                                                 cache ret w)))))
                            (page 1)))
           :in-theory (union-theories
                       '(fn-nlp-octets-of-nthcdr fn-nlp-report-is-octets fn-nlp-len-nthcdr
                         fn-nlp-report-is-a-list
                         fn-nlp-append-take-nthcdr fn-nlp-true-listp-stream
                         fn-nlp-nthcdr-is-not-none fn-nlp-stream-of-the-start
                         posp natp nfix zp car-cons cdr-cons fix (:e zp) (:e posp)
                         (:e fn-record-uint32p)
                         (:type-prescription len) unicity-of-1 commutativity-of-*
                         (:compound-recognizer zp-compound-recognizer)
                         (:compound-recognizer posp-compound-recognizer)
                         (:compound-recognizer natp-compound-recognizer))
                       (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; Other clients

(local
 (defthm fn-nlp-find-of-drop-other
   (implies (not (equal u v))
            (equal (fn-nlp-find v (fn-nlp-drop u entries))
                   (fn-nlp-find v entries)))))

(local
 (defthm fn-nlp-find-of-prefix
   (or (equal (fn-nlp-find v (fn-nlp-prefix n entries)) (fn-nlp-find v entries))
       (equal (fn-nlp-find v (fn-nlp-prefix n entries)) nil))
   :rule-classes nil))

(local
 (defthm fn-nlp-find-of-keep-other
   (implies (not (equal u v))
            (or (equal (fn-nlp-find v (fn-nlp-keep u page pend items entries))
                       (fn-nlp-find v entries))
                (equal (fn-nlp-find v (fn-nlp-keep u page pend items entries)) nil)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-nlp-find-of-prefix
                                    (n (- *fn-nlp-max-versions* 1))
                                    (entries (fn-nlp-drop u entries))))))))

(local
 (defthm fn-nlp-serve-keeps-other-versions
   (implies (not (equal u v))
            (let ((after (fn-nlp-find v (fn-nlp-cache-entries
                                         (cadr (fn-nlp-serve u page pend items last
                                                             entries w))))))
              (or (equal after (fn-nlp-find v entries))
                  (equal after nil))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-nlp-find-of-keep-other
                                    (page (fn-nlp-next-page page))
                                    (pend (cadr (fn-nlp-take pend items w)))
                                    (items (caddr (fn-nlp-take pend items w))))
                         (:instance fn-nlp-find-of-drop-other (u u) (v v)))
            :in-theory '(fn-nlp-serve fn-nlp-cache-entries car-cons cdr-cons)))))

; KEYSTONE (a version's cursor is its own).  The subject is `fn-nlp-answer'.
; A request that does not name version V, and that does not start the
; version V (the version counter wraps only after 2^32 - 1 starts), leaves
; V's cursor exactly where it stood, or drops it (the oldest of more than
; `*fn-nlp-max-versions*'): V's client then reads `version-gone' by name and
; restarts; it never reads a page of another report under V.
(defthm fn-nlp-answer-keeps-other-versions
  (let ((d (fn-nlp-request-decode req))
        (after (fn-nlp-entry-stream v page (cadr (fn-nlp-answer req cache ret w)))))
    (implies (and (not (equal (nth 2 d) v))
                  (not (equal (fn-nlp-next-version (fn-nlp-cache-last cache)) v)))
             (or (equal after (fn-nlp-entry-stream v page cache))
                 (equal after :none))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nlp-serve-keeps-other-versions
                            (u (fn-nlp-next-version (fn-nlp-cache-last cache)))
                            (page 0) (pend (fn-nlp-header ret)) (items (fn-retain-pins ret))
                            (last (fn-nlp-next-version (fn-nlp-cache-last cache)))
                            (entries (fn-nlp-cache-entries cache)))
                 (:instance fn-nlp-serve-keeps-other-versions
                            (u (nth 2 (fn-nlp-request-decode req)))
                            (page (nth 3 (fn-nlp-request-decode req)))
                            (pend (nth 2 (fn-nlp-find (nth 2 (fn-nlp-request-decode req))
                                                      (fn-nlp-cache-entries cache))))
                            (items (nth 3 (fn-nlp-find (nth 2 (fn-nlp-request-decode req))
                                                       (fn-nlp-cache-entries cache))))
                            (last (fn-nlp-cache-last cache))
                            (entries (fn-nlp-cache-entries cache))))
           :in-theory '(fn-nlp-answer fn-nlp-entry-stream car-cons cdr-cons))))

; -----------------------------------------------------------------------------
; The offline command's pages
;
; `operator CONFIG obligations' with no owner running reads the Store it
; replayed and writes the report a page at a time (host/native/io.lisp
; `fnn-command-live-pages'): the cursor starts at the whole report
; (`fn-nlp-offline-start') and each step writes one page
; (`fn-nlp-offline-step': (CHUNK CURSOR' DONEP)).

(defun fn-nlp-offline-start (ret)
  (declare (xargs :guard t :verify-guards nil))
  (cons (fn-nlp-header ret) (fn-retain-pins ret)))

(defun fn-nlp-cursor-pend (cursor)
  (declare (xargs :guard t))
  (if (consp cursor) (car cursor) nil))

(defun fn-nlp-cursor-items (cursor)
  (declare (xargs :guard t))
  (if (consp cursor) (cdr cursor) nil))

(defun fn-nlp-offline-step (cursor w)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-nlp-take (fn-nlp-cursor-pend cursor) (fn-nlp-cursor-items cursor) w)))
    (list (car r) (cons (cadr r) (caddr r)) (fn-nlp-donep (cadr r) (caddr r)))))

; The host's loop, FUEL steps: (:done OCTETS) or (:fuel).
(defun fn-nlp-offline-run (fuel cursor w)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel)
      (list :fuel)
    (let ((st (fn-nlp-offline-step cursor w)))
      (if (caddr st)
          (list :done (car st))
        (let ((rest (fn-nlp-offline-run (- fuel 1) (cadr st) w)))
          (if (equal (car rest) :done)
              (list :done (append (car st) (cadr rest)))
            rest))))))

(local
 (defthm fn-nlp-offline-run-joins-the-stream
   (implies (equal (car (fn-nlp-offline-run fuel cursor w)) :done)
            (equal (cadr (fn-nlp-offline-run fuel cursor w))
                   (fn-nlp-stream (fn-nlp-cursor-pend cursor) (fn-nlp-cursor-items cursor))))
   :hints (("Goal" :induct (fn-nlp-offline-run fuel cursor w)
            :in-theory (e/d (fn-nlp-offline-step)
                            (fn-nlp-take fn-nlp-stream fn-nlp-donep)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-nlp-last-page-is-the-rest
                                   (pend (fn-nlp-cursor-pend cursor)) (items (fn-nlp-cursor-items cursor)))
                        (:instance fn-nlp-take-cuts-the-stream
                                   (pend (fn-nlp-cursor-pend cursor)) (items (fn-nlp-cursor-items cursor)))))))))

; KEYSTONE (the offline pages join to the report).  The subjects are
; `fn-nlp-offline-start' and `fn-nlp-offline-step', which host/native/io.lisp
; `fnn-command-live-pages' calls (through host/native-live-status-host.lisp
; `fn-native-live-pages-host-offline-start' and `-offline-step'), composed
; as the host composes them: the pages it writes, joined, are the report of
; the Store it replayed, which is the offline report of kind :obligations
; (`fn-nlp-report-is-the-obligations-report').
(defthm fn-nlp-offline-pages-join-to-the-report
  (implies (equal (car (fn-nlp-offline-run fuel (fn-nlp-offline-start ret) w)) :done)
           (equal (cadr (fn-nlp-offline-run fuel (fn-nlp-offline-start ret) w))
                  (fn-nlp-report ret)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-nlp-offline-run-joins-the-stream
                                   (cursor (fn-nlp-offline-start ret))))
           :in-theory '(fn-nlp-offline-start car-cons cdr-cons fn-nlp-cursor-pend fn-nlp-cursor-items
                        (:type-prescription fn-nlp-header)
                        fn-nlp-stream-of-the-start))))

; The page path runs guard-verified: the renderer, the cut, the owner's page
; and the offline step.  (The frame decoders read through
; `fn-record-read-uint', which is not guard-verified, like every FNLS
; decoder of books/native-live-status.lisp.)
(verify-guards fn-nlp-header)
(verify-guards fn-nlp-fill)
(verify-guards fn-nlp-take)
(verify-guards fn-nlp-serve)
(verify-guards fn-nlp-live-retention)
(verify-guards fn-nlp-offline-start)
(verify-guards fn-nlp-offline-step)

; The whole-report exchange (FNLS kind 1) refuses a paged kind BY NAME: the
; owner never renders it whole.  `fn-nls-client-step' reads the word back as
; (:refused) (a client before this lane), `fn-nlp-whole-refusedp' names it.
(defconst *fn-nlp-refusal-paged*
  (fn-record-string-octets "report-is-paged"))
