; D6's keystones, statement first (fn2/docs/d-machines-nntp.md section 15.7).
; Their subject is the served core at its adapter boundary after a seeded
; published state: fn2-cursor-wire-run, the wires of clients reading a
; store whose articles were recorded and published through C-S3's own
; operations (put, arg, resolve, stage, bind, publish), one batch an
; article, before the clients connect (as tests/txn-unit.lisp seeds identity
; facts). The reference is fn2-cursor-spec-wire, the replies RFC 3977 and
; H's model (fn2/tests/model/nntp_model.py) give over the list view of the
; same state; it is written from them, never from the cursor. Teeth are in
; tests/cursor-unit.lisp.
(in-package "ACL2")
(include-book "owed-txn")
(fn2-book-layer :d)

; Reading served beside posting (the seeds use transaction slot 0's
; successor rows), with two groups carried. Each seeded batch takes one
; private overlay per schema it writes (four) and an arena each: 32
; overlays, 64 4 KiB pool slots, and 32 64 KiB slots so the sealer can
; reserve its run pages (it stops the core :sealer-full otherwise,
; C-SEAL-BACKPRESSURE), with one large-upload window.
(defconst *fn2-cursor-overview-sid* 3)
(defconst *fn2-cursor-profile*
 (put-assoc-equal :groups '(("local.test" . 1) ("local.empty" . 2))
  (put-assoc-equal :identity-overlays 32
   (put-assoc-equal :large-upload-windows 1
    (put-assoc-equal :reading t
     (put-assoc-equal :x 2
      (put-assoc-equal :pool-classes '((8 . 1024) (64 . 4096) (32 . 65536)) *fn2-txn-posting-profile*)))))))

; ---------------------------------------------------------------------------
; A seed is (GROUP MID LINE): an article accepted into group GROUP (an
; identifier of the profile's :groups) with Message-ID MID and overview line
; LINE (strings). Seed I is batch and commit position I+1; its number in its
; group is assigned by the group-count fold (high + 1), so numbers follow
; seeding order. Its content identity is 32 octets of I+1 (the content is
; not read by a cursor), its article row live, version 1, of LINE's length.
(defun fn2-cs-octets (s) (declare (xargs :verify-guards nil)) (fn2-cw-chars (coerce s 'list)))
(defun fn2-cs-write (bytes slot gen off fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom bytes) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-core-write slot gen off (car bytes) 200 0 1 fn2-core)
      (if (eq code :ok) (fn2-cs-write (cdr bytes) slot gen (+ 1 off) fn2-core) (mv code fn2-core)))))
(defun fn2-cs-fill (bytes fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv c slot gen fn2-core) (fn2-core-reserve (if (< 1000 (len bytes)) 1 0) 200 0 1 fn2-core))
       ((unless (eq c :ok)) (mv c 0 0 fn2-core))
       ((mv c fn2-core) (fn2-cs-write bytes slot gen 0 fn2-core)))
    (mv c slot gen fn2-core)))
(defun fn2-cs-drive (fuel d fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (zp fuel) (mv :fuel fn2-core)
    (mv-let (answer fn2-core) (fn2-identity-step d 4096 fn2-core)
      (if (eq answer :more) (fn2-cs-drive (- fuel 1) d fn2-core) (mv answer fn2-core)))))
(defun fn2-cs-resolve (fuel tx fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (zp fuel) (mv :fuel fn2-core)
    (mv-let (answer fn2-core) (fn2-successor-resolve tx 4096 fn2-core)
      (if (eq answer :more) (fn2-cs-resolve (- fuel 1) tx fn2-core) (mv answer fn2-core)))))
(defmacro fn2-cs-chain (&rest calls)
  (if (atom calls) '(mv :ok fn2-core)
    (if (atom (cdr calls)) (car calls)
      `(mv-let (c fn2-core) ,(car calls) (if (eq c :ok) (fn2-cs-chain ,@(cdr calls)) (mv (list c ',(car (car calls))) fn2-core))))))
(defun fn2-cs-seed (seed b fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((group (nth 0 seed)) (mid (fn2-cs-octets (nth 1 seed))) (line (fn2-cs-octets (nth 2 seed)))
       ((mv c1 mslot mgen fn2-core) (fn2-cs-fill mid fn2-core))
       ((mv c2 dslot dgen fn2-core) (fn2-cs-fill (make-list 32 :initial-element (mod b 256)) fn2-core))
       ((mv c3 lslot lgen fn2-core) (fn2-cs-fill line fn2-core))
       ((unless (and (eq c1 :ok) (eq c2 :ok) (eq c3 :ok))) (mv (list :fill c1 c2 c3) fn2-core))
       ((mv c fn2-core) (fn2-identity-offer 0 mslot mgen 0 (len mid) dslot dgen 0 200 0 1 fn2-core))
       ((unless (eq c :ok)) (mv (list :offer c) fn2-core))
       ((mv a fn2-core) (fn2-cs-drive 100 0 fn2-core))
       ((unless (eq a :stored)) (mv (list :decide a) fn2-core))
       ((mv c fn2-core)
        (fn2-cs-chain
         (fn2-successor-put 0 0 *fn2-txn-identity-sid* :record fn2-core)
         (fn2-successor-arg 0 0 0 :event 0 fn2-core)
         (fn2-successor-arg 0 0 1 :value 3 fn2-core)
         (fn2-successor-put 0 1 *fn2-txn-counts-sid* :accept fn2-core)
         (fn2-successor-arg 0 1 0 :value group fn2-core)
         (fn2-successor-put 0 2 *fn2-cursor-overview-sid* :insert fn2-core)
         (fn2-successor-arg 0 2 *fn2-overview-entry-field-group* :value group fn2-core)
         (fn2-successor-arg 0 2 *fn2-overview-entry-field-number* :out
                            (+ (* 1 256) *fn2-group-counts-entry-field-high*) fn2-core)
         (fn2-successor-arg 0 2 *fn2-overview-entry-field-article* :event 0 fn2-core)
         (fn2-successor-arg 0 2 *fn2-overview-entry-field-position* :event 0 fn2-core)
         (fn2-successor-arg-octets 0 2 *fn2-overview-entry-field-line* lslot lgen 0 (len line) 200 0 1 fn2-core)
         (fn2-successor-put 0 3 *fn2-txn-article-sid* :insert fn2-core)
         (fn2-successor-arg 0 3 *fn2-article-entry-field-article* :event 0 fn2-core)
         (fn2-successor-arg 0 3 *fn2-article-entry-field-birth* :event 0 fn2-core)
         (fn2-successor-arg 0 3 *fn2-article-entry-field-state* :value *fn2-txn-article-live* fn2-core)
         (fn2-successor-arg 0 3 *fn2-article-entry-field-version* :value *fn2-txn-article-version* fn2-core)
         (fn2-successor-arg-octets 0 3 *fn2-article-entry-field-source* dslot dgen 0 32 200 0 1 fn2-core)
         (fn2-successor-arg 0 3 *fn2-article-entry-field-bytes* :value (len line) fn2-core)
         (fn2-successor-arg 0 3 *fn2-article-entry-field-lines* :value 1 fn2-core)))
       ((unless (eq c :ok)) (mv (list :slots c) fn2-core))
       ((mv c fn2-core) (fn2-cs-resolve 40 0 fn2-core))
       ((unless (eq c :ok)) (mv (list :resolve c) fn2-core))
       ((mv c & fn2-core) (fn2-successor-stage 0 fn2-core))
       ((unless (eq c :ok)) (mv (list :stage c) fn2-core))
       ((mv c fn2-core)
        (fn2-cs-chain
         (fn2-successor-bind 0 b b fn2-core)
         (fn2-successor-publish b fn2-core)
         (fn2-successor-release 0 fn2-core)
         (fn2-core-release mslot mgen 200 0 1 fn2-core)
         (fn2-core-release dslot dgen 200 0 1 fn2-core)
         (fn2-core-release lslot lgen 200 0 1 fn2-core))))
    (mv c fn2-core)))
(defun fn2-cs-seed-all (seeds b fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom seeds) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-cs-seed (car seeds) b fn2-core)
      (if (eq code :ok) (fn2-cs-seed-all (cdr seeds) (+ 1 b) fn2-core) (mv (list b code) fn2-core)))))

; The adapter loop of fn2-cw-loop, counting the core's visits, and
; publishing one seed of LATER (batch B on) after every round in which the
; adapter completed something once the clients have received two lines (the
; greeting and the first reply): publications interleave with the reads
; that follow the first command. (mv status clients visits seeded fn2-core)
(defun fn2-cs-replies (clients)
  (declare (xargs :verify-guards nil))
  (if (atom clients) 0 (+ (count 10 (nth 2 (car clients))) (fn2-cs-replies (cdr clients)))))
(defun fn2-cs-loop (fuel idle accepted clients later b visits seeded fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :fuel clients visits seeded fn2-core)
    (b* (((mv & nobs nvisits nactions fn2-core) (fn2-turn fn2-core))
         ((mv took accepted clients fn2-core) (fn2-cw-adapter-one accepted clients fn2-core))
         ((mv seeded later b fn2-core)
          (if (and took (consp later) (eq seeded :ok) (<= 2 (fn2-cs-replies clients)))
              (mv-let (code fn2-core) (fn2-cs-seed (car later) b fn2-core) (mv code (cdr later) (+ 1 b) fn2-core))
            (mv seeded later b fn2-core)))
         (visits (+ visits (nfix nvisits)))
         (idle (if (or took (< 0 nobs) (< 0 nvisits) (< 0 nactions)) 0 (+ 1 idle))))
      (if (or (<= 3 idle) (not (equal (fn2-core-stop-reason fn2-core) 0)))
          (mv :quiet clients visits seeded fn2-core)
        (fn2-cs-loop (- fuel 1) idle accepted clients later b visits seeded fn2-core)))))

; The served core after SEEDS, then the clients of TRANSCRIPTS (octets and
; chunk sizes), with LATER published while they read: (seeded status wires
; stop-reason visits).
(defun fn2-cursor-serve-run (profile seeds later transcripts)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
           ((mv seeded fn2-core) (fn2-cs-seed-all seeds 1 fn2-core))
           ((mv status clients visits seeded fn2-core)
            (fn2-cs-loop (+ 2000 (* 600 (len transcripts)) (* 4 (fn2-cw-arrivals transcripts)))
                         0 0 (fn2-cw-clients transcripts) later (+ 1 (len seeds)) 0 seeded fn2-core)))
        (mv (list seeded status (fn2-cw-results clients) (fn2-core-stop-reason fn2-core) visits) fn2-core))
      result)))
(defun fn2-cursor-wire-run (profile seeds transcripts)
  (declare (xargs :verify-guards nil))
  (fn2-cursor-serve-run profile seeds nil transcripts))

; ---------------------------------------------------------------------------
; The reference. State: the profile's groups ((NAME . GROUP) ...) and the
; seeds. A connection's selection is (group-name current-number). Commands
; are strings; the covered set is GROUP, LISTGROUP, NEXT, LAST, STAT,
; OVER, XOVER and QUIT, each with the argument forms RFC 3977 gives them.
(defun fn2-csp-words (cs word acc)
  (declare (xargs :verify-guards nil))
  (cond ((atom cs) (reverse (if word (cons (coerce (reverse word) 'string) acc) acc)))
        ((member (car cs) '(#\Space #\Tab))
         (fn2-csp-words (cdr cs) nil (if word (cons (coerce (reverse word) 'string) acc) acc)))
        (t (fn2-csp-words (cdr cs) (cons (car cs) word) acc))))
(defun fn2-csp-split (s) (declare (xargs :verify-guards nil)) (fn2-csp-words (coerce s 'list) nil nil))
(defun fn2-csp-nat (cs acc)
  (declare (xargs :verify-guards nil))
  (cond ((atom cs) acc)
        ((digit-char-p (car cs)) (fn2-csp-nat (cdr cs) (+ (* 10 (nfix acc)) (digit-char-p (car cs)))))
        (t nil)))
(defun fn2-csp-number (s)
  (declare (xargs :verify-guards nil))
  (and (stringp s) (< 0 (length s)) (<= (length s) 16) (fn2-csp-nat (coerce s 'list) 0)))
; "n", "n-", "n-m" as (lo . hi); nil when malformed. HI-OPEN is the bound an
; open range reaches (the model's watermark).
(defun fn2-csp-range (s hi-open)
  (declare (xargs :verify-guards nil))
  (let* ((cs (coerce s 'list)) (dash (position #\- cs)))
    (if (not dash) (let ((n (fn2-csp-number s))) (and n (cons n n)))
      (let ((lo (fn2-csp-number (coerce (take dash cs) 'string)))
            (rest (nthcdr (+ 1 dash) cs)))
        (and lo (if (atom rest) (cons lo hi-open)
                  (let ((hi (fn2-csp-number (coerce rest 'string)))) (and hi (cons lo hi)))))))))
(defun fn2-csp-msgidp (s)
  (declare (xargs :verify-guards nil))
  (and (stringp s) (< 2 (length s)) (eql (char s 0) #\<) (eql (char s (- (length s) 1)) #\>)))
(defun fn2-csp-gid (name groups) (declare (xargs :verify-guards nil)) (cdr (assoc-equal name groups)))
; The group's rows ((number mid line) ...) in number order: seeds in order,
; numbered from 1 within their group.
(defun fn2-csp-rows (gid seeds n)
  (declare (xargs :verify-guards nil))
  (cond ((atom seeds) nil)
        ((equal (nth 0 (car seeds)) gid)
         (cons (list n (nth 1 (car seeds)) (nth 2 (car seeds))) (fn2-csp-rows gid (cdr seeds) (+ 1 n))))
        (t (fn2-csp-rows gid (cdr seeds) n))))
(defun fn2-csp-in (lo hi rows)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil)
        ((and (<= lo (car (car rows))) (<= (car (car rows)) hi)) (cons (car rows) (fn2-csp-in lo hi (cdr rows))))
        (t (fn2-csp-in lo hi (cdr rows)))))
(defun fn2-csp-row (n rows) (declare (xargs :verify-guards nil)) (assoc-equal n rows))
(defun fn2-csp-row-by-mid (mid rows)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil) ((equal (nth 1 (car rows)) mid) (car rows)) (t (fn2-csp-row-by-mid mid (cdr rows)))))
(defun fn2-csp-seeded-mid-p (mid seeds)
  (declare (xargs :verify-guards nil))
  (and (consp seeds) (or (equal (nth 1 (car seeds)) mid) (fn2-csp-seeded-mid-p mid (cdr seeds)))))
;; The overview line of the article seeded with MID.
(defun fn2-csp-seed-line (mid seeds)
  (declare (xargs :verify-guards nil))
  (cond ((atom seeds) "") ((equal (nth 1 (car seeds)) mid) (nth 2 (car seeds))) (t (fn2-csp-seed-line mid (cdr seeds)))))
(defun fn2-csp-high (rows) (declare (xargs :verify-guards nil)) (if (atom rows) 0 (car (car (last rows)))))
(defun fn2-csp-str (n) (declare (xargs :verify-guards nil)) (coerce (explode-nonnegative-integer (nfix n) 10 nil) 'string))
(defun fn2-csp-cat (parts)
  (declare (xargs :verify-guards nil))
  (if (atom parts) "" (concatenate 'string (car parts) (fn2-csp-cat (cdr parts)))))
; GROUP's numbers: an empty group answers 0, high + 1, high (the model's
; (0, wm + 1, wm)).
(defun fn2-csp-211 (name rows tail)
  (declare (xargs :verify-guards nil))
  (let ((high (fn2-csp-high rows)))
    (fn2-csp-cat (list "211 " (fn2-csp-str (len rows)) " " (fn2-csp-str (if rows (car (car rows)) (+ 1 high)))
                       " " (fn2-csp-str high) " " name tail))))
(defun fn2-csp-numbers (rows) (declare (xargs :verify-guards nil))
  (if (atom rows) nil (cons (fn2-csp-str (car (car rows))) (fn2-csp-numbers (cdr rows)))))
(defun fn2-csp-overview (rows) (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons (fn2-csp-cat (list (fn2-csp-str (car (car rows))) (coerce (list (code-char 9)) 'string) (nth 2 (car rows))))
          (fn2-csp-overview (cdr rows)))))

; One command: (mv reply-lines selection close).
(defun fn2-csp-command (line sel groups seeds)
  (declare (xargs :verify-guards nil))
  (b* ((words (fn2-csp-split line)) (verb (string-upcase (or (car words) ""))) (args (cdr words))
       (gname (car sel)) (cur (cadr sel))
       (rows (and gname (fn2-csp-rows (fn2-csp-gid gname groups) seeds 1))))
    (cond
     ((equal verb "QUIT") (mv (list "205 closing connection") sel t))
     ((or (equal verb "GROUP") (equal verb "LISTGROUP"))
      (b* ((listing (equal verb "LISTGROUP"))
           (name (if args (car args) gname))
           ((unless name) (mv (list "412 no newsgroup selected") sel nil))
           ((unless (fn2-csp-gid name groups)) (mv (list "411 no such newsgroup") sel nil))
           (rs (fn2-csp-rows (fn2-csp-gid name groups) seeds 1))
           (bounds (and (cdr args) (fn2-csp-range (cadr args) (fn2-csp-high rs))))
           (shown (if bounds (fn2-csp-in (car bounds) (cdr bounds) rs) rs))
           (sel2 (list name (and rs (car (car rs))))))
        (if listing
            (mv (append (list (fn2-csp-211 name rs " list follows")) (fn2-csp-numbers shown) (list ".")) sel2 nil)
          (mv (list (fn2-csp-211 name rs "")) sel2 nil))))
     ((or (equal verb "NEXT") (equal verb "LAST"))
      (b* (((unless gname) (mv (list "412 no newsgroup selected") sel nil))
           ((unless (and cur (fn2-csp-row cur rows))) (mv (list "420 no current article") sel nil))
           (cands (if (equal verb "NEXT") (fn2-csp-in (+ 1 cur) (fn2-csp-high rows) rows)
                    (fn2-csp-in 0 (- cur 1) rows)))
           ((unless cands) (mv (list (if (equal verb "NEXT") "421 no next article" "422 no previous article")) sel nil))
           (r (if (equal verb "NEXT") (car cands) (car (last cands)))))
        (mv (list (fn2-csp-cat (list "223 " (fn2-csp-str (car r)) " " (nth 1 r) " retrieved"))) (list gname (car r)) nil)))
     ((equal verb "STAT")
      (cond ((and args (fn2-csp-msgidp (car args)))
             (if (fn2-csp-seeded-mid-p (car args) seeds)
                 ;; by Message-ID the number is 0 (RFC 3977 6.2.4; H's model accepts 0)
                 (mv (list (fn2-csp-cat (list "223 0 " (car args) " retrieved"))) sel nil)
               (mv (list "430 no article with that message-id") sel nil)))
            ((not gname) (mv (list "412 no newsgroup selected") sel nil))
            ((and (not args) (not cur)) (mv (list "420 no current article") sel nil))
            (t (let* ((n (if args (fn2-csp-number (car args)) cur)) (r (fn2-csp-row n rows)))
                 (cond (r (mv (list (fn2-csp-cat (list "223 " (fn2-csp-str n) " " (nth 1 r) " retrieved"))) (list gname n) nil))
                       (args (mv (list "423 no article with that number") sel nil))
                       (t (mv (list "420 no current article") sel nil)))))))
     ((or (equal verb "OVER") (equal verb "XOVER"))
      (cond ((and args (fn2-csp-msgidp (car args)))
             (if (fn2-csp-seeded-mid-p (car args) seeds)
                 (let ((r (fn2-csp-row-by-mid (car args) rows)))
                   (mv (append (list "224 overview information follows")
                               (fn2-csp-overview (list (list (if r (car r) 0) (car args)
                                                             (fn2-csp-seed-line (car args) seeds))))
                               (list "."))
                       sel nil))
               (mv (list "430 no article with that message-id") sel nil)))
            ((not gname) (mv (list "412 no newsgroup selected") sel nil))
            ((and (not args) (not cur)) (mv (list "420 no current article") sel nil))
            (t (let* ((b (if args (fn2-csp-range (car args) (fn2-csp-high rows)) (cons cur cur)))
                      (shown (fn2-csp-in (car b) (cdr b) rows)))
                 (cond (shown (mv (append (list "224 overview information follows") (fn2-csp-overview shown) (list ".")) sel nil))
                       ((not args) (mv (list "420 no current article") sel nil))
                       ((equal verb "OVER") (mv (list "423 no articles in that range") sel nil))
                       (t (mv (list "420 no article(s) selected") sel nil)))))))
     (t (mv (list "500 command not recognized") sel nil)))))

; A transcript's replies, the greeting first (posting is served beside
; reading in this profile): (lines close).
(defun fn2-csp-run (lines sel groups seeds acc)
  (declare (xargs :verify-guards nil))
  (if (atom lines) (list (reverse acc) nil)
    (mv-let (reply sel2 close) (fn2-csp-command (car lines) sel groups seeds)
      (if close (list (append (reverse acc) reply) t)
        (fn2-csp-run (cdr lines) sel2 groups seeds (revappend reply acc))))))
(defun fn2-cursor-spec-wire (groups seeds lines)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-csp-run lines (list nil nil) groups seeds nil)))
    (list (fn2-cw-crlf-octets (cons "200 fn-nntp experimental server ready" (car r))) (cadr r))))

; The served wire of one client reading LINES in chunks SIZES after SEEDS,
; with LATER published while it reads; and the core's visits for it.
(defun fn2-cursor-wire-interleaved (seeds later lines sizes)
  (declare (xargs :verify-guards nil))
  (car (nth 2 (fn2-cursor-serve-run *fn2-cursor-profile* seeds later (list (list (fn2-cw-crlf-octets lines) sizes))))))
(defun fn2-cursor-wire-solo (seeds lines sizes)
  (declare (xargs :verify-guards nil))
  (fn2-cursor-wire-interleaved seeds nil lines sizes))
(defun fn2-cursor-visits (seeds lines)
  (declare (xargs :verify-guards nil))
  (nth 4 (fn2-cursor-serve-run *fn2-cursor-profile* seeds nil (list (list (fn2-cw-crlf-octets lines) nil)))))

; The premises: seeds name carried groups with distinct Message-IDs and
; overview lines of printable octets and TAB (no CR or LF); lines are covered
; commands of at most 510 octets ending with QUIT.
(defun fn2-csp-printablep (cs)
  (declare (xargs :verify-guards nil))
  (or (atom cs) (and (characterp (car cs)) (<= 32 (char-code (car cs))) (< (char-code (car cs)) 127)
                     (fn2-csp-printablep (cdr cs)))))
;; An overview line: printable octets and TAB (its field separator).
(defun fn2-csp-linep (cs)
  (declare (xargs :verify-guards nil))
  (or (atom cs) (and (characterp (car cs)) (or (eql (car cs) (code-char 9)) (and (<= 32 (char-code (car cs))) (< (char-code (car cs)) 127)))
                     (fn2-csp-linep (cdr cs)))))
(defun fn2-csp-seedsp (seeds groups mids)
  (declare (xargs :verify-guards nil))
  (if (atom seeds) (null seeds)
    (let ((s (car seeds)))
      (and (true-listp s) (equal (len s) 3) (rassoc-equal (nth 0 s) groups)
           (stringp (nth 1 s)) (fn2-csp-msgidp (nth 1 s)) (<= (length (nth 1 s)) 250)
           (fn2-csp-printablep (coerce (nth 1 s) 'list)) (not (member-equal (nth 1 s) mids))
           (stringp (nth 2 s)) (<= (length (nth 2 s)) 1000) (fn2-csp-linep (coerce (nth 2 s) 'list))
           (fn2-csp-seedsp (cdr seeds) groups (cons (nth 1 s) mids))))))
(defun fn2-csp-coveredp (line)
  (declare (xargs :verify-guards nil))
  (and (stringp line) (<= (length line) 510) (fn2-csp-printablep (coerce line 'list))
       (member-equal (string-upcase (or (car (fn2-csp-split line)) ""))
                     '("GROUP" "LISTGROUP" "NEXT" "LAST" "STAT" "OVER" "XOVER" "QUIT"))))
(defun fn2-csp-linesp (lines)
  (declare (xargs :verify-guards nil))
  (and (consp lines) (fn2-csp-coveredp (car lines))
       (or (and (atom (cdr lines)) (equal (string-upcase (car lines)) "QUIT")) (fn2-csp-linesp (cdr lines)))))

(defthm-owed fn2-cursor-reply-exact (seeds lines sizes)
  (implies (and (fn2-csp-seedsp seeds (fn2-profile-get :groups *fn2-cursor-profile*) nil)
                (fn2-csp-linesp lines) (pos-listp sizes))
           (equal (fn2-cursor-wire-solo seeds lines sizes)
                  (fn2-cursor-spec-wire (fn2-profile-get :groups *fn2-cursor-profile*) seeds lines)))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-cursor-test-spec fn2-cursor-test-spec-negative fn2-cursor-test-seeded)
  :doc "D6 (section 15.7): after a published state seeded through C-S3, a reader's replies to GROUP, LISTGROUP, NEXT, LAST, STAT, OVER and XOVER, in every chunking, are the bytes RFC 3977 and H's model give over the list view of that state (an empty group answers 0 high+1 high; numbers follow commit order within a group; by Message-ID the number is 0, which RFC 3977 and H's model admit). D6 1/n serves all but LISTGROUP with no name and OVER <id> (1/n-b), and tests/cursor-unit.lisp checks served = reference over the transcript less those two, whole and chunked; the row stays owed until 1/n-b.")

; OVER over [LO, HI] after GROUP local.test (group 1).
(defun fn2-cursor-over-lines (lo hi)
  (declare (xargs :verify-guards nil))
  (list "GROUP local.test" (fn2-csp-cat (list "OVER " (fn2-csp-str lo) "-" (fn2-csp-str hi))) "QUIT"))
(defconst *fn2-cursor-visits-base* 64)
(defconst *fn2-cursor-visits-per-entry* 16)
(defthm-owed fn2-cursor-range-cost (seeds lo hi)
  (implies (and (fn2-csp-seedsp seeds (fn2-profile-get :groups *fn2-cursor-profile*) nil) (natp lo) (natp hi) (<= lo hi)
                (<= hi 2147483647))
           (and (equal (fn2-cursor-wire-solo seeds (fn2-cursor-over-lines lo hi) nil)
                       (fn2-cursor-spec-wire (fn2-profile-get :groups *fn2-cursor-profile*) seeds (fn2-cursor-over-lines lo hi)))
                (<= (fn2-cursor-visits seeds (fn2-cursor-over-lines lo hi))
                    (+ *fn2-cursor-visits-base*
                       (* *fn2-cursor-visits-per-entry* (len (fn2-csp-in lo hi (fn2-csp-rows 1 seeds 1))))))))
  :schema :bound :from (:operation-set fn2-conn-wire)
  :teeth (fn2-cursor-test-range-cost fn2-cursor-test-range-cost-negative)
  :doc "Scenario 6 (section 15.4): GROUP then OVER lo-hi is answered exactly, and the core's machine visits for the whole transcript are at most a constant plus a constant per entry in the range, whatever hi - lo is: never a numeric walk. The conjunction keeps it non-vacuous (a node that answers nothing is cheap but not exact).")

;; No command after the first re-pins the view (GROUP and LISTGROUP do).
(defun fn2-csp-no-repin-p (lines)
  (declare (xargs :verify-guards nil))
  (or (atom lines)
      (and (not (member-equal (string-upcase (or (car (fn2-csp-split (car lines))) "")) '("GROUP" "LISTGROUP")))
           (fn2-csp-no-repin-p (cdr lines)))))
(defthm-owed fn2-cursor-view-pinned (seeds later lines sizes)
  (implies (and (fn2-csp-seedsp (append seeds later) (fn2-profile-get :groups *fn2-cursor-profile*) nil)
                (fn2-csp-linesp lines) (pos-listp sizes)
                (equal (string-upcase (car (fn2-csp-split (car lines)))) "GROUP")
                (fn2-csp-no-repin-p (cdr lines)))
           (equal (fn2-cursor-wire-interleaved seeds later lines sizes)
                  (fn2-cursor-spec-wire (fn2-profile-get :groups *fn2-cursor-profile*) seeds lines)))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-cursor-test-pinned fn2-cursor-test-pinned-negative)
  :doc "STORAGE-DESIGN 4 decision 2 (section 15.1, the model's logical snapshot): a connection that opened with GROUP and does not re-pin reads the view pinned there; batches LATER published after its first reply (between its commands and between the pages of a reply) change none of its replies. FN2-CURSOR-WIRE-INTERLEAVED publishes one seed of LATER after each adapter round once the client holds two reply lines.")

; ---------------------------------------------------------------------------
; C-S4 (e): the identity read's typed result (IDENTITY-ACROSS-PEERS ruling
; 8: selection, evidence status as the locally known candidates at this
; cut, availability, coverage, authorization). Its subject reads a store
; seeded as above plus CONFLICTS, conflict evidence recorded through C-S3
; (each (MID BYTE): a content of 32 octets of BYTE for an already accepted
; Message-ID), through read row 0 of a profile that serves reading.
(defconst *fn2-read-profile*
 (put-assoc-equal :groups '(("local.test" . 1) ("local.empty" . 2) ("alt.misc" . 3))
  (put-assoc-equal :reading t
   (put-assoc-equal :x 2
    *fn2-cursor-profile*))))
(defun fn2-cs-conflict (mid byte b fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((mid (fn2-cs-octets mid))
       ((mv & mslot mgen fn2-core) (fn2-cs-fill mid fn2-core))
       ((mv & dslot dgen fn2-core) (fn2-cs-fill (make-list 32 :initial-element byte) fn2-core))
       ((mv c fn2-core) (fn2-identity-offer 0 mslot mgen 0 (len mid) dslot dgen 0 200 0 1 fn2-core))
       ((unless (eq c :ok)) (mv (list :offer c) fn2-core))
       ((mv a fn2-core) (fn2-cs-drive 100 0 fn2-core))
       ((mv c fn2-core)
        (fn2-cs-chain (fn2-successor-put 0 0 *fn2-txn-identity-sid* :record fn2-core)
                      (fn2-successor-arg 0 0 0 :event 0 fn2-core) (fn2-successor-arg 0 0 1 :value 3 fn2-core)))
       ((unless (eq c :ok)) (mv (list a :slots c) fn2-core))
       ((mv c fn2-core) (fn2-cs-resolve 40 0 fn2-core))
       ((unless (eq c :ok)) (mv (list a :resolve c) fn2-core))
       ((mv c & fn2-core) (fn2-successor-stage 0 fn2-core))
       ((unless (eq c :ok)) (mv (list a :stage c) fn2-core))
       ((mv c fn2-core)
        (fn2-cs-chain (fn2-successor-bind 0 b b fn2-core) (fn2-successor-publish b fn2-core) (fn2-successor-release 0 fn2-core)
                      (fn2-core-release mslot mgen 200 0 1 fn2-core) (fn2-core-release dslot dgen 200 0 1 fn2-core))))
    (mv (if (and (eq a :conflict) (eq c :ok)) :ok (list a c)) fn2-core)))
(defun fn2-cs-conflict-all (conflicts b fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom conflicts) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-cs-conflict (car (car conflicts)) (cadr (car conflicts)) b fn2-core)
      (if (eq code :ok) (fn2-cs-conflict-all (cdr conflicts) (+ 1 b) fn2-core) (mv (list b code) fn2-core)))))
(defun fn2-ri-loop (fuel x slot gen len fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (zp fuel) (mv :fuel 0 0 fn2-core)
    (mv-let (code article candidates fn2-core) (fn2-read-identity x slot gen 0 len 200 0 1 4096 fn2-core)
      (if (eq code :more) (fn2-ri-loop (- fuel 1) x slot gen len fn2-core) (mv code article candidates fn2-core)))))
;; The served answer as the five fields of ruling 8: the selection and the
;; candidates come from fn2-read-identity; availability, coverage and
;; authorization are not served by C's engine as it stands (:not-served).
(defun fn2-read-identity-typed (seeds conflicts mid)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-read-profile* :null nil fn2-core))
           ((mv c1 fn2-core) (fn2-cs-seed-all seeds 1 fn2-core))
           ((mv c2 fn2-core) (fn2-cs-conflict-all conflicts (+ 1 (len seeds)) fn2-core))
           ((unless (and (eq c1 :ok) (eq c2 :ok))) (mv (list :seeding c1 c2) fn2-core))
           (octets (fn2-cs-octets mid))
           ((mv & slot gen fn2-core) (fn2-cs-fill octets fn2-core))
           ((mv code article candidates fn2-core) (fn2-ri-loop 400 0 slot gen (len octets) fn2-core)))
        (mv (list (if (eq code :found) (list :found article) code) candidates :not-served :not-served :not-served) fn2-core))
      result)))
;; The reference over the list view: the selection is the seed's article
;; (its commit position, I+1) when MID was seeded, else :evidence when MID
;; has conflict evidence, else :absent; the candidates the conflicts of MID;
;; the body held exactly when selected (no reclamation yet), coverage
;; complete (every admitted fact is local), authorization the anonymous
;; reader's (no access rule before E).
(defun fn2-ri-position (seeds mid i)
  (declare (xargs :verify-guards nil))
  (cond ((atom seeds) nil) ((equal (nth 1 (car seeds)) mid) (+ 1 i)) (t (fn2-ri-position (cdr seeds) mid (+ 1 i)))))
(defun fn2-ri-count (conflicts mid)
  (declare (xargs :verify-guards nil))
  (cond ((atom conflicts) 0) ((equal (car (car conflicts)) mid) (+ 1 (fn2-ri-count (cdr conflicts) mid)))
        (t (fn2-ri-count (cdr conflicts) mid))))
(defun fn2-read-identity-spec (seeds conflicts mid)
  (declare (xargs :verify-guards nil))
  (let ((p (fn2-ri-position seeds mid 0)) (n (fn2-ri-count conflicts mid)))
    (list (cond (p (list :found p)) ((< 0 n) :evidence) (t :absent)) n
          (if p :held :none) :complete :anonymous)))
(defun fn2-ri-conflictsp (conflicts seeds)
  (declare (xargs :verify-guards nil))
  (or (atom conflicts)
      (and (consp (car conflicts)) (fn2-ri-position seeds (car (car conflicts)) 0) (natp (cadr (car conflicts)))
           (< (cadr (car conflicts)) 256) (fn2-ri-conflictsp (cdr conflicts) seeds))))
(defthm-owed fn2-read-identity-typed-exact (seeds conflicts mid)
  (implies (and (fn2-csp-seedsp seeds (fn2-profile-get :groups *fn2-read-profile*) nil) (fn2-ri-conflictsp conflicts seeds)
                (stringp mid))
           (equal (fn2-read-identity-typed seeds conflicts mid) (fn2-read-identity-spec seeds conflicts mid)))
  :schema :invariant
  :teeth (fn2-read-identity-test-selection fn2-read-identity-test-negative)
  :doc "IDENTITY-ACROSS-PEERS ruling 8 over C-S4 (e): the identity read by Message-ID answers the typed read result: the selection, the evidence status (the locally known conflict candidates at this cut, counted, never a global count), availability, coverage and authorization. Owed on two counts. (1) C's engine as it stands stores (name, content) as :accepted/:conflict with at most four contents a name, so the read answers the selection and the candidates only; availability, coverage and authorization are :not-served until C's record change under rulings 3 and 7 (attributed receipts apart from binding evidence, the four-per-id constant deleted, an exact lookup plus a per-name summary plus a pageable evidence cursor) and S-ARTICLE-LOCATION give it an answer; the read is rewritten over those then. (2) The candidates are the contents met in the block, which the future evidence cursor pages instead of walking. Teeth: the selection and the candidates against the reference, and a reference that tells a conflict apart.")
