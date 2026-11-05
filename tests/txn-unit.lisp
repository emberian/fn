; D5 1/n evidence: POST through the transaction machine (docs/d-machines-
; nntp.md section 14.4). The upload whose header is complete takes a
; transaction row; the transaction claims the Message-ID's octets, asks C's
; identity decision once the upload has its digest, declares the article row
; in its batch's private successor, and at :ready stages it and calls the
; batch admission, which is B-S2's interim (:not-served) until B lands the
; transaction member: a valid article is answered with the interim refusal.
; Duplicate and conflict answers are reached by seeding the identity
; overlay through C-S3's own operations (decide, record, stage, bind,
; publish) before the clients connect, with the content identity of the
; source the client then sends (BLAKE3 of the unstuffed octets) or of
; another. Every transcript also arrives byte by byte and in 7-octet chunks.
; Run: sh tools/certify.sh tests/txn-unit.lisp
(in-package "ACL2")
(include-book "../books/owed-txn")
(include-book "../sim/check-wire")
(include-book "std/util/bstar" :dir :system)

; Posting served with two upload windows of 4 KiB chunks, and room for C's
; engine (owed-txn.lisp).
(defconst *fn2-tu-profile* *fn2-txn-posting-profile*)

(defun fn2-tu-text (lines) (declare (xargs :verify-guards nil)) (fn2-cw-crlf-octets lines))
(defun fn2-tu-sizes (n k) (declare (xargs :verify-guards nil)) (make-list (+ 1 (floor n k)) :initial-element k))

; Seeding: a fact (Message-ID octets, content identity) recorded and
; published through C-S3 on decision row 0 before any transaction exists,
; its octets in workspaces of an owner no machine is (kind 200).
(defun fn2-tu-write (bytes slot gen off fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom bytes) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-core-write slot gen off (car bytes) 200 0 1 fn2-core)
      (if (eq code :ok) (fn2-tu-write (cdr bytes) slot gen (+ 1 off) fn2-core) (mv code fn2-core)))))
(defun fn2-tu-drive (fuel d fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (zp fuel) (mv :fuel fn2-core)
    (mv-let (answer fn2-core) (fn2-identity-decide d 4096 fn2-core)
      (if (eq answer :more) (fn2-tu-drive (- fuel 1) d fn2-core) (mv answer fn2-core)))))
(defun fn2-tu-resolve (fuel tx fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (zp fuel) (mv :fuel fn2-core)
    (mv-let (answer fn2-core) (fn2-successor-resolve tx 4096 fn2-core)
      (if (eq answer :more) (fn2-tu-resolve (- fuel 1) tx fn2-core) (mv answer fn2-core)))))
(defun fn2-tu-seed (mid digest batch fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv c1 mslot mgen fn2-core) (fn2-core-reserve 0 200 0 1 fn2-core))
       ((mv c2 dslot dgen fn2-core) (fn2-core-reserve 0 200 0 1 fn2-core))
       ((mv c3 fn2-core) (fn2-tu-write mid mslot mgen 0 fn2-core))
       ((mv c4 fn2-core) (fn2-tu-write digest dslot dgen 0 fn2-core))
       ((mv c5 fn2-core) (fn2-identity-decide-start 0 mslot mgen 0 (len mid) dslot dgen 0 200 0 1 fn2-core))
       ((mv a fn2-core) (fn2-tu-drive 100 0 fn2-core))
       ((mv c6 & & h & &) (fn2-identity-facts 0 fn2-core))
       ;; C §4a: a stored offer is a local acceptance, a conflicting one evidence only
       ((mv c7 fn2-core) (fn2-txn-put-identity 0 mslot mgen 0 (len mid) dslot dgen 0 200 0 1 h 3 (if (eq a :stored) 1 0) fn2-core))
       (c8 :ok)
       ((mv c9 fn2-core) (fn2-tu-resolve 40 0 fn2-core))
       ((mv c10 & fn2-core) (fn2-successor-stage 0 fn2-core))
       ((mv c11 fn2-core) (fn2-successor-bind 0 batch batch fn2-core))
       ((mv c12 fn2-core) (fn2-successor-publish batch fn2-core))
       (fn2-core (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (fn2-commit-root)
                   (fn2-commit-root-set-first-key 0 (+ 1 batch) fn2-commit-root) fn2-core))
       ((mv c13 fn2-core) (fn2-successor-release 0 fn2-core))
       ((mv c14 fn2-core) (fn2-core-release mslot mgen 200 0 1 fn2-core))
       ((mv c15 fn2-core) (fn2-core-release dslot dgen 200 0 1 fn2-core)))
    (mv (if (and (eq c1 :ok) (eq c2 :ok) (eq c3 :ok) (eq c4 :ok) (eq c5 :ok) (member-eq a '(:stored :conflict))
                 (eq c6 :ok) (eq c7 :ok) (eq c8 :ok) (eq c9 :ok) (eq c10 :ok) (eq c11 :ok) (eq c12 :ok)
                 (eq c13 :ok) (eq c14 :ok) (eq c15 :ok))
            :ok
          (list c1 c2 c3 c4 c5 a c6 c7 c8 c9 c10 c11 c12 c13 c14 c15))
        fn2-core)))
(defun fn2-tu-seed-all (seeds batch fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom seeds) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-tu-seed (car (car seeds)) (cadr (car seeds)) batch fn2-core)
      (if (eq code :ok) (fn2-tu-seed-all (cdr seeds) (+ 1 batch) fn2-core) (mv code fn2-core)))))

; The wires of TRANSCRIPTS after SEEDS: (seeded status wires stop-reason).
(defun fn2-tu-run-on (profile seeds transcripts store)
  ;; STORE: the device before the run ((offset . octets) or a bad sector (offset . :io))
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
           ((mv & fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv seeded fn2-core) (fn2-tu-seed-all seeds 1 fn2-core))
           ((mv status clients & fn2-core)
            (fn2-cw-loop (+ 2500 (* 600 (len transcripts)) (* 4 (fn2-cw-arrivals transcripts)))
                         0 0 (fn2-cw-clients transcripts) store fn2-core)))
        (mv (list seeded status (fn2-cw-results clients) (fn2-core-stop-reason fn2-core)) fn2-core))
      result)))
(defun fn2-tu-run (profile seeds transcripts)
  (declare (xargs :verify-guards nil))
  (fn2-tu-run-on profile seeds transcripts nil))
(defun fn2-tu-wire (seeds lines k)
  (declare (xargs :verify-guards nil))
  (let* ((octets (fn2-tu-text lines))
         (r (fn2-tu-run *fn2-tu-profile* seeds (list (list octets (fn2-tu-sizes (len octets) k))))))
    (list (car r) (nth 1 r) (nth 3 r) (car (car (nth 2 r))) (cadr (car (nth 2 r))))))
(defun fn2-tu-check (seeds lines expect)
  (declare (xargs :verify-guards nil))
  (let ((want (list :ok :quiet 0 (fn2-tu-text expect) t)))
    (and (or (fn2-wire-pass-p (fn2-tu-text lines) (fn2-tu-text expect) t)
             (cw "WIRE ~x0~%" (fn2-wire-check (fn2-tu-text lines) (fn2-tu-text expect) t)))
         (or (equal (fn2-tu-wire seeds lines 4096) want) (cw "whole ~x0~%" (fn2-tu-wire seeds lines 4096)))
         (or (equal (fn2-tu-wire seeds lines 7) want) (cw "by 7 ~x0~%" (fn2-tu-wire seeds lines 7)))
         (or (equal (fn2-tu-wire seeds lines 1) want) (cw "by 1 ~x0~%" (fn2-tu-wire seeds lines 1))))))

(defconst *fn2-tu-greeting* "200 fn-nntp experimental server ready")
(defconst *fn2-tu-340* "340 send article to be posted")
(defconst *fn2-tu-205* "205 closing connection")
(defconst *fn2-tu-mid* "<one@example.invalid>")
(defconst *fn2-tu-good* (list "From: a@example.invalid" "Subject: hello" "Newsgroups: local.test"
                              (concatenate 'string "Message-ID: " *fn2-tu-mid*) "" "body" "..stuffed"))
; The source the poster sent: the unstuffed lines, the terminator excluded.
(defconst *fn2-tu-good-source*
  (fn2-tu-text (list "From: a@example.invalid" "Subject: hello" "Newsgroups: local.test"
                     (concatenate 'string "Message-ID: " *fn2-tu-mid*) "" "body" ".stuffed")))
(defconst *fn2-tu-mid-octets* (fn2-cw-chars (coerce *fn2-tu-mid* 'list)))
(defconst *fn2-tu-same* (list (list *fn2-tu-mid-octets* (fn-blake3 *fn2-tu-good-source*))))
(defconst *fn2-tu-other* (list (list *fn2-tu-mid-octets* (fn-blake3 (append *fn2-tu-good-source* (list 120 13 10))))))
(defun fn2-tu-post (lines) (declare (xargs :verify-guards nil)) (append '("POST") lines '("." "QUIT")))
(defun fn2-tu-expect (reply)
  (declare (xargs :verify-guards nil))
  (list *fn2-tu-greeting* *fn2-tu-340* reply *fn2-tu-205*))

(defun fn2-tu-fixtures ()
  (declare (xargs :verify-guards nil))
  (and
   ;; accepted: a valid article reaches :ready, emits its member, commits and
   ;; publishes through B's commit batch, and answers 240, no stop
   (fn2-tu-check nil (fn2-tu-post *fn2-tu-good*) (fn2-tu-expect "240 article received OK"))
   ;; duplicate: the same Message-ID and source are recorded
   (fn2-tu-check *fn2-tu-same* (fn2-tu-post *fn2-tu-good*)
                 (fn2-tu-expect "441 posting failed; this article is already stored here"))
   ;; conflict: the Message-ID is recorded with another content
   (fn2-tu-check *fn2-tu-other* (fn2-tu-post *fn2-tu-good*)
                 (fn2-tu-expect "441 posting failed; a different article with this Message-ID is stored here"))
   ;; the model's order: the upload's definite refusals before identity
   (fn2-tu-check *fn2-tu-same* (fn2-tu-post (remove-equal "Subject: hello" *fn2-tu-good*))
                 (fn2-tu-expect "441 posting failed; Subject is required"))
   ;; identity before the injected fields: a recorded duplicate carrying Xref
   ;; is the duplicate; unrecorded, the Xref refusal
   (fn2-tu-check *fn2-tu-same*
                 (fn2-tu-post (append (butlast *fn2-tu-good* 3) '("Xref: h g:1") (nthcdr 4 *fn2-tu-good*)))
                 (fn2-tu-expect "441 posting failed; a different article with this Message-ID is stored here"))
   (fn2-tu-check nil
                 (fn2-tu-post (append (butlast *fn2-tu-good* 3) '("Xref: h g:1") (nthcdr 4 *fn2-tu-good*)))
                 (fn2-tu-expect "441 posting failed; Xref must not be supplied"))
   ;; S-GROUP: no named group is carried: refused by group, after identity
   ;; and before the injected fields; one carried among others is enough
   (fn2-tu-check nil (fn2-tu-post (update-nth 2 "Newsgroups: no.such.group, other.group" *fn2-tu-good*))
                 (fn2-tu-expect "441 posting failed; a named newsgroup is not carried here"))
   (fn2-tu-check nil (fn2-tu-post (append (update-nth 2 "Newsgroups: no.such.group" (butlast *fn2-tu-good* 3))
                                          '("Xref: h g:1") (nthcdr 4 *fn2-tu-good*)))
                 (fn2-tu-expect "441 posting failed; a named newsgroup is not carried here"))
   ;; (another Newsgroups is another source: identity first, so the conflict)
   (fn2-tu-check *fn2-tu-same* (fn2-tu-post (update-nth 2 "Newsgroups: no.such.group" *fn2-tu-good*))
                 (fn2-tu-expect "441 posting failed; a different article with this Message-ID is stored here"))
   (fn2-tu-check nil (fn2-tu-post (update-nth 2 "Newsgroups: x.y,local.test , z" *fn2-tu-good*))
                 (fn2-tu-expect "240 article received OK"))
   ;; no Message-ID: the node generates one (injection), so the seeded
   ;; article's Message-ID is not this one's
   (fn2-tu-check *fn2-tu-same* (fn2-tu-post (remove-equal (nth 3 *fn2-tu-good*) *fn2-tu-good*))
                 (fn2-tu-expect "240 article received OK"))
   ;; two posts pipelined on one connection, the second a duplicate
   (fn2-tu-check *fn2-tu-same*
                 (append '("POST") (remove-equal (nth 3 *fn2-tu-good*) *fn2-tu-good*) '(".")
                         (fn2-tu-post *fn2-tu-good*))
                 (list *fn2-tu-greeting* *fn2-tu-340* "240 article received OK" *fn2-tu-340*
                       "441 posting failed; this article is already stored here" *fn2-tu-205*))))
(assert-event (fn2-tu-fixtures))

; Two clients offer the same Message-ID at once: the second's claim waits in
; the first's FIFO and is handed over at the first's outcome; both are
; answered, the duplicate in both when it is recorded, and 240 followed by
; the duplicate refusal when the first client commits it first.
(defun fn2-tu-two (seeds lines k)
  (declare (xargs :verify-guards nil))
  (let* ((octets (fn2-tu-text lines)) (one (list octets (fn2-tu-sizes (len octets) k))))
    (fn2-tu-run *fn2-tu-profile* seeds (list one one))))
(assert-event
 (let ((r (fn2-tu-two *fn2-tu-same* (fn2-tu-post *fn2-tu-good*) 5))
       (want (list (fn2-tu-text (fn2-tu-expect "441 posting failed; this article is already stored here")) t)))
   (or (and (equal (car r) :ok) (equal (nth 1 r) :quiet) (equal (nth 3 r) 0)
            (equal (nth 2 r) (list want want)))
       (cw "two ~x0~%" r))))
(assert-event
 (let ((r (fn2-tu-two nil (fn2-tu-post *fn2-tu-good*) 3))
       (want1 (list (fn2-tu-text (fn2-tu-expect "240 article received OK")) t))
       (want2 (list (fn2-tu-text (fn2-tu-expect "441 posting failed; this article is already stored here")) t)))
   (or (and (equal (car r) :ok) (equal (nth 1 r) :quiet) (equal (nth 3 r) 0)
            (or (equal (nth 2 r) (list want1 want2))
                (equal (nth 2 r) (list want2 want1))))
       (cw "two ~x0~%" r))))

; ------------------------------------------------------------------------
; The owed rows' teeth (owed-txn.lisp). Each positive tooth is the row's
; statement at three fragmentations; each negative shows the predicate
; refuses the answer it states.
(defun fn2-tu-solo-all (lines want)
  (declare (xargs :verify-guards nil))
  (let ((octets (fn2-txn-post-octets lines)))
    (and (equal (fn2-txn-wire-solo octets '(4096)) want)
         (equal (fn2-txn-wire-solo octets (fn2-tu-sizes (len octets) 7)) want)
         (equal (fn2-txn-wire-solo octets (fn2-tu-sizes (len octets) 1)) want))))
(defun fn2-txn-test-admission-interim ()
  (declare (xargs :verify-guards nil))
  (fn2-tu-solo-all *fn2-txn-article* (fn2-txn-interim-wire "240 article received OK")))
(defun fn2-txn-test-admission-interim-negative ()
  (declare (xargs :verify-guards nil))
  (not (equal (fn2-txn-wire-solo (fn2-txn-post-octets *fn2-txn-article*) '(4096))
              (fn2-txn-interim-wire "441 posting failed"))))
(defun fn2-txn-test-generated ()
  (declare (xargs :verify-guards nil))
  (fn2-tu-solo-all (remove-equal (nth 3 *fn2-txn-article*) *fn2-txn-article*)
                   (fn2-txn-interim-wire "240 article received OK")))
(defun fn2-txn-test-generated-negative ()
  (declare (xargs :verify-guards nil))
  ;; the same article without Subject: the verdict refuses it, generated identifier or not
  (not (equal (fn2-txn-wire-solo (fn2-txn-post-octets (remove-equal "Subject: hello"
                                                                    (remove-equal (nth 3 *fn2-txn-article*) *fn2-txn-article*)))
                                 '(4096))
              (fn2-txn-interim-wire "240 article received OK"))))
(assert-event (and (fn2-txn-test-admission-interim) (fn2-txn-test-admission-interim-negative)
                   (fn2-txn-test-generated) (fn2-txn-test-generated-negative)))

; End-to-end M2 spine: POST stores the source in an extent of its own
; (written and fenced before the batch's journal), binds its location into
; the article row with group counts, overview and group-address entries, and
; publishes, so a reader on the same connection sees the posted article via
; GROUP, OVER, OVER <id>, HEAD, BODY and ARTICLE: the octets read back from
; the device through B's block read, the header in its posted order and the
; body dot-stuffed again.
(defconst *fn2-tu-read-profile*
  (put-assoc-equal :reading t (put-assoc-equal :x 2 *fn2-tu-profile*)))
(defun fn2-tu-tab () (declare (xargs :verify-guards nil)) (coerce (list (code-char 9)) 'string))
(defun fn2-tu-ov-line (num)
  (declare (xargs :verify-guards nil))
  (concatenate 'string num (fn2-tu-tab) "hello" (fn2-tu-tab) "a@example.invalid" (fn2-tu-tab)
               (fn2-tu-tab) *fn2-tu-mid* (fn2-tu-tab) (fn2-tu-tab) "118" (fn2-tu-tab) "2"))
(defconst *fn2-tu-post-read-lines*
  (append '("POST") *fn2-tu-good* '(".")
          '("GROUP local.test"
            "OVER 1"
            "OVER <one@example.invalid>"
            "HEAD 1"
            "BODY 1"
            "ARTICLE 1"
            "BODY <one@example.invalid>"
            "QUIT")))
(defconst *fn2-tu-post-read-expect*
  (list *fn2-tu-greeting*
        *fn2-tu-340*
        "240 article received OK"
        "211 1 1 1 local.test"
        "224 overview information follows"
        (fn2-tu-ov-line "1")
        "."
        "224 overview information follows"
        (fn2-tu-ov-line "1")
        "."
        ;; the posted header, in its order, as stored
        "221 1 <one@example.invalid> headers follow"
        "From: a@example.invalid"
        "Subject: hello"
        "Newsgroups: local.test"
        "Message-ID: <one@example.invalid>"
        "."
        "222 1 <one@example.invalid> body follows"
        "body"
        "..stuffed"
        "."
        "220 1 <one@example.invalid> article follows"
        "From: a@example.invalid"
        "Subject: hello"
        "Newsgroups: local.test"
        "Message-ID: <one@example.invalid>"
        ""
        "body"
        "..stuffed"
        "."
        "222 0 <one@example.invalid> body follows"
        "body"
        "..stuffed"
        "."
        *fn2-tu-205*))
(defun fn2-txn-test-post-and-read ()
  (declare (xargs :verify-guards nil))
  (let* ((octets (fn2-tu-text *fn2-tu-post-read-lines*))
         (want (list :ok :quiet 0 (fn2-tu-text *fn2-tu-post-read-expect*) t))
         (r (fn2-tu-run *fn2-tu-read-profile* nil (list (list octets (fn2-tu-sizes (len octets) 4096)))))
         (got (list (car r) (nth 1 r) (nth 3 r) (car (car (nth 2 r))) (cadr (car (nth 2 r))))))
    (and (fn2-wire-pass-p octets (fn2-tu-text *fn2-tu-post-read-expect*) t)
         (or (equal got want) (cw "post-and-read ~x0~%want ~x1~%" got want)))))
(assert-event (fn2-txn-test-post-and-read))


; A two-chunk POST (the upload window's chunk 0 holds 4096 octets; this
; source is 6,296): 240, and BODY reads every posted line back from the
; device, the line that starts with "." stuffed again (it lies in chunk 1).
(defun fn2-tu-long-body (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil
    (cons (concatenate 'string (if (equal n 7) "." "") "line "
                       (coerce (explode-nonnegative-integer n 10 nil) 'string)
                       " 0123456789012345678901234567890123456789012345678901")
          (fn2-tu-long-body (- n 1)))))
(defun fn2-tu-stuff (lines)
  (declare (xargs :verify-guards nil))
  (if (atom lines) nil
    (cons (if (and (< 0 (length (car lines))) (equal (char (car lines) 0) #\.))
              (concatenate 'string "." (car lines)) (car lines))
          (fn2-tu-stuff (cdr lines)))))
(defconst *fn2-tu-long* (append (list "From: a@example.invalid" "Subject: hello" "Newsgroups: local.test"
                                      "Message-ID: <long@example.invalid>" "")
                                (fn2-tu-long-body 100)))
(defun fn2-txn-test-two-chunks ()
  (declare (xargs :verify-guards nil))
  (let* ((lines (append '("POST") (fn2-tu-stuff *fn2-tu-long*) '(".") '("GROUP local.test" "BODY 1" "QUIT")))
         (octets (fn2-tu-text lines))
         (expect (append (list *fn2-tu-greeting* *fn2-tu-340* "240 article received OK" "211 1 1 1 local.test"
                               "222 1 <long@example.invalid> body follows")
                         (fn2-tu-stuff (fn2-tu-long-body 100))
                         (list "." *fn2-tu-205*)))
         (want (list :ok :quiet 0 (fn2-tu-text expect) t))
         (r (fn2-tu-run *fn2-tu-read-profile* nil (list (list octets (fn2-tu-sizes (len octets) 4096)))))
         (got (list (car r) (nth 1 r) (nth 3 r) (car (car (nth 2 r))) (cadr (car (nth 2 r))))))
    (and (< 4096 (len (fn2-tu-text *fn2-tu-long*)))
         (or (equal got want) (cw "two-chunks ~x0~%want ~x1~%" got want)))))
(assert-event (fn2-txn-test-two-chunks))

; A Read that fails after the 22x line went closes the connection (it
; replaced the core's stop :machine-phase): the second storage unit of every
; extent is a bad sector, so BODY 1 of the two-chunk article sends its 222
; line and the pages of the first unit, then the read of the second fails.
; The wire is a proper prefix of the complete reply (no terminator, no 205
; for the QUIT behind it), the client is closed, and the core runs on.
(defun fn2-tu-bad-second-units (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil
    (cons (cons (+ (* (- n 1) *fn2-commit-extent-bytes*) *fn2-commit-unit-bytes*) :io)
          (fn2-tu-bad-second-units (- n 1)))))
(defun fn2-tu-prefix-p (p l)
  (declare (xargs :verify-guards nil))
  (or (atom p) (and (consp l) (equal (car p) (car l)) (fn2-tu-prefix-p (cdr p) (cdr l)))))
(defun fn2-txn-test-read-fail-closes ()
  (declare (xargs :verify-guards nil))
  (let* ((lines (append '("POST") (fn2-tu-stuff *fn2-tu-long*) '(".") '("GROUP local.test" "BODY 1" "QUIT")))
         (octets (fn2-tu-text lines))
         (said (fn2-tu-text (list *fn2-tu-greeting* *fn2-tu-340* "240 article received OK" "211 1 1 1 local.test"
                                  "222 1 <long@example.invalid> body follows")))
         (whole (fn2-tu-text (append (list *fn2-tu-greeting* *fn2-tu-340* "240 article received OK" "211 1 1 1 local.test"
                                           "222 1 <long@example.invalid> body follows")
                                     (fn2-tu-stuff (fn2-tu-long-body 100))
                                     (list "." *fn2-tu-205*))))
         (r (fn2-tu-run-on *fn2-tu-read-profile* nil (list (list octets (fn2-tu-sizes (len octets) 4096)))
                           (fn2-tu-bad-second-units 64)))
         (wire (car (car (nth 2 r)))) (closed (cadr (car (nth 2 r)))))
    (or (and (equal (car r) :ok) (equal (nth 1 r) :quiet) (equal (nth 3 r) 0)
             (fn2-tu-prefix-p said wire) (fn2-tu-prefix-p wire whole) (< (len wire) (len whole)) closed)
        (cw "read-fail-closes ~x0 closed ~x1 wire ~x2 of ~x3 octets~%" (list (car r) (nth 1 r) (nth 3 r)) closed
            (len wire) (len whole)))))
(assert-event (fn2-txn-test-read-fail-closes))

; Injection read back: a POST without a Message-ID answers 240, and HEAD 1
; and ARTICLE 1 serve the stored octets: the generated field first
; (<fn2.1.A@P>, P the profile's :path-identity, the writer epoch 1 and the payload extent's
; allocation), then the posted header in its order and the body; the 221
; and 220 lines carry the same identifier the field does.
(defun fn2-tu-mid-of (line)
  ;; "221 1 <id> headers follow" -> "<id>"
  (declare (xargs :verify-guards nil))
  (let* ((s (coerce line 'list)) (a (member #\< s)) (b (member #\> a)))
    (and a b (coerce (take (+ 1 (- (len a) (len b))) a) 'string))))
(defun fn2-tu-codes-chars (l)
  (declare (xargs :verify-guards nil))
  (if (atom l) nil (cons (code-char (nfix (car l))) (fn2-tu-codes-chars (cdr l)))))
(defun fn2-tu-lines-of (octets)
  (declare (xargs :verify-guards nil :measure (len octets)))
  (mv-let (found line rest) (fn2-wire-take-line octets nil)
    (if (or (not found) (>= (len rest) (len octets))) nil
      (cons (coerce (fn2-tu-codes-chars line) 'string) (fn2-tu-lines-of rest)))))
(defun fn2-tu-digits-p (cs)
  (declare (xargs :verify-guards nil))
  (and (consp cs) (true-listp cs) (subsetp cs '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))))
(defun fn2-tu-generated-mid-p (mid path)
  ;; <fn2.1.DIGITS@PATH>
  (declare (xargs :verify-guards nil))
  (let* ((s (coerce mid 'list)) (pre (coerce "<fn2.1." 'list))
         (post (coerce (concatenate 'string "@" path ">") 'list)))
    (and (< (+ (len pre) (len post)) (len s))
         (equal (take (len pre) s) pre)
         (equal (nthcdr (- (len s) (len post)) s) post)
         (fn2-tu-digits-p (take (- (len s) (+ (len pre) (len post))) (nthcdr (len pre) s))))))
(defun fn2-txn-test-generated-read (path)
  (declare (xargs :verify-guards nil))
  (let* ((posted (remove-equal (nth 3 *fn2-tu-good*) *fn2-tu-good*))
         (lines (append '("POST") posted '(".") '("GROUP local.test" "HEAD 1" "ARTICLE 1" "QUIT")))
         (octets (fn2-tu-text lines))
         (r (fn2-tu-run (put-assoc-equal :path-identity path *fn2-tu-read-profile*) nil (list (list octets (fn2-tu-sizes (len octets) 4096)))))
         (wire (car (car (nth 2 r))))
         (got (fn2-tu-lines-of wire))
         (mid (fn2-tu-mid-of (or (nth 4 got) "")))
         (field (concatenate 'string "Message-ID: " (or mid "")))
         (expect (list *fn2-tu-greeting* *fn2-tu-340* "240 article received OK" "211 1 1 1 local.test"
                       (concatenate 'string "221 1 " (or mid "") " headers follow")
                       field "From: a@example.invalid" "Subject: hello" "Newsgroups: local.test" "."
                       (concatenate 'string "220 1 " (or mid "") " article follows")
                       field "From: a@example.invalid" "Subject: hello" "Newsgroups: local.test" ""
                       "body" "..stuffed" "." *fn2-tu-205*)))
    (or (and (equal (car r) :ok) (equal (nth 1 r) :quiet) (equal (nth 3 r) 0)
             (stringp mid) (fn2-tu-generated-mid-p mid path)
             (equal wire (fn2-tu-text expect)) (cadr (car (nth 2 r))))
        (cw "generated-read ~x0 ~x1~%" (list (car r) (nth 1 r) (nth 3 r) mid) got))))
; The identifier's right side is the profile's path identity: the tiny
; profile's, and another node's.
(assert-event (and (fn2-txn-test-generated-read "fn2.invalid")
                   (fn2-txn-test-generated-read "news.example-1.org")
                   (not (fn2-tu-generated-mid-p "<fn2.1.7@fn2.invalid>" "news.example-1.org"))))
