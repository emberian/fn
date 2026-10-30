; D5 1/n evidence: POST through the transaction machine (fn2/docs/d-machines-
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
; Run: sh fn2/tools/certify.sh tests/txn-unit.lisp
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
    (mv-let (answer fn2-core) (fn2-identity-step d 4096 fn2-core)
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
       ((mv c5 fn2-core) (fn2-identity-offer 0 mslot mgen 0 (len mid) dslot dgen 0 200 0 1 fn2-core))
       ((mv a fn2-core) (fn2-tu-drive 100 0 fn2-core))
       ((mv c6 fn2-core) (fn2-successor-put 0 0 1 :record fn2-core))
       ((mv c7 fn2-core) (fn2-successor-arg 0 0 0 :value batch fn2-core))
       ((mv c8 fn2-core) (fn2-successor-arg 0 0 1 :value 3 fn2-core))
       ((mv c9 fn2-core) (fn2-tu-resolve 40 0 fn2-core))
       ((mv c10 & fn2-core) (fn2-successor-stage 0 fn2-core))
       ((mv c11 fn2-core) (fn2-successor-bind 0 batch batch fn2-core))
       ((mv c12 fn2-core) (fn2-successor-publish batch fn2-core))
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
(defun fn2-tu-run (profile seeds transcripts)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
           ((mv seeded fn2-core) (fn2-tu-seed-all seeds 1 fn2-core))
           ((mv status clients fn2-core)
            (fn2-cw-loop (+ 2000 (* 600 (len transcripts)) (* 4 (fn2-cw-arrivals transcripts)))
                         0 0 (fn2-cw-clients transcripts) fn2-core)))
        (mv (list seeded status (fn2-cw-results clients) (fn2-core-stop-reason fn2-core)) fn2-core))
      result)))
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
   ;; refused: a valid article reaches :ready and the interim admission
   ;; (B-S2 not served): the generic line, no stop
   (fn2-tu-check nil (fn2-tu-post *fn2-tu-good*) (fn2-tu-expect "441 posting failed"))
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
                 (fn2-tu-expect "441 posting failed"))
   ;; no Message-ID: the interim (the generated one comes with injection)
   (fn2-tu-check *fn2-tu-same* (fn2-tu-post (remove-equal (nth 3 *fn2-tu-good*) *fn2-tu-good*))
                 (fn2-tu-expect "441 posting failed"))
   ;; two posts pipelined on one connection, the second a duplicate
   (fn2-tu-check *fn2-tu-same*
                 (append '("POST") (remove-equal (nth 3 *fn2-tu-good*) *fn2-tu-good*) '(".")
                         (fn2-tu-post *fn2-tu-good*))
                 (list *fn2-tu-greeting* *fn2-tu-340* "441 posting failed" *fn2-tu-340*
                       "441 posting failed; this article is already stored here" *fn2-tu-205*))))
(assert-event (fn2-tu-fixtures))

; Two clients offer the same Message-ID at once: the second's claim waits in
; the first's FIFO and is handed over at the first's outcome; both are
; answered, the duplicate in both when it is recorded.
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
       (want (list (fn2-tu-text (fn2-tu-expect "441 posting failed")) t)))
   (or (and (equal (car r) :ok) (equal (nth 1 r) :quiet) (equal (nth 3 r) 0)
            (equal (nth 2 r) (list want want)))
       (cw "two ~x0~%" r))))

; ------------------------------------------------------------------------
; The interims' teeth (owed-txn.lisp). Each positive tooth is the row's
; statement at three fragmentations; each negative shows the predicate
; refuses the answer the interim stands in for.
(defun fn2-tu-solo-all (lines want)
  (declare (xargs :verify-guards nil))
  (let ((octets (fn2-txn-post-octets lines)))
    (and (equal (fn2-txn-wire-solo octets '(4096)) want)
         (equal (fn2-txn-wire-solo octets (fn2-tu-sizes (len octets) 7)) want)
         (equal (fn2-txn-wire-solo octets (fn2-tu-sizes (len octets) 1)) want))))
(defun fn2-txn-test-admission-interim ()
  (declare (xargs :verify-guards nil))
  (fn2-tu-solo-all *fn2-txn-article* (fn2-txn-interim-wire "441 posting failed")))
(defun fn2-txn-test-admission-interim-negative ()
  (declare (xargs :verify-guards nil))
  (not (equal (fn2-txn-wire-solo (fn2-txn-post-octets *fn2-txn-article*) '(4096))
              (fn2-txn-interim-wire "240 article received OK"))))
(defun fn2-txn-test-generated-interim ()
  (declare (xargs :verify-guards nil))
  (fn2-tu-solo-all (remove-equal (nth 3 *fn2-txn-article*) *fn2-txn-article*)
                   (fn2-txn-interim-wire "441 posting failed")))
(defun fn2-txn-test-generated-interim-negative ()
  (declare (xargs :verify-guards nil))
  ;; the same article without Subject: the verdict, not the interim
  (not (equal (fn2-txn-wire-solo (fn2-txn-post-octets (remove-equal "Subject: hello"
                                                                    (remove-equal (nth 3 *fn2-txn-article*) *fn2-txn-article*)))
                                 '(4096))
              (fn2-txn-interim-wire "441 posting failed"))))
(assert-event (and (fn2-txn-test-admission-interim) (fn2-txn-test-admission-interim-negative)
                   (fn2-txn-test-generated-interim) (fn2-txn-test-generated-interim-negative)))
