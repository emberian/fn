; Teeth for PKT-600's repair (PRF-213, NNT-044; books/served-tls-prefix.lisp):
; a read that carries more than one complete article yields after each, the
; host feeds the rest back, and nothing is dropped.  Every witness computes
; through fn-served-step-counted (the reference of the transition the host
; calls: fn-served-step-counted-fast-is-reference, fn-scar-feed-span-is-feed-
; counted) and fn-served-drain / fn-served-drain-run (the host loop in
; host/native/owner.lisp, written over it).  The three shapes the brief names:
; two POSTs in one read, two TAKETHIS in one read, a TAKETHIS split across two
; reads.
(in-package "ACL2")
(include-book "../../books/served-tls-prefix")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun spt-o (s) (fn-nntp-string-octets s))
(defun spt-line (s) (append (spt-o s) '(13 10)))

; -----------------------------------------------------------------------------
; A posting reader connection (the fixture of tests/acl2/served-tests.lisp).

(defconst *spt-groups* '("fn.letters" "fn.test"))
(defconst *spt-config*
  (fn-inj-make-config t (spt-o "fn.example.invalid")
                      (list (spt-o "fn.letters") (spt-o "fn.test")) 32768))
(defconst *spt-observation* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *spt-reader*
  (fn-served-result-conn
   (fn-served-open (fn-initial-state *spt-groups*) 510 8192
                   *spt-config* *spt-observation* *spt-observation*
                   (fn-auth-open-config))))
(assert-event (fn-served-connp *spt-reader*))

(defun spt-article (subject)
  (append (spt-line "From: poster@example.invalid")
          (spt-line (concatenate 'string "Subject: " subject))
          (spt-line "Newsgroups: fn.letters")
          (spt-line "")
          (spt-line "Hello, news.")
          (spt-line ".")))
(defconst *spt-post-a* (append (spt-line "POST") (spt-article "a")))
(defconst *spt-post-b* (append (spt-line "POST") (spt-article "b")))
(defconst *spt-two-posts* (append *spt-post-a* *spt-post-b*))
; The realistic pipelined shape (RFC 3977 section 3.5): the first article,
; and in the same write the next command.
(defconst *spt-article-then-post*
  (append (spt-article "a") (spt-line "POST")))

(defun spt-counted (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil)) (fn-served-step-counted conn octets fn-arena))
(defun spt-consumed (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-served-counted-consumed (spt-counted conn octets fn-arena)))
(defun spt-effects (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-served-result-effects (fn-served-counted-result (spt-counted conn octets fn-arena))))
(defun spt-whole (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-served-result-effects (fn-served-step conn octets fn-arena)))

; Two POSTs in one read.  The read yields after the first article: exactly
; its octets are consumed, and its one submission is the one the owner takes.
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift fn-served-drain 2)
(bpr-lift fn-served-drain-run 2)
(bpr-lift fn-served-drain-taken 2)
(bpr-lift fn-served-step 2)
(bpr-lift fn-served-step-counted 2)
(bpr-lift spt-all-same-run 3)
(bpr-lift spt-consumed 2)
(bpr-lift spt-counted 2)
(bpr-lift spt-effects 2)
(bpr-lift spt-whole 2)
(assert-event (equal (in-arena-spt-consumed *sr-arena* *spt-reader* *spt-two-posts*) (len *spt-post-a*)))
(assert-event (equal (len (fn-served-submissions (in-arena-spt-effects *sr-arena* *spt-reader* *spt-two-posts*))) 1))
(assert-event (fn-served-submission (in-arena-spt-effects *sr-arena* *spt-reader* *spt-two-posts*)))
; The same yield as the first POST read alone (the consumed-prefix keystone).
(assert-event (equal (fn-served-counted-result (in-arena-spt-counted *sr-arena* *spt-reader* *spt-two-posts*))
                     (in-arena-fn-served-step *sr-arena* *spt-reader* *spt-post-a*)))
; The defect PKT-600 names: the one-read fold carries BOTH submissions, and
; the owner's one take per read (fn-served-submission) saw only the first.
(assert-event (equal (len (fn-served-submissions (in-arena-spt-whole *sr-arena* *spt-reader* *spt-two-posts*))) 2))
; The host loop takes both, in order, and they are the one-read fold's two.
(assert-event (equal (len (in-arena-fn-served-drain-taken *sr-arena* *spt-reader* *spt-two-posts*)) 2))
(assert-event (equal (in-arena-fn-served-drain-taken *sr-arena* *spt-reader* *spt-two-posts*)
                     (fn-served-submissions (in-arena-spt-whole *sr-arena* *spt-reader* *spt-two-posts*))))
(assert-event (not (equal (car (in-arena-fn-served-drain-taken *sr-arena* *spt-reader* *spt-two-posts*))
                          (cadr (in-arena-fn-served-drain-taken *sr-arena* *spt-reader* *spt-two-posts*)))))
; And its replies and connection are the one-read fold's (fn-served-drain-is-step).
(assert-event (equal (in-arena-fn-served-drain *sr-arena* *spt-reader* *spt-two-posts*)
                     (in-arena-fn-served-step *sr-arena* *spt-reader* *spt-two-posts*)))

; The article and the next command in one write: the read yields after the
; article, before POST is answered, so the 340 cannot precede the article's
; outcome on the wire.
(defconst *spt-offered*
  (fn-served-result-conn (in-arena-fn-served-step *sr-arena* *spt-reader* (spt-line "POST"))))
(assert-event (equal (in-arena-spt-consumed *sr-arena* *spt-offered* *spt-article-then-post*)
                     (len (spt-article "a"))))
(assert-event (equal (fn-served-reply-octets (in-arena-spt-effects *sr-arena* *spt-offered* *spt-article-then-post*))
                     nil))
(assert-event (equal (take 4 (fn-served-reply-octets
                              (fn-served-result-effects
                               (in-arena-fn-served-drain *sr-arena* *spt-offered* *spt-article-then-post*))))
                     '(51 52 48 32)))

; -----------------------------------------------------------------------------
; A streaming peer (the record of tests/acl2/peer-transit-forms-tests.lisp).

(defconst *spt-peer*
  (fn-cfg-peer-make "innA" "inn.hbox.test" '(:nntp "127.0.0.1" 1119)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.1")))
(defconst *spt-cfg*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-policy "path-identity" "fnA.hbox.test")
                                         (fn-cfg-set-peer-delta *spt-peer*)))
                           *fn-cfg-default-stamp*))))
(defconst *spt-node* (fn-node-initial-state *spt-groups* 1048576))
(defconst *spt-feed*
  (fn-served-result-conn
   (fn-served-open-peer (fn-node-acceptance *spt-node*) 510 8192
                        *spt-config* *spt-observation* *spt-observation*
                        "innA" *spt-node* *spt-cfg* (fn-auth-open-config))))
(assert-event (fn-served-connp *spt-feed*))

(defun spt-takethis (n)
  (let ((id (concatenate 'string "<t" n "@example.invalid>")))
    (append (spt-line (concatenate 'string "TAKETHIS " id))
            (spt-line "Path: inn.hbox.test!not-for-mail")
            (spt-line "From: feeder@example.invalid")
            (spt-line "Newsgroups: fn.test")
            (spt-line (concatenate 'string "Message-ID: " id))
            (spt-line "Subject: streamed")
            (spt-line "")
            (spt-line "body")
            (spt-line "."))))
(defconst *spt-t1* (spt-takethis "1"))
(defconst *spt-t2* (spt-takethis "2"))
(defconst *spt-two-takethis* (append *spt-t1* *spt-t2*))

; Two TAKETHIS in one read (innfeed's shape): one yield per article.
(assert-event (equal (in-arena-spt-consumed *sr-arena* *spt-feed* *spt-two-takethis*) (len *spt-t1*)))
(assert-event (equal (len (fn-served-submissions (in-arena-spt-effects *sr-arena* *spt-feed* *spt-two-takethis*))) 1))
(assert-event (equal (len (fn-served-submissions (in-arena-spt-whole *sr-arena* *spt-feed* *spt-two-takethis*))) 2))
(assert-event (equal (in-arena-fn-served-drain-taken *sr-arena* *spt-feed* *spt-two-takethis*)
                     (fn-served-submissions (in-arena-spt-whole *sr-arena* *spt-feed* *spt-two-takethis*))))
(assert-event (equal (len (in-arena-fn-served-drain-taken *sr-arena* *spt-feed* *spt-two-takethis*)) 2))
(assert-event (fn-peer-submissionp (car (in-arena-fn-served-drain-taken *sr-arena* *spt-feed* *spt-two-takethis*))))
(assert-event (fn-peer-submissionp (cadr (in-arena-fn-served-drain-taken *sr-arena* *spt-feed* *spt-two-takethis*))))

; A TAKETHIS split across two reads, the cut inside its body: the first read
; consumes all of it and submits nothing, the second submits it, and the run
; is the one-read run (fn-served-drain-run-is-boundary-independent).
(defconst *spt-cut* (- (len *spt-t1*) 9))
(defconst *spt-split* (list (take *spt-cut* *spt-two-takethis*)
                            (nthcdr *spt-cut* *spt-two-takethis*)))
(assert-event (equal (in-arena-spt-consumed *sr-arena* *spt-feed* (car *spt-split*)) *spt-cut*))
(assert-event (null (fn-served-submissions (in-arena-spt-effects *sr-arena* *spt-feed* (car *spt-split*)))))
(assert-event (equal (fn-served-concat *spt-split*) *spt-two-takethis*))
(assert-event (equal (in-arena-fn-served-drain-run *sr-arena* *spt-feed* *spt-split*)
                     (in-arena-fn-served-drain-run *sr-arena* *spt-feed* (list *spt-two-takethis*))))
(assert-event (equal (len (fn-served-submissions
                           (fn-served-result-effects
                            (in-arena-fn-served-drain-run *sr-arena* *spt-feed* *spt-split*))))
                     2))

; The review of 2026-09-26 (gpt-6, wave 5, section 6) asks for cuts inside
; the terminators and arbitrary fragmentation.  Every TAKETHIS here comes
; with no CHECK before it (RFC 4644 section 2.5 permits that), so no bound on
; outstanding CHECK replies limits the submissions a read carries.
(defun spt-cuts-at (xs cuts)
  ;; XS split before each index in CUTS (ascending), as the network might.
  (declare (xargs :measure (len cuts)))
  (if (and (consp cuts) (natp (car cuts)) (< 0 (car cuts)) (< (car cuts) (len xs)))
      (cons (take (car cuts) xs)
            (spt-cuts-at (nthcdr (car cuts) xs)
                         (let ((rest (cdr cuts)))
                           (if (and (consp rest) (natp (car rest)))
                               (cons (- (car rest) (car cuts)) (cdr rest))
                             nil))))
    (list xs)))
(defun spt-bytes (xs)
  ;; one read per octet
  (if (consp xs) (cons (list (car xs)) (spt-bytes (cdr xs))) nil))
; The terminator of the first article is its last three octets: cut between
; `.' and CR, between CR and LF, and right after LF.
(defconst *spt-dot* (- (len *spt-t1*) 3))
(defconst *spt-term-cuts*
  (list (spt-cuts-at *spt-two-takethis* (list (+ *spt-dot* 1)))
        (spt-cuts-at *spt-two-takethis* (list (+ *spt-dot* 2)))
        (spt-cuts-at *spt-two-takethis* (list (+ *spt-dot* 1) (+ *spt-dot* 2)
                                              (+ *spt-dot* 3)))
        (spt-bytes *spt-two-takethis*)))
(defun spt-all-same-run (conn cuttings whole fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp cuttings)
      (and (equal (fn-served-concat (car cuttings)) whole)
           (equal (fn-served-drain-run conn (car cuttings) fn-arena)
                  (fn-served-drain-run conn (list whole) fn-arena))
           (equal (len (fn-served-submissions
                        (fn-served-result-effects
                         (fn-served-drain-run conn (car cuttings) fn-arena))))
                  2)
           (spt-all-same-run conn (cdr cuttings) whole fn-arena))
    t))
(assert-event (equal (len (car *spt-term-cuts*)) 2))
(assert-event (equal (len (caddr *spt-term-cuts*)) 4))
(assert-event (equal (len (cadddr *spt-term-cuts*)) (len *spt-two-takethis*)))
(assert-event (in-arena-spt-all-same-run *sr-arena* *spt-feed* *spt-term-cuts* *spt-two-takethis*))
; Byte by byte, the read that carries the first terminator's LF is the one
; that yields with the first submission, and nothing is left over.
(assert-event (equal (in-arena-fn-served-drain-taken *sr-arena* *spt-feed* *spt-two-takethis*)
                     (fn-served-submissions
                      (fn-served-result-effects
                       (in-arena-fn-served-drain-run *sr-arena* *spt-feed* (spt-bytes *spt-two-takethis*))))))

; -----------------------------------------------------------------------------
; Teeth.
;
; fn-served-drain-run-is-boundary-independent: its one hypothesis is the equal
; concatenation.  Without it: two streams that differ by one article, both
; valid chunk lists on a real connection, reach different results.
(assert-event (not (equal (fn-served-concat (list *spt-t1*))
                          (fn-served-concat (list *spt-two-takethis*)))))
(assert-event (not (equal (in-arena-fn-served-drain-run *sr-arena* *spt-feed* (list *spt-t1*))
                          (in-arena-fn-served-drain-run *sr-arena* *spt-feed* (list *spt-two-takethis*)))))
(local
 (must-fail
  (defthm spt-boundary-independence-without-equal-octets
    (equal (fn-served-drain-run conn one fn-arena)
           (fn-served-drain-run conn two fn-arena)))))

; The yield is what the repair adds, and the whole read is not a yielding read:
; the false "the one-read fold carries at most one submission" (what the owner
; relied on before PKT-600) is refuted by the two-POST read above.
(local
 (must-fail
  (defthm spt-one-read-carries-at-most-one-submission
    (implies (fn-served-connp conn)
             (<= (len (fn-served-submissions
                       (fn-served-result-effects (fn-served-step conn octets fn-arena))))
                 1)))))
(assert-event (fn-served-connp *spt-reader*))
(assert-event (< 1 (len (fn-served-submissions (in-arena-spt-whole *sr-arena* *spt-reader* *spt-two-posts*)))))

; The counted read over the whole region is not the one-read fold once a
; submission made it yield: the old `fn-served-step-counted-result-is-step'
; statement is false, with the two-POST read as its counterexample.
(assert-event (not (equal (fn-served-counted-result (in-arena-spt-counted *sr-arena* *spt-reader* *spt-two-posts*))
                          (in-arena-fn-served-step *sr-arena* *spt-reader* *spt-two-posts*))))
(local
 (must-fail
  (defthm spt-old-counted-result-is-whole-step
    (equal (fn-served-counted-result (fn-served-step-counted conn octets fn-arena))
           (fn-served-step conn octets fn-arena)))))

; fn-served-step-counted-carries-at-most-one-submission and
; fn-served-drain-takes-every-submission keep the served invariant
; (fn-served-connp) as their hypothesis.  Its removal has no witness here: a
; connection outside the invariant whose one dispatch emits two submissions is
; not known, and the weakened theorem is not proved (PKT-615).  The retained
; hypothesis holds on both fixtures above, and the conclusions are exercised
; on reads that carry two submissions.
(assert-event (<= (len (fn-served-submissions (in-arena-spt-effects *sr-arena* *spt-feed* *spt-two-takethis*))) 1))
