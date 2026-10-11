; Witnesses and teeth for books/filed-history (O1 packet 4, P4-R): the
; history invariant FN-O1-FILES-FILEDP carried by every Store transition.
;
; A concrete store (store-node-tests' reserved store, groups fn.letters and
; fn.test) stages and then publishes a filed article record: the held row is
; interned at handle 0 of an arena holding the payload, so the staged row
; meets FN-O1-PREPARE-KEEPS-THE-FILES-FILED's hypothesis (P4-R5), and the
; record-directory :ok that appends it (the one step that changes the
; records, P4-R1) leaves the files filed, with the row among the records and
; no candidate left.  The finish (R2), a crash that keeps the record (R3, the
; :present choice) and, after the crash, the recovery (R4) are evaluated on
; the same store, and a seal of one more payload (R6) keeps the files filed.
; The removal tooth of R5's hypothesis: a record whose groups its payload's
; Newsgroups do not name (groups fn.test, payload naming fn.letters only) is
; staged by the same prepare, the other hypothesis (the initial files filed)
; holds, and the files are NOT filed after it.
(in-package "ACL2")
(include-book "../../books/filed-history")
(include-book "store-node-tests")
(include-book "held-rows-tests")
(include-book "../../books/crypto-attach")
(include-book "../../books/codec-attach")

(defconst *otf-crlf* (coerce '(#\Return #\Newline) 'string))
(defun otf-src (newsgroups)
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" *otf-crlf*
                "Newsgroups: " newsgroups *otf-crlf*
                "Subject: s" *otf-crlf*
                "Message-ID: <w1@b.example>" *otf-crlf*
                *otf-crlf* "body" *otf-crlf*)))
(defun otf-wire (payload groups)
  (fn-record-make 0 0 0 "<w1@b.example>" payload groups
                  "otf-pin" "otf-content" "otf-release" 2 841000000))
; filed: groups fn.letters, the payload names fn.test and fn.letters
(defconst *otf-good* (otf-wire (otf-src "fn.test,fn.letters") '("fn.letters")))
; unfiled: groups fn.test, the payload names fn.letters only
(defconst *otf-bad* (otf-wire (otf-src "fn.letters") '("fn.test")))

(defun otf-scenario (w extra fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-hrt-events (list w) nil 0 fn-arena)
    (let* ((row (car rows))
           (s0 *sn-reserved*)
           (s1 (fn-sn-prepare s0 row))
           (f1 (fn-sn-files s1))
           (s2 (fn-sn-test-publish s1))
           (f2 (fn-sn-files s2))
           (s3 (fn-sn-finish s2))
           (c (fn-sn-crash s2 :old :present))
           (r (fn-sn-recover c))
           (hyp (fn-o1-records-filedp (fn-cat-history-articles (list row) fn-arena))))
      (let ((items (list (fn-o1-files-filedp (fn-sn-files s0) fn-arena)               ; 0 R0-shaped start
                  hyp                                                          ; 1 R5's hypothesis
                  (fn-sf-phase f1)                                             ; 2 staged
                  (equal (fn-sf-record-candidate f1) row)                      ; 3
                  (fn-o1-files-filedp f1 fn-arena)                             ; 4 R5
                  (fn-sf-phase f2)                                             ; 5 completing
                  (equal (fn-sf-records f2) (list row))                        ; 6 R1 appended
                  (equal (fn-sf-record-candidate f2) nil)                      ; 7
                  (fn-o1-files-filedp f2 fn-arena)                             ; 8 R1
                  (equal (fn-cat-history-articles (fn-sf-records f2) fn-arena) (list w)) ; 9
                  (fn-o1-files-filedp (fn-sn-files s3) fn-arena)               ; 10 R2
                  (equal (fn-sf-records (fn-sn-files c)) (list row))           ; 11 crash kept it
                  (fn-o1-files-filedp (fn-sn-files c) fn-arena)                ; 12 R3
                  (fn-o1-files-filedp (fn-sn-files r) fn-arena)                ; 13 R4
                  (fn-rows-handles-inp (fn-sf-records f2) fn-arena))))         ; 14 R6 hyps
        (let ((fn-arena (fn-arena-seal-list extra fn-arena)))
          (mv (append items (list (fn-o1-files-filedp f2 fn-arena))) fn-arena))))))   ; 15 R6
(defun otf-exec (w extra)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena) (otf-scenario w extra fn-arena)
      r)))

(defconst *otf-g* (otf-exec *otf-good* (otf-src "fn.other")))
(defconst *otf-b* (otf-exec *otf-bad* (otf-src "fn.other")))

; the reachable witness: staged, published, finished, crashed, recovered, sealed
(assert-event (equal *otf-g* '(t t :record-staged t t :completing t t t t t t t t t t)))
; the removal tooth of R5's hypothesis: the unfiled record is staged all the same,
; the start is filed, and the files are not filed after the prepare
(assert-event (and (nth 0 *otf-b*)
                   (not (nth 1 *otf-b*))
                   (eq (nth 2 *otf-b*) :record-staged)
                   (nth 3 *otf-b*)
                   (not (nth 4 *otf-b*))))
; ... and the append at the record directory publishes the unfiled record
; into the history: the history invariant is lost exactly there
(assert-event (and (nth 6 *otf-b*) (not (nth 8 *otf-b*))))
