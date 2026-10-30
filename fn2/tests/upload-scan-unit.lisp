; D4 1/n evidence for the upload's header scan and definite verdict
; (fn2/books/upload-scan.lisp; fn2/docs/d-machines-nntp.md section 14.3.2).
; Each fixture is one dot-unstuffed article source with the word written
; here from the rule it exercises: H's model (fn2/tests/model/nntp_model.py,
; _article_block, headers, stored_msgid) for the order and the field
; reading, specs/article-parser.md for header syntax. Every fixture is also
; run with the octets arriving in two pieces at every split point and with
; the smallest budget, so the continuation is exercised at every boundary.
; Run: sh fn2/tools/certify.sh tests/upload-scan-unit.lisp
(in-package "ACL2")
(include-book "../books/upload-scan")

(defun fn2-usu-octets (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (atom cs) nil (cons (char-code (car cs)) (fn2-usu-octets (cdr cs)))))
(defun fn2-usu-crlf (lines)
  (declare (xargs :guard (string-listp lines)))
  (if (atom lines) ""
    (concatenate 'string (car lines) (coerce (list (code-char 13) (code-char 10)) 'string)
                 (fn2-usu-crlf (cdr lines)))))
(defun fn2-usu-feed (octets slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom octets) fn2-pool
    (mv-let (code fn2-pool) (fn2-gram-put (nfix (car octets)) slot gen 1 1 1 fn2-pool)
      (declare (ignore code))
      (fn2-usu-feed (cdr octets) slot gen fn2-pool))))

; Scan to a stop: repeat while the scan made progress on a full budget.
(defun fn2-usu-drive (fuel budget st slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :fuel st)
    (b* (((list off field visible fields lines seen mo ml no nl po pl) st)
         ((mv status off field visible fields lines seen mo ml no nl po pl &)
          (fn2-upload-scan budget off field visible fields lines seen mo ml no nl po pl slot gen 1 1 1 fn2-pool))
         (st (list off field visible fields lines seen mo ml no nl po pl)))
      (if (eq status :budget) (fn2-usu-drive (- fuel 1) budget st slot gen fn2-pool)
        (mv status st)))))
(defconst *fn2-usu-start* (list 0 *fn2-upload-field-none* nil 0 0 0 0 0 0 0 0 0))

; The word for SOURCE under RULE: the octets arrive as PREFIX octets, a scan,
; then the rest (SPLIT nil: all at once), scanned with BUDGET per call. The
; transit command's Message-ID is CMID. Returns (word injected).
(defun fn2-usu-run (rule source split budget bound cmid)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (result fn2-pool)
      (b* ((fn2-pool (fn2-pool-init '((2 . 65536)) 1 1000 fn2-pool))
           ((mv & slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool))
           ((mv & cslot cgen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool))
           (fn2-pool (fn2-usu-feed (fn2-usu-octets (coerce cmid 'list)) cslot cgen fn2-pool))
           (octets (fn2-usu-octets (coerce source 'list)))
           (k (if split (min split (len octets)) (len octets)))
           (fn2-pool (fn2-usu-feed (take k octets) slot gen fn2-pool))
           ((mv status st) (fn2-usu-drive 200 budget *fn2-usu-start* slot gen fn2-pool))
           (fn2-pool (fn2-usu-feed (nthcdr k octets) slot gen fn2-pool))
           ((mv status st) (if (eq status :more) (fn2-usu-drive 200 budget st slot gen fn2-pool) (mv status st)))
           ((list & & & & & seen mo ml & & po pl) st)
           ((mv word injected)
            (fn2-upload-verdict rule status seen mo ml po pl (len octets) bound cslot cgen 0 (length cmid) 1 1 1
                                slot gen 1 1 1 fn2-pool)))
        (mv (list word injected) fn2-pool))
      result)))

; Every split point and the two budgets agree with the expected word.
(defun fn2-usu-splits (k rule source bound cmid expect)
  (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 (length source)) (nfix k)))))
  (cond ((< (length source) (nfix k)) t)
        ((not (equal (fn2-usu-run rule source (nfix k) *fn2-upload-line-cost* bound cmid) expect))
         (cw "split ~x0 of ~x1: ~x2~%" k source (fn2-usu-run rule source (nfix k) *fn2-upload-line-cost* bound cmid)))
        (t (fn2-usu-splits (+ 1 (nfix k)) rule source bound cmid expect))))
(defun fn2-usu-check (rule lines bound cmid expect)
  (declare (xargs :verify-guards nil))
  (let ((source (if (stringp lines) lines (fn2-usu-crlf lines))))
    (and (or (equal (fn2-usu-run rule source nil 4096 bound cmid) expect)
             (cw "whole ~x0: ~x1 expected ~x2~%" lines (fn2-usu-run rule source nil 4096 bound cmid) expect))
         (fn2-usu-splits 0 rule source bound cmid expect))))

(defconst *fn2-usu-good* '("From: a@example.invalid" "Subject: hello" "Newsgroups: local.test"
                           "Message-ID: <one@example.invalid>" "" "body line" ".. a stuffed dot was here"))
(defun fn2-usu-long-line (n) (declare (xargs :verify-guards nil)) (coerce (make-list n :initial-element #\x) 'string))

(defun fn2-usu-fixtures ()
  (declare (xargs :verify-guards nil))
  (let ((b 32768) (none ""))
    (and
     ;; accepted shapes
     (fn2-usu-check :post *fn2-usu-good* b none '(:ok nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "" "") b none '(:ok nil))
     (fn2-usu-check :post '("From: a" "Subject: folded" "  continued" "Newsgroups: g," " h" "" "x") b none '(:ok nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Path: a!b.c!d" "" "x") b none '(:ok nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Message-ID: <a@[10.0.0.1]>" "" "x") b none '(:ok nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Message-ID:  <a.b@c.d>  " "" "x") b none '(:ok nil))
     (fn2-usu-check :post '("FROM: a" "subject: s" "NewsGroups: g" "X-Other: y" "X-Other: z" "" "x") b none '(:ok nil))
     ;; Xref and Injection fields: refused by the transaction after its group check
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Xref: h g:1" "" "x") b none '(:ok t))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Injection-Info: h" "" "x") b none '(:ok t))
     ;; the bound comes first, whatever else is wrong
     (fn2-usu-check :post '("Subject: s" "" "x") 5 none '(:too-large nil))
     ;; separator and required fields
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g") b none '(:malformed nil))
     (fn2-usu-check :post '("From: a" "Newsgroups: g" "" "x") b none '(:missing nil))
     (fn2-usu-check :post '("" "x") b none '(:missing nil))
     ;; header syntax (fn1's, specs/article-parser.md)
     (fn2-usu-check :post '(" leading continuation" "From: a" "Subject: s" "Newsgroups: g" "" "x") b none '(:malformed nil))
     (fn2-usu-check :post '("From: a" "Subject: " "Newsgroups: g" "" "x") b none '(:malformed nil))
     (fn2-usu-check :post '("From:a" "Subject: s" "Newsgroups: g" "" "x") b none '(:malformed nil))
     (fn2-usu-check :post '("No colon here" "" "x") b none '(:malformed nil))
     (fn2-usu-check :post (list "From: a" "Subject: s" (concatenate 'string "Newsgroups: g" (coerce (list (code-char 200)) 'string)) "" "x") b none '(:malformed nil))
     (fn2-usu-check :post (list "From: a" "Subject: s" (concatenate 'string "X-Long: " (fn2-usu-long-line 991)) "Newsgroups: g" "" "x") b none '(:line-length nil))
     (fn2-usu-check :post (list "From: a" "Subject: s" (concatenate 'string "X-Long: " (fn2-usu-long-line 990)) "Newsgroups: g" "" "x") b none '(:ok nil))
     ;; duplicates of the six fields the model counts
     (fn2-usu-check :post '("From: a" "From: b" "Subject: s" "Newsgroups: g" "" "x") b none '(:duplicate-field nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Date: d" "Date: e" "" "x") b none '(:duplicate-field nil))
     ;; Path (POST only)
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Path: a!b!.posted" "" "x") b none '(:path nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Path: a!!b" "" "x") b none '(:path nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Path: a b" "" "x") b none '(:path nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Path: a!b" " !c" "" "x") b none '(:path nil))
     ;; Message-ID syntax
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Message-ID: <nohost>" "" "x") b none '(:message-id nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Message-ID: <a..b@c>" "" "x") b none '(:message-id nil))
     (fn2-usu-check :post '("From: a" "Subject: s" "Newsgroups: g" "Message-ID: <a@b>" " folded" "" "x") b none '(:message-id nil))
     ;; transit: Message-ID, Date and Path required; the command's ID must match
     (fn2-usu-check :ihave '("From: a" "Subject: s" "Newsgroups: g" "Message-ID: <t@x>" "Path: p" "" "x") b "<t@x>" '(:missing nil))
     (fn2-usu-check :ihave '("From: a" "Subject: s" "Newsgroups: g" "Message-ID: <t@x>" "Date: d" "Path: p" "" "x") b "<t@x>" '(:ok nil))
     (fn2-usu-check :takethis '("From: a" "Subject: s" "Newsgroups: g" "Message-ID: <t@x>" "Date: d" "Path: p" "" "x") b "<u@x>" '(:mismatch nil))
     (fn2-usu-check :takethis '("From: a" "Subject: s" "Newsgroups: g" "Message-ID: <t@x>" "Date: d" "Path: p!POSTED" "" "x") b "<t@x>" '(:ok nil)))))

(assert-event (fn2-usu-fixtures))
