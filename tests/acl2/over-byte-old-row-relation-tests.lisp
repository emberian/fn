(in-package "ACL2")
(include-book "../../books/over-byte-old-row-relation")

(defconst *obort-source*
 (append (fn-record-string-octets "Subject: a") '(13 10 32 98 13 10)
         (fn-record-string-octets "From: c") '(13 10)
         (fn-record-string-octets "Date: d") '(13 10)
         (fn-record-string-octets "Message-ID: <e@x>") '(13 10)
         (fn-record-string-octets "References: <r@x>") '(13 10 13 10 122 13 10)))
(defun obort-token ()
 (mv-let (owners pins status) (fn-rpin-step nil '(31 nil nil) '(:acquire 7))
  (declare (ignore pins status)) (fn-rpin-token 7 owners)))
(defun obort-advance (s steps fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :measure (nfix steps) :verify-guards nil))
 (if (zp steps) s
  (mv-let (out next) (fn-obc-one s fn-arena fn-cat)
   (declare (ignore out)) (obort-advance next (1- steps) fn-arena fn-cat))))
(defun-nx obort-old-row-conclusionp (s article number fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (let ((parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))))
  (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
         (append (fn-nov-line number (fn-nov-overview article fn-arena)) '(13 10)))))

(defthm obort-reachable-actual-old-row-positive
 (let* ((fn-arena (list *obort-source*))
        (wire (fn-record-make 0 1 0 "<e@x>" *obort-source*
                              '("fn.test") "o" "s" "e" 1 5))
        (fn-cat (list (fn-held-with-numbers (fn-held-plain wire 0) '(("fn.test" . 1)))))
        (article (fn-make-article "<e@x>" 0 '("fn.test") '(("fn.test" . 1)) t 1))
        (s (obort-advance
             (fn-obc-begin (fn-ovw-cursor "fn.test" 1 1 1 nil t) (obort-token))
             (len *obort-source*) fn-arena fn-cat))
        (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena)))
        (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
  (and (equal (nth 2 s) :parse) (fn-obc-parser-prefix-p s fn-arena fn-cat)
       (equal (fn-lpc-verdict parser) :valid) (fn-cbor-octet-listp bytes)
       (equal (fn-nntp-article-bytes article fn-arena) bytes)
       (fn-hnov-ok (fn-hnov-of bytes))
       (equal (fn-nov-overview article fn-arena)
         (list :ok (fn-record-string-octets (fn-hnov-subject (fn-hnov-of bytes)))
                   (fn-record-string-octets (fn-hnov-from (fn-hnov-of bytes)))
                   (fn-record-string-octets (fn-hnov-date (fn-hnov-of bytes)))
                   (fn-record-string-octets (fn-hnov-msgid (fn-hnov-of bytes)))
                   (fn-record-string-octets (fn-hnov-references (fn-hnov-of bytes)))
                   (len bytes) (fn-hf-body-lines-of bytes)))
       (obort-old-row-conclusionp s article 1 fn-arena fn-cat)))
 :rule-classes nil)

; Literal successful-source removal: a malformed actual source is terminal,
; with every retained prefix/source hypothesis, but the old row is :error.
(defthm obort-without-valid-corrupted-state
 (let* ((bytes '(65 13 10 13 10)) (fn-arena (list bytes)) (fn-cat nil)
        (s (fn-obc-make nil :pin :parse
             (fn-lpc-feed (butlast bytes 1) (fn-lpc-begin 0 (len bytes) :pin)) nil 0))
        (article (fn-make-article "<e@x>" 0 nil nil t 1)))
  (and (equal (nth 2 s) :parse) (fn-obc-parser-prefix-p s fn-arena fn-cat)
       (not (equal (fn-lpc-verdict (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))) :valid))
       (fn-cbor-octet-listp (nth (fn-obc-selected-handle s fn-cat) fn-arena))
       (equal (fn-nntp-article-bytes article fn-arena)
              (nth (fn-obc-selected-handle s fn-cat) fn-arena))
       (not (obort-old-row-conclusionp s article 1 fn-arena fn-cat))))
 :rule-classes nil)

(defthm obort-without-phase-corrupted-state
 (let* ((fn-arena (list *obort-source*)) (fn-cat nil)
        (other (append *obort-source* '(122 13 10)))
        (s (fn-obc-make nil :pin :seek
              (fn-lpc-feed other (fn-lpc-begin 0 (len other) :pin)) nil 0))
        (article (fn-make-article "<e@x>" 0 nil nil t 1)))
  (and (not (equal (nth 2 s) :parse))
       (fn-obc-parser-prefix-p s fn-arena fn-cat)
       (equal (fn-lpc-verdict (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))) :valid)
       (fn-cbor-octet-listp (nth (fn-obc-selected-handle s fn-cat) fn-arena))
       (equal (fn-nntp-article-bytes article fn-arena)
              (nth (fn-obc-selected-handle s fn-cat) fn-arena))
       (not (obort-old-row-conclusionp s article 1 fn-arena fn-cat))))
 :rule-classes nil)

(defthm obort-without-prefix-corrupted-state
 (let* ((fn-arena (list *obort-source*)) (fn-cat nil)
        (other (append *obort-source* '(122 13 10)))
        (s (fn-obc-make nil :pin :parse
              (fn-lpc-feed other (fn-lpc-begin 0 (len other) :pin)) nil 0))
        (article (fn-make-article "<e@x>" 0 nil nil t 1)))
  (and (equal (nth 2 s) :parse)
       (not (fn-obc-parser-prefix-p s fn-arena fn-cat))
       (equal (fn-lpc-verdict (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))) :valid)
       (fn-cbor-octet-listp (nth (fn-obc-selected-handle s fn-cat) fn-arena))
       (equal (fn-nntp-article-bytes article fn-arena)
              (nth (fn-obc-selected-handle s fn-cat) fn-arena))
       (not (obort-old-row-conclusionp s article 1 fn-arena fn-cat))))
 :rule-classes nil)

(defthm obort-without-octets-corrupted-state
 (let* ((bytes (append (butlast *obort-source* 3) '(256 13 10)))
        (fn-arena (list bytes)) (fn-cat nil)
        (s (fn-obc-make nil :pin :parse
             (fn-lpc-feed (butlast bytes 1) (fn-lpc-begin 0 (len bytes) :pin)) nil 0))
        (article (fn-make-article "<e@x>" 0 nil nil t 1)))
  (and (equal (nth 2 s) :parse) (fn-obc-parser-prefix-p s fn-arena fn-cat)
       (equal (fn-lpc-verdict (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))) :valid)
       (not (fn-cbor-octet-listp (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
       (equal (fn-nntp-article-bytes article fn-arena)
              (nth (fn-obc-selected-handle s fn-cat) fn-arena))
       (not (obort-old-row-conclusionp s article 1 fn-arena fn-cat))))
 :rule-classes nil)

(defthm obort-without-article-source-corrupted-state
 (let* ((fn-arena (list *obort-source*)) (fn-cat nil)
        (s (fn-obc-make nil :pin :parse
             (fn-lpc-feed (butlast *obort-source* 1)
                          (fn-lpc-begin 0 (len *obort-source*) :pin)) nil 0))
        (article (fn-make-article "<e@x>" (update-nth 9 113 *obort-source*) nil nil t 1)))
  (and (equal (nth 2 s) :parse) (fn-obc-parser-prefix-p s fn-arena fn-cat)
       (equal (fn-lpc-verdict (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))) :valid)
       (fn-cbor-octet-listp (nth (fn-obc-selected-handle s fn-cat) fn-arena))
       (not (equal (fn-nntp-article-bytes article fn-arena)
                   (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
       (not (obort-old-row-conclusionp s article 1 fn-arena fn-cat))))
 :rule-classes nil)

; Removing successful overview alone breaks the old-source tuple equation.
(defthm obort-old-overview-without-success-corrupted-state
 (let* ((fn-arena (list '(65 13 10 13 10)))
        (article (fn-make-article "<e@x>" 0 nil nil t 1))
        (bytes (fn-nntp-article-bytes article fn-arena)) (nov (fn-hnov-of bytes)))
  (and (not (fn-hnov-ok nov))
       (not (equal (fn-nov-overview article fn-arena)
         (list :ok (fn-record-string-octets (fn-hnov-subject nov))
                   (fn-record-string-octets (fn-hnov-from nov))
                   (fn-record-string-octets (fn-hnov-date nov))
                   (fn-record-string-octets (fn-hnov-msgid nov))
                   (fn-record-string-octets (fn-hnov-references nov))
                   (len bytes) (fn-hf-body-lines-of bytes))))))
 :rule-classes nil)
