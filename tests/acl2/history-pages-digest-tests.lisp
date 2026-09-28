; fn: teeth for books/history-pages.lisp's digest keystone (lane arena-store-4,
; 2026-09-28; split from history-pages-tests.lisp by lane arena-store-2's
; witnesses).
;
; What this book is evidence FOR.  KEYSTONE fn-hp-page-digest-is-leaf (the
; page store's page digest, BLAKE3 over the page's words, is the FNADTSN2
; leaf) gets a ground positive witness asserting its complete antecedent and
; conclusion, and per hypothesis a witness where the retained hypothesis
; holds, the omitted one fails and the conclusion fails (and a
; must-fail-checked of the theorem without it).  The theorem has no
; hypothesis on the octet buffer: the digest clears it before copying the
; words.  Apart from history-pages-tests because each witness evaluates the
; digest over the abstract stobj's list model (about 2 s a page).
(in-package "ACL2")
(include-book "../../books/history-pages")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; Ground histories.
(defconst *hpt-e1* (list :retained 1 "<a@x>" (list 1 2 3) "subject line"))
(defconst *hpt-e2* (list :other 7 nil))
(defconst *hpt-h2* (list *hpt-e1* *hpt-e2*))

(defun hpt-pack (n b)
  ; the octets B as N little-endian words: what the host's fill leaves
  (if (zp n) nil (cons (adt-unle 8 b) (hpt-pack (1- n) (nthcdr 8 b)))))

(defconst *hpt-img2* (fn-hp-image *hpt-h2* 0))
(defconst *hpt-w2* (hpt-pack (floor (len *hpt-img2*) 8) *hpt-img2*))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-page-digest-is-leaf.

(defthm hpt-digest-w
  (let ((mem (update-nth *pgs-wi* *hpt-w2* (create-pgs-mem))))
    (and (natp 1)
         (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 1) (pgs-x-arr 0 mem))))
                (fn-hp-page (fn-hp-image *hpt-h2* 0) 1))
         (equal (mv-nth 0 (pgs-x-page-digest 1 mem (create-fn-octets-pg)))
                (pgs-octets-be-nat (nth 1 (adt-page-digests *fn-hp-schema* (fn-hp-rows *hpt-h2* 0)))))))
  :rule-classes nil)

; Removal of the words hypothesis: one word of page 1 changed.
(defthm hpt-digest-words-removal
  (let ((mem (update-nth *pgs-wi* (update-nth 2048 7 *hpt-w2*) (create-pgs-mem))))
    (and (natp 1)
         (not (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 1) (pgs-x-arr 0 mem))))
                     (fn-hp-page (fn-hp-image *hpt-h2* 0) 1)))
         (not (equal (mv-nth 0 (pgs-x-page-digest 1 mem (create-fn-octets-pg)))
                     (pgs-octets-be-nat (nth 1 (adt-page-digests *fn-hp-schema* (fn-hp-rows *hpt-h2* 0))))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
 (defthm hpt-false-digest-without-words
   (implies (natp k)
            (equal (mv-nth 0 (pgs-x-page-digest k pgs-mem fn-octets-pg))
                   (pgs-octets-be-nat (nth k (adt-page-digests *fn-hp-schema* (fn-hp-rows h salt)))))))))

; Removal of (natp k): K = 1/2 reads the words from 1024 (half a page in),
; which are the image's octets from 8192, while the table's leaf at 1/2 is
; leaf 0.
(defthm hpt-digest-natp-removal
  (let ((mem (update-nth *pgs-wi* *hpt-w2* (create-pgs-mem))))
    (and (not (natp 1/2))
         (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 1/2) (pgs-x-arr 0 mem))))
                (fn-hp-page (fn-hp-image *hpt-h2* 0) 1/2))
         (not (equal (mv-nth 0 (pgs-x-page-digest 1/2 mem (create-fn-octets-pg)))
                     (pgs-octets-be-nat (nth 1/2 (adt-page-digests *fn-hp-schema* (fn-hp-rows *hpt-h2* 0))))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
 (defthm hpt-false-digest-without-natp
   (implies (and
                 (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 k) (pgs-x-arr 0 pgs-mem))))
                        (fn-hp-page (fn-hp-image h salt) k)))
            (equal (mv-nth 0 (pgs-x-page-digest k pgs-mem fn-octets-pg))
                   (pgs-octets-be-nat (nth k (adt-page-digests *fn-hp-schema* (fn-hp-rows h salt)))))))))

