; fn: teeth for books/history-pages.lisp (lane arena-store-2, 2026-09-27).
;
; What this book is evidence FOR.  Each KEYSTONE of the history's FNADTSN1
; image gets a ground positive witness asserting its complete antecedent and
; conclusion, and per hypothesis a witness where the retained hypotheses
; hold, the omitted one fails and the conclusion fails (and a
; must-fail-checked of the theorem without it).  Named exceptions:
;   fn-hp-decode-image's two u64 bounds: a counterexample needs an image of
;     2^64 octets (not constructible); symbolic, as history-columns-tests'
;     length bound.
;   fn-hp-page-digest-is-leaf's (fn-shs-p fn-shs): inherited from
;     `pgs-x-words-digest-is-sha256'; the digest re-initializes the state it
;     reads, so no ground shape violation changes the answer, and a
;     non-stobj argument does not evaluate.  Kept, not witnessed.
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

; One event whose tree is longer than a page: the pool has two pages, so an
; append of a small event leaves the pool's first page alone.
(defun hpt-string (n acc) (if (zp n) acc (hpt-string (1- n) (cons #\x acc))))
(defconst *hpt-big* (list :retained 2 "<b@x>" (coerce (hpt-string 20000 nil) 'string)))

; 2048 events fill each column's first page exactly; one more doubles them.
(defun hpt-many (n acc)
  (if (zp n) acc (hpt-many (1- n) (cons (list :e n "abcdefghijklmnopqrstu") acc))))
(defconst *hpt-many* (hpt-many 2048 nil))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-decode-image.

(defthm hpt-decode-w
  (and (fn-hp-events-okp *hpt-h2*)
       (< (len *hpt-h2*) *adt-u64-limit*)
       (< (len (fn-hp-image *hpt-h2* 0)) *adt-u64-limit*)
       (equal (fn-hp-decode (fn-hp-image *hpt-h2* 0) 0) (list :ok *hpt-h2*)))
  :rule-classes nil)

; Removal of (fn-hp-events-okp h): a rational is no tree; its image does not
; decode to it.
(defthm hpt-decode-okp-removal
  (and (not (fn-hp-events-okp (list 1/2)))
       (< (len (list 1/2)) *adt-u64-limit*)
       (< (len (fn-hp-image (list 1/2) 0)) *adt-u64-limit*)
       (not (equal (fn-hp-decode (fn-hp-image (list 1/2) 0) 0) (list :ok (list 1/2)))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
 (defthm hpt-false-decode-without-okp
   (implies (and (< (len h) *adt-u64-limit*)
                 (< (len (fn-hp-image h salt)) *adt-u64-limit*))
            (equal (fn-hp-decode (fn-hp-image h salt) salt) (list :ok h))))))

; A decoder refusal by name: a corrupted MKEY cell.
(defthm hpt-decode-refuses-mkey
  (equal (fn-hp-decode (update-nth (* 16384 1) 99 *hpt-img2*) 0) (list :refused :mkey))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-page-digest-is-leaf.

(defthm hpt-digest-w
  (let ((mem (update-nth *pgs-wi* *hpt-w2* (create-pgs-mem))))
    (and (fn-shs-p (create-fn-shs)) (natp 1)
         (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 1) (pgs-x-arr 0 mem))))
                (fn-hp-page (fn-hp-image *hpt-h2* 0) 1))
         (equal (mv-nth 0 (pgs-x-page-digest 1 mem (create-fn-shs)))
                (pgs-octets-be-nat (nth 1 (adt-page-digests *fn-hp-schema* (fn-hp-rows *hpt-h2* 0)))))))
  :rule-classes nil)

; Removal of the words hypothesis: one word of page 1 changed.
(defthm hpt-digest-words-removal
  (let ((mem (update-nth *pgs-wi* (update-nth 2048 7 *hpt-w2*) (create-pgs-mem))))
    (and (fn-shs-p (create-fn-shs)) (natp 1)
         (not (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 1) (pgs-x-arr 0 mem))))
                     (fn-hp-page (fn-hp-image *hpt-h2* 0) 1)))
         (not (equal (mv-nth 0 (pgs-x-page-digest 1 mem (create-fn-shs)))
                     (pgs-octets-be-nat (nth 1 (adt-page-digests *fn-hp-schema* (fn-hp-rows *hpt-h2* 0))))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
 (defthm hpt-false-digest-without-words
   (implies (and (fn-shs-p fn-shs) (natp k))
            (equal (mv-nth 0 (pgs-x-page-digest k pgs-mem fn-shs))
                   (pgs-octets-be-nat (nth k (adt-page-digests *fn-hp-schema* (fn-hp-rows h salt)))))))))

; Removal of (natp k): K = 1/2 reads the words from 1024 (half a page in),
; which are the image's octets from 8192, while the table's leaf at 1/2 is
; leaf 0.
(defthm hpt-digest-natp-removal
  (let ((mem (update-nth *pgs-wi* *hpt-w2* (create-pgs-mem))))
    (and (fn-shs-p (create-fn-shs)) (not (natp 1/2))
         (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 1/2) (pgs-x-arr 0 mem))))
                (fn-hp-page (fn-hp-image *hpt-h2* 0) 1/2))
         (not (equal (mv-nth 0 (pgs-x-page-digest 1/2 mem (create-fn-shs)))
                     (pgs-octets-be-nat (nth 1/2 (adt-page-digests *fn-hp-schema* (fn-hp-rows *hpt-h2* 0))))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
 (defthm hpt-false-digest-without-natp
   (implies (and (fn-shs-p fn-shs)
                 (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 k) (pgs-x-arr 0 pgs-mem))))
                        (fn-hp-page (fn-hp-image h salt) k)))
            (equal (mv-nth 0 (pgs-x-page-digest k pgs-mem fn-shs))
                   (pgs-octets-be-nat (nth k (adt-page-digests *fn-hp-schema* (fn-hp-rows h salt)))))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-append-changes-only-dirty.
;
; H = (big), NEW = (e2): the pool (region 4) has two pages; its first page
; (image page 5) is not dirty and is unchanged.
(defconst *hpt-hb* (list *hpt-big*))
(defconst *hpt-nb* (list *hpt-e2*))

(defthm hpt-dirty-w
  (and (natp 5)
       (not (member-equal 5 (fn-hp-append-dirty *hpt-hb* *hpt-nb* 0)))
       (equal (fn-hp-page (fn-hp-image (append *hpt-hb* *hpt-nb*) 0) 5)
              (fn-hp-page (fn-hp-image *hpt-hb* 0) 5))
       ; what the positive witness is about: the dirty list is not every page
       (equal (fn-hp-append-dirty *hpt-hb* *hpt-nb* 0) '(0 1 2 3 4 6))
       (equal (fn-hp-npages (append *hpt-hb* *hpt-nb*) 0) 7))
  :rule-classes nil)

; Removal of (not (member k dirty)): the header page changes (N).
(defthm hpt-dirty-member-removal
  (and (natp 0)
       (member-equal 0 (fn-hp-append-dirty *hpt-hb* *hpt-nb* 0))
       (not (equal (fn-hp-page (fn-hp-image (append *hpt-hb* *hpt-nb*) 0) 0)
                   (fn-hp-page (fn-hp-image *hpt-hb* 0) 0))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
 (defthm hpt-false-dirty-without-member
   (implies (natp k)
            (equal (fn-hp-page (fn-hp-image (append h new) salt) k)
                   (fn-hp-page (fn-hp-image h salt) k))))))

; Removal of (natp k): "page" 3/2 spans the MKEY column's page's second
; half and the length column's first half, where the new cell lands.
(defthm hpt-dirty-natp-removal
  (and (not (natp 3/2))
       (not (member-equal 3/2 (fn-hp-append-dirty *hpt-hb* *hpt-nb* 0)))
       (not (equal (fn-hp-page (fn-hp-image (append *hpt-hb* *hpt-nb*) 0) 3/2)
                   (fn-hp-page (fn-hp-image *hpt-hb* 0) 3/2))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
 (defthm hpt-false-dirty-without-natp
   (implies (not (member-equal k (fn-hp-append-dirty h new salt)))
            (equal (fn-hp-page (fn-hp-image (append h new) salt) k)
                   (fn-hp-page (fn-hp-image h salt) k))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-append-dirty-bound.

(defthm hpt-bound-w
  (and (fn-hp-caps-same (fn-hp-regs *hpt-hb* 0) (fn-hp-regs (append *hpt-hb* *hpt-nb*) 0))
       (<= (* *adt-page* (len (fn-hp-append-dirty *hpt-hb* *hpt-nb* 0)))
           (+ (* 11 *adt-page*) (* 32 (len *hpt-nb*)) (fn-hp-enc-len *hpt-nb*))))
  :rule-classes nil)

; Removal of the caps hypothesis: appending the 2049th event doubles every
; column, so every page after the header moves: 17 dirty pages, over the
; bound of 11 + (32 + 24) / 16384.
(defthm hpt-bound-caps-removal
  (and (not (fn-hp-caps-same (fn-hp-regs *hpt-many* 0)
                             (fn-hp-regs (append *hpt-many* *hpt-nb*) 0)))
       (equal (len (fn-hp-append-dirty *hpt-many* *hpt-nb* 0)) 17)
       (not (<= (* *adt-page* (len (fn-hp-append-dirty *hpt-many* *hpt-nb* 0)))
                (+ (* 11 *adt-page*) (* 32 (len *hpt-nb*)) (fn-hp-enc-len *hpt-nb*)))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
 (defthm hpt-false-bound-without-caps
   (<= (* *adt-page* (len (fn-hp-append-dirty h new salt)))
       (+ (* 11 *adt-page*) (* 32 (len new)) (fn-hp-enc-len new))))))
