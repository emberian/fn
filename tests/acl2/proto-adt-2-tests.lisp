; Teeth for lane proto-adt-2 (2026-09-27): the keyed set, the byte format,
; compaction, nested kinds, and a real nested shape run on the columns.
;
; For each keystone: a reachable positive witness that checks the complete
; antecedent and the conclusion, and per omitted hypothesis a witness that
; checks the retained hypotheses, the failure of the omitted one, and the
; failure of the conclusion.  Executed witnesses run the live stobjs.

(in-package "ACL2")
(include-book "../../books/proto/adt-bytes")
(include-book "../../books/proto/adt-compact-lib")
(include-book "../../books/proto/adt-config-groups")
(include-book "std/testing/assert-bang" :dir :system)

; -----------------------------------------------------------------------------
; 1. The keyed keystones at ground instances.  S: (key octets, a u32).

(defconst *ks* '((:octets) (:u32)))
(defconst *kr1* '((1) 5))
(defconst *kr2* '((2) 7))
(defconst *kc1* (adt-kinsert-c *ks* 0 *kr1* (adt-kempty-c *ks*)))
(defconst *ka1* (list *kr1*))
(defconst *kc2* (adt-kinsert-c *ks* 0 *kr2* *kc1*))
(defconst *ka2* (adt-kinsert :stack *kr2* *ka1*))

; adt-kcorr-insert: positive
(assert-event (and (adt-kcorr *ks* :stack 0 *kc1* *ka1*)
                   (adt-rec-p *ks* *kr2*)
                   (not (adt-kmem 0 (nth 0 *kr2*) *ka1*))
                   (adt-kcorr *ks* :stack 0 (adt-kinsert-c *ks* 0 *kr2* *kc1*)
                              (adt-kinsert :stack *kr2* *ka1*))))
; without freshness: a second record with key (1)
(assert-event (and (adt-kcorr *ks* :stack 0 *kc1* *ka1*)
                   (adt-rec-p *ks* '((1) 9))
                   (adt-kmem 0 '(1) *ka1*)
                   (not (adt-kcorr *ks* :stack 0 (adt-kinsert-c *ks* 0 '((1) 9) *kc1*)
                                   (adt-kinsert :stack '((1) 9) *ka1*)))))
; without the record's type: a u32 field at 2^32
(assert-event (and (adt-kcorr *ks* :stack 0 *kc1* *ka1*)
                   (not (adt-rec-p *ks* '((3) 4294967296)))
                   (not (adt-kmem 0 '(3) *ka1*))
                   (not (adt-kcorr *ks* :stack 0 (adt-kinsert-c *ks* 0 '((3) 4294967296) *kc1*)
                                   (adt-kinsert :stack '((3) 4294967296) *ka1*)))))
; without the correspondence: the empty image against (r1)
(assert-event (and (not (adt-kcorr *ks* :stack 0 (adt-kempty-c *ks*) *ka1*))
                   (adt-rec-p *ks* *kr2*)
                   (not (adt-kmem 0 (nth 0 *kr2*) *ka1*))
                   (not (adt-kcorr *ks* :stack 0 (adt-kinsert-c *ks* 0 *kr2* (adt-kempty-c *ks*))
                                   (adt-kinsert :stack *kr2* *ka1*)))))

; adt-kcorr-remove: positive (the value is (r2 r1): cons at the front)
(assert-event (and (equal *ka2* (list *kr2* *kr1*))
                   (adt-kcorr *ks* :stack 0 *kc2* *ka2*)
                   (adt-kcorr *ks* :stack 0 (adt-kremove-c *ks* 0 '(1) *kc2*)
                              (adt-kremove 0 '(1) *ka2*))
                   (equal (adt-kremove 0 '(1) *ka2*) (list *kr2*))))
; without the correspondence: the one-record image against (r2 r1)
(assert-event (and (not (adt-kcorr *ks* :stack 0 *kc1* *ka2*))
                   (not (adt-kcorr *ks* :stack 0 (adt-kremove-c *ks* 0 '(1) *kc1*)
                                   (adt-kremove 0 '(1) *ka2*)))))

; adt-kcorr-find: positive, and absent keys answer nil
(assert-event (and (adt-kcorr *ks* :stack 0 *kc2* *ka2*)
                   (equal (adt-kfind-c *ks* 0 '(2) *kc2*) *kr2*)
                   (equal (adt-kfind-c *ks* 0 '(2) *kc2*) (adt-kfind 0 '(2) *ka2*))
                   (equal (adt-kfind-c *ks* 0 '(4) *kc2*) nil)))
; without the correspondence: the one-record image misses (2)
(assert-event (and (not (adt-kcorr *ks* :stack 0 *kc1* *ka2*))
                   (not (equal (adt-kfind-c *ks* 0 '(2) *kc1*) (adt-kfind 0 '(2) *ka2*)))))

; A dead slot: after the remove, (1)'s slot is still in the image, dead.
(assert-event (let ((c (adt-kremove-c *ks* 0 '(1) *kc2*)))
                (and (equal (len (adt-abs (adt-pschema *ks*) c)) 2)
                     (equal (adt-live-recs (adt-abs (adt-pschema *ks*) c)) (list *kr2*)))))

; -----------------------------------------------------------------------------
; 2. Compaction: two histories, one value, two images; one compacted image.

(defconst *kh1* (adt-kremove-c *ks* 0 '(1) *kc2*))                       ; r1, r2, remove r1
(defconst *kh2* (adt-kinsert-c *ks* 0 *kr2* (adt-kempty-c *ks*)))        ; r2
(assert-event (and (adt-kcorr *ks* :stack 0 *kh1* (list *kr2*))
                   (adt-kcorr *ks* :stack 0 *kh2* (list *kr2*))
                   (not (equal *kh1* *kh2*))
                   (equal (adt-kcompact-c *ks* :stack 0 *kh1*) (adt-kcompact-c *ks* :stack 0 *kh2*))
                   (equal (adt-kcompact-c *ks* :stack 0 *kh1*) (adt-kcanon *ks* :stack 0 (list *kr2*)))
                   (adt-kcorr *ks* :stack 0 (adt-kcompact-c *ks* :stack 0 *kh1*) (list *kr2*))))
; without the correspondence (adt-kcompact-is-kcanon): an image of a
; different value compacts to a different canonical image
(assert-event (and (not (adt-kcorr *ks* :stack 0 *kc2* (list *kr2*)))
                   (not (equal (adt-kcompact-c *ks* :stack 0 *kc2*)
                               (adt-kcanon *ks* :stack 0 (list *kr2*))))))

; The sequence: a set of an octets field leaves dead octets; compaction
; returns the fill to the value's octet total.
(defconst *qs* '((:octets) (:u8)))
(defconst *qa* '(((1 2 3) 4)))
(defconst *qc* (adt-set-c *qs* 0 0 '(9) (adt-canon *qs* *qa*)))
(assert-event (and (adt-corr *qs* *qc* '(((9) 4)))
                   (equal (nth (+ 2 (adt-ncols *qs*)) *qc*) 4)
                   (equal (adt-vbytes *qs* '(((9) 4))) 1)
                   (equal (nth (+ 2 (adt-ncols *qs*)) (adt-compact-c *qs* *qc*)) 1)
                   (adt-corr *qs* (adt-compact-c *qs* *qc*) '(((9) 4)))))

; -----------------------------------------------------------------------------
; 3. The byte format.

(defconst *bs* '((:u64) (:octets) (:bool) (:enum :a :b)))
(defconst *ba* '((7 (104 105) t :b) (18446744073709551615 (1 2 3 4 5) nil :a)))
(defconst *bb* (adt-ser *bs* *ba*))

; adt-decode-ser: positive (7 pages: header, four columns + offset/length, pool)
(assert-event (and (adt-bschemap *bs*) (adt-seq-p *bs* *ba*)
                   (< (len *ba*) *adt-u64-limit*) (< (len *bb*) *adt-u64-limit*)
                   (equal (len *bb*) (* 7 *adt-page*))
                   (equal (adt-decode *bs* *bb*) (list :ok *ba*))))
; without a byte schema: a natural bounded by 2^64 is stored in 8 octets
(assert-event (with-guard-checking :none
               (let* ((s '((:nat 18446744073709551616))) (a '((18446744073709551616))))
                 (and (not (adt-bschemap s)) (adt-seq-p s a)
                      (< (len (adt-ser s a)) *adt-u64-limit*)
                      (not (equal (adt-decode s (adt-ser s a)) (list :ok a)))))))
; without the value's type: a u8 cell of 300
(assert-event (let* ((s '((:u8))) (a '((300))))
                (and (adt-bschemap s) (not (adt-seq-p s a))
                     (< (len (adt-ser s a)) *adt-u64-limit*)
                     (not (equal (adt-decode s (adt-ser s a)) (list :ok a))))))
; The decoder refuses by name.
(assert-event (and (equal (adt-decode *bs* (update-nth 0 0 *bb*)) '(:refused :magic))
                   (equal (adt-decode '((:u64)) *bb*) '(:refused :schema))
                   (equal (adt-decode *bs* (take (* 6 *adt-page*) *bb*)) '(:refused :length))
                   (equal (adt-decode *bs* (take 100 *bb*)) '(:refused :short))))
; Integrity is the page digests' job, not the decoder's: a flipped pool
; octet decodes to another value; its page's leaf changes.
(assert-event (let ((bad (update-nth (* 6 *adt-page*) 9 *bb*)))
                (and (equal (car (adt-decode *bs* bad)) :ok)
                     (not (equal (adt-decode *bs* bad) (list :ok *ba*)))
                     (not (equal (fn-sha256 (take *adt-page* (nthcdr (* 6 *adt-page*) bad)))
                                 (nth 6 (adt-page-digests *bs* *ba*)))))))
; adt-page-digest-nth, and one leaf per page
(assert-event (and (equal (len (adt-page-digests *bs* *ba*)) 7)
                   (equal (nth 0 (adt-page-digests *bs* *ba*)) (fn-sha256 (take *adt-page* *bb*)))))
; adt-ser-image-of-corr: two images of one value (a set leaves dead octets),
; one byte string
(defconst *img-a* (adt-set-c *bs* 1 0 '(104 105) (adt-set-c *bs* 1 0 '(3) (adt-canon *bs* *ba*))))
(assert-event (and (adt-corr *bs* *img-a* *ba*)
                   (adt-corr *bs* (adt-canon *bs* *ba*) *ba*)
                   (not (equal *img-a* (adt-canon *bs* *ba*)))
                   (equal (adt-ser-image *bs* *img-a*) *bb*)
                   (equal (adt-ser-image *bs* (adt-canon *bs* *ba*)) *bb*)))
; without the correspondence: an image of another value has other bytes
(assert-event (and (not (adt-corr *bs* (adt-canon *bs* (cdr *ba*)) *ba*))
                   (not (equal (adt-ser-image *bs* (adt-canon *bs* (cdr *ba*))) *bb*))))

; -----------------------------------------------------------------------------
; 4. Nested kinds: the round trip (adt-nunf-nfl) on a sum with payload.

(defconst *nk* '(:sum (:a (:prod (:u32) (:octets))) (:b (:string)) (:c (:alt nil (:u8)))))
(assert-event (and (adt-nkind :k *nk*)
                   (equal (adt-nflat :k *nk*)
                          '((:enum :a :b :c) (:u32) (:octets) (:octets) (:bool) (:u8)))
                   (adt-nval :k *nk* '(:a 5 (1 2)))
                   (equal (adt-nunf :k *nk* (append (adt-nfl :k *nk* '(:a 5 (1 2))) '(z)) nil)
                          '((:a 5 (1 2)) z))
                   (adt-nval :k *nk* '(:b . "x"))
                   (equal (adt-nfl :k *nk* '(:b . "x")) '(:b 0 nil (120) nil 0))
                   (equal (adt-nunf :k *nk* (adt-nfl :k *nk* '(:b . "x")) nil) '((:b . "x")))
                   (adt-nval :k *nk* '(:c))
                   (equal (adt-nunf :k *nk* (adt-nfl :k *nk* '(:c)) nil) '((:c)))))
; without validity: a tag the sum does not have does not come back
(assert-event (and (adt-nkind :k *nk*)
                   (not (adt-nval :k *nk* '(:d 1)))
                   (not (equal (car (adt-nunf :k *nk* (adt-nfl :k *nk* '(:d 1)) nil)) '(:d 1)))))
; without a kind: an unknown kind is not a kind
(assert-event (not (adt-nkind :k '(:tree (:u8)))))

; -----------------------------------------------------------------------------
; 5. The group table on the columns (nested stamp, option): create, create
;    again (revive in place, keep the watermark), retire -- each the model's.

(defconst *st0* '(:fn-clock-observation 10 20 1 t))

(defun cfgroup-run ()
  (with-local-stobj cfgroup
    (mv-let (out cfgroup)
      (let* ((cfgroup (cfgroup-create 1 *st0* "alt.test" "fn-policy-default-1" cfgroup))
             (cfgroup (cfgroup-create 1 *st0* "comp.misc" "fn-policy-default-1" cfgroup))
             (cfgroup (cfgroup-retire 2 "alt.test" cfgroup))
             (cfgroup (cfgroup-create 3 *st0* "alt.test" "fn-policy-read-only-1" cfgroup)))
        (mv (list (cfgroup-find "alt.test" cfgroup) (cfgroup-find "comp.misc" cfgroup)
                  (cfgroup-get-retired-gen "comp.misc" cfgroup) (cfgroup-has "rec.x" cfgroup))
            cfgroup))
      out)))

(defun cfgroup-model ()
  (let* ((es (fn-cfg-groups-create nil 1 *st0* "alt.test" "fn-policy-default-1"))
         (es (fn-cfg-groups-create es 1 *st0* "comp.misc" "fn-policy-default-1"))
         (es (fn-cfg-groups-retire es 2 "alt.test"))
         (es (fn-cfg-groups-create es 3 *st0* "alt.test" "fn-policy-read-only-1")))
    (list (fn-cfg-group-find es "alt.test") (fn-cfg-group-find es "comp.misc")
          (fn-cfg-group-retired-gen (fn-cfg-group-find es "comp.misc"))
          (if (fn-cfg-group-find es "rec.x") t nil))))

(assert-event (and (equal (cfgroup-run) (cfgroup-model))
                   (equal (car (cfgroup-run))
                          (list "alt.test" 3 *st0* nil "fn-policy-read-only-1" 0))))
