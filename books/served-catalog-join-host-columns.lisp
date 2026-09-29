; served-catalog-join-host-columns.lisp -- the catalog's column facts carried
; across the host's protocol (lane join-f2-2, 2026-09-29; PRF-302).
;
; The served read's premise fn-scol-okp (books/served-columns.lisp: every
; catalog row's decided column is the column of its bytes in the arena) is a
; fact about the arena, the catalog and nothing else.  fn-sjh-colsp carries
; it with the two facts that keep it through the host's changes: the catalog
; rows' handles are inside the arena (so a seal, an append, keeps every row's
; bytes), and the pending row's column is its bytes' (so the finish's commit
; keeps it).  It is established at every open (the intern decides each row's
; column from the bytes it seals) and kept by the only entries that change
; the arena, the catalog or the pending row: the POST and signed-composite
; prepares (the seal, the catalog prepare), the finishes (fn-sca-finish), the
; known abort and refused reservation (the pending row cleared), and the log
; route's commit reseat (the arena is the same arena).  Every other host
; entry leaves all three alone.  fn-sjh-okp-at-owner-chunk-span-carried is the
; read keystone with the premise discharged by it.

(in-package "ACL2")

(include-book "served-catalog-join-host-entries")
(include-book "served-catalog-join-host-identity")
(include-book "payload-commit-extent") ; fn-arx-commit-reseats: the commit's reseat
(include-book "payload-lz-replay")     ; fn-lzr-commit-reseats

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The carried predicate.


(defun-nx fn-sjh-colsp (pending fn-arena fn-cat)
  (and (fn-scol-okp fn-arena fn-cat)
       (fn-scol-handles-below fn-cat (len fn-arena))
       (implies pending
                (and (fn-scol-row-okp (fn-pc-held pending) fn-arena)
                     (fn-scol-handles-below (list (fn-pc-held pending)) (len fn-arena))))))

(defthm fn-sjh-colsp-gives-scol-okp
  (implies (fn-sjh-colsp pending fn-arena fn-cat)
           (fn-scol-okp fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-colsp))))

(defthm fn-sjh-colsp-without-pending
  (implies (fn-sjh-colsp pending fn-arena fn-cat)
           (fn-sjh-colsp nil fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-colsp))))

;; handles-below of a commit, a withdraw, the finish.
(defthm fn-sjh-col-handles-below-of-append
  (equal (fn-scol-handles-below (append a b) n)
         (and (fn-scol-handles-below a n) (fn-scol-handles-below b n)))
  :hints (("Goal" :in-theory (enable fn-scol-handles-below))))

(defthm fn-sjh-col-handles-below-of-update-nth
  (implies (and (fn-scol-handles-below rows n)
                (fn-scol-handles-below (list row) n)
                (natp seq) (< seq (len rows)))
           (fn-scol-handles-below (update-nth seq row rows) n))
  :hints (("Goal" :in-theory (enable fn-scol-handles-below update-nth))))

(defthm fn-sjh-col-handles-below-nth
  (implies (and (fn-scol-handles-below rows n) (natp seq) (< seq (len rows)))
           (fn-scol-handles-below (list (nth seq rows)) n))
  :hints (("Goal" :in-theory (enable fn-scol-handles-below nth))))


; -----------------------------------------------------------------------------
; The finish.


(defthm fn-sjh-col-payload-of-with-withdrawn
  (equal (fn-record-payload (fn-held-with-withdrawn h w)) (fn-record-payload h))
  :hints (("Goal" :in-theory (enable fn-held-with-withdrawn))))

(defthm fn-sjh-col-payload-of-assign
  (equal (fn-record-payload (fn-cat-assign h c)) (fn-record-payload h))
  :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers))))

(defthm fn-sjh-col-handles-below-singleton
  (equal (fn-scol-handles-below (list r) n)
         (and (natp (fn-record-payload r)) (< (fn-record-payload r) (nfix n))))
  :hints (("Goal" :in-theory (enable fn-scol-handles-below))))

(defthm fn-sjh-col-handles-below-of-commit
  (implies (and (fn-scol-handles-below fn-cat n)
                (fn-scol-handles-below (list h) n))
           (fn-scol-handles-below (fn-cat-commit h fn-cat) n))
  :hints (("Goal" :in-theory (e/d (fn-cat-commit-is-append) (fn-cat-assign fn-scol-handles-below)))))


(defthm fn-sjh-col-handles-below-of-mark-withdrawn
  (implies (and (fn-scol-handles-below c n) (natp target))
           (fn-scol-handles-below (fn-cat-mark-withdrawn target v by c) n))
  :hints (("Goal" :in-theory (e/d (fn-cat-mark-withdrawn) (fn-held-with-withdrawn fn-scol-handles-below))
           :use ((:instance fn-sjh-col-handles-below-nth (rows c) (seq target))))))
(defthm fn-sjh-col-handles-below-of-sca-withdraw-targets
  (implies (and (fn-scol-handles-below fn-cat n) (natp by))
           (fn-scol-handles-below (fn-sca-withdraw-targets targets view-index by fn-cat) n))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets view-index by fn-cat)
           :in-theory (e/d (fn-sca-withdraw-targets)
                           (fn-cat-view-last-visible fn-cat-withdraw fn-midx-lookup fn-scol-handles-below)))))


(defthm fn-sjh-col-handles-below-of-sca-finish
  (implies (and (fn-scol-handles-below fn-cat n)
                (fn-scol-handles-below (list (fn-pc-held pending)) n)
                (or (null pending) (natp (fn-pc-expected pending))))
           (fn-scol-handles-below (mv-nth 2 (fn-sca-finish token pending view-index targets fn-cat)) n))
  :hints (("Goal" :in-theory (e/d (fn-sca-finish fn-sca-complete fn-cat-complete fn-cat-complete-hidden)
                                  (fn-sca-withdraw-targets fn-cat-commit fn-held-with-withdrawn fn-midx-lookup
                                   fn-delta-of-row fn-cat-at fn-scol-handles-below)))))

; KEYSTONE (the columns across the host's finishes: fn-owner-finish-submission
; and fn-owner-finish-identity run fn-sca-finish with the pending row).
(defthm fn-sjh-colsp-at-finish
  (implies (and (fn-sjh-colsp pending fn-arena fn-cat)
                (fn-pc-p pending))
           (fn-sjh-colsp nil fn-arena (mv-nth 2 (fn-sca-finish token pending view-index targets fn-cat))))
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-colsp fn-sjh-pc-p-non-nil)
                                             (theory 'minimal-theory))
           :use ((:instance fn-scol-okp-of-sca-finish)
                 (:instance fn-sjh-col-handles-below-of-sca-finish (n (len fn-arena)))
                 (:instance fn-pc-p-fields (pc pending))))))


; -----------------------------------------------------------------------------
; The prepares: the seal and the catalog prepare.


(defthm fn-sjh-col-record-payload-octets
  (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
  :hints (("Goal" :in-theory (enable fn-record-p fn-record-shapep fn-record-payloadp fn-record-internals))))

(defthm fn-sjh-col-nth-len-of-snoc
  (equal (nth (len a) (append a (list x))) x)
  :hints (("Goal" :induct (len a) :in-theory (enable nth))))

(defthm fn-sjh-col-len-of-snoc
  (equal (len (append a (list x))) (+ 1 (len a))))

(defthm fn-sjh-col-bytes-at-sealed-handle
  (implies (fn-arena-p fn-arena)
           (equal (fn-nntp-payload-bytes (len fn-arena) (fn-arena-seal-list xs fn-arena)) xs))
  :hints (("Goal" :in-theory (union-theories '(fn-nntp-payload-bytes fn-arena-seal-list-is-append
                                               fn-arena-payload-is-nth fn-arena-count-is-len
                                               fn-sjh-col-nth-len-of-snoc fn-sjh-col-len-of-snoc
                                               natp (:type-prescription len))
                                             (theory 'minimal-theory)))))

(defthm fn-sjh-col-sealed-row-okp
  (implies (and (fn-arena-p fn-arena) (fn-record-p w) (natp generation))
           (let ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
                 (a2 (fn-arena-seal-list (fn-record-payload w) fn-arena)))
             (and (fn-scol-row-okp row a2)
                  (fn-scol-handles-below (list row) (len a2)))))
  :hints (("Goal" :in-theory (e/d (fn-arena-count-is-len fn-arena-seal-list-is-append)
                                  (fn-intern-row-at fn-scol-row-okp fn-record-p))
           :use ((:instance fn-scol-row-okp-of-intern-row-at
                            (h (fn-arena-count fn-arena))
                            (fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))
                 (:instance fn-sjh-col-bytes-at-sealed-handle (xs (fn-record-payload w)))
                 (:instance fn-sjh-intern-row-fields (h (fn-arena-count fn-arena)))))))

(defthm fn-sjh-col-handles-below-monotone
  (implies (and (fn-scol-handles-below rows n) (<= (nfix n) (nfix m)))
           (fn-scol-handles-below rows m))
  :hints (("Goal" :in-theory (enable fn-scol-handles-below))))

(defthm fn-sjh-col-seal-keeps-colsp-nil
  (implies (and (fn-sjh-colsp pending fn-arena fn-cat)
                (fn-arena-p fn-arena)
                (fn-cbor-octet-listp xs))
           (fn-sjh-colsp nil (fn-arena-seal-list xs fn-arena) fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-sjh-colsp fn-arena-seal-list-is-append) (fn-scol-okp fn-scol-handles-below))
           :use ((:instance fn-scol-okp-of-seal-list)
                 (:instance fn-sjh-col-handles-below-monotone
                            (rows fn-cat) (n (len fn-arena)) (m (+ 1 (len fn-arena))))))))


(defthm fn-sjh-colsp-of-sealed-prepare
  (let* ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
         (arena2 (fn-arena-seal-list (fn-record-payload w) fn-arena))
         (pc (fn-cat-prepare-sealed w row plan reservation nil arena2 fn-cat)))
    (implies (and (fn-sjh-colsp pending fn-arena fn-cat)
                  (fn-arena-p fn-arena)
                  (fn-record-p w) (natp generation))
             (fn-sjh-colsp pc arena2 fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sjh-seal-buffer-is-seal-list fn-arena-count-is-len)
                           (fn-intern-row-at fn-cat-prepare-sealed fn-scol-okp fn-scol-row-okp
                            fn-scol-handles-below fn-record-p fn-arena-seal-list-is-append))
           :use ((:instance fn-sjh-col-seal-keeps-colsp-nil (xs (fn-record-payload w)))
                 (:instance fn-sjh-col-record-payload-octets)
                 (:instance fn-sjh-col-sealed-row-okp)
                 (:instance fn-sjh-intern-row-held-p (h (fn-arena-count fn-arena)))
                 (:instance fn-sjh-intern-row-fields (h (fn-arena-count fn-arena)))
                 (:instance fn-arena-seal-count (xs (fn-record-payload w)))
                 (:instance fn-sjh-prepare-sealed-facts
                            (held (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
                            (fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))
                 (:instance fn-sjh-colsp (pending nil) (fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))
                 (:instance fn-sjh-colsp
                            (pending (fn-cat-prepare-sealed w (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))
                                                            plan reservation nil
                                                            (fn-arena-seal-list (fn-record-payload w) fn-arena) fn-cat))
                            (fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))))))

; KEYSTONE (the columns across the host's article POST: fn-owner-prepare-buffer,
; the seal of the record's payload, fn-owner-cat-prepare-sealed).
(defthm fn-sjh-colsp-at-owner-prepare-buffer
  (let* ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
         (arena2 (fn-arena-seal-buffer fn-octets fn-arena))
         (pc (fn-cat-prepare-sealed w row plan reservation nil arena2 fn-cat)))
    (implies (and (fn-sjh-colsp pending fn-arena fn-cat)
                  (fn-arena-p fn-arena)
                  (fn-record-p w) (natp generation)
                  (equal (fn-octets-list fn-octets) (fn-record-payload w)))
             (fn-sjh-colsp pc arena2 fn-cat)))
  :hints (("Goal" :in-theory '(fn-sjh-seal-buffer-is-seal-list)
           :use ((:instance fn-sjh-colsp-of-sealed-prepare)))))

; KEYSTONE (the columns across the signed composite's prepare:
; fn-owner-prepare-identity, the seal of the composite's article payload, the
; catalog's prepare of its held row).
(defthm fn-sjh-colsp-at-owner-prepare-identity-sealed
  (let* ((h (fn-arena-count fn-arena))
         (a (fn-replay-composite-record w))
         (held (fn-intern-row-at a keyring generation h))
         (arena2 (fn-arena-seal-list (fn-record-payload a) fn-arena))
         (pc (fn-cat-prepare-sealed a held plan reservation nil arena2 fn-cat)))
    (implies (and (fn-sjh-colsp pending fn-arena fn-cat)
                  (fn-arena-p fn-arena)
                  (fn-record-p a) (natp generation))
             (fn-sjh-colsp pc arena2 fn-cat)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-colsp-of-sealed-prepare (w (fn-replay-composite-record w)))))))


; -----------------------------------------------------------------------------
; The commit's reseat and the read.


; KEYSTONE (the columns across the log route's commit reseat, host/native/io.lisp
; fnn-log-reseat-fenced: fn-arx-commit-reseats and fn-lzr-commit-reseats over
; members the commit made faithful, then fn-arena-release): the arena is the
; same arena (fn-arx-commit-reseats-keep-the-arena,
; fn-lzr-commit-reseats-keep-the-arena, fn-arena-release-unfolds).
(defthm fn-sjh-colsp-at-commit-reseat
  (implies (and (fn-sjh-colsp pending fn-arena fn-cat)
                (fn-arena-p fn-arena)
                (fn-arx-commit-faithful-p members))
           (and (fn-sjh-colsp pending (fn-arx-commit-reseats members fn-arena) fn-cat)
                (fn-sjh-colsp pending (fn-lzr-commit-reseats members dicts fn-arena) fn-cat)
                (fn-sjh-colsp pending (fn-arena-release h fn-arena) fn-cat)))
  :hints (("Goal" :in-theory (union-theories '(fn-arx-commit-reseats-keep-the-arena
                                               fn-lzr-commit-reseats-keep-the-arena
                                               fn-arena-release-unfolds)
                                             (theory 'minimal-theory)))))

; The read keystone with the column premise carried (fn-sjh-colsp gives
; fn-scol-okp): host/owner-host.lisp fn-owner-chunk-span-at.
(defthm fn-sjh-okp-at-owner-chunk-span-carried
  (implies (and (fn-gacc-okp cache) (fn-sjh-colsp pending fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-okp (fn-ocfg-owner
                        (fn-own-tls-result-owner
                         (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                                fn-octets fn-arena fn-cat))))
                       pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-colsp-gives-scol-okp)
           :use ((:instance fn-sjh-okp-at-owner-chunk-span)))))
