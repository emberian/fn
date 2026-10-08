; fn: staging a checkpoint's delta rows into the page store's image (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM-20261006.md section 3.3, 2b).
;
; The host holds interned rows and the payload arena.  `fn-pck-x-stage-rows'
; writes the words of each row, from the octet buffer
; (books/paged-checkpoint-exec.lisp), into `pgs-mem' at the tape position the
; previous rows ended at, one `pgs-x-write' per word (the write marks its page
; dirty).  Nothing else is written: the tail page already holds the prefix's
; words with zeros after, so the pages marked dirty are exactly the pages of
; (tail ++ delta).
;
;   fn-pck-x-stage-is-the-dirty   the keystone.  With P the word count of the
;       prefix's tape and TAIL its last partial page, a staged delta leaves,
;       on the pages `pgs-dirty-lpages' of the model's tape dirty set, the
;       words `pgs-x-abs-dirty' reads (the page store's DIRTY) equal to that
;       dirty set (the tape part of `fn-pck-dirty': pages 8 and up of
;       `fn-pck-row-extend-dirty').  The verdict is :ok.
;   pcks-stage-rows               the words: the window of the image after the
;       stage is the window before with the delta's words (mod 2^64) laid at
;       the tape position, `pcks-put' (one `pgs-x-write' per word, proved by
;       `pcks-put-row' and its frame lemmas).
;
; Scope, named.  Premises of the keystone, each a statement the host must hold:
;   (1) `pcks-res': every tape position of the delta is writable (its page is
;       in the image and resident, `pgs-vi' = 2).  A page that is not resident
;       answers (:need-page LP) under lazy open: that path is owed
;       (PCK-STAGE-NEED-PAGE) and is outside this statement;
;   (2) the dirty pages hold the tape's words before the stage: the tail page
;       is the prefix's tail followed by zeros, later pages are zero (the
;       `pgs-x-abs-dirty' equation on the zero delta);
;   (3) `adt-tp-seq-lens-ok': every record's program has fewer than 2^64 octets
;       (the generator's premise: every word fits the image's 64 bits);
;   (4) the delta's records and their metadata trees are encodable
;       (`fn-pck-sccb-listp'), and the payload file after the delta is under
;       2^64 octets (`fn-pck-plen-okp');
;   (5) BASE, where the delta's first payload frame starts, is the prefix's
;       payload-file length (`fn-pck-plen'); the rows' offset words are the
;       frames' starts plus 37, their length words the payloads' lengths, and
;       their last four words the frames' trailer words
;       (`fn-pck-x-tl', from the constrained seam `fn-cpl-trailer-words': the
;       host takes them from s-cpl's frame writer, whose bridge to the seam
;       is that lane's theorem).
; The root region (pages 0..7) is not staged here: it is the live fold state's.

(in-package "ACL2")
(include-book "paged-checkpoint-exec")
(include-book "pagestore-exec")
(include-book "pagestore-refine")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-pck-x-rw (j tl fn-octets)
  ; Word J of the row whose metadata program is in the buffer, TL the row's
  ; six trailing words (offset, length, trailer words d0..d3).
  (declare (xargs :stobjs fn-octets
                  :guard (and (true-listp tl) (equal (len tl) 6)
                              (natp j) (< j (fn-pck-x-row-words (fn-octets-len fn-octets))))
                  :verify-guards nil))
  (fn-pck-x-row-word j (nth 0 tl) (nth 1 tl) (nth 2 tl) (nth 3 tl) (nth 4 tl) (nth 5 tl) fn-octets))

(defun fn-pck-x-payload-len (row fn-arena)
  ; The payload octets of the event ROW denotes (the host reads this off the
  ; arena extent; here the arena's wire event).
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (len (fn-pck-payload (fn-row-wire-of row fn-arena))))

(defun fn-pck-x-tl (row fn-arena base)
  ; The row's trailing words for the frame at BASE: the ref (37 octets into the
  ; frame, the payload length) and the frame trailer's four words.  The trailer
  ; is the constrained seam fn-cpl-trailer-words; s-cpl's frame writer is what
  ; the host takes it from.
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((tw (fn-cpl-trailer-words (fn-pck-payload (fn-row-wire-of row fn-arena)))))
    (list (+ *fn-cpl-header-octets* base) (fn-pck-x-payload-len row fn-arena)
          (car tw) (cadr tw) (caddr tw) (cadddr tw))))

(defun fn-pck-x-put-row (j nw p tl fn-octets pgs-mem)
  ; Words J..NW-1 of the buffered row to tape position P + J.
  (declare (xargs :stobjs (fn-octets pgs-mem) :verify-guards nil
                  :measure (nfix (- (nfix nw) (nfix j)))))
  (if (not (and (natp j) (natp nw) (< j nw)))
      (mv :ok pgs-mem)
    (let* ((q (+ p j))
           (lp (+ *fn-pck-root-pages* (floor q *pgs-page-words*)))
           (off (mod q *pgs-page-words*)))
      (mv-let (v pgs-mem)
        (pgs-x-write lp off (fn-pck-x-rw j tl fn-octets) pgs-mem)
        (if (eq v :ok)
            (fn-pck-x-put-row (1+ j) nw p tl fn-octets pgs-mem)
          (mv v pgs-mem))))))

(defun fn-pck-x-st-next (row fn-arena st)
  ; The fold state after the event ROW denotes (the model's pck-ssr1; the host
  ; carries its fold state in the same step).
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (pck-ssr1 st (fn-row-wire-of row fn-arena)))

(defun fn-pck-x-stage-rows (rows p base st fn-arena fn-octets pgs-mem)
  ; (mv VERDICT fn-octets pgs-mem): the rows' words from tape position P on,
  ; the first row's payload frame at BASE in the payload file, frames end to end.
  (declare (xargs :stobjs (fn-arena fn-octets pgs-mem) :verify-guards nil))
  (if (atom rows)
      (mv :ok fn-octets pgs-mem)
    (let* ((fn-octets (fn-pck-x-encode-row (car rows) fn-arena st fn-octets))
           (nw (fn-pck-x-row-words (fn-octets-len fn-octets)))
           (tl (fn-pck-x-tl (car rows) fn-arena base)))
      (mv-let (v pgs-mem)
        (fn-pck-x-put-row 0 nw p tl fn-octets pgs-mem)
        (if (eq v :ok)
            (fn-pck-x-stage-rows (cdr rows) (+ p nw)
                                 (+ base (fn-cpl-frame-octets (fn-pck-x-payload-len (car rows) fn-arena)))
                                 (fn-pck-x-st-next (car rows) fn-arena st)
                                 fn-arena fn-octets pgs-mem)
          (mv v fn-octets pgs-mem))))))

; -----------------------------------------------------------------------------
; Proof.

(defthm pcks-len-append (equal (len (append x y)) (+ (len x) (len y))))

(defun pcks-ind (a k) (declare (xargs :measure (nfix k))) (if (zp k) a (pcks-ind (1+ a) (1- k))))

(defthm pgs-x-write-facts
  (implies (and (natp lp) (natp off) (natp a) (natp j)
                (equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
           (let ((m1 (mv-nth 1 (pgs-x-write lp off v pgs-mem))))
             (and (< off 2048) (< lp (pgs-d-length pgs-mem)) (< lp (pgs-v-length pgs-mem))
                  (<= (* 2048 (+ 1 lp)) (pgs-w-length pgs-mem))
                  (equal (pgs-vi lp pgs-mem) 2)
                  (equal (pgs-wi a m1) (if (equal a (+ (* 2048 lp) off)) (pgs-dlo v) (pgs-wi a pgs-mem)))
                  (equal (pgs-w-length m1) (pgs-w-length pgs-mem))
                  (equal (pgs-d-length m1) (pgs-d-length pgs-mem))
                  (equal (pgs-v-length m1) (pgs-v-length pgs-mem))
                  (equal (pgs-vi j m1) (pgs-vi j pgs-mem)))))
  :hints (("Goal" :in-theory (enable pgs-x-write pgs-wi pgs-vi pgs-di update-pgs-wi update-pgs-di pgs-w-length pgs-d-length pgs-v-length))))

(defthm pgs-x-write-ok
  (implies (and (natp lp) (natp off) (< off 2048) (< lp (pgs-d-length pgs-mem)) (< lp (pgs-v-length pgs-mem))
                (<= (* 2048 (+ 1 lp)) (pgs-w-length pgs-mem))
                (equal (pgs-vi lp pgs-mem) 2))
           (equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
  :hints (("Goal" :in-theory (enable pgs-x-write))))

(defthm pgs-x-word-0
  (equal (pgs-x-word 0 i pgs-mem) (pgs-wi i pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-word$inline))))

(defthm pcks-wi-of-write
  (implies (and (natp lp) (natp off) (natp a)
                (equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
           (equal (pgs-wi a (mv-nth 1 (pgs-x-write lp off v pgs-mem)))
                  (if (equal a (+ (* 2048 lp) off)) (pgs-dlo v) (pgs-wi a pgs-mem))))
  :hints (("Goal" :use ((:instance pgs-x-write-facts (j 0))))))

(defthm pcks-words-step
  (implies (and (natp k) (< 0 k))
           (equal (pgs-x-words 0 a k pgs-mem)
                  (cons (pgs-wi a pgs-mem) (pgs-x-words 0 (1+ a) (1- k) pgs-mem))))
  :hints (("Goal" :expand ((pgs-x-words 0 a k pgs-mem)) :in-theory (enable pgs-x-word-0))))

(defthm pcks-update-nth-cons
  (implies (natp n)
           (equal (update-nth n v (cons x r))
                  (if (zp n) (cons v r) (cons x (update-nth (1- n) v r))))))

(defthm pcks-words-zero (equal (pgs-x-words 0 a 0 pgs-mem) nil)
  :hints (("Goal" :expand ((pgs-x-words 0 a 0 pgs-mem)))))

(defthm pgs-x-words-of-write
  (implies (and (natp lp) (natp off) (natp a) (natp k)
                (equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
           (equal (pgs-x-words 0 a k (mv-nth 1 (pgs-x-write lp off v pgs-mem)))
                  (if (and (<= a (+ (* 2048 lp) off)) (< (+ (* 2048 lp) off) (+ a k)))
                      (update-nth (- (+ (* 2048 lp) off) a) (pgs-dlo v) (pgs-x-words 0 a k pgs-mem))
                    (pgs-x-words 0 a k pgs-mem))))
  :hints (("Goal" :induct (pcks-ind a k)
           :in-theory (disable pgs-x-write pgs-dlo pgs-wi pgs-x-words))))

(in-theory (disable pcks-words-step pcks-words-zero pcks-update-nth-cons))

(defun pcks-writable (q pgs-mem)
  (declare (xargs :stobjs pgs-mem))
  (let ((lp (+ 8 (floor (nfix q) 2048))))
    (and (< lp (pgs-d-length pgs-mem)) (< lp (pgs-v-length pgs-mem))
         (<= (* 2048 (+ 1 lp)) (pgs-w-length pgs-mem))
         (equal (pgs-vi lp pgs-mem) 2))))

(defun pcks-res (lo hi pgs-mem)
  ; Every tape position in [LO, HI) is writable.
  (declare (xargs :stobjs pgs-mem :measure (nfix (- (nfix hi) (nfix lo)))))
  (if (and (natp lo) (natp hi) (< lo hi))
      (and (pcks-writable lo pgs-mem) (pcks-res (1+ lo) hi pgs-mem))
    t))

(defun pcks-put (i ws l)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ws) l (pcks-put (1+ i) (cdr ws) (update-nth i (car ws) l))))

(defun fn-pck-x-row-dwords (j nw tl fn-octets)
  ; The words J..NW-1 of the buffered row as the page store keeps them (mod 2^64).
  (declare (xargs :stobjs fn-octets :verify-guards nil :measure (nfix (- (nfix nw) (nfix j)))))
  (if (and (natp j) (natp nw) (< j nw))
      (cons (pgs-dlo (fn-pck-x-rw j tl fn-octets)) (fn-pck-x-row-dwords (1+ j) nw tl fn-octets))
    nil))

(defthm pcks-writable-of-write
  (implies (and (natp lp) (natp off) (equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
           (equal (pcks-writable q (mv-nth 1 (pgs-x-write lp off v pgs-mem)))
                  (pcks-writable q pgs-mem)))
  :hints (("Goal" :use ((:instance pgs-x-write-facts (a 0) (j (+ 8 (floor (nfix q) 2048)))))
           :in-theory (e/d (pcks-writable) (pgs-x-write)))))

(defthm pcks-res-of-write
  (implies (and (natp lp) (natp off) (equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
           (equal (pcks-res lo hi (mv-nth 1 (pgs-x-write lp off v pgs-mem)))
                  (pcks-res lo hi pgs-mem)))
  :hints (("Goal" :induct (pcks-res lo hi pgs-mem)
           :in-theory (disable pgs-x-write pcks-writable))))

(defthm pcks-addr
  (implies (natp q)
           (equal (+ (* 2048 (+ 8 (floor q 2048))) (mod q 2048)) (+ 16384 q)))
  :hints (("Goal" :in-theory (enable mod floor))))

(defthm pcks-write-at-q-ok
  (implies (and (natp q) (pcks-writable q pgs-mem))
           (equal (mv-nth 0 (pgs-x-write (+ 8 (floor q 2048)) (mod q 2048) v pgs-mem)) :ok))
  :hints (("Goal" :use ((:instance pgs-x-write-ok (lp (+ 8 (floor q 2048))) (off (mod q 2048))))
           :in-theory (e/d (pcks-writable) (pgs-x-write-ok pgs-x-write)))))

(defthm pcks-words-of-write-at-q
  (implies (and (natp q) (natp a) (natp k) (pcks-writable q pgs-mem))
           (equal (pgs-x-words 0 a k (mv-nth 1 (pgs-x-write (+ 8 (floor q 2048)) (mod q 2048) v pgs-mem)))
                  (if (and (<= a (+ 16384 q)) (< (+ 16384 q) (+ a k)))
                      (update-nth (- (+ 16384 q) a) (pgs-dlo v) (pgs-x-words 0 a k pgs-mem))
                    (pgs-x-words 0 a k pgs-mem))))
  :hints (("Goal" :use ((:instance pgs-x-words-of-write (lp (+ 8 (floor q 2048))) (off (mod q 2048)))
                        pcks-write-at-q-ok pcks-addr)
           :in-theory (disable pgs-x-words-of-write pcks-write-at-q-ok pcks-addr pgs-x-write pgs-dlo pcks-writable pgs-x-words))))

(defthm pcks-res-of-write-at-q
  (implies (and (natp q) (pcks-writable q pgs-mem))
           (equal (pcks-res lo hi (mv-nth 1 (pgs-x-write (+ 8 (floor q 2048)) (mod q 2048) v pgs-mem)))
                  (pcks-res lo hi pgs-mem)))
  :hints (("Goal" :use ((:instance pcks-res-of-write (lp (+ 8 (floor q 2048))) (off (mod q 2048)))
                        pcks-write-at-q-ok)
           :in-theory (disable pcks-res-of-write pcks-write-at-q-ok pgs-x-write pcks-writable))))

(defun pcks-wr (q v pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (pgs-x-write (+ 8 (floor q 2048)) (mod q 2048) v pgs-mem))

(defthm pcks-wr-ok
  (implies (and (natp q) (pcks-writable q pgs-mem))
           (equal (mv-nth 0 (pcks-wr q v pgs-mem)) :ok))
  :hints (("Goal" :in-theory (disable pcks-writable) :use pcks-write-at-q-ok :expand ((pcks-wr q v pgs-mem)))))

(defthm pcks-wr-words
  (implies (and (natp q) (natp a) (natp k) (pcks-writable q pgs-mem))
           (equal (pgs-x-words 0 a k (mv-nth 1 (pcks-wr q v pgs-mem)))
                  (if (and (<= a (+ 16384 q)) (< (+ 16384 q) (+ a k)))
                      (update-nth (- (+ 16384 q) a) (pgs-dlo v) (pgs-x-words 0 a k pgs-mem))
                    (pgs-x-words 0 a k pgs-mem))))
  :hints (("Goal" :in-theory (disable pcks-writable pgs-dlo pgs-x-words) :use pcks-words-of-write-at-q :expand ((pcks-wr q v pgs-mem)))))

(defthm pcks-wr-res
  (implies (and (natp q) (pcks-writable q pgs-mem))
           (equal (pcks-res lo hi (mv-nth 1 (pcks-wr q v pgs-mem)))
                  (pcks-res lo hi pgs-mem)))
  :hints (("Goal" :in-theory (disable pcks-writable pcks-res) :use pcks-res-of-write-at-q :expand ((pcks-wr q v pgs-mem)))))

(defthm pcks-put-row-open
  (implies (and (natp j) (natp nw) (< j nw))
           (equal (fn-pck-x-put-row j nw p tl fn-octets pgs-mem)
                  (mv-let (v m) (pcks-wr (+ p j) (fn-pck-x-rw j tl fn-octets) pgs-mem)
                    (if (eq v :ok) (fn-pck-x-put-row (1+ j) nw p tl fn-octets m) (mv v m)))))
  :hints (("Goal" :expand ((fn-pck-x-put-row j nw p tl fn-octets pgs-mem)) :in-theory (enable pcks-wr))))

(defthm pcks-put-row-done
  (implies (and (natp j) (natp nw) (<= nw j))
           (equal (fn-pck-x-put-row j nw p tl fn-octets pgs-mem) (mv :ok pgs-mem)))
  :hints (("Goal" :expand ((fn-pck-x-put-row j nw p tl fn-octets pgs-mem)))))

(defthm pcks-res-step
  (implies (and (natp lo) (natp hi) (< lo hi))
           (equal (pcks-res lo hi pgs-mem)
                  (and (pcks-writable lo pgs-mem) (pcks-res (1+ lo) hi pgs-mem))))
  :hints (("Goal" :expand ((pcks-res lo hi pgs-mem)))))

(defthm pcks-res-done
  (implies (and (natp lo) (natp hi) (<= hi lo)) (pcks-res lo hi pgs-mem))
  :hints (("Goal" :expand ((pcks-res lo hi pgs-mem)))))

(defun pcks-put-ind (j nw p tl fn-octets pgs-mem)
  (declare (xargs :stobjs (fn-octets pgs-mem) :verify-guards nil
                  :measure (nfix (- (nfix nw) (nfix j)))))
  (if (and (natp j) (natp nw) (< j nw))
      (mv-let (v pgs-mem) (pcks-wr (+ p j) (fn-pck-x-rw j tl fn-octets) pgs-mem)
        (if (eq v :ok) (pcks-put-ind (1+ j) nw p tl fn-octets pgs-mem) (mv v pgs-mem)))
    (mv :ok pgs-mem)))

(defthm pcks-wr-ok-car
  (implies (and (natp q) (pcks-writable q pgs-mem))
           (equal (car (pcks-wr q v pgs-mem)) :ok))
  :hints (("Goal" :use pcks-wr-ok :in-theory (disable pcks-wr-ok pcks-wr pcks-writable))))

(defthm pcks-wr-consp (consp (pcks-wr q v pgs-mem))
  :hints (("Goal" :in-theory (enable pcks-wr pgs-x-write))))

(defthm pcks-put-row
  (implies (and (natp j) (natp nw) (natp p) (natp a) (natp k)
                (pcks-res (+ p j) (+ p nw) pgs-mem)
                (<= a (+ 16384 p j)) (or (<= nw j) (<= (+ 16384 p nw) (+ a k))))
           (and (equal (mv-nth 0 (fn-pck-x-put-row j nw p tl fn-octets pgs-mem)) :ok)
                (equal (pgs-x-words 0 a k (mv-nth 1 (fn-pck-x-put-row j nw p tl fn-octets pgs-mem)))
                       (pcks-put (- (+ 16384 p j) a) (fn-pck-x-row-dwords j nw tl fn-octets)
                                 (pgs-x-words 0 a k pgs-mem)))))
  :hints (("Goal" :induct (pcks-put-ind j nw p tl fn-octets pgs-mem)
           :in-theory (union-theories '(pcks-res-step pcks-res-done (:induction pcks-put-ind)
                                        pcks-put-row-open pcks-put-row-done)
                                      (disable fn-pck-x-put-row pgs-x-write pcks-writable pgs-dlo pgs-x-words
                                               fn-pck-x-row-word fn-pck-x-row-dwords pcks-res pcks-wr pcks-words-step pcks-update-nth-cons)))
          (and stable-under-simplificationp
               '(:expand ((fn-pck-x-row-dwords j nw tl fn-octets))))))

(defun pcks-dlo-list (ws)
  (declare (xargs :guard t))
  (if (atom ws) nil (cons (pgs-dlo (car ws)) (pcks-dlo-list (cdr ws)))))

(defthm pcks-put-append
  (implies (natp i)
           (equal (pcks-put i (append ws1 ws2) l)
                  (pcks-put (+ i (len ws1)) ws2 (pcks-put i ws1 l))))
  :hints (("Goal" :induct (pcks-put i ws1 l))))

(defthm pcks-put-row-res
  (implies (and (natp j) (natp nw) (natp p) (pcks-res (+ p j) (+ p nw) pgs-mem))
           (equal (pcks-res lo hi (mv-nth 1 (fn-pck-x-put-row j nw p tl fn-octets pgs-mem)))
                  (pcks-res lo hi pgs-mem)))
  :hints (("Goal" :induct (pcks-put-ind j nw p tl fn-octets pgs-mem)
           :in-theory (union-theories '(pcks-res-step pcks-res-done (:induction pcks-put-ind)
                                        pcks-put-row-open pcks-put-row-done)
                                      (disable fn-pck-x-put-row pgs-x-write pcks-writable pgs-dlo pgs-x-words
                                               fn-pck-x-row-word fn-pck-x-row-dwords pcks-res pcks-wr
                                               pcks-words-step pcks-update-nth-cons)))))

(defun pcks-agree (j nw tl fn-octets rw)
  (declare (xargs :stobjs fn-octets :verify-guards nil :measure (nfix (- (nfix nw) (nfix j)))))
  (if (and (natp j) (natp nw) (< j nw))
      (and (equal (fn-pck-x-rw j tl fn-octets) (nth j rw)) (pcks-agree (1+ j) nw tl fn-octets rw))
    t))

(defthm pcks-dwords-of-agree
  (implies (and (natp j) (equal nw (len rw)) (pcks-agree j nw tl fn-octets rw))
           (equal (fn-pck-x-row-dwords j nw tl fn-octets) (pcks-dlo-list (nthcdr j rw))))
  :hints (("Goal" :induct (pcks-agree j nw tl fn-octets rw)
           :in-theory (disable fn-pck-x-row-word pgs-dlo))
          ("Subgoal *1/2" :expand ((fn-pck-x-row-dwords j nw tl fn-octets) (nthcdr j rw)))
          ("Subgoal *1/1" :expand ((fn-pck-x-row-dwords j nw tl fn-octets)))))

(defthm pcks-rw-of-encode-row
  ; Word J the stager reads is word J of the model's row.
  (implies (and (fn-sccb-treep (fn-pck-meta (fn-row-wire-of row fn-arena) st)) (natp j)
                (< j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st))))))
           (equal (fn-pck-x-rw j (fn-pck-x-tl row fn-arena base) (fn-pck-x-encode-row row fn-arena st fn-octets))
                  (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-row-wire-of row fn-arena) base st)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-x-rw fn-pck-x-tl fn-pck-x-payload-len)
                           (fn-pck-x-encode-row fn-pck-x-row-word fn-pck-x-row-words adt-tp-rw fn-pck-enc-row fn-scc-program
                            fn-row-wire-of fn-pck-meta fn-pck-payload fn-pck-x-row-word-of-row-is-the-row))
           :use ((:instance fn-pck-x-row-word-of-row-is-the-row
                            (frame base)
                            (off (+ *fn-cpl-header-octets* base))
                            (plen (len (fn-pck-payload (fn-row-wire-of row fn-arena))))
                            (d0 (car (fn-cpl-trailer-words (fn-pck-payload (fn-row-wire-of row fn-arena)))))
                            (d1 (cadr (fn-cpl-trailer-words (fn-pck-payload (fn-row-wire-of row fn-arena)))))
                            (d2 (caddr (fn-cpl-trailer-words (fn-pck-payload (fn-row-wire-of row fn-arena)))))
                            (d3 (cadddr (fn-cpl-trailer-words (fn-pck-payload (fn-row-wire-of row fn-arena))))))))))

(defthm pcks-agree-of-encode-row
  (implies (and (fn-sccb-treep (fn-pck-meta (fn-row-wire-of row fn-arena) st)) (natp j))
           (pcks-agree j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st))))
                       (fn-pck-x-tl row fn-arena base)
                       (fn-pck-x-encode-row row fn-arena st fn-octets)
                       (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-row-wire-of row fn-arena) base st))))
  :hints (("Goal" :induct (pcks-agree j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st))))
                                      (fn-pck-x-tl row fn-arena base)
                                      (fn-pck-x-encode-row row fn-arena st fn-octets)
                                      (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-row-wire-of row fn-arena) base st)))
           :in-theory (disable fn-pck-x-encode-row fn-pck-x-row-word fn-pck-x-row-words adt-tp-rw fn-pck-enc-row fn-scc-program
                               fn-row-wire-of fn-pck-x-tl fn-pck-x-rw fn-pck-meta))
          ("Subgoal *1/2" :expand ((pcks-agree j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st))))
                                      (fn-pck-x-tl row fn-arena base)
                                      (fn-pck-x-encode-row row fn-arena st fn-octets)
                                      (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-row-wire-of row fn-arena) base st))))
                          :use pcks-rw-of-encode-row)
          ("Subgoal *1/1" :expand ((pcks-agree j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st))))
                                      (fn-pck-x-tl row fn-arena base)
                                      (fn-pck-x-encode-row row fn-arena st fn-octets)
                                      (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-row-wire-of row fn-arena) base st)))))))

(defthm pcks-octets-len-of-encode-row
  (implies (fn-sccb-treep (fn-pck-meta (fn-row-wire-of row fn-arena) st))
           (equal (fn-octets-len (fn-pck-x-encode-row row fn-arena st fn-octets))
                  (len (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st)))))
  :hints (("Goal" :use ((:instance fn-pck-x-encode-row-is-the-meta-program)
                        (:instance fn-oct-len-is-len (fn-octets (fn-pck-x-encode-row row fn-arena st fn-octets)))
                        (:instance fn-oct-list-is-identity (fn-octets (fn-pck-x-encode-row row fn-arena st fn-octets))))
           :in-theory (disable fn-pck-x-encode-row-is-the-meta-program fn-pck-x-encode-row fn-oct-len-is-len fn-oct-list-is-identity))))

(defthm pcks-row-dwords
  (implies (fn-sccb-treep (fn-pck-meta (fn-row-wire-of row fn-arena) st))
           (equal (fn-pck-x-row-dwords 0 (fn-pck-x-row-words (fn-octets-len (fn-pck-x-encode-row row fn-arena st fn-octets)))
                                       (fn-pck-x-tl row fn-arena base)
                                       (fn-pck-x-encode-row row fn-arena st fn-octets))
                  (pcks-dlo-list (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-row-wire-of row fn-arena) base st)))))
  :hints (("Goal" :use ((:instance pcks-dwords-of-agree (j 0)
                                   (nw (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st)))))
                                   (tl (fn-pck-x-tl row fn-arena base))
                                   (fn-octets (fn-pck-x-encode-row row fn-arena st fn-octets))
                                   (rw (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-row-wire-of row fn-arena) base st))))
                        (:instance pcks-agree-of-encode-row (j 0)) pcks-octets-len-of-encode-row
                        (:instance fn-pck-x-row-words-is-the-row-length (w (fn-row-wire-of row fn-arena)) (off base)))
           :in-theory (disable fn-oct-len-is-len pcks-octets-len-of-encode-row pcks-dwords-of-agree pcks-agree-of-encode-row fn-pck-x-row-words-is-the-row-length
                               fn-pck-x-encode-row fn-pck-x-row-words adt-tp-rw fn-pck-enc-row fn-scc-program fn-row-wire-of pcks-agree pgs-dlo
                               fn-pck-x-tl fn-pck-meta))))

(defthm pcks-res-hi
  (implies (and (natp lo) (natp hi) (natp hi2) (<= hi2 hi) (pcks-res lo hi pgs-mem))
           (pcks-res lo hi2 pgs-mem))
  :hints (("Goal" :induct (pcks-res lo hi2 pgs-mem)
           :in-theory (union-theories '(pcks-res-step pcks-res-done (:induction pcks-res)) (disable pcks-res pcks-writable)))))

(defthm pcks-res-lo
  (implies (and (natp lo) (natp hi) (natp lo2) (<= lo lo2) (pcks-res lo hi pgs-mem))
           (pcks-res lo2 hi pgs-mem))
  :hints (("Goal" :induct (pcks-res lo hi pgs-mem)
           :in-theory (union-theories '(pcks-res-step pcks-res-done (:induction pcks-res)) (disable pcks-res pcks-writable)))))

(defthm pcks-res-sub
  (implies (and (natp lo) (natp hi) (natp lo2) (natp hi2) (<= lo lo2) (<= hi2 hi) (pcks-res lo hi pgs-mem))
           (pcks-res lo2 hi2 pgs-mem))
  :hints (("Goal" :use ((:instance pcks-res-lo) (:instance pcks-res-hi (lo lo2) (hi hi)))
           :in-theory (disable pcks-res-lo pcks-res-hi pcks-res))))

(defthm pcks-stage-open
  (implies (consp rows)
           (equal (fn-pck-x-stage-rows rows p base st fn-arena fn-octets pgs-mem)
                  (let ((fn-octets (fn-pck-x-encode-row (car rows) fn-arena st fn-octets)))
                    (mv-let (v pgs-mem)
                      (fn-pck-x-put-row 0 (fn-pck-x-row-words (fn-octets-len fn-octets)) p
                                        (fn-pck-x-tl (car rows) fn-arena base) fn-octets pgs-mem)
                      (if (eq v :ok)
                          (fn-pck-x-stage-rows (cdr rows) (+ p (fn-pck-x-row-words (fn-octets-len fn-octets)))
                                               (+ base (fn-cpl-frame-octets (fn-pck-x-payload-len (car rows) fn-arena)))
                                               (fn-pck-x-st-next (car rows) fn-arena st)
                                               fn-arena fn-octets pgs-mem)
                        (mv v fn-octets pgs-mem))))))
  :hints (("Goal" :expand ((fn-pck-x-stage-rows rows p base st fn-arena fn-octets pgs-mem)))))

(defthm pcks-stage-done
  (implies (atom rows)
           (equal (fn-pck-x-stage-rows rows p base st fn-arena fn-octets pgs-mem) (mv :ok fn-octets pgs-mem)))
  :hints (("Goal" :expand ((fn-pck-x-stage-rows rows p base st fn-arena fn-octets pgs-mem)))))

(defthm pcks-len-dlo-list (equal (len (pcks-dlo-list ws)) (len ws)))

(defun pcks-wlen (rows fn-arena st)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom rows) 0
    (+ (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of (car rows) fn-arena) st))))
       (pcks-wlen (cdr rows) fn-arena (fn-pck-x-st-next (car rows) fn-arena st)))))

(defun pcks-wlist (rows base st fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom rows) nil
    (append (pcks-dlo-list (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-row-wire-of (car rows) fn-arena) base st)))
            (pcks-wlist (cdr rows)
                        (+ base (fn-cpl-frame-octets (fn-pck-x-payload-len (car rows) fn-arena)))
                        (fn-pck-x-st-next (car rows) fn-arena st)
                        fn-arena))))

(defthm pcks-wlen-is-len-wlist
  (equal (len (pcks-wlist rows base st fn-arena)) (pcks-wlen rows fn-arena st))
  :hints (("Goal" :induct (pcks-wlist rows base st fn-arena)
           :in-theory (e/d (pcks-len-append pcks-len-dlo-list fn-pck-x-row-words-is-the-row-length)
                           (adt-tp-rw fn-pck-enc-row fn-scc-program fn-row-wire-of fn-pck-meta fn-pck-x-payload-len)))))

(defthm pcks-put-row-res-rest
  (implies (and (natp nw) (natp p) (natp r) (pcks-res p (+ p nw r) pgs-mem))
           (pcks-res (+ p nw) (+ p nw r) (mv-nth 1 (fn-pck-x-put-row 0 nw p tl fn-octets pgs-mem))))
  :hints (("Goal" :use ((:instance pcks-put-row-res (j 0) (lo (+ p nw)) (hi (+ p nw r)))
                        (:instance pcks-res-sub (lo p) (hi (+ p nw r)) (lo2 p) (hi2 (+ p nw))))
           :in-theory (disable pcks-put-row-res pcks-res-sub pcks-res fn-pck-x-put-row pcks-put-row-open pcks-put-row-done))))

(defthm pcks-wlen-natp (natp (pcks-wlen rows fn-arena st))
  :hints (("Goal" :in-theory (disable fn-pck-x-row-words)))
  :rule-classes (:rewrite :type-prescription))

(defthm pcks-put-row-ok-car
  (implies (and (natp j) (natp nw) (natp p) (natp a) (natp k)
                (pcks-res (+ p j) (+ p nw) pgs-mem)
                (<= a (+ 16384 p j)) (or (<= nw j) (<= (+ 16384 p nw) (+ a k))))
           (equal (car (fn-pck-x-put-row j nw p tl fn-octets pgs-mem)) :ok))
  :hints (("Goal" :use pcks-put-row :in-theory (disable pcks-put-row fn-pck-x-put-row pcks-res pgs-x-words pgs-dlo))))

(defthm pcks-put-nil (equal (pcks-put i nil l) l))

(defthm pcks-row-dwords2
  (implies (fn-sccb-treep (fn-pck-meta (fn-row-wire-of row fn-arena) st))
           (equal (fn-pck-x-row-dwords 0 (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st))))
                                       (fn-pck-x-tl row fn-arena base)
                                       (fn-pck-x-encode-row row fn-arena st fn-octets))
                  (pcks-dlo-list (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-row-wire-of row fn-arena) base st)))))
  :hints (("Goal" :use (pcks-row-dwords pcks-octets-len-of-encode-row)
           :in-theory (disable pcks-row-dwords pcks-octets-len-of-encode-row fn-oct-len-is-len))))

(defun pcks-stage-ind (rows p base st fn-arena fn-octets pgs-mem)
  (declare (xargs :stobjs (fn-arena fn-octets pgs-mem) :verify-guards nil))
  (if (atom rows)
      (mv fn-octets pgs-mem)
    (let ((fn-octets (fn-pck-x-encode-row (car rows) fn-arena st fn-octets)))
      (mv-let (v pgs-mem)
        (fn-pck-x-put-row 0 (fn-pck-x-row-words (fn-octets-len fn-octets)) p
                          (fn-pck-x-tl (car rows) fn-arena base) fn-octets pgs-mem)
        (declare (ignore v))
        (pcks-stage-ind (cdr rows) (+ p (fn-pck-x-row-words (fn-octets-len fn-octets)))
                        (+ base (fn-cpl-frame-octets (fn-pck-x-payload-len (car rows) fn-arena)))
                        (fn-pck-x-st-next (car rows) fn-arena st)
                        fn-arena fn-octets pgs-mem)))))

(defun pcks-treesp (rows fn-arena st)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom rows) t
    (and (fn-sccb-treep (fn-pck-meta (fn-row-wire-of (car rows) fn-arena) st)) (pcks-treesp (cdr rows) fn-arena (fn-pck-x-st-next (car rows) fn-arena st)))))

(defthm pcks-stage-cons-step
  (let* ((buf1 (fn-pck-x-encode-row (car rows) fn-arena st fn-octets))
         (nw (fn-pck-x-row-words (fn-octets-len buf1)))
         (base1 (+ base (fn-cpl-frame-octets (fn-pck-x-payload-len (car rows) fn-arena))))
         (st1 (fn-pck-x-st-next (car rows) fn-arena st))
         (mem1 (mv-nth 1 (fn-pck-x-put-row 0 nw p (fn-pck-x-tl (car rows) fn-arena base) buf1 pgs-mem))))
    (implies (and (consp rows) (natp p) (natp a) (natp k)
                  (pcks-treesp rows fn-arena st)
                  (pcks-res p (+ p (pcks-wlen rows fn-arena st)) pgs-mem)
                  (<= a (+ 16384 p))
                  (<= (+ 16384 p (pcks-wlen rows fn-arena st)) (+ a k))
                  (implies (and (natp (+ p nw)) (natp a) (natp k) (pcks-treesp (cdr rows) fn-arena st1)
                                (pcks-res (+ p nw) (+ (+ p nw) (pcks-wlen (cdr rows) fn-arena st1)) mem1)
                                (<= a (+ 16384 p nw))
                                (<= (+ 16384 (+ p nw) (pcks-wlen (cdr rows) fn-arena st1)) (+ a k)))
                           (and (equal (mv-nth 0 (fn-pck-x-stage-rows (cdr rows) (+ p nw) base1 st1 fn-arena buf1 mem1)) :ok)
                                (equal (pgs-x-words 0 a k (mv-nth 2 (fn-pck-x-stage-rows (cdr rows) (+ p nw) base1 st1 fn-arena buf1 mem1)))
                                       (pcks-put (- (+ 16384 (+ p nw)) a) (pcks-wlist (cdr rows) base1 st1 fn-arena)
                                                 (pgs-x-words 0 a k mem1))))))
             (and (equal (mv-nth 0 (fn-pck-x-stage-rows rows p base st fn-arena fn-octets pgs-mem)) :ok)
                  (equal (pgs-x-words 0 a k (mv-nth 2 (fn-pck-x-stage-rows rows p base st fn-arena fn-octets pgs-mem)))
                         (pcks-put (- (+ 16384 p) a) (pcks-wlist rows base st fn-arena) (pgs-x-words 0 a k pgs-mem))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcks-res-hi (lo p) (hi (+ p (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of (car rows) fn-arena) st)))) (pcks-wlen (cdr rows) fn-arena (fn-pck-x-st-next (car rows) fn-arena st))))
                                 (hi2 (+ p (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of (car rows) fn-arena) st)))))))
                 (:instance pcks-put-row-res-rest
                                 (nw (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta (fn-row-wire-of (car rows) fn-arena) st)))))
                                 (r (pcks-wlen (cdr rows) fn-arena (fn-pck-x-st-next (car rows) fn-arena st)))
                                 (tl (fn-pck-x-tl (car rows) fn-arena base))
                                 (fn-octets (fn-pck-x-encode-row (car rows) fn-arena st fn-octets))))
           :in-theory (union-theories '(pcks-put-nil pcks-put-row pcks-put-row-ok-car pcks-res-hi pcks-wlen-natp pcks-row-dwords2 pcks-octets-len-of-encode-row
                                        pcks-put-row-res-rest pcks-put-append pcks-len-dlo-list pcks-wlen-is-len-wlist
                                        fn-pck-x-row-words-is-the-row-length)
                                      (disable pcks-row-dwords fn-pck-x-row-dwords pckx-row-of-program pcks-put-row-open pcks-put-row-done pcks-stage-open pcks-stage-done
                                               pcks-res-step pcks-res-done pcks-wr fn-pck-x-rw fn-pck-x-row-word fn-pck-x-stage-rows
                                               pcks-res pcks-put pgs-x-words pgs-dlo fn-pck-x-put-row
                                               fn-pck-x-encode-row fn-pck-x-row-words fn-row-wire-of fn-pck-enc-row adt-tp-rw
                                               fn-oct-len-is-len pcks-words-step pcks-update-nth-cons
                                               pcks-wlen pcks-wlist fn-pck-x-st-next fn-pck-x-tl fn-pck-meta fn-pck-x-payload-len)))
          (and stable-under-simplificationp
               '(:expand ((fn-pck-x-stage-rows rows p base st fn-arena fn-octets pgs-mem)
                          (pcks-wlen rows fn-arena st) (pcks-wlist rows base st fn-arena) (pcks-treesp rows fn-arena st) (fn-pck-x-st-next (car rows) fn-arena st))))))

(defthm pcks-stage-rows
  (implies (and (natp p) (natp a) (natp k)
                (pcks-treesp rows fn-arena st)
                (pcks-res p (+ p (pcks-wlen rows fn-arena st)) pgs-mem)
                (<= a (+ 16384 p))
                (<= (+ 16384 p (pcks-wlen rows fn-arena st)) (+ a k)))
           (and (equal (mv-nth 0 (fn-pck-x-stage-rows rows p base st fn-arena fn-octets pgs-mem)) :ok)
                (equal (pgs-x-words 0 a k (mv-nth 2 (fn-pck-x-stage-rows rows p base st fn-arena fn-octets pgs-mem)))
                       (pcks-put (- (+ 16384 p) a) (pcks-wlist rows base st fn-arena) (pgs-x-words 0 a k pgs-mem)))))
  :hints (("Goal" :induct (pcks-stage-ind rows p base st fn-arena fn-octets pgs-mem)
           :in-theory (union-theories '((:induction pcks-stage-ind) pcks-stage-done pcks-put-nil pcks-res-done)
                                      (disable pcks-stage-cons-step pcks-stage-open pcks-put-row-open pcks-res-step
                                               fn-pck-x-stage-rows pcks-res pcks-put pgs-x-words pcks-wlen pcks-wlist pcks-treesp)))
          ("Subgoal *1/1" :expand ((pcks-wlist rows base st fn-arena)))
          ("Subgoal *1/2" :use pcks-stage-cons-step :in-theory (union-theories (theory 'minimal-theory) '(atom)))))

; -----------------------------------------------------------------------------
; From the staged words to the dirty set.

(defun pcks-iota (a n)
  (declare (xargs :guard (and (natp a) (natp n))))
  (if (zp n) nil (cons a (pcks-iota (1+ a) (1- n)))))

(defthm pcks-len-words (implies (natp k) (equal (len (pgs-x-words 0 a k pgs-mem)) k))
  :hints (("Goal" :induct (pcks-ind a k) :in-theory (enable pcks-words-step pcks-words-zero))))

(defthm pcks-take-of-append-block
  (implies (and (true-listp blk) (equal (len blk) n) (natp n))
           (equal (adt-tp-take n (append blk rest)) blk))
  :hints (("Goal" :in-theory (enable adt-tp-take))))

(defthm pcks-nthcdr-of-append-block
  (implies (and (true-listp blk) (equal (len blk) n) (natp n))
           (equal (nthcdr n (append blk rest)) rest)))

(defthm pcks-pages-of-block
  (implies (and (true-listp blk) (equal (len blk) 2048) (true-listp rest))
           (equal (adt-tp-pages (append blk rest)) (cons blk (adt-tp-pages rest))))
  :hints (("Goal" :expand ((adt-tp-pages (append blk rest)))
           :in-theory (e/d (adt-tp-page) (adt-tp-pages)))))

(defthm pcks-true-listp-words (true-listp (pgs-x-words 0 a k pgs-mem))
  :hints (("Goal" :induct (pcks-ind a k) :in-theory (enable pcks-words-step pcks-words-zero)))
  :rule-classes (:rewrite :type-prescription))

(defthm pcks-iota-step
  (implies (posp n) (equal (pcks-iota lp0 n) (cons lp0 (pcks-iota (1+ lp0) (1- n)))))
  :hints (("Goal" :expand ((pcks-iota lp0 n)))))

(defthm pcks-abs-dirty-cons
  (equal (pgs-x-abs-dirty (cons lp rest) pgs-mem)
         (cons (cons lp (pgs-x-words 0 (* 2048 (nfix lp)) 2048 pgs-mem)) (pgs-x-abs-dirty rest pgs-mem)))
  :hints (("Goal" :expand ((pgs-x-abs-dirty (cons lp rest) pgs-mem)))))

(defthm pcks-abs-dirty-nil (equal (pgs-x-abs-dirty nil pgs-mem) nil))

(defthm pcks-words-split2
  (implies (and (natp lp0) (posp n))
           (equal (pgs-x-words 0 (* 2048 lp0) (* 2048 n) pgs-mem)
                  (append (pgs-x-words 0 (* 2048 lp0) 2048 pgs-mem)
                          (pgs-x-words 0 (* 2048 (1+ lp0)) (* 2048 (1- n)) pgs-mem))))
  :hints (("Goal" :use ((:instance pgs-x-words-split (s 0) (a (* 2048 lp0)) (k1 2048) (k2 (* 2048 (1- n)))))
           :in-theory (disable pgs-x-words-split pgs-x-words)))
  :rule-classes nil)

(defthm pcks-iota-zero (equal (pcks-iota a 0) nil))

(defthm pcks-abs-dirty-iota
  (implies (and (natp lp0) (natp n))
           (equal (pgs-x-abs-dirty (pcks-iota lp0 n) pgs-mem)
                  (adt-tp-number lp0 (adt-tp-pages (pgs-x-words 0 (* 2048 lp0) (* 2048 n) pgs-mem)))))
  :hints (("Goal" :induct (pcks-iota lp0 n)
           :in-theory (e/d ((:induction pcks-iota) pcks-iota-step pcks-iota-zero pcks-abs-dirty-cons pcks-abs-dirty-nil pcks-pages-of-block
                            pcks-len-words pcks-true-listp-words pcks-words-zero adt-tp-number)
                           (pgs-x-words (:definition pcks-iota) adt-tp-pages pgs-x-abs-dirty)))
          ("Subgoal *1/2" :use ((:instance pcks-words-split2 (n n))))))

(defthm pcks-pad-multiple
  (implies (natp m) (equal (adt-tp-pad (* 2048 m)) 0))
  :hints (("Goal" :induct (pcks-ind 0 m) :in-theory (enable adt-tp-pad))))

(defthm pcks-nthcdr-too-long
  (implies (and (true-listp w) (natp n) (<= (len w) n)) (equal (nthcdr n w) nil))
  :hints (("Goal" :induct (nthcdr n w))))

(defthm pcks-pages-short
  (implies (and (true-listp w) (consp w) (<= (len w) 2048))
           (equal (adt-tp-pages w) (list (adt-tp-page w))))
  :hints (("Goal" :expand ((adt-tp-pages w)) :in-theory (disable adt-tp-pages adt-tp-page adt-tp-tail-is-page-prefix))))

(defthm pcks-pages-of-padded-short
  (implies (and (true-listp w) (consp w) (<= (len w) 2048))
           (equal (adt-tp-pages (append w (adt-tp-zeros (adt-tp-pad (len w))))) (adt-tp-pages w)))
  :hints (("Goal" :in-theory (e/d (adt-tp-page adt-tp-pad-short adt-tp-take-of-append)
                                  (adt-tp-pages adt-tp-pad-long adt-tp-tail-is-page-prefix))
           :use ((:instance adt-tp-pages-long (w (append w (adt-tp-zeros (adt-tp-pad (len w))))))
                 pcks-pages-short)))
  :rule-classes nil)

(defthm pcks-pages-of-padded
  (implies (true-listp w)
           (equal (adt-tp-pages (append w (adt-tp-zeros (adt-tp-pad (len w))))) (adt-tp-pages w)))
  :hints (("Goal" :induct (adt-tp-pages w)
           :in-theory (disable (:definition adt-tp-pages) adt-tp-pages-long adt-tp-tail-is-page-prefix adt-tp-pad-long adt-tp-pad-short))
          ("Subgoal *1/2" :cases ((<= (len w) 2048)))
          ("Subgoal *1/2.2" :use ((:instance adt-tp-pages-long (w w))
                                  (:instance adt-tp-pages-long (w (append w (adt-tp-zeros (adt-tp-pad (len w))))))
                                  (:instance adt-tp-pad-long (n (len w)))
                                  (:instance adt-tp-nthcdr-of-append (n 2048) (a w) (b (adt-tp-zeros (adt-tp-pad (len w)))))
                                  (:instance adt-tp-take-of-append (n 2048) (a w) (b (adt-tp-zeros (adt-tp-pad (len w))))))
           :in-theory (disable adt-tp-pages adt-tp-pages-long adt-tp-tail-is-page-prefix adt-tp-pad-long adt-tp-pad-short
                               adt-tp-nthcdr-of-append adt-tp-take-of-append))
          ("Subgoal *1/2.1" :use (pcks-pages-of-padded-short)
           :in-theory (disable adt-tp-pages adt-tp-pages-long adt-tp-tail-is-page-prefix adt-tp-pad-long adt-tp-pad-short))))

(defthm pcks-append-nil (implies (true-listp x) (equal (append x nil) x)))

(defthm pcks-flat-of-multiple
  (implies (and (true-listp x) (natp m) (equal (len x) (* 2048 m)))
           (equal (adt-tp-flat (adt-tp-pages x)) x))
  :hints (("Goal" :use ((:instance adt-tp-flat-of-pages (w x)) (:instance pcks-pad-multiple))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '((:executable-counterpart adt-tp-zeros) pcks-append-nil)))))

(defun pcks-put-ind2 (a ws)
  (if (atom ws) a (pcks-put-ind2 (append a (list (car ws))) (cdr ws))))

(defthm pcks-append-cons-assoc
  (equal (append (append a (list w)) x) (append a (cons w x))))

(defthm pcks-zeros-succ (implies (natp n) (equal (adt-tp-zeros (+ 1 n)) (cons 0 (adt-tp-zeros n))))
  :hints (("Goal" :expand ((adt-tp-zeros (+ 1 n))))))

(defthm pcks-put-over-zeros
  (implies (true-listp a)
           (equal (pcks-put (len a) ws (append a (append (adt-tp-zeros (len ws)) r)))
                  (append a (append ws r))))
  :hints (("Goal" :induct (pcks-put-ind2 a ws))
          ("Subgoal *1/2" :use ((:instance adt-tp-update-nth-at-end (p (car ws)) (b (append (adt-tp-zeros (len ws)) r))))
           :in-theory (enable pcks-put pcks-len-append pcks-append-cons-assoc pcks-zeros-succ))))

(defthm pcks-dlo-list-append
  (equal (pcks-dlo-list (append a b)) (append (pcks-dlo-list a) (pcks-dlo-list b))))

(defthm pcks-dlo-list-id
  (implies (adt-tp-u64s w) (equal (pcks-dlo-list w) w))
  :hints (("Goal" :induct (pcks-dlo-list w) :in-theory (enable adt-tp-u64s pgs-dlo unsigned-byte-p))))

(defthm pcks-wlist-is-dlo-of-words
  (equal (pcks-wlist rows base st fn-arena)
         (pcks-dlo-list (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from (fn-rows-wire-of rows fn-arena) base st))))
  :hints (("Goal" :induct (pcks-wlist rows base st fn-arena)
           :in-theory (e/d (fn-rows-wire-of fn-pck-rows-from adt-tp-seq-words) (pcks-dlo-list adt-tp-rw fn-pck-enc-row fn-row-wire-of pckx-row-of-program fn-pck-meta)))
          ("Subgoal *1/2" :expand ((pcks-wlist rows base st fn-arena))
           :in-theory (e/d (fn-rows-wire-of fn-pck-rows-from adt-tp-seq-words pcks-dlo-list-append fn-pck-x-payload-len)
                           (adt-tp-rw fn-pck-enc-row fn-row-wire-of pckx-row-of-program fn-pck-meta)))))

(defthm pcks-wlen-is-len-words
  (equal (pcks-wlen rows fn-arena st)
         (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from (fn-rows-wire-of rows fn-arena) base st))))
  :hints (("Goal" :use (pcks-wlen-is-len-wlist pcks-wlist-is-dlo-of-words (:instance pcks-len-dlo-list (ws (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from (fn-rows-wire-of rows fn-arena) base st)))))
           :in-theory (disable pcks-wlen-is-len-wlist pcks-wlist-is-dlo-of-words pcks-len-dlo-list pcks-wlist pcks-wlen))))

(defthm pcks-floor-plus-2048
  (implies (natp y) (equal (floor (+ 2048 y) 2048) (+ 1 (floor y 2048)))))

(defthm pcks-npages-closed
  (implies (natp x) (equal (adt-tp-npages x) (floor (+ x 2047) 2048)))
  :hints (("Goal" :induct (adt-tp-npages x) :in-theory (enable adt-tp-npages))))

(defthm pcks-floor-plus-multiple
  (implies (and (natp y) (natp k)) (equal (floor (+ y (* 2048 k)) 2048) (+ k (floor y 2048)))))

(defthm pcks-last-page
  (implies (and (natp cnt) (natp l) (< 0 l))
           (equal (+ (floor cnt 2048)
                     (floor (+ (- cnt (* 2048 (floor cnt 2048))) l 2047) 2048))
                  (+ 1 (floor (+ cnt l -1) 2048))))
  :hints (("Goal" :use ((:instance pcks-floor-plus-multiple (y (+ (- cnt (* 2048 (floor cnt 2048))) l -1)) (k (floor cnt 2048)))
                        (:instance pcks-floor-plus-2048 (y (+ (- cnt (* 2048 (floor cnt 2048))) l -1))))
           :in-theory (disable pcks-floor-plus-multiple pcks-floor-plus-2048))))

(defun pcks-number-ind (j a b)
  (if (or (atom a) (atom b)) (list j a b) (pcks-number-ind (1+ j) (cdr a) (cdr b))))

(defthm pcks-shift-of-number
  (implies (and (natp k) (natp j))
           (equal (pck-shift k (adt-tp-number j ps)) (adt-tp-number (+ k j) ps)))
  :hints (("Goal" :induct (adt-tp-number j ps) :in-theory (enable pck-shift adt-tp-number))))

(defthm pcks-dirty-lpages-of-number
  (implies (natp j)
           (equal (pgs-dirty-lpages (adt-tp-number j ps)) (pcks-iota j (len ps))))
  :hints (("Goal" :induct (adt-tp-number j ps) :in-theory (enable pgs-dirty-lpages adt-tp-number pcks-iota))))

(defthm pcks-number-injective
  (implies (and (natp j) (true-listp a) (true-listp b) (equal (adt-tp-number j a) (adt-tp-number j b)))
           (equal a b))
  :rule-classes nil
  :hints (("Goal" :induct (pcks-number-ind j a b) :in-theory (enable adt-tp-number))))

(defthm pcks-window-post
  (implies (and (true-listp tail) (true-listp w) (true-listp win0) (natp n)
                (equal (len win0) (* 2048 n))
                (equal (adt-tp-pages win0) (adt-tp-pages (append tail (adt-tp-zeros (len w))))))
           (equal (adt-tp-pages (pcks-put (len tail) w win0))
                  (adt-tp-pages (append tail w))))
  :hints (("Goal" :use ((:instance pcks-flat-of-multiple (x win0) (m n))
                        (:instance adt-tp-flat-of-pages (w (append tail (adt-tp-zeros (len w)))))
                        (:instance pcks-put-over-zeros (a tail) (ws w) (r (adt-tp-zeros (adt-tp-pad (len (append tail (adt-tp-zeros (len w))))))))
                        (:instance pcks-pages-of-padded (w (append tail w))))
           :in-theory (disable pcks-flat-of-multiple adt-tp-flat-of-pages pcks-put-over-zeros pcks-pages-of-padded
                               adt-tp-pages adt-tp-pad adt-tp-flat pcks-put adt-tp-tail-is-page-prefix)))
  :rule-classes nil)

(defthm pcks-ceil-bound
  (implies (natp x) (<= x (* 2048 (floor (+ x 2047) 2048))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable floor))))

(defthm pcks-dirty-at-open
  (implies (consp n)
           (equal (adt-tp-dirty-at cnt tail n)
                  (adt-tp-number (floor cnt 2048) (adt-tp-pages (append tail n)))))
  :hints (("Goal" :in-theory (enable adt-tp-dirty-at))))

(defthm pcks-dirty-at-nil
  (equal (adt-tp-dirty-at cnt tail nil) nil)
  :hints (("Goal" :in-theory (enable adt-tp-dirty-at))))

(defthm pcks-consp-zeros (implies (posp l) (consp (adt-tp-zeros l)))
  :hints (("Goal" :expand ((adt-tp-zeros l)))))

(defthm pcks-len-pages-of-tail-words
  (implies (and (true-listp tail) (true-listp w) (consp w) (natp (len tail)))
           (equal (len (adt-tp-pages (append tail w)))
                  (floor (+ (len tail) (len w) 2047) 2048)))
  :hints (("Goal" :use ((:instance adt-tp-len-pages (w (append tail w)))
                        (:instance pcks-npages-closed (x (len (append tail w)))))
           :in-theory (disable adt-tp-len-pages pcks-npages-closed adt-tp-pages adt-tp-npages))))

(defthm pcks-stage-window
  (implies (and (natp lp0) (true-listp tail) (true-listp w) (consp w)
                (equal n (floor (+ (len tail) (len w) 2047) 2048))
                (equal (pgs-x-abs-dirty (pcks-iota lp0 n) mem0)
                       (adt-tp-number lp0 (adt-tp-pages (append tail (adt-tp-zeros (len w)))))))
           (equal (adt-tp-number lp0 (adt-tp-pages (pcks-put (len tail) w (pgs-x-words 0 (* 2048 lp0) (* 2048 n) mem0))))
                  (adt-tp-number lp0 (adt-tp-pages (append tail w)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance pcks-abs-dirty-iota (pgs-mem mem0) (n n))
                        (:instance pcks-number-injective (j lp0)
                                   (a (adt-tp-pages (pgs-x-words 0 (* 2048 lp0) (* 2048 n) mem0)))
                                   (b (adt-tp-pages (append tail (adt-tp-zeros (len w))))))
                        (:instance pcks-window-post (n n) (win0 (pgs-x-words 0 (* 2048 lp0) (* 2048 n) mem0)))
                        (:instance pcks-len-words (a (* 2048 lp0)) (k (* 2048 n)) (pgs-mem mem0)))
           :in-theory (disable pcks-abs-dirty-iota pcks-len-words
                               pcks-true-listp-words pgs-x-words pcks-put adt-tp-pages adt-tp-number adt-tp-zeros pcks-iota
                               pgs-x-abs-dirty adt-tp-tail-is-page-prefix))))

(defthm pcks-window-dirty
  (implies (and (natp lp0) (true-listp tail) (true-listp w) (consp w)
                (equal n (floor (+ (len tail) (len w) 2047) 2048))
                (equal (pgs-x-words 0 (* 2048 lp0) (* 2048 n) mem1)
                       (pcks-put (len tail) w (pgs-x-words 0 (* 2048 lp0) (* 2048 n) mem0)))
                (equal (pgs-x-abs-dirty (pcks-iota lp0 n) mem0)
                       (adt-tp-number lp0 (adt-tp-pages (append tail (adt-tp-zeros (len w)))))))
           (equal (pgs-x-abs-dirty (pcks-iota lp0 n) mem1)
                  (adt-tp-number lp0 (adt-tp-pages (append tail w)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance pcks-abs-dirty-iota (pgs-mem mem1) (n n))
                        (:instance pcks-stage-window))
           :in-theory (disable pcks-abs-dirty-iota pcks-put pgs-x-words adt-tp-pages adt-tp-number pcks-iota
                               pgs-x-abs-dirty adt-tp-zeros))))

(defthm pcks-adt-take-is-take
  (implies (and (natp j) (<= j (len w)))
           (equal (adt-tp-take j w) (take j w)))
  :hints (("Goal" :induct (adt-tp-take j w) :in-theory (enable adt-tp-take))))

(defthm pcks-adt-take-of-words
  (implies (and (natp j) (natp k) (<= j k))
           (equal (adt-tp-take j (pgs-x-words 0 a k pgs-mem)) (pgs-x-words 0 a j pgs-mem)))
  :hints (("Goal" :use ((:instance pgs-x-take-of-words (s 0))
                        (:instance pcks-adt-take-is-take (j j) (w (pgs-x-words 0 a k pgs-mem)))
                        (:instance pcks-len-words (a a) (k k)))
           :in-theory (disable pgs-x-take-of-words pcks-adt-take-is-take pcks-len-words pgs-x-words))))

(defthm pcks-stage-dirty-at-cons
  (let* ((recs (fn-rows-wire-of rows fn-arena))
         (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs base st)))
         (d (pck-shift 8 (adt-tp-dirty-at cnt tail w)))
         (lp (pgs-dirty-lpages d)))
    (implies (and (natp cnt) (true-listp tail) (equal (len tail) (- cnt (* 2048 (floor cnt 2048))))
                  (pcks-treesp rows fn-arena st) (adt-tp-u64s w) (consp w)
                  (pcks-res cnt (+ cnt (len w)) pgs-mem)
                  (equal (pgs-x-abs-dirty lp pgs-mem)
                         (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros (len w))))))
             (and (equal (mv-nth 0 (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem)) :ok)
                  (equal (pgs-x-abs-dirty lp (mv-nth 2 (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem)))
                         d))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcks-stage-rows (p cnt) (a (* 2048 (+ 8 (floor cnt 2048))))
                            (k (* 2048 (floor (+ (len tail)
                                                 (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from (fn-rows-wire-of rows fn-arena) base st)))
                                                 2047) 2048))))
                 (:instance pcks-window-dirty (lp0 (+ 8 (floor cnt 2048)))
                            (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from (fn-rows-wire-of rows fn-arena) base st)))
                            (n (floor (+ (len tail) (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from (fn-rows-wire-of rows fn-arena) base st)))
                                         2047) 2048))
                            (mem0 pgs-mem)
                            (mem1 (mv-nth 2 (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem)))))
           :in-theory (union-theories '(pcks-shift-of-number pcks-dirty-lpages-of-number pcks-dirty-at-open
                                        pcks-len-pages-of-tail-words pcks-consp-zeros pcks-wlen-is-len-words pcks-wlist-is-dlo-of-words
                                        pcks-dlo-list-id pcks-adt-take-of-words)
                                      (disable pcks-stage-rows fn-pck-x-stage-rows pcks-res pcks-put pgs-x-words
                                               pcks-wlen pcks-wlist pgs-x-abs-dirty adt-tp-zeros adt-tp-tail-is-page-prefix)))))

(defthm pcks-stage-dirty-at-nil
  (let* ((recs (fn-rows-wire-of rows fn-arena))
         (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs base st))))
    (implies (and (natp cnt) (pcks-treesp rows fn-arena st) (atom w)
                  (pcks-res cnt (+ cnt (len w)) pgs-mem))
             (equal (mv-nth 0 (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem)) :ok)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcks-stage-rows (p cnt) (a (+ 16384 cnt)) (k 0))
                 (:instance pcks-wlen-is-len-words))
           :in-theory (disable pcks-stage-rows pcks-wlen-is-len-words fn-pck-x-stage-rows pcks-res pcks-put pgs-x-words pcks-wlen pcks-wlist))))

(defthm pcks-stage-dirty-at
  (let* ((recs (fn-rows-wire-of rows fn-arena))
         (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs base st)))
         (d (pck-shift 8 (adt-tp-dirty-at cnt tail w)))
         (lp (pgs-dirty-lpages d)))
    (implies (and (natp cnt) (true-listp tail) (equal (len tail) (- cnt (* 2048 (floor cnt 2048))))
                  (pcks-treesp rows fn-arena st) (adt-tp-u64s w)
                  (pcks-res cnt (+ cnt (len w)) pgs-mem)
                  (equal (pgs-x-abs-dirty lp pgs-mem)
                         (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros (len w))))))
             (and (equal (mv-nth 0 (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem)) :ok)
                  (equal (pgs-x-abs-dirty lp (mv-nth 2 (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem)))
                         d))))
  :hints (("Goal" :do-not-induct t
           :cases ((consp (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from (fn-rows-wire-of rows fn-arena) base st))))
           ; pgs-dirty-lpages is named: certified inside the owner image
           ; (owner@books:books/owner) its definition and executable
           ; counterpart are not open here, so (pgs-dirty-lpages nil) would
           ; never evaluate and pcks-abs-dirty-nil could not fire.
           :in-theory (union-theories '(pcks-dirty-at-nil pcks-abs-dirty-nil
                                        pgs-dirty-lpages (:executable-counterpart pgs-dirty-lpages))
                                      (disable pcks-stage-dirty-at-cons pcks-stage-dirty-at-nil fn-pck-x-stage-rows pcks-res pcks-put pgs-x-words
                                               pcks-wlen pcks-wlist pgs-x-abs-dirty)))
          ("Subgoal 1" :use pcks-stage-dirty-at-cons)
          ("Subgoal 2" :use pcks-stage-dirty-at-nil)))

(defthm pcks-treesp-of-sccb-listp
  (implies (fn-pck-sccb-listp (fn-rows-wire-of rows fn-arena) st) (pcks-treesp rows fn-arena st))
  :hints (("Goal" :induct (pcks-treesp rows fn-arena st)
           :in-theory (e/d (fn-rows-wire-of fn-pck-sccb-listp pcks-treesp) (fn-row-wire-of)))))

(defthm pcks-len-tail
  (implies (and (true-listp pw) (natp k) (<= (* 2048 k) (len pw)))
           (equal (len (nthcdr (* 2048 k) pw)) (- (len pw) (* 2048 k)))))

(defthm pcks-extend-dirty-is-dirty-at
  (let ((pw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix))))
    (equal (fn-pck-row-extend-dirty (fn-pck-rows prefix) xs)
           (adt-tp-dirty-at (len pw)
                            (nthcdr (* 2048 (floor (len pw) 2048)) pw)
                            (adt-tp-seq-words *fn-pck-row-schema* xs))))
  :hints (("Goal" :use ((:instance fn-pck-row-extend-dirty-at-is-extend-dirty (a (fn-pck-rows prefix))))
           :in-theory (e/d (fn-pck-row-extend-dirty-at adt-tp-extend-dirty-at)
                           (fn-pck-row-extend-dirty-at-is-extend-dirty adt-tp-dirty-at adt-tp-tail-is-page-prefix)))))

(defthm fn-pck-x-stage-is-the-dirty
  ; Staging the delta's rows from P = the prefix's word count, their payload
  ; frames laid end to end from BASE = the prefix's payload-file length, writes
  ; exactly the tape part of the model's dirty set: the pages the commit will
  ; digest hold the words `fn-pck-dirty' names.
  (let* ((delta (fn-rows-wire-of rows fn-arena))
         (pw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix)))
         (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from delta base st)))
         (tape (pck-shift *fn-pck-root-pages*
                          (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows-from delta base st))))
         (lp (pgs-dirty-lpages tape)))
    (implies (and (equal cnt (len pw))
                  (equal tail (nthcdr (* *pgs-page-words* (floor (len pw) *pgs-page-words*)) pw))
                  (equal base (fn-pck-plen prefix 0))
                  (equal st (fn-pck-st-of (fn-pck-seed) prefix))
                  (fn-pck-sccb-listp delta st)
                  (fn-pck-plen-okp (append prefix delta))
                  (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows-from delta base st))
                  (pcks-res cnt (+ cnt (len w)) pgs-mem)
                  (equal (pgs-x-abs-dirty lp pgs-mem)
                         (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros (len w))))))
             (and (equal (mv-nth 0 (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem)) :ok)
                  (equal (pgs-x-abs-dirty lp (mv-nth 2 (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem)))
                         tape))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcks-stage-dirty-at (cnt (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix))))
                            (tail (nthcdr (* 2048 (floor (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix))) 2048))
                                          (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix)))))
                 (:instance adt-tp-u64s-seq-words (s *fn-pck-row-schema*) (a (fn-pck-rows-from (fn-rows-wire-of rows fn-arena) base st)))
                 (:instance pck-rows-from-ap (recs (fn-rows-wire-of rows fn-arena)))
                 (:instance pcks-len-tail (pw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix)))
                            (k (floor (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix))) 2048))))
           :in-theory (e/d (pcks-extend-dirty-is-dirty-at pcks-treesp-of-sccb-listp)
                           (pcks-stage-dirty-at fn-pck-x-stage-rows pcks-res pcks-put
                            pgs-x-words pcks-wlen pcks-wlist pgs-x-abs-dirty adt-tp-zeros adt-tp-tail-is-page-prefix
                            adt-tp-dirty-at pcks-len-tail adt-tp-u64s-seq-words pck-rows-from-ap)))))
