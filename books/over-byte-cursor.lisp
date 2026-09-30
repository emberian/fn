; Complete row continuation for the served OVER assembler. PRF-1066.
; Dormant until the row-selection/parser/plan refinement and host boundary
; are joined. Each ONE reads at most one source octet; a host keeps every
; completed ONE before issuing a cold page dependency. The arena generation
; PIN is captured from response ownership, never from the catalog view V.
(in-package "ACL2")
(include-book "over-row-state")
(include-book "catalog-number-read")
(include-book "response-plan-token")
(include-book "nov-row-capture")
(include-book "legacy-parser-header")
(include-book "over-row-pieces")

; Proof vocabulary; never executed by ONE or by a served admission guard.
(defun fn-obc-statep (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (true-listp s) (equal (len s) 6)
       (or (null (nth 0 s)) (fn-ovw-cursorp (nth 0 s)))
       (fn-rpin-tokenp (nth 1 s)) (natp (nth 5 s))
       (case (nth 2 s)
         (:seek (consp (nth 0 s)))
         (:parse (and (consp (nth 0 s))
                      (fn-lpc-ready-p (nth 3 s) fn-arena)
                      (fn-lpc-cursor-bounds-p (nth 3 s))))
         (:emit (fn-npw-piecesp (nth 4 s) fn-arena))
         (otherwise nil))))

(local
 (defthm fn-obc-statep-fields
   (implies (fn-obc-statep s fn-arena)
            (and (true-listp s) (true-listp (nth 0 s)) (natp (nth 5 s))
                 (implies (equal (nth 2 s) :seek)
                          (natp (nth 3 (nth 0 s))))
                 (implies (equal (nth 2 s) :parse)
                          (fn-lpc-ready-p (nth 3 s) fn-arena))
                 (implies (equal (nth 2 s) :emit)
                          (fn-npw-piecesp (nth 4 s) fn-arena))))
   :hints (("Goal" :in-theory
            (e/d (fn-obc-statep fn-ovw-cursorp)
                 (fn-lpc-ready-p fn-lpc-cursor-bounds-p fn-rpin-tokenp
                  fn-npw-piecesp nth true-listp natp))))))

(local
 (defthm fn-obc-selected-sequence-in-bounds
   (implies (fn-cnx-view-seq group k v fn-cat)
            (and (natp (fn-cnx-view-seq group k v fn-cat))
                 (< (fn-cnx-view-seq group k v fn-cat) (fn-cat-count fn-cat))))
   :hints (("Goal" :in-theory
            (e/d (fn-cnx-view-seq)
                 (fn-cat-group-number fn-cat-visible-at fn-cat-count-is-len))))))

; The selected row's scalar handle premise. The owner carries the catalog
; representation invariant; the boundary proof derives this local premise
; without running a whole-catalog validation during a served quantum.
(defun fn-obc-source-ready-p (s fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if (eq (fn-lpc-at 2 s) :seek)
      (let* ((range (fn-lpc-at 0 s))
             (seq (fn-cnx-view-seq (fn-lpc-at 0 range)
                                  (nfix (fn-lpc-at 1 range))
                                  (nfix (fn-lpc-at 3 range)) fn-cat)))
        (if seq
            (let ((h (fn-record-payload (fn-cat-at seq fn-cat))))
              (and (natp h) (< h (fn-arena-count fn-arena))))
          t))
    t))

(verify-guards fn-obc-source-ready-p
  :hints (("Goal" :in-theory (disable fn-cnx-view-seq fn-cat-at-is-nth
                                      fn-cat-count-is-len fn-lpc-at))))

(local
 (defthm fn-obc-at-is-nth
   (equal (fn-lpc-at i x) (nth (nfix i) x))
   :hints (("Goal" :in-theory (enable fn-lpc-at fn-ag-car fn-ag-cdr nth)))))

; Bounds are carried by the parser; this bridge does not inspect a source
; byte or validate its complete header. Keep the free bound local.
(local
 (defthm fn-obc-span-piece-shape
   (implies (and (fn-lpc-span-bound-p span h pin bound)
                 (natp h) (< h (fn-arena-count fn-arena))
                 (<= (nfix bound) (fn-arena-payload-len h fn-arena)))
            (fn-npw-partp (fn-obc-span-piece span) fn-arena))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-obc-span-piece fn-lpc-span-bound-p
                             fn-npw-partp fn-lpc-at)
                            (fn-arena-count-is-len
                             fn-arena-payload-len-is-len-nth))))))

(local
 (defthm fn-obc-digit-run-is-octets
   (implies (and (true-listp bytes) (fn-nntp-decimal-tokenp bytes))
            (fn-cbor-octet-listp bytes))
   :hints (("Goal" :induct (fn-nntp-decimal-tokenp bytes)
            :in-theory (enable fn-nntp-decimal-tokenp fn-nntp-decimal-digitp
                               fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-obc-number-piece-shape
   (fn-npw-partp (fn-nntp-decimal-field number) fn-arena)
   :hints (("Goal" :in-theory
            (enable fn-npw-partp fn-nntp-decimal-field
                    fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))

(local
 (defthm fn-obc-parser-field-piece-has-shape
   (implies (and (natp k) (fn-lpc-ready-p parser fn-arena)
                 (fn-lpc-cursor-bounds-p parser))
            (fn-npw-partp (fn-obc-span-piece (fn-lpc-field parser k)) fn-arena))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lpc-field-retains-pinned-source (s parser))
                  (:instance fn-obc-span-piece-shape
                             (span (fn-lpc-field parser k))
                             (h (fn-lpc-at 0 parser))
                             (pin (fn-lpc-at 2 parser))
                             (bound (fn-lpc-at 3 parser))))
            :in-theory
            (e/d (fn-lpc-ready-p)
                 (fn-lpc-field fn-lpc-at fn-lpc-cursor-bounds-p
                  fn-lpc-span-bound-p fn-obc-span-piece fn-npw-partp
                  fn-obc-span-piece-shape fn-lpc-field-retains-pinned-source
                  fn-arena-count-is-len fn-arena-payload-len-is-len-nth))))))

(local
 (defthm fn-obc-decimal-piece-shape
   (implies (natp n) (fn-npw-partp (list :decimal n nil) fn-arena))
   :hints (("Goal" :in-theory (enable fn-npw-partp)))))

(local
 (defthm fn-obc-fixed-separators-shape
   (and (fn-npw-partp '(9) fn-arena) (fn-npw-partp '(13 10) fn-arena))
   :hints (("Goal" :in-theory (enable fn-npw-partp)))))

(defthm fn-obc-parser-pieces-have-shape
  (implies (and (fn-lpc-ready-p parser fn-arena)
                (fn-lpc-cursor-bounds-p parser))
           (fn-npw-piecesp (fn-obc-parser-pieces number parser) fn-arena))
  :hints (("Goal" :in-theory
           (e/d (fn-obc-parser-pieces fn-npw-piecesp)
                (fn-npw-partp fn-obc-span-piece fn-lpc-field fn-lpc-ready-p
                 fn-lpc-at fn-lpc-body-lines fn-lpc-cursor-bounds-p
                 fn-nntp-decimal-field)))))

; Selected-row proof premise. The eventual served boundary derives it
; from F; the cursor transition never calls this recognizer.
(defun fn-obc-cached-ready-p (s fn-cat)
  (declare (xargs :stobjs fn-cat :guard t :verify-guards nil))
  (if (eq (fn-lpc-at 2 s) :seek)
      (let* ((range (fn-lpc-at 0 s))
             (seq (fn-cnx-view-seq (fn-lpc-at 0 range)
                                  (nfix (fn-lpc-at 1 range))
                                  (nfix (fn-lpc-at 3 range)) fn-cat))
             (facts (and seq (fn-nrf-facts seq fn-cat))))
        (or (not facts) (fn-hnov-p (fn-hf-nov facts))))
    t))

(verify-guards fn-obc-cached-ready-p
  :hints (("Goal" :in-theory (disable fn-cnx-view-seq fn-nrf-facts fn-lpc-at))))

(local
 (defthm fn-obc-cached-pieces-have-shape
   (implies (fn-hnov-p (fn-hf-nov facts))
            (fn-npw-piecesp (fn-npw-column-pieces number facts octets) fn-arena))
   :hints (("Goal" :in-theory
            (e/d (fn-npw-column-pieces fn-npw-piecesp fn-npw-partp
                  fn-hnov-p fn-hnov-internals)
                 (fn-nntp-decimal-field))))))

(local
 (defthm fn-obc-framing-pieces-have-shape
   (and (fn-npw-partp (fn-ovw-status (fn-proto-text * :overview)) fn-arena)
        (fn-npw-partp (fn-ovw-status (fn-ovw-empty-text legacy)) fn-arena)
        (fn-npw-partp '(46 13 10) fn-arena))
   :hints (("Goal" :in-theory
            (enable fn-npw-partp fn-ovw-empty-text fn-ovw-status)))))

(local
 (defthm fn-obc-row-ready-has-shape
   (implies (and (fn-ovw-cursorp range) (fn-rpin-tokenp pin)
                 (fn-npw-piecesp pieces fn-arena))
            (fn-obc-statep (fn-obc-row-ready range pin pieces) fn-arena))
   :hints (("Goal" :do-not-induct t
            :in-theory
            (e/d (fn-obc-statep fn-obc-row-ready fn-obc-make
                  fn-obc-next-range fn-ovw-cursorp fn-ovw-cursor
                  fn-npw-piecesp fn-npw-partp)
                 (fn-rpin-tokenp fn-ovw-status))))))

; ONE is the atomic boundary for a cold throw. Only :parse and :emit read
; arena bytes, each through a one-unit existing cursor. Every returned
; continuation becomes the next call's input; no completed prefix is replayed.
(defun fn-obc-one (s fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                  :guard (and (fn-obc-statep s fn-arena)
                              (fn-obc-source-ready-p s fn-arena fn-cat))))
  (let ((range (nth 0 s)) (pin (nth 1 s)))
    (case (nth 2 s)
      (:seek
       (let ((k (nfix (nth 1 range))) (top (nfix (nth 2 range))))
         (if (< top k)
             (mv nil
                 (fn-obc-make nil pin :emit nil
                   (list (if (nth 5 range)
                             (fn-ovw-status (fn-ovw-empty-text (nth 4 range)))
                           '(46 13 10))) 0))
           (let* ((seq (fn-cnx-view-seq (nth 0 range) k (nth 3 range) fn-cat))
                  (row (and seq (fn-cat-at seq fn-cat)))
                  (facts (and seq (fn-nrf-facts seq fn-cat))))
             (if (or (not seq) (not (posp k))
                     (< *fn-nntp-max-article-number* k)
                     (not (fn-scat-msgid-idp (fn-record-msgid row))))
                 (mv nil (fn-obc-begin (fn-obc-next-range range (nth 5 range)) pin))
               (if facts
                   (if (and (fn-hnov-ok (fn-hf-nov facts))
                            (not (fn-hnov-tomb (fn-hf-nov facts))))
                       (mv nil (fn-obc-row-ready range pin
                                 (fn-npw-column-pieces k facts
                                   (fn-arena-payload-len (nfix (fn-record-payload row)) fn-arena))))
                     (mv nil (fn-obc-begin (fn-obc-next-range range (nth 5 range)) pin)))
                 (mv nil (fn-obc-make range pin :parse
                           (fn-lpc-begin (nfix (fn-record-payload row))
                             (fn-arena-payload-len (nfix (fn-record-payload row)) fn-arena) pin)
                           nil 0))))))))
      (:parse
       (mv-let (parser consumed work verdict)
         (fn-lpc-tick (nth 3 s) 1 fn-arena)
         (declare (ignore consumed work))
         (cond
          ((eq verdict :yield) (mv nil (fn-obc-make range pin :parse parser nil 0)))
          ((and (eq verdict :valid) (not (fn-lpc-tombstonep parser)))
           (mv nil (fn-obc-row-ready range pin
                     (fn-obc-parser-pieces (nth 1 range) parser))))
          (t (mv nil (fn-obc-begin (fn-obc-next-range range (nth 5 range)) pin))))))
      (:emit
       (if (consp (nth 4 s))
           (mv-let (out pieces pos) (fn-npw-one (nth 4 s) (nth 5 s) fn-arena)
             (mv out (fn-obc-make range pin :emit nil pieces pos)))
         (mv nil (and range (fn-obc-begin range pin)))))
      (otherwise (mv nil nil)))))

(verify-guards fn-obc-one
  :hints (("Goal" :do-not-induct t :use fn-obc-statep-fields
           :in-theory
           (e/d (fn-obc-source-ready-p)
                (fn-obc-statep fn-ovw-cursorp fn-lpc-tick fn-npw-one
                    fn-lpc-begin fn-lpc-cursor-bounds-p fn-lpc-tombstonep
                    fn-lpc-at fn-hf-nov fn-obc-next-range fn-obc-row-ready
                    fn-npw-column-pieces fn-obc-parser-pieces fn-lpc-ready-p
                    fn-npw-piecesp fn-cnx-view-seq fn-rpin-tokenp fn-nrf-facts
                    fn-cat-at-is-nth fn-cat-count-is-len nth)))))

; This is a representation theorem, conditional on the selected-row
; premises. Their derivation from the owner's carried F remains a separate
; served-boundary obligation; no validator is added to ONE.
(defthm fn-obc-one-preserves-state-shape
  (implies (and (fn-obc-statep s fn-arena)
                (fn-obc-source-ready-p s fn-arena fn-cat)
                (fn-obc-cached-ready-p s fn-cat))
           (let ((next (mv-nth 1 (fn-obc-one s fn-arena fn-cat))))
             (or (not next) (fn-obc-statep next fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lpc-tick-preserves-ready (s (nth 3 s)) (fuel 1))
                 (:instance fn-lpc-tick-preserves-bounds (s (nth 3 s)) (fuel 1))
                 (:instance fn-npw-one-keeps-pieces
                            (pieces (nth 4 s)) (pos (nth 5 s)))
                 (:instance fn-npw-one-position-natural
                            (pieces (nth 4 s)) (pos (nth 5 s)))
                 (:instance fn-obc-parser-pieces-have-shape
                            (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena)))
                            (number (nth 1 (nth 0 s)))))
           :in-theory
           (e/d (fn-obc-one fn-obc-statep fn-obc-source-ready-p
                 fn-obc-cached-ready-p fn-obc-make fn-obc-begin
                 fn-obc-next-range fn-ovw-cursorp fn-ovw-cursor
                 fn-npw-piecesp fn-npw-partp)
                (fn-npw-one fn-lpc-tick fn-obc-row-ready fn-obc-parser-pieces
                 fn-npw-column-pieces fn-cnx-view-seq fn-cat-at fn-nrf-facts
                 fn-lpc-ready-p fn-lpc-cursor-bounds-p fn-lpc-begin fn-rpin-tokenp
                 fn-lpc-at fn-hf-nov fn-hnov-p fn-hnov-ok fn-hnov-tomb
                 fn-lpc-tombstonep fn-arena-count-is-len
                 fn-arena-payload-len-is-len-nth)))))

(defthm fn-obc-one-output-bounded
  (<= (len (mv-nth 0 (fn-obc-one s fn-arena fn-cat))) 1)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-npw-one-output-bounded
                                   (pieces (nth 4 s)) (pos (nth 5 s))))
                  :in-theory (disable fn-npw-one fn-lpc-tick
                                      fn-obc-row-ready fn-obc-make fn-obc-begin
                                      fn-cnx-view-seq fn-cat-at fn-nrf-facts
                                      fn-npw-column-pieces fn-obc-parser-pieces))))

(defthm fn-obc-one-retains-origin
  (let ((next (mv-nth 1 (fn-obc-one s fn-arena fn-cat))))
    (implies next (equal (nth 1 next) (nth 1 s))))
  :hints (("Goal" :in-theory
           (e/d (fn-obc-one fn-obc-make fn-obc-row-ready fn-obc-begin)
                (fn-npw-one fn-lpc-tick fn-cnx-view-seq fn-cat-at
                 fn-nrf-facts fn-npw-column-pieces fn-obc-parser-pieces)))))

(defthm fn-obc-one-output-octets
  (implies (fn-obc-statep s fn-arena)
           (fn-cbor-octet-listp (mv-nth 0 (fn-obc-one s fn-arena fn-cat))))
  :hints (("Goal" :use ((:instance fn-npw-one-output-octets
                                   (pieces (nth 4 s)) (pos (nth 5 s))))
                  :in-theory (e/d (fn-obc-statep)
                                  (fn-npw-one fn-lpc-tick fn-npw-piecesp
                                   fn-obc-row-ready fn-obc-make fn-obc-begin
                                   fn-cnx-view-seq fn-cat-at fn-nrf-facts
                                   fn-npw-column-pieces fn-obc-parser-pieces)))))

(defthm fn-obc-one-output-true-list
  (implies (fn-obc-statep s fn-arena)
           (true-listp (mv-nth 0 (fn-obc-one s fn-arena fn-cat))))
  :hints (("Goal"
           :use ((:instance fn-npw-one-output-true-list
                            (pieces (nth 4 s)) (pos (nth 5 s))))
           :in-theory (e/d (fn-obc-statep)
                           (fn-npw-one fn-lpc-tick fn-npw-piecesp
                            fn-obc-row-ready fn-obc-make fn-obc-begin
                            fn-cnx-view-seq fn-cat-at fn-nrf-facts
                            fn-npw-column-pieces fn-obc-parser-pieces)))))

; The host's quantum protocol. The host repeats ONE only on :continue,
; saving the returned Q before the next call. A cold throw discards only
; that call, then FINISH commits the previously accumulated prefix and exact
; row continuation. Cold await is off-lock; the next charged scheduling
; attempt starts a new quantum from the saved row continuation.
(defun fn-obc-quantum-begin (s fuel)
  (declare (xargs :guard t))
  (list s (nfix fuel) nil 0))

(defun fn-obc-quantum-status (q)
  (declare (xargs :guard (true-listp q)))
  (if (and (nth 0 q) (posp (nth 1 q))) :continue :ready))

(defun fn-obc-quantum-one (q fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                  :guard (and (true-listp q) (natp (nth 1 q))
                              (true-listp (nth 2 q)) (natp (nth 3 q))
                              (or (null (nth 0 q))
                                  (and (fn-obc-statep (nth 0 q) fn-arena)
                                       (fn-obc-source-ready-p (nth 0 q) fn-arena fn-cat))))))
  (if (eq (fn-obc-quantum-status q) :continue)
      (mv-let (out next) (fn-obc-one (nth 0 q) fn-arena fn-cat)
        (list next (1- (nth 1 q)) (revappend out (nth 2 q)) (+ 1 (nth 3 q))))
    q))

(verify-guards fn-obc-quantum-one
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-obc-one-output-true-list (s (nth 0 q))))
           :in-theory (e/d (fn-obc-quantum-status)
                           (fn-obc-one fn-obc-statep fn-obc-source-ready-p
                            nth fn-obc-one-output-true-list)))))

(defun fn-obc-quantum-finish (q)
  (declare (xargs :guard (and (true-listp q) (true-listp (nth 2 q)))))
  (mv (revappend (nth 2 q) nil) (nth 0 q)))

(defthm fn-obc-quantum-one-consumes-one-unit
  (implies (and (true-listp q) (natp (nth 1 q)) (natp (nth 3 q))
                (equal (fn-obc-quantum-status q) :continue))
           (let ((next (fn-obc-quantum-one q fn-arena fn-cat)))
             (and (equal (nth 1 next) (- (nth 1 q) 1))
                  (equal (nth 3 next) (+ (nth 3 q) 1))
                  (< (nth 1 next) (nth 1 q)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-obc-one))))

(defthm fn-obc-quantum-ready-stays-ready
  (implies (not (equal (fn-obc-quantum-status q) :continue))
           (equal (fn-obc-quantum-one q fn-arena fn-cat) q))
  :hints (("Goal" :in-theory (disable fn-obc-one fn-obc-quantum-status))))

(defthm fn-obc-quantum-one-budget-total-by-definition
  (implies (and (true-listp q) (natp (nth 1 q)) (natp (nth 3 q)))
           (equal (+ (nth 1 (fn-obc-quantum-one q fn-arena fn-cat))
                     (nth 3 (fn-obc-quantum-one q fn-arena fn-cat)))
                  (+ (nth 1 q) (nth 3 q))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-obc-one))))

(defthm fn-obc-quantum-one-output-bound
  (implies (and (true-listp q) (true-listp (nth 2 q))
                (fn-obc-statep (nth 0 q) fn-arena))
           (<= (len (nth 2 (fn-obc-quantum-one q fn-arena fn-cat)))
               (+ 1 (len (nth 2 q)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-obc-one-output-bounded (s (nth 0 q)))
                 (:instance fn-obc-one-output-true-list (s (nth 0 q))))
           :in-theory (disable fn-obc-one fn-obc-statep))))

; Finishing the last successfully returned quantum commits exactly its
; saved prefix and continuation. A later attempted ONE contributes nothing
; unless it returns; this is the algebra used by the pending cold boundary.
(defthm fn-obc-quantum-one-extends-saved-prefix
  (implies (and (true-listp q) (true-listp (nth 2 q))
                (equal (fn-obc-quantum-status q) :continue)
                (fn-obc-statep (nth 0 q) fn-arena))
           (let ((next (fn-obc-quantum-one q fn-arena fn-cat)))
             (and
              (equal (mv-nth 0 (fn-obc-quantum-finish next))
                     (append (mv-nth 0 (fn-obc-quantum-finish q))
                             (mv-nth 0 (fn-obc-one (nth 0 q) fn-arena fn-cat))))
              (equal (mv-nth 1 (fn-obc-quantum-finish next))
                     (mv-nth 1 (fn-obc-one (nth 0 q) fn-arena fn-cat))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-obc-one-output-true-list (s (nth 0 q))))
           :in-theory (e/d (fn-obc-quantum-one fn-obc-quantum-finish)
                           (fn-obc-one fn-obc-quantum-status fn-obc-statep)))))
