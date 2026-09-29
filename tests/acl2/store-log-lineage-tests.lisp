; Witnesses and teeth for books/store-log-lineage (lane store-lineage, PRF-979):
; the open's lineage decision over a segment's head, and the
; HYPOTHESIS-REMOVAL WITNESS over the lineage clause -- without it the old
; open (the plan, the scan of the empty first suffix segment, the splice
; probe) decides the same for the store's own GENESIS and a fork's; with it
; the fork's is refused :foreign-lineage by name.
;
; Frames are computed under the digest's attachment (books/frame-trailer):
; assert-event, never a defconst.
(in-package "ACL2")
(include-book "../../books/store-log-lineage")
(include-book "../../books/frame-trailer")

(defun slgl-unit () (declare (xargs :guard t)) 4)
(defun slgl-max () (declare (xargs :guard t)) 4096)
(defun slgl-t0 () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
; The closed segment's last trailer as this log holds it (P), and as a fork's
; diverged history reached it (Q): two chain values, equal counts behind them.
(defun slgl-p () (declare (xargs :guard t)) (make-list 32 :initial-element 7))
(defun slgl-q () (declare (xargs :guard t)) (make-list 32 :initial-element 9))
(defun slgl-k () (declare (xargs :guard t)) 2)
; Segment 2 as the rotation wrote it from P: the head alone (the empty suffix).
(defun slgl-head () (declare (xargs :guard t :verify-guards nil))
  (fn-lgl-rotation-entry (slgl-p) (slgl-k) (slgl-unit)))
; The F row's GENESIS this store's checkpoint carries, and the fork's.
(defun slgl-g () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-trailer (fn-lgl-rotation-frame (slgl-p) (slgl-k))))
(defun slgl-g-fork () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-trailer (fn-lgl-rotation-frame (slgl-q) (slgl-k))))
; A record entry after the head: the non-empty suffix.
(defun slgl-suffix () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-entry (slgl-g) (list '(1 2 3)) (slgl-unit)))

; -----------------------------------------------------------------------------
; 1. The entry as written: readable, sized, opening to what was sealed.
(assert-event
 (and (fn-frame-digestp (slgl-p)) (fn-frame-digestp (slgl-q)) (fn-lgl-indexp (slgl-k))
      (not (equal (slgl-p) (slgl-q)))
      (equal (len (fn-lgl-rotation-frame (slgl-p) (slgl-k))) (+ 42 36))
      (equal (len (slgl-head)) (fn-lgl-head-len (slgl-unit)))
      (equal (mod (len (slgl-head)) (slgl-unit)) 0)
      (fn-lgl-headed-p (slgl-head) (slgl-max))
      (equal (fn-lgl-head-prev (slgl-head) (slgl-max)) (slgl-p))
      (equal (fn-lgl-head-index (slgl-head) (slgl-max)) (fn-cbor-u32-bytes (slgl-k)))
      (equal (fn-lgl-head-trailer (slgl-head)) (slgl-g))
      (fn-frame-digestp (slgl-g))
      (not (equal (slgl-g) (slgl-g-fork)))))

; -----------------------------------------------------------------------------
; 2. Reachable positive witness of fn-lgl-open-of-rotated-segment: the whole
; antecedent (P a digest, K an index above 1, MAX in range) and the whole
; conclusion, for the empty suffix and for a suffix of one record entry.
(assert-event
 (and (fn-frame-digestp (slgl-p)) (fn-lgl-indexp (slgl-k)) (not (equal (slgl-k) 1))
      (natp (slgl-max)) (<= *fn-lgl-payload-octets* (slgl-max)) (<= (slgl-max) *fn-frame-max-payload*)
      (equal (fn-lgl-open (slgl-k) (slgl-g) (slgl-head) (slgl-t0) (slgl-max)) nil)
      (equal (fn-lgl-open (slgl-k) (slgl-g-fork) (slgl-head) (slgl-t0) (slgl-max))
             '(:refused :foreign-lineage))
      (equal (fn-lgl-open (slgl-k) (slgl-g) (append (slgl-head) (slgl-suffix)) (slgl-t0) (slgl-max)) nil)
      (equal (fn-lgl-open (slgl-k) (slgl-g-fork) (append (slgl-head) (slgl-suffix)) (slgl-t0) (slgl-max))
             '(:refused :foreign-lineage))))

; The scan of the segment from the head's claimed predecessor: the entry is
; an entry of the chain with no records, and the records after it are the
; suffix's, chained from GENESIS (what the host streams after the decision).
; Holds once books/store-log.lisp admits kind 3 (READY 2 of the lane); until
; then the scan stops before the head -- asserted as the format change lands.

; -----------------------------------------------------------------------------
; 3. THE TOOTH: hypothesis-removal witness over the lineage clause.
; Without it the open's decisions over this store's EMPTY first suffix
; segment -- the plan over journal/, the scan from GENESIS, the splice probe
; -- are the same for the store's own GENESIS and the fork's: nothing in them
; reads GENESIS against the log.  With it (fn-lgl-open) the fork's is refused
; and the store's own accepted, over the same log.
(assert-event
 (let ((names (list "000001.log" "000002.log")))
   (and (equal (fn-lgs-open-plan names (slgl-k)) '(:scan (2) (1)))
        (equal (fn-lg-scan nil (slgl-g) (slgl-unit) (slgl-max))
               (fn-lg-scan nil (slgl-g-fork) (slgl-unit) (slgl-max)))
        (equal (fn-lg-scan nil (slgl-g) (slgl-unit) (slgl-max)) '(nil . 0))
        (equal (fn-lgs-chain-broken-p nil (slgl-g) (slgl-unit) (slgl-max))
               (fn-lgs-chain-broken-p nil (slgl-g-fork) (slgl-unit) (slgl-max)))
        (equal (fn-lgs-chain-broken-p nil (slgl-g) (slgl-unit) (slgl-max)) nil)
        ; the retained decisions still hold over the headed segment
        (equal (fn-lgs-open-plan names (slgl-k)) '(:scan (2) (1)))
        ; the clause: the same log, the two GENESIS values, decided apart
        (equal (fn-lgl-open (slgl-k) (slgl-g) (slgl-head) (slgl-t0) (slgl-max)) nil)
        (equal (fn-lgl-open (slgl-k) (slgl-g-fork) (slgl-head) (slgl-t0) (slgl-max))
               '(:refused :foreign-lineage)))))

; -----------------------------------------------------------------------------
; 4. Corrupted-state witnesses (labelled apart from the lineage tooth): a
; head that is not a readable rotation entry, an empty K a checkpoint names,
; a head naming another index, and segment 1's genesis.
(assert-event
 (and (equal (fn-lgl-open (slgl-k) (slgl-g) nil (slgl-t0) (slgl-max))
             '(:refused :segment-head-damaged))
      (equal (fn-lgl-open (slgl-k) (slgl-g)
                          (cons (logxor 1 (car (slgl-head))) (cdr (slgl-head)))
                          (slgl-t0) (slgl-max))
             '(:refused :segment-head-damaged))
      (equal (fn-lgl-open (slgl-k) (slgl-g) (slgl-suffix) (slgl-t0) (slgl-max))
             '(:refused :segment-head-damaged))
      (equal (fn-lgl-open 3 (slgl-g) (slgl-head) (slgl-t0) (slgl-max))
             '(:refused :segment-misnamed))
      (equal (fn-lgl-open 1 (slgl-t0) nil (slgl-t0) (slgl-max)) nil)
      (equal (fn-lgl-open 1 (slgl-g) nil (slgl-t0) (slgl-max))
             '(:refused :foreign-lineage))))

; -----------------------------------------------------------------------------
; 5. fn-lgl-fork-refused and fn-lgl-accepted-shares-lineage carry the per-pair
; hypotheses fn-lgl-trailer-distinct and fn-lgl-chain-distinct as
; fn-hib-chain-distinct does: hypotheses on the two frames (segments) actually
; compared, not computable facts; their consequents here are asserted in 1
; (the two trailers differ) and 2 (the fork's is refused).
