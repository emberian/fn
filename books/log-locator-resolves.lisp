; LC -> C22/LB seam, v3 (v2 + the :tombstone raw range). Admissible-shaped DEFINITIONS, not loaded or proved.
; Load AFTER the granted locator book and LB's generated fn-lbc stobj.
; Supplied by LB / LB-LOG-MODEL (C), with LA replacements when LA1/LA6 land:
;   fn-lbc-p, fn-lbc-count (fn-lbc), fn-lbc-at (i fn-lbc segs),
;   fn-lbc-loc0 / fn-lbc-loc1 (i fn-lbc),
;   fn-lb-log-payload (row segs), fn-la-payload-wire (stored-payload),
;   fn-la-tombstone-raw (tombstone) (P10's LA, provisional),
;   fn-lb-log-model-segsp (segs),
;   fn-lb-log-model-read-range (segment offset length segs),
;   fn-lb-log-model-read-home-frame (position segs),
;   fn-lb-log-model-home-frame (row).
; The three log-model readers/encoder return :bad on malformed/missing data.
; They read real bytes and encode independent semantic fields, respectively.
; Supplied by existing books: fn-held-p, fn-rcl-tombstonep (books/reclaim-tombstone). Supplied by GRANTED locator (unchanged):
;   fn-loc-make, fn-locp, fn-loc-segment, fn-loc-offset, fn-loc-len.
; No payload-wire or LA record definition is invented here. No record is dropped:
; reclamation appends a tombstone MOVE retaining the original sequence/home.
; No special missing-record locator exists. Segment id 0 is not reserved.
; fn-lc-pins is an ordinary token -> u64 segment-ID alist, not the HL buffer.
; :verify-guards nil defers guard proofs to the approved landing; it does not
; assert guard verification. No defthm, axiom, attachment or :program event here.
(in-package "ACL2")
(include-book "log-locator")
(include-book "catalog-columns")

; Admission support only: keep the row relation opaque while proving
; that the recursive row index decreases.  The granted forms are intact.
(local (set-default-hints
  '((quote (:in-theory (disable (:definition fn-lc-locator-resolves)))))))


(defun fn-lc-home-position (loc0 loc1)
  (declare (xargs :guard (fn-locp loc0 loc1) :verify-guards nil))
  (list (fn-loc-segment loc0 loc1)
        (+ (fn-loc-offset loc0 loc1) (fn-loc-len loc0 loc1))))

(defun fn-lc-count (fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
  (fn-lbc-count fn-lbc))

(defun fn-lc-segsp (segs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lb-log-model-segsp segs))

(defun fn-lc-read-range (loc0 loc1 segs)
  (declare (xargs :guard (and (fn-locp loc0 loc1) (fn-lc-segsp segs))
                  :verify-guards nil))
  (fn-lb-log-model-read-range (fn-loc-segment loc0 loc1)
                              (fn-loc-offset loc0 loc1)
                              (fn-loc-len loc0 loc1) segs))

(defun fn-lc-read-home-frame (position segs)
  (declare (xargs :guard (and (true-listp position) (fn-lc-segsp segs))
                  :verify-guards nil))
  (fn-lb-log-model-read-home-frame position segs))

(defun fn-lc-expected-home-frame (row)
  (declare (xargs :guard (and (fn-held-p row)
                              (fn-lb-value-treep (fn-lb-log-model-homes row))) :verify-guards nil))
  (fn-lb-log-model-home-frame row))

;; The stored range of a row's payload (LA, P10 10-12): an article is stored in wire
;; form (LA6, fn-la-payload-wire, kinds :article and :move); a reclaimed article's
;; tombstone is stored RAW under PRE kind :tombstone (fn-la-tombstone-raw: the stored
;; range is the payload octets). A tombstone-shaped payload is never admitted
;; (fn-rcl-tombstone-refused-at-carrier-form), so the payload decides the kind.
(defun fn-lc-expected-range (payload)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-rcl-tombstonep payload)
      (fn-la-tombstone-raw payload)
    (fn-la-payload-wire payload)))

(defun fn-lc-bound-row (i fn-lbc segs)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (fn-lbc-p fn-lbc) (natp i)
                              (< i (fn-lc-count fn-lbc)) (fn-lc-segsp segs)
                              (fn-lbc-lc-guardp segs fn-lbc))
                  :verify-guards nil))
  (fn-lbc-at i fn-lbc segs))

(defun fn-lc-locator-resolves (fn-lbc i segs)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (fn-lbc-p fn-lbc) (natp i)
                              (< i (fn-lc-count fn-lbc)) (fn-lc-segsp segs)
                              (fn-lbc-lc-guardp segs fn-lbc))
                  :verify-guards nil))
  (let* ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
         (row (fn-lc-bound-row i fn-lbc segs)))
    (and (fn-locp a b) (fn-held-p row)
         (not (equal (fn-lc-read-range a b segs) :bad))
         (equal (fn-lc-read-range a b segs)
                (fn-lc-expected-range (fn-lb-log-payload row segs)))
         (not (equal (fn-lc-read-home-frame (fn-lc-home-position a b) segs) :bad))
         (equal (fn-lc-read-home-frame (fn-lc-home-position a b) segs)
                (fn-lc-expected-home-frame row)))))

(defun fn-lc-resolve-from (i fn-lbc segs)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (fn-lbc-p fn-lbc) (natp i)
                              (<= i (fn-lc-count fn-lbc)) (fn-lc-segsp segs)
                              (fn-lbc-lc-guardp segs fn-lbc))
                  :measure (nfix (- (fn-lc-count fn-lbc) (nfix i)))
                  :verify-guards nil))
  (if (and (natp i) (< i (fn-lc-count fn-lbc)))
      (and (fn-lc-locator-resolves fn-lbc i segs)
           (fn-lc-resolve-from (+ 1 i) fn-lbc segs))
    t))

(defun fn-lc-locators-resolve (fn-lbc segs)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (fn-lbc-p fn-lbc) (fn-lc-segsp segs)
                              (fn-lbc-lc-guardp segs fn-lbc))
                  :verify-guards nil))
  (fn-lc-resolve-from 0 fn-lbc segs))

(defun fn-lc-pin-tokens (fn-lc-pins)
  (declare (xargs :guard (alistp fn-lc-pins) :verify-guards nil))
  (if (consp fn-lc-pins)
      (cons (caar fn-lc-pins) (fn-lc-pin-tokens (cdr fn-lc-pins)))
    nil))

(defun fn-lc-pin-entries-p (fn-lc-pins)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fn-lc-pins)
      (and (consp (car fn-lc-pins))
           (natp (caar fn-lc-pins))
           (unsigned-byte-p 64 (cdar fn-lc-pins))
           (fn-lc-pin-entries-p (cdr fn-lc-pins)))
    (null fn-lc-pins)))

(defun fn-lc-pins-p (fn-lc-pins)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-lc-pin-entries-p fn-lc-pins)
       (no-duplicatesp-equal (fn-lc-pin-tokens fn-lc-pins))))

(defun fn-lc-pin-references (fn-lc-pins seg)
  (declare (xargs :guard (and (fn-lc-pins-p fn-lc-pins)
                              (unsigned-byte-p 64 seg))
                  :verify-guards nil))
  (if (consp fn-lc-pins)
      (or (equal (cdar fn-lc-pins) seg)
          (fn-lc-pin-references (cdr fn-lc-pins) seg))
    nil))

; LB6 request ownership query: membership alone does not identify THIS reader.
(defun fn-lc-pin-ownedp (token seg fn-lc-pins)
  (declare (xargs :guard (and (natp token) (unsigned-byte-p 64 seg)
                              (fn-lc-pins-p fn-lc-pins))
                  :verify-guards nil))
  (let ((entry (assoc-equal token fn-lc-pins)))
    (and (consp entry) (equal (cdr entry) seg))))
