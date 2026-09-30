(in-package "ACL2")
(include-book "../../books/post-identity-captured-payload-refinement")
(include-book "post-identity-captured-tests")

; Reach comparison entry from the actual mandatory binding-gated begin.
; The fixture supplies one actual parser/observation transition at a time.
(defun pic-pyt-until-entry (c incoming held fuel)
 (declare (xargs :measure (nfix fuel) :verify-guards nil))
 (let ((next (pic-test-drive c incoming held 1)))
  (if (or (zp fuel) (equal (fn-pic-get phase c) :done)
          (and (equal (fn-pic-get phase c) :source-held)
               (or (equal (fn-pic-get phase next) :compare-incoming)
                   (and (equal (fn-pic-get phase next) :done)
                        (equal (fn-pic-get result next) :conflict))))) c
   (pic-pyt-until-entry next incoming held (1- fuel)))))
(defun pic-pyt-before (incoming held)
 (declare (xargs :verify-guards nil))
 (pic-pyt-until-entry
   (fn-pic-begin *pic-test-selected* *pic-test-grant*
     (pic-test-held "<m>" nil *pic-test-binding*) *pic-test-incoming*
     (len incoming) "<m>" *pic-test-binding* nil) incoming held 2000))
(defun pic-pyt-start (incoming held)
 (declare (xargs :verify-guards nil))
 (pic-test-drive (pic-pyt-before incoming held) incoming held 1))
(defun pic-pyt-held-observation (c byte)
 (let ((d (fn-pic-demand c)))
  (list :payload-byte (fn-pic-get selected c) (fn-pic-get grant c) 0 (fn-pic-at 1 d) byte)))

(defthm pic-pyt-entry-feedback-whole-positive
 (let* ((c (pic-pyt-before '(65 66 67) '(65 66 67)))
        (next (mv-nth 1 (fn-pic-feed-funded c :control 1))))
  (and (fn-pic-payload-entryp c '(65 66 67) '(65 66 67))
       (equal (fn-pic-get phase c) :source-held)
       (equal (fn-pic-demand c) :control)
       (equal (fn-pic-get phase next) :compare-incoming)
       (fn-pic-payload-outcomep next '(65 66 67) '(65 66 67))
       (fn-pic-payload-productp next '(65 66 67) '(65 66 67))
       (equal (fn-pic-get incoming-desc next) '(0 0 0))
       (equal (fn-pic-get held-desc next) '(0 0 0))))
 :rule-classes nil)
(defthm pic-pyt-entry-read-source-positive
 (let* ((c (pic-pyt-before *pic-test-stamped* *pic-test-stamped*))
        (next (mv-nth 1 (fn-pic-next c 1 *pic-test-stamped*))))
  (and (fn-pic-payload-entryp c *pic-test-stamped* *pic-test-stamped*)
       (equal (fn-pic-get phase c) :source-held)
       (equal (fn-pic-get phase next) :compare-incoming)
       (fn-pic-payload-outcomep next *pic-test-stamped* *pic-test-stamped*)
       (fn-pic-payload-productp next *pic-test-stamped* *pic-test-stamped*)
       (equal (fn-pic-span-value (fn-pic-get incoming-desc next) *pic-test-stamped*) *pic-test-source*)
       (equal (fn-pic-span-value (fn-pic-get held-desc next) *pic-test-stamped*) *pic-test-source*)))
 :rule-classes nil)
(defthm pic-pyt-entry-feedback-length-conflict-positive
 (let* ((c (pic-pyt-before '(65 66 67) '(65 66)))
        (next (mv-nth 1 (fn-pic-feed-funded c :control 1))))
  (and (fn-pic-payload-entryp c '(65 66 67) '(65 66))
       (equal (fn-pic-get phase c) :source-held)
       (equal (fn-pic-get phase next) :done) (equal (fn-pic-get result next) :conflict)
       (fn-pic-payload-outcomep next '(65 66 67) '(65 66))))
 :rule-classes nil)
(defthm pic-pyt-incoming-read-positive
 (let* ((c (pic-pyt-start '(65 66 67) '(65 66 67)))
        (next (mv-nth 1 (fn-pic-next c 2 '(65 66 67)))))
  (and (fn-pic-payload-productp c '(65 66 67) '(65 66 67))
       (fn-cbor-octet-listp '(65 66 67))
       (fn-pic-payload-outcomep next '(65 66 67) '(65 66 67))
       (fn-pic-payload-productp next '(65 66 67) '(65 66 67))
       (equal (fn-pic-get phase next) :compare-held) (equal (fn-pic-get cached next) 65)))
 :rule-classes nil)
(defthm pic-pyt-held-feedback-positive-resumption
 (let* ((c (mv-nth 1 (fn-pic-next (pic-pyt-start '(65 66 67) '(65 66 67)) 2 '(65 66 67))))
        (observation (pic-pyt-held-observation c 65))
        (next (mv-nth 1 (fn-pic-feed-funded c observation 1))))
  (and (fn-pic-payload-productp c '(65 66 67) '(65 66 67))
       (fn-pic-payload-observationp c observation '(65 66 67) '(65 66 67))
       (fn-pic-payload-outcomep next '(65 66 67) '(65 66 67))
       (fn-pic-payload-productp next '(65 66 67) '(65 66 67))
       (equal (fn-pic-get phase next) :compare-incoming) (equal (fn-pic-get pos next) 1)))
 :rule-classes nil)
(defthm pic-pyt-held-feedback-positive-conflict
 (let* ((c (mv-nth 1 (fn-pic-next (pic-pyt-start '(65 66 67) '(68 66 67)) 2 '(65 66 67))))
        (observation (pic-pyt-held-observation c 68))
        (next (mv-nth 1 (fn-pic-feed-funded c observation 1))))
  (and (fn-pic-payload-productp c '(65 66 67) '(68 66 67))
       (fn-pic-payload-observationp c observation '(65 66 67) '(68 66 67))
       (fn-pic-payload-outcomep next '(65 66 67) '(68 66 67))
       (equal (fn-pic-get phase next) :done) (equal (fn-pic-get result next) :conflict)))
 :rule-classes nil)
(defun pic-pyt-until-complete (c incoming held fuel)
 (declare (xargs :measure (nfix fuel) :verify-guards nil))
 (if (or (zp fuel) (equal (fn-pic-get phase c) :done)
         (and (equal (fn-pic-get phase c) :compare-incoming) (equal (fn-pic-demand c) :control))) c
  (pic-pyt-until-complete (pic-test-drive c incoming held 1) incoming held (1- fuel))))
(defthm pic-pyt-complete-read-positive-groups
 (let* ((c (pic-pyt-until-complete (pic-pyt-start '(65 66 67) '(65 66 67)) '(65 66 67) '(65 66 67) 100))
        (next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (fn-pic-payload-productp c '(65 66 67) '(65 66 67))
       (fn-cbor-octet-listp '(65 66 67))
       (fn-pic-payload-observationp c :control '(65 66 67) '(65 66 67))
       (fn-pic-payload-outcomep next '(65 66 67) '(65 66 67))
       (equal (fn-pic-get phase next) :groups)
       (equal (fn-pic-span-value (fn-pic-get incoming-desc next) '(65 66 67))
              (fn-pic-span-value (fn-pic-get held-desc next) '(65 66 67)))))
 :rule-classes nil)

; Corrupted prefix skips unequal bytes. The exact control observation and
; concrete input domain remain; both actual subjects falsely enter groups.
(defthm pic-pyt-product-removal-corrupted-prefix
 (let* ((c (fn-pic-set pos 3 (pic-pyt-start '(65 66 67) '(65 66 68))))
        (a (mv-nth 1 (fn-pic-feed-funded c :control 1)))
        (b (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (not (fn-pic-payload-productp c '(65 66 67) '(65 66 68)))
       (fn-pic-payload-observationp c :control '(65 66 67) '(65 66 68))
       (fn-cbor-octet-listp '(65 66 67))
       (not (fn-pic-payload-outcomep a '(65 66 67) '(65 66 68)))
       (not (fn-pic-payload-outcomep b '(65 66 67) '(65 66 68)))
       (equal (fn-pic-get phase a) :groups) (equal (fn-pic-get phase b) :groups)))
 :rule-classes nil)
; Mutated held byte passes the typed observation gate but violates exact
; immutable-byte agreement, causing a false conflict on equal payloads.
(defthm pic-pyt-observation-removal-mutated-held-byte
 (let* ((c (mv-nth 1 (fn-pic-next (pic-pyt-start '(65 66 67) '(65 66 67)) 2 '(65 66 67))))
        (observation (pic-pyt-held-observation c 68))
        (next (mv-nth 1 (fn-pic-feed-funded c observation 1))))
  (and (fn-pic-payload-productp c '(65 66 67) '(65 66 67))
       (fn-pic-observation-okp c (fn-pic-demand c) observation)
       (not (fn-pic-payload-observationp c observation '(65 66 67) '(65 66 67)))
       (not (fn-pic-payload-outcomep next '(65 66 67) '(65 66 67)))
       (equal (fn-pic-get result next) :conflict)))
 :rule-classes nil)
; Logical out-of-domain incoming source; the served stobj guard excludes it.
; Product equality is retained, but the reader correctly refuses byte256.
(defthm pic-pyt-octet-domain-removal-corrupted-input
 (let* ((c (pic-pyt-start '(65 66 67) '(65 66 67)))
        (next (mv-nth 1 (fn-pic-next c 2 '(256 66 67)))))
  (and (fn-pic-payload-productp c '(256 66 67) '(256 66 67))
       (not (fn-cbor-octet-listp '(256 66 67)))
       (not (fn-pic-payload-outcomep next '(256 66 67) '(256 66 67)))
       (equal (fn-pic-get result next) :refused)))
 :rule-classes nil)
; Corrupted held capture extent falsely produces a length conflict. Phase is
; retained and both sources are equal, so the conditional entry fails.
(defthm pic-pyt-entry-removal-corrupted-extent
 (let* ((c (fn-pic-set held-n 4 (pic-pyt-before '(65 66 67) '(65 66 67))))
        (next (mv-nth 1 (fn-pic-feed-funded c :control 1)))
        (read-next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (not (fn-pic-payload-entryp c '(65 66 67) '(65 66 67)))
       (equal (fn-pic-get phase c) :source-held)
       (equal (fn-pic-get phase next) :done) (equal (fn-pic-get result next) :conflict)
       (not (fn-pic-payload-outcomep next '(65 66 67) '(65 66 67)))
       (equal (fn-pic-get phase read-next) :done) (equal (fn-pic-get result read-next) :conflict)
       (not (fn-pic-payload-outcomep read-next '(65 66 67) '(65 66 67)))))
 :rule-classes nil)
; At zero fuel, both subjects retain a corrupt existing comparison. The
; complete entry predicate remains, while only its source-held phase fails.
(defthm pic-pyt-entry-phase-removal-corrupted-existing-comparison
 (let* ((c (fn-pic-set pos 3 (pic-pyt-start '(65 66 67) '(65 66 68))))
        (a (mv-nth 1 (fn-pic-feed-funded c nil 0)))
        (b (mv-nth 1 (fn-pic-next c 0 '(65 66 67)))))
  (and (fn-pic-payload-entryp c '(65 66 67) '(65 66 68))
       (not (equal (fn-pic-get phase c) :source-held))
       (equal (fn-pic-get phase a) :compare-incoming) (equal (fn-pic-get phase b) :compare-incoming)
       (not (fn-pic-payload-outcomep a '(65 66 67) '(65 66 68)))
       (not (fn-pic-payload-outcomep b '(65 66 67) '(65 66 68)))))
 :rule-classes nil)

; A missing held inverse selects the exact whole-octet fallback for both
; descriptors even though the incoming source descriptor exists.
(defthm pic-pyt-entry-read-one-inverse-fallback-positive
 (let* ((c (pic-pyt-before *pic-test-stamped* *pic-test-source*))
        (next (mv-nth 1 (fn-pic-next c 1 *pic-test-stamped*))))
  (and (fn-pic-payload-entryp c *pic-test-stamped* *pic-test-source*)
       (equal (fn-pic-get phase c) :source-held)
       (fn-pic-get incoming-desc c)
       (equal (fn-pic-get phase next) :done) (equal (fn-pic-get result next) :conflict)
       (equal (fn-pic-get incoming-desc next) '(0 0 0))
       (equal (fn-pic-get held-desc next) '(0 0 0))
       (fn-pic-payload-outcomep next *pic-test-stamped* *pic-test-source*)))
 :rule-classes nil)
