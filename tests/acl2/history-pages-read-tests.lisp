; fn: teeth for books/history-pages-exec.lisp and books/history-pages-read.lisp
; (lane arena-store-2, 2026-09-28).
;
; What this book is evidence FOR.  The open's header check and the row read
; the host calls (need-verdicts, never a fill) answer the history, over a
; page store state whose verified pages hold the image's words.  A ground
; history's image is installed as the stobj's words (as the host's fills
; leave them); each keystone gets a positive witness asserting its complete
; antecedent and conclusion, and per hypothesis a witness where the
; retained ones hold, the omitted one fails and the conclusion fails, with a
; must-fail-checked of the weakened statement.  Named exceptions: the
; `fn-hp-okp' u64 bounds (need 2^64 octets); and `fn-hp-okp' as a whole in
; `fn-hp-x-header-is-image', inherited from `adt-ser-header-reads' (the
; header of a history whose events are not trees still reads back its N and
; regions: no ground counterexample; kept, not witnessed).
(in-package "ACL2")
(include-book "../../books/history-pages-read")
(include-book "must-fail-checked")

(local (in-theory (enable fn-hp-vhold-is-x)))

(assert-event
 (and (eq (symbol-class 'fn-hp-x-at (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hp-x-header (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hp-at-core (w state)) :common-lisp-compliant)))

(defconst *hrt-h* (list (list :retained 1 "<a@x>" (list 1 2 3) "subject line") (list :other 7 nil)))
(defconst *hrt-iw* (fn-hp-iw *hrt-h* 0))
(defconst *hrt-np* (fn-hp-npages *hrt-h* 0))
(defconst *hrt-v2* (make-list *hrt-np* :initial-element 2))

(defun hrt-mem (w v)
  ; a page store state: words W, page flags V, every table page verified
  (update-nth *pgs-wi* w
              (update-nth *pgs-vi* v
                          (update-nth *pgs-di* (make-list *hrt-np* :initial-element 0)
                                      (update-nth *pgs-tvi* '(2) (list nil nil nil nil nil nil))))))

(defconst *hrt-lens* (fn-hp-lens *hrt-h* 0))
(defconst *hrt-starts* (fn-hp-starts *hrt-h* 0))
; the first word of row 1's pool entry
(defconst *hrt-row1-word* (+ (* 2048 (nth 4 *hrt-starts*)) (floor (fn-hp-pes-len (take 1 *hrt-h*)) 8)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-x-header-is-image.

(defthm hrt-header-w
  (let ((mem (hrt-mem *hrt-iw* *hrt-v2*)))
    (and (fn-hp-okp *hrt-h* 0) (equal *hrt-np* (fn-hp-npages *hrt-h* 0))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-h* 0))
         (equal (mv-nth 0 (fn-hp-x-header *hrt-np* mem)) :ok)
         (equal (mv-nth 1 (fn-hp-x-header *hrt-np* mem))
                (list :ok (len *hrt-h*) (fn-hp-lens *hrt-h* 0) (fn-hp-starts *hrt-h* 0)))))
  :rule-classes nil)

; The schema-digest mismatch is a named refusal: another schema's image
; (word 2 of the header changed) is refused :schema, never rebuilt.
(defthm hrt-header-schema-refused
  (let ((mem (hrt-mem (update-nth 2 99 *hrt-iw*) *hrt-v2*)))
    (and (equal (mv-nth 0 (fn-hp-x-header *hrt-np* mem)) :ok)
         (equal (mv-nth 1 (fn-hp-x-header *hrt-np* mem)) (list :refused :schema))))
  :rule-classes nil)

; Removal of the verified-pages relation: page 0 verified but its N word
; changed; the header answers another N.
(defthm hrt-header-vhold-removal
  (let ((mem (hrt-mem (update-nth 6 1 *hrt-iw*) *hrt-v2*)))
    (and (fn-hp-okp *hrt-h* 0) (equal *hrt-np* (fn-hp-npages *hrt-h* 0))
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-h* 0)))
         (equal (mv-nth 0 (fn-hp-x-header *hrt-np* mem)) :ok)
         (not (equal (mv-nth 1 (fn-hp-x-header *hrt-np* mem))
                     (list :ok (len *hrt-h*) (fn-hp-lens *hrt-h* 0) (fn-hp-starts *hrt-h* 0))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
  (defthm hrt-false-header-without-vhold
    (implies (and (fn-hp-okp h salt) (equal npages (fn-hp-npages h salt))
                  (equal (mv-nth 0 (fn-hp-x-header npages pgs-mem)) :ok))
             (equal (mv-nth 1 (fn-hp-x-header npages pgs-mem))
                    (list :ok (len h) (fn-hp-lens h salt) (fn-hp-starts h salt)))))))

; Removal of the verdict: page 0 not verified; the header answers a need.
(defthm hrt-header-verdict-removal
  (let ((mem (hrt-mem *hrt-iw* (update-nth 0 0 *hrt-v2*))))
    (and (fn-hp-okp *hrt-h* 0) (equal *hrt-np* (fn-hp-npages *hrt-h* 0))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-h* 0))
         (not (equal (mv-nth 0 (fn-hp-x-header *hrt-np* mem)) :ok))
         (not (equal (mv-nth 1 (fn-hp-x-header *hrt-np* mem))
                     (list :ok (len *hrt-h*) (fn-hp-lens *hrt-h* 0) (fn-hp-starts *hrt-h* 0))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
  (defthm hrt-false-header-without-verdict
    (implies (and (fn-hp-okp h salt) (equal npages (fn-hp-npages h salt))
                  (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt)))
             (equal (mv-nth 1 (fn-hp-x-header npages pgs-mem))
                    (list :ok (len h) (fn-hp-lens h salt) (fn-hp-starts h salt)))))))

; Removal of the page count: the store claims one page more.
(defthm hrt-header-npages-removal
  (let ((mem (hrt-mem *hrt-iw* *hrt-v2*)))
    (and (fn-hp-okp *hrt-h* 0) (not (equal (+ 1 *hrt-np*) (fn-hp-npages *hrt-h* 0)))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-h* 0))
         (equal (mv-nth 0 (fn-hp-x-header (+ 1 *hrt-np*) mem)) :ok)
         (equal (mv-nth 1 (fn-hp-x-header (+ 1 *hrt-np*) mem)) (list :refused :length))))
  :rule-classes nil)

(must-fail-checked
 (with-prover-step-limit 30000
  (defthm hrt-false-header-without-npages
    (implies (and (fn-hp-okp h salt)
                  (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                  (equal (mv-nth 0 (fn-hp-x-header npages pgs-mem)) :ok))
             (equal (mv-nth 1 (fn-hp-x-header npages pgs-mem))
                    (list :ok (len h) (fn-hp-lens h salt) (fn-hp-starts h salt)))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-x-at-is-nth.

(defthm hrt-at-w
  (let ((mem (hrt-mem *hrt-iw* *hrt-v2*)))
    (and (fn-hp-okp *hrt-h* 0) (natp 1) (< 1 (len *hrt-h*))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-h* 0))
         (equal (mv-nth 0 (fn-hp-x-at 1 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem)) :ok)
         (equal (mv-nth 1 (fn-hp-x-at 1 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem))
                (list :ok (nth 1 *hrt-h*)))))
  :rule-classes nil)

; Removal of the verified-pages relation: a verified pool page carries a
; changed word; the read does not answer the event.
(defthm hrt-at-vhold-removal
  (let ((mem (hrt-mem (update-nth *hrt-row1-word* 7 *hrt-iw*) *hrt-v2*)))
    (and (fn-hp-okp *hrt-h* 0) (natp 1) (< 1 (len *hrt-h*))
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-h* 0)))
         (equal (mv-nth 0 (fn-hp-x-at 1 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem)) :ok)
         (not (equal (mv-nth 1 (fn-hp-x-at 1 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem))
                     (list :ok (nth 1 *hrt-h*))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
  (defthm hrt-false-at-without-vhold
    (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h))
                  (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem)) :ok))
             (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem))
                    (list :ok (nth seq h)))))))

; Removal of the verdict: the MKEY column's page is not verified; the read
; answers a need and no event.
(defthm hrt-at-verdict-removal
  (let ((mem (hrt-mem *hrt-iw* (update-nth 1 0 *hrt-v2*))))
    (and (fn-hp-okp *hrt-h* 0) (natp 1) (< 1 (len *hrt-h*))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-h* 0))
         (not (equal (mv-nth 0 (fn-hp-x-at 1 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem)) :ok))
         (not (equal (mv-nth 1 (fn-hp-x-at 1 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem))
                     (list :ok (nth 1 *hrt-h*))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
  (defthm hrt-false-at-without-verdict
    (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h))
                  (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt)))
             (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem))
                    (list :ok (nth seq h)))))))

; Removal of (< seq (len h)): past the end the read refuses :seq.
(defthm hrt-at-seq-removal
  (let ((mem (hrt-mem *hrt-iw* *hrt-v2*)))
    (and (fn-hp-okp *hrt-h* 0) (natp 2) (not (< 2 (len *hrt-h*)))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-h* 0))
         (equal (mv-nth 0 (fn-hp-x-at 2 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem)) :ok)
         (not (equal (mv-nth 1 (fn-hp-x-at 2 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem))
                     (list :ok (nth 2 *hrt-h*))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
  (defthm hrt-false-at-without-bound
    (implies (and (fn-hp-okp h salt) (natp seq)
                  (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                  (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem)) :ok))
             (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem))
                    (list :ok (nth seq h)))))))

; Removal of (natp seq): -1 reads the words just before each column.
(defthm hrt-at-natp-removal
  (let ((mem (hrt-mem *hrt-iw* *hrt-v2*)))
    (and (fn-hp-okp *hrt-h* 0) (not (natp -1)) (< -1 (len *hrt-h*))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-h* 0))
         (equal (mv-nth 0 (fn-hp-x-at -1 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem)) :ok)
         (not (equal (mv-nth 1 (fn-hp-x-at -1 0 (len *hrt-h*) *hrt-lens* *hrt-starts* mem))
                     (list :ok (nth -1 *hrt-h*))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
  (defthm hrt-false-at-without-natp
    (implies (and (fn-hp-okp h salt) (< seq (len h))
                  (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                  (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem)) :ok))
             (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem))
                    (list :ok (nth seq h)))))))

; Removal of (fn-hp-okp h salt): a rational is no tree; over its own image
; the read does not answer it.
(defconst *hrt-bad* (list 1/2))
(defthm hrt-at-okp-removal
  (let ((mem (hrt-mem (fn-hp-iw *hrt-bad* 0)
                      (make-list (fn-hp-npages *hrt-bad* 0) :initial-element 2))))
    (and (not (fn-hp-okp *hrt-bad* 0)) (natp 0) (< 0 (len *hrt-bad*))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hrt-bad* 0))
         (equal (mv-nth 0 (fn-hp-x-at 0 0 1 (fn-hp-lens *hrt-bad* 0) (fn-hp-starts *hrt-bad* 0) mem)) :ok)
         (not (equal (mv-nth 1 (fn-hp-x-at 0 0 1 (fn-hp-lens *hrt-bad* 0) (fn-hp-starts *hrt-bad* 0) mem))
                     (list :ok (nth 0 *hrt-bad*))))))
  :rule-classes nil)
(must-fail-checked
 (with-prover-step-limit 30000
  (defthm hrt-false-at-without-okp
    (implies (and (natp seq) (< seq (len h))
                  (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                  (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem)) :ok))
             (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem))
                    (list :ok (nth seq h)))))))
