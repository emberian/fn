(in-package "ACL2")
(include-book "../../books/over-byte-full-run-relation")
; Ground logical recursion only; this is a prover limit, not runtime funding.
(local (set-rewrite-stack-limit 10000))

(defconst *obct-source*
 (append (fn-record-string-octets "Subject: a") '(13 10)
         (fn-record-string-octets "From: c") '(13 10)
         (fn-record-string-octets "Date: d") '(13 10)
         (fn-record-string-octets "Message-ID: <e@x>") '(13 10 13 10 122 13 10)))
(defun obct-token ()
 (mv-let (owners pins status) (fn-rpin-step nil '(31 nil nil) '(:acquire 7))
  (declare (ignore pins status)) (fn-rpin-token 7 owners)))
(defun obct-row (h number facts)
 (fn-held-make 0 1 0 "<e@x>" h '("fn.test") "o" "s" "e" 1 5 facts
               (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0)
               (list (cons "fn.test" number)) nil))
(defun obct-begin (v)
 (fn-obc-begin (fn-ovw-cursor "fn.test" 1 4 v nil t) (obct-token)))

(defun-nx obct-one-ready-conclusion (s fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (fn-obc-semantic-ready-p (mv-nth 1 (fn-obc-one s fn-arena fn-cat)) fn-arena fn-cat))
(defun-nx obct-run-conclusion (s steps fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (let ((result (fn-obc-source-run s steps fn-arena fn-cat)))
  (and (true-listp (mv-nth 0 result))
       (fn-obc-semantic-ready-p (mv-nth 1 result) fn-arena fn-cat)
       (equal (append (mv-nth 0 result)
                      (fn-obc-actual-old-residual (mv-nth 1 result) fn-arena fn-cat))
              (fn-obc-actual-old-residual s fn-arena fn-cat)))))

; Actual BEGIN→ONE→parser ONE, including every retained carry premise.
; This is a fixed logical source fixture, not an ingress/publication claim.
(defthm obct-positive-seek-and-parser-carry
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row 0 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (obct-begin 7)) (next (mv-nth 1 (fn-obc-one s fn-arena fn-cat))))
  (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
       (fn-cat-p fn-cat) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (fn-scol-okp fn-arena fn-cat)
       (obct-one-ready-conclusion s fn-arena fn-cat)
       (equal (nth 2 next) :parse)
       (obct-one-ready-conclusion next fn-arena fn-cat)
       (obct-run-conclusion s 1 fn-arena fn-cat)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (s n a c) (fn-obc-source-run s n a c)))
                  :in-theory (enable fn-obc-source-run))))

(defthm obct-positive-complete-multirow-hole-invalid-and-cached
 (let* ((invalid '(120 13 10))
        (fn-arena (list *obct-source* invalid *obct-source*))
        (fn-cat (list (obct-row 0 1 (fn-hf-make (len *obct-source*) nil 0 nil))
                      (obct-row 1 2 (fn-held-facts-of invalid))
                      (obct-row 2 3 (fn-held-facts-of *obct-source*))))
        (s (obct-begin 7)) (result (fn-obc-source-run s 200 fn-arena fn-cat)))
  (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
       (fn-cat-p fn-cat) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (fn-scol-okp fn-arena fn-cat)
       (obct-run-conclusion s 200 fn-arena fn-cat)
       (not (mv-nth 1 result))
       (equal (mv-nth 0 result) (fn-obc-actual-old-residual s fn-arena fn-cat))
       (equal (fn-cat-count fn-cat) 3) (equal (nth 3 (nth 0 s)) 7)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (s n a c) (fn-obc-source-run s n a c)))
                  :in-theory (enable fn-obc-source-run))))

(defthm obct-without-carried-semantic-state-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row 0 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (fn-obc-make (fn-ovw-cursor "fn.test" 0 4 7 nil t)
                        (obct-token) :parse (fn-lpc-begin 0 (len *obct-source*) (obct-token)) nil 0)))
  (and (not (fn-obc-semantic-ready-p s fn-arena fn-cat))
       (fn-cat-p fn-cat) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (fn-scol-okp fn-arena fn-cat)
       (not (obct-one-ready-conclusion s fn-arena fn-cat))
       (not (obct-run-conclusion s 1 fn-arena fn-cat))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (s n a c) (fn-obc-source-run s n a c)))
                  :in-theory (enable fn-obc-source-run))))

(defthm obct-without-catalog-shape-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row :not-handle 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (obct-begin 7)))
  (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
       (not (fn-cat-p fn-cat)) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (fn-scol-okp fn-arena fn-cat)
       (not (obct-one-ready-conclusion s fn-arena fn-cat))
       (not (obct-run-conclusion s 1 fn-arena fn-cat))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (s n a c) (fn-obc-source-run s n a c)))
                  :in-theory (enable fn-obc-source-run))))

(defthm obct-without-source-handle-bounds-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row 1 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (obct-begin 7)))
  (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
       (fn-cat-p fn-cat) (not (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
       (fn-scol-okp fn-arena fn-cat)
       (not (obct-one-ready-conclusion s fn-arena fn-cat))
       (not (obct-run-conclusion s 1 fn-arena fn-cat))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (s n a c) (fn-obc-source-run s n a c)))
                  :in-theory (enable fn-obc-source-run))))

(defthm obct-without-carried-column-source-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (bad-facts (fn-hf-make (len *obct-source*) nil 0
                     (list nil nil nil (fn-hnov-make nil t 777 "c" "d" "<e@x>" ""))))
        (fn-cat (list (obct-row 0 1 bad-facts))) (s (obct-begin 7)))
  (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
       (fn-cat-p fn-cat) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (not (fn-scol-okp fn-arena fn-cat))
       (not (obct-one-ready-conclusion s fn-arena fn-cat))
       (not (obct-run-conclusion s 1 fn-arena fn-cat))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (s n a c) (fn-obc-source-run s n a c)))
                  :in-theory (enable fn-obc-source-run))))

(defun-nx obct-output-residual-conclusion (s fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (let ((result (fn-obc-one s fn-arena fn-cat)))
  (equal (append (mv-nth 0 result)
                 (fn-obc-actual-old-residual (mv-nth 1 result) fn-arena fn-cat))
         (fn-obc-actual-old-residual s fn-arena fn-cat))))
(defun-nx obct-quantum-conclusion (q fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (equal (fn-obc-quantum-old-reply (fn-obc-quantum-one q fn-arena fn-cat) fn-arena fn-cat)
        (fn-obc-quantum-old-reply q fn-arena fn-cat)))

(defthm obct-positive-actual-quantum-prefix-and-residual
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row 0 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (obct-begin 7)) (q (list s 3 '(10 13 120) 2)))
  (and (fn-obc-semantic-ready-p s fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat)
       (equal (fn-obc-quantum-status q) :continue)
       (obct-output-residual-conclusion s fn-arena fn-cat)
       (obct-quantum-conclusion q fn-arena fn-cat)
       (equal (nth 2 (fn-obc-quantum-one q fn-arena fn-cat)) '(10 13 120))
       (equal (nth 3 (fn-obc-quantum-one q fn-arena fn-cat)) 3)))
 :rule-classes nil)

(defthm obct-residual-and-quantum-without-semantic-carry-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row 0 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (range (fn-ovw-cursor "fn.test" 1 1 7 nil t))
        (s (fn-obc-make range (obct-token) :parse
             (fn-lpc-feed (append *obct-source* '(122 13 10))
               (fn-lpc-begin 0 (+ 3 (len *obct-source*)) (obct-token))) nil 0))
        (q (list s 1 '(10 13 120) 2)))
  (and (not (fn-obc-semantic-ready-p s fn-arena fn-cat))
       (fn-scol-okp fn-arena fn-cat)
       (not (obct-output-residual-conclusion s fn-arena fn-cat))
       (not (obct-quantum-conclusion q fn-arena fn-cat))))
 :rule-classes nil)

(defthm obct-residual-and-quantum-without-columns-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (bad-facts (fn-hf-make (len *obct-source*) nil 0
                     (list nil nil nil (fn-hnov-make nil t 777 "c" "d" "<e@x>" ""))))
        (fn-cat (list (obct-row 0 1 bad-facts))) (s (obct-begin 7))
        (q (list s 1 '(10 13 120) 2)))
  (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
       (not (fn-scol-okp fn-arena fn-cat))
       (not (obct-output-residual-conclusion s fn-arena fn-cat))
       (not (obct-quantum-conclusion q fn-arena fn-cat))))
 :rule-classes nil)

(defun-nx obct-selection-conclusion (s fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (fn-obc-parse-selection-p (mv-nth 1 (fn-obc-one s fn-arena fn-cat)) fn-arena fn-cat))

(defthm obct-positive-begin-and-selection
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row 0 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (range (fn-ovw-cursor "fn.test" 1 4 7 nil t)) (pin (obct-token))
        (s (fn-obc-begin range pin)))
  (and (fn-ovw-cursorp range) (fn-rpin-tokenp pin)
       (fn-obc-semantic-ready-p s fn-arena fn-cat)
       (fn-obc-parse-selection-p s fn-arena fn-cat)
       (fn-obc-source-ready-p s fn-arena fn-cat) (fn-arena-p fn-arena)
       (or (not (equal (nth 2 s) :seek)) (natp (nth 3 (nth 0 s))))
       (obct-selection-conclusion s fn-arena fn-cat)))
 :rule-classes nil)

(defthm obct-begin-without-cursor-corrupted-state
 (let* ((range (fn-ovw-cursor "fn.test" 1 4 :bad nil t)) (pin (obct-token))
        (fn-arena nil) (fn-cat nil))
  (and (not (fn-ovw-cursorp range)) (fn-rpin-tokenp pin)
       (not (fn-obc-semantic-ready-p (fn-obc-begin range pin) fn-arena fn-cat))))
 :rule-classes nil)
(defthm obct-begin-without-pin-corrupted-state
 (let* ((range (fn-ovw-cursor "fn.test" 1 4 7 nil t)) (pin :bad)
        (fn-arena nil) (fn-cat nil))
  (and (fn-ovw-cursorp range) (not (fn-rpin-tokenp pin))
       (not (fn-obc-semantic-ready-p (fn-obc-begin range pin) fn-arena fn-cat))))
 :rule-classes nil)

(defthm obct-selection-without-selection-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row 0 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (fn-obc-make (fn-ovw-cursor "fn.test" 0 4 7 nil t) (obct-token) :parse (fn-lpc-begin 0 (len *obct-source*) (obct-token)) nil 0)))
  (and (not (fn-obc-parse-selection-p s fn-arena fn-cat))
       (fn-obc-source-ready-p s fn-arena fn-cat)
       (fn-arena-p fn-arena)
       (or (not (equal (nth 2 s) :seek)) (natp (nth 3 (nth 0 s))))
       (not (obct-selection-conclusion s fn-arena fn-cat))))
 :rule-classes nil)

(defthm obct-selection-without-source-ready-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row :not-handle 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (obct-begin 7)))
  (and (fn-obc-parse-selection-p s fn-arena fn-cat)
       (not (fn-obc-source-ready-p s fn-arena fn-cat))
       (fn-arena-p fn-arena)
       (or (not (equal (nth 2 s) :seek)) (natp (nth 3 (nth 0 s))))
       (not (obct-selection-conclusion s fn-arena fn-cat))))
 :rule-classes nil)

(defthm obct-selection-without-arena-corrupted-state
 (let* ((fn-arena (list (list 777)))
        (fn-cat (list (obct-row 0 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (obct-begin 7)))
  (and (fn-obc-parse-selection-p s fn-arena fn-cat)
       (fn-obc-source-ready-p s fn-arena fn-cat)
       (not (fn-arena-p fn-arena))
       (or (not (equal (nth 2 s) :seek)) (natp (nth 3 (nth 0 s))))
       (not (obct-selection-conclusion s fn-arena fn-cat))))
 :rule-classes nil)

(defthm obct-selection-without-seek-view-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row :not-handle 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (obct-begin 1/2)))
  (and (fn-obc-parse-selection-p s fn-arena fn-cat)
       (fn-obc-source-ready-p s fn-arena fn-cat)
       (fn-arena-p fn-arena)
       (not (or (not (equal (nth 2 s) :seek)) (natp (nth 3 (nth 0 s)))))
       (not (obct-selection-conclusion s fn-arena fn-cat))))
 :rule-classes nil)

(defthm obct-positive-carried-columns-source
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row 0 1 (fn-held-facts-of *obct-source*))))
        (s (obct-begin 7)))
  (and (fn-scol-okp fn-arena fn-cat)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)))
 :rule-classes nil)
(defthm obct-carried-columns-source-without-columns-corrupted-state
 (let* ((fn-arena (list *obct-source*))
        (bad-facts (fn-hf-make (len *obct-source*) nil 0
                     (list nil nil nil (fn-hnov-make nil t 777 "c" "d" "<e@x>" ""))))
        (fn-cat (list (obct-row 0 1 bad-facts))) (s (obct-begin 7)))
  (and (not (fn-scol-okp fn-arena fn-cat))
       (not (fn-obc-seek-cached-source-p s fn-arena fn-cat))))
 :rule-classes nil)
; Literal completion remains distinct from finite exact continuation.
(defthm obct-completed-corollary-without-completion
 (let* ((fn-arena (list *obct-source*))
        (fn-cat (list (obct-row 0 1 (fn-hf-make (len *obct-source*) nil 0 nil))))
        (s (obct-begin 7)) (result (fn-obc-source-run s 1 fn-arena fn-cat)))
  (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
       (fn-cat-p fn-cat) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (fn-scol-okp fn-arena fn-cat) (mv-nth 1 result)
       (not (equal (mv-nth 0 result) (fn-obc-actual-old-residual s fn-arena fn-cat)))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (s n a c) (fn-obc-source-run s n a c)))
                  :in-theory (enable fn-obc-source-run))))
