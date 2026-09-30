(in-package "ACL2")
(include-book "../../books/legacy-parser-continuation")

(defconst *lpr-source* '(83 58 32 120 13 10 13 10))
(defconst *lpr-arena* (list *lpr-source*))
(defconst *lpr-begin* (fn-lpc-begin 0 8 :pin))

(defthm lpr-append-positive
 (let ((a '(83 58)) (b '(32 120)))
  (equal (fn-lpc-feed (append a b) *lpr-begin*)
         (fn-lpc-feed b (fn-lpc-feed a *lpr-begin*)))) :rule-classes nil)
(defthm lpr-begin-positive
 (fn-lpr-prefix-p *lpr-begin* 0 :pin *lpr-source*) :rule-classes nil)
(defthm lpr-resume-positive
 (let* ((s (fn-lpc-feed '(83 58) *lpr-begin*))
        (next (mv-nth 0 (fn-lpc-tick s 1 *lpr-arena*))))
  (and (fn-lpr-prefix-p s 0 :pin *lpr-source*)
       (equal *lpr-source* (nth 0 *lpr-arena*))
       (fn-lpr-prefix-p next 0 :pin *lpr-source*))) :rule-classes nil)
(defthm lpr-terminal-positive
 (let ((s (fn-lpc-feed *lpr-source* *lpr-begin*)))
  (and (fn-lpr-prefix-p s 0 :pin *lpr-source*)
       (not (equal (fn-lpc-verdict s) :yield))
       (equal s (fn-lpc-feed *lpr-source* (fn-lpc-begin 0 (len *lpr-source*) :pin)))))
 :rule-classes nil)
; Rejected grammar still traverses the complete source and body facts.
(defthm lpr-invalid-terminal-positive
 (let* ((bytes '(0 13 10 13 10 13 10))
        (s (fn-lpc-feed bytes (fn-lpc-begin 0 (len bytes) :pin))))
  (and (fn-lpr-prefix-p s 0 :pin bytes)
       (not (equal (fn-lpc-verdict s) :yield))
       (equal s (fn-lpc-feed bytes (fn-lpc-begin 0 (len bytes) :pin)))))
 :rule-classes nil)

; Hypothesis-removal corrupted state: magic carry was erased before byte0.
(defthm lpr-one-without-prefix
 (let* ((bytes '(0)) (arena (list bytes))
        (s (fn-lpc-put 7 nil (fn-lpc-begin 0 1 :pin)))
        (next (mv-nth 0 (fn-lpc-tick s 1 arena))))
  (and (not (fn-lpr-prefix-p s 0 :pin bytes)) (equal bytes (nth 0 arena))
       (not (fn-lpr-prefix-p next 0 :pin bytes)))) :rule-classes nil)
(defthm lpr-one-without-source-binding
 (let* ((bytes '(83)) (arena '((84))) (s (fn-lpc-begin 0 1 :pin))
        (next (mv-nth 0 (fn-lpc-tick s 1 arena))))
  (and (fn-lpr-prefix-p s 0 :pin bytes) (not (equal bytes (nth 0 arena)))
       (not (fn-lpr-prefix-p next 0 :pin bytes)))) :rule-classes nil)
(defthm lpr-terminal-without-prefix
 (let* ((bytes '(83)) (s (fn-lpc-begin 0 0 :pin)))
  (and (not (fn-lpr-prefix-p s 0 :pin bytes))
       (not (equal (fn-lpc-verdict s) :yield))
       (not (equal s (fn-lpc-feed bytes (fn-lpc-begin 0 (len bytes) :pin))))))
 :rule-classes nil)
(defthm lpr-terminal-without-terminal-verdict
 (let* ((bytes '(83)) (s (fn-lpc-begin 0 1 :pin)))
  (and (fn-lpr-prefix-p s 0 :pin bytes)
       (not (not (equal (fn-lpc-verdict s) :yield)))
       (not (equal s (fn-lpc-feed bytes (fn-lpc-begin 0 (len bytes) :pin))))))
 :rule-classes nil)

; Mutation: a malformed header phase cannot be treated as early terminal.
(defthm lpr-header-bad-still-yields
 (let* ((bytes '(0 13 10 13 10)) (begin (fn-lpc-begin 0 5 :pin))
        (s (fn-lpc-byte begin 0)))
  (and (equal (fn-lpc-at 0 (fn-lpc-at 4 s)) :bad)
       (equal (fn-lpc-verdict s) :yield)
       (fn-lpr-prefix-p s 0 :pin bytes)
       (not (equal s (fn-lpc-feed bytes begin))))) :rule-classes nil)

(defun lpr-exec-run (s h pin bytes fuel fn-arena)
 (declare (xargs :stobjs fn-arena :measure (nfix fuel) :verify-guards nil))
 (if (zp fuel) (mv (fn-lpr-prefix-p s h pin bytes) fn-arena)
  (mv-let (next consumed work verdict) (fn-lpc-tick s 1 fn-arena)
   (declare (ignore consumed work verdict))
   (mv-let (ok fn-arena) (lpr-exec-run next h pin bytes (1- fuel) fn-arena)
    (mv (and (fn-lpr-prefix-p s h pin bytes) ok) fn-arena)))))
(defun lpr-exec-case (bytes fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list bytes fn-arena))
        (s (fn-lpc-begin 0 (len bytes) :pin)))
  (lpr-exec-run s 0 :pin bytes (+ 1 (len bytes)) fn-arena)))
(defun lpr-exec (bytes)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (result fn-arena) (lpr-exec-case bytes fn-arena) result)))
(assert-event (and (lpr-exec *lpr-source*) (lpr-exec '(0 13 10 13 10 13 10))))
