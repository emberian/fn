; LC C1: bounded checks against the COMMITTED LB representation.
; Start with the successful live MOVE seam before the crash schedule sweep.
; This is a prerequisite check: fn-lc-clean's approved column equality forces
; this exact pair of setters, while its sibling requires corr afterward.
; No alternative catalog, log interpretation, or correspondence is supplied.
(in-package "ACL2")
(include-book "../../books/log-locator-resolves")

(defun lct-held (seq)
  (declare (xargs :guard (natp seq) :verify-guards nil))
  (fn-held-make seq (+ 1 seq) 0
    (if (equal seq 0) "<a@x>" "<b@x>") seq nil "o" "s" "e" 1 5
    (fn-hf-make 24 14 1 nil)
    (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0) nil nil))

(defconst *lct-payload*
  (append (fn-record-string-octets "Subject: a") '(13 10 13 10)
          (fn-record-string-octets "body") '(13 10)))

; SOURCE-COUNT is 1 or 2. The last row moves to a fresh, empty segment.
; One row -> ordinal 0 to 0 is the control; two rows -> ordinal 1 to 0.
(defun lct-live-move-case (source-count fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (member-equal source-count '(1 2))
                  :verify-guards nil))
  (let* ((h0 (lct-held 0)) (h1 (lct-held 1))
         (rows (if (equal source-count 1) (list h0) (list h0 h1)))
         (old-log (fn-lb-log-model-append h0 *lct-payload* 1 nil))
         (old-log (if (equal source-count 1) old-log
                    (fn-lb-log-model-append h1 *lct-payload* 1 old-log)))
         (i (- source-count 1)) (row (nth i rows))
         (fn-lbc (fn-lbc-open-rebuild rows old-log fn-lbc))
         ; corr is defun-nx. Its executable row conjunct alone suffices to
         ; refute the full relation after a MOVE. Full initial corr remains
         ; a separate logical obligation (see the report's timed-out probes),
         ; never an executable private corr twin.
         (before (fn-lbc-rows-corr 0 rows 0 fn-lbc old-log))
         (before-resolves (fn-lc-locators-resolve fn-lbc old-log))
         (old-ordinal (fn-lbc-directory-value i :entry-ordinal fn-lbc))
         (old-loc0 (fn-lbc-loc0 i fn-lbc))
         (old-loc1 (fn-lbc-loc1 i fn-lbc))
         (new-log (fn-lb-log-model-append row *lct-payload* 2 old-log))
         (entry (car (caddr (fn-lb-log-model-segment 2 new-log))))
         (loc1 (+ (* (nth 3 entry) 4294967296) (nth 4 entry)))
         ; Same two setters as the approved fn-lc-replay-move sketch;
         ; executable stobj syntax binds each result. No directory update.
         (fn-lbc (update-fn-lbc-loc0 i 2 fn-lbc))
         (fn-lbc (update-fn-lbc-loc1 i loc1 fn-lbc)))
    (mv (list :source-count source-count
              :rows-ok (fn-cat$ap rows) :stobj-ok (fn-lbc-p fn-lbc)
              :before-rows-corr before :before-resolves before-resolves
              :old-locator (list old-loc0 old-loc1)
              :new-locator (list 2 loc1)
              :old-ordinal old-ordinal :new-entry-ordinal (nth 0 entry)
              :directory-ordinal (fn-lbc-directory-value i :entry-ordinal fn-lbc)
              :same-range (equal (fn-lc-read-range old-loc0 old-loc1 old-log)
                                 (fn-lc-read-range 2 loc1 new-log))
              :same-home (equal (fn-lc-read-home-frame
                                  (fn-lc-home-position old-loc0 old-loc1) old-log)
                                (fn-lc-read-home-frame
                                  (fn-lc-home-position 2 loc1) new-log))
              :after-resolves (fn-lc-locators-resolve fn-lbc new-log)
              :after-rows-corr (fn-lbc-rows-corr 0 rows 0 fn-lbc new-log))
        fn-lbc)))

(defun lct-live-move (source-count)
  (declare (xargs :guard (member-equal source-count '(1 2)) :verify-guards nil))
  (with-local-stobj fn-lbc
    (mv-let (result fn-lbc) (lct-live-move-case source-count fn-lbc) result)))

(defun lct-result-field (key result)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count result)))
  (if (consp result)
      (if (equal key (car result)) (cadr result)
        (lct-result-field key (cddr result)))
    nil))

(defun lct-result-okp (result)
  (declare (xargs :guard t :verify-guards nil))
  (and (lct-result-field :rows-ok result) (lct-result-field :stobj-ok result)
       (lct-result-field :before-rows-corr result) (lct-result-field :before-resolves result)
       (lct-result-field :same-range result) (lct-result-field :same-home result)
       (lct-result-field :after-resolves result) (lct-result-field :after-rows-corr result)))

; Leg A starts before the retained (dependent, still red) MOVE/corr cases.
; Only frame bytes, pgs, and LC's header/tail observation are used here.
(include-book "../../books/log-checkpoint-tail")

(defun lca-pgs-digest (x)
  (declare (xargs :guard t)) (acl2-count x))
(defattach pgs-digest lca-pgs-digest)

(defun lca-tail-disk (header)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((table (list (list 2 1 (pgs-digest header))))
         (directory (list (list 1 1 (pgs-digest table))))
         (record (pgs-make-rec 1 3 1 (pgs-digest directory))))
    (cons (list (cons 1 table) (cons 2 header) (cons 3 directory))
          (list (cons :lc (cons record nil))))))

(defun lca-entry-boundedp (entries bound)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (and (natp (car entries)) (<= (car entries) (nfix bound))
           (lca-entry-boundedp (cdr entries) bound)) t))

(defun lca-bridge-case (moves)
  (declare (xargs :guard (member-equal moves '(0 1 2)) :verify-guards nil))
  (let* ((wire (fn-la-payload-wire *lct-payload*))
         (home (fn-lb-log-model-home-frame (lct-held 0)))
         (record (fn-record-make 0 1 0 "<a@x>" *lct-payload* nil "o" "s" "e" 1 5))
         (stored (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                               *fn-frame-store-kind* (fn-record-encode-impl record)))
         (prefix (fn-lg-entry *fn-lg-genesis* (list stored) 1))
         (prev (fn-lg-trailer (fn-lg-frame *fn-lg-genesis* (list stored))))
         (move1 (fn-lc-move-frame prev 0 wire home))
         (move2 (fn-lc-move-frame (fn-lg-trailer move1) 0 wire home))
         (tail (cond ((equal moves 0) nil) ((equal moves 1) move1)
                     (t (append move1 move2))))
         (header (list :lc-header (list 1 (len prefix) 1 1 prev) 2 nil
                       nil (list (list :lc-tail-policy 1 1024))))
         (disk (lca-tail-disk header))
         (segs (list (list 1 (append prefix tail) nil)))
         (selection (fn-lc-open-selection disk :lc :eager 1 segs header))
         (entries (fn-lc-tail-entries disk :lc :eager segs)))
    (list :moves moves :pgs-open (car (pgs-open disk :lc :eager))
          :segs-typed (fn-lc-segsp segs) :retains (fn-lc-segs-retain segs header)
          :selection selection :logical-tail (fn-lc-selection-tail selection)
          :entries entries :entry-bound (fn-lc-entry-octets-bound 1024)
          :entries-bounded (lca-entry-boundedp entries (fn-lc-entry-octets-bound 1024))
          :bridge (<= (len entries) (+ 1 (len (fn-lc-selection-tail selection)))))))

(defun lca-bridge-case-okp (moves)
  (declare (xargs :guard (member-equal moves '(0 1 2)) :verify-guards nil))
  (let ((case (lca-bridge-case moves)))
    (and (equal (lct-result-field :pgs-open case) :ok)
         (lct-result-field :segs-typed case) (lct-result-field :retains case)
         (equal (car (lct-result-field :selection case)) :checkpoint)
         (lct-result-field :entries-bounded case) (lct-result-field :bridge case))))

(with-guard-checking-event :none (assert-event (lca-bridge-case-okp 0)))
(with-guard-checking-event :none (assert-event (lca-bridge-case-okp 1)))
(with-guard-checking-event :none (assert-event (lca-bridge-case-okp 2)))

; Independent root-slot/pin/tail cross product: three segment ids, ten
; slot states each, eight pin sets, five tail minima = 12,000 states.
(include-book "../../books/log-cleaning")

(defun lca-mask-ids (mask id count)
  (declare (xargs :guard t :measure (nfix count) :verify-guards nil))
  (if (zp count) nil
    (append (if (equal (mod (nfix mask) 2) 1) (list (nfix id)) nil)
            (lca-mask-ids (floor (nfix mask) 2) (+ 1 (nfix id)) (1- count)))))
(defun lca-mask-pins (ids)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ids) (cons (cons (car ids) (car ids)) (lca-mask-pins (cdr ids))) nil))
(defun lca-slot-state (n)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((equal n 8) nil) ((equal n 9) :torn)
        (t (list :lc-slot-observation :unchecked-checksum (lca-mask-ids n 0 3)))))
(defun lca-unlink-case (code)
  (declare (xargs :guard (natp code) :verify-guards nil))
  (let* ((seg (mod code 3)) (q (floor code 3))
         (s0 (lca-slot-state (mod q 10))) (q (floor q 10))
         (s1 (lca-slot-state (mod q 10))) (q (floor q 10))
         (pins (lca-mask-pins (lca-mask-ids (mod q 8) 0 3)))
         (tail (nth (mod (floor q 8) 5) '(nil 0 1 2 3)))
         (disk (cons nil (list (cons :lc (cons s0 s1)))))
         (allowed (fn-lc-unlink-allowedp seg disk :lc pins tail)))
    (list :state (list seg s0 s1 pins tail) :allowed allowed
          :ok (and (fn-lc-pins-p pins)
                   (or (not allowed)
                       (and (not (fn-lc-slot-references s0 seg))
                            (not (fn-lc-slot-references s1 seg))
                            (not (fn-lc-pin-references pins seg))
                            (not (fn-lc-tail-references tail seg))))))))
(defun lca-unlink-check-from (n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (if (zp n) (list :ok 0 0)
    (if (equal n 1)
        (let ((one (lca-unlink-case 0)))
          (if (lct-result-field :ok one)
              (list :ok 1 (if (lct-result-field :allowed one) 1 0)) (list :fail one)))
      (let* ((one (lca-unlink-case (1- n)))
             (rest (lca-unlink-check-from (1- n))))
        (if (not (lct-result-field :ok one)) (list :fail one)
          (if (not (equal (car rest) :ok)) rest
            (list :ok (+ 1 (nth 1 rest))
                  (+ (if (lct-result-field :allowed one) 1 0) (nth 2 rest)))))))))

; PGS publication: every subset of the three writes and old/torn/new slot,
; in both modes, over tails with 0/1/2 maintenance events = 144 images.
(defun lca-publication-case (code)
  (declare (xargs :guard (natp code) :verify-guards nil))
  (let* ((moves (mod code 3)) (q (floor code 3))
         (mask (mod q 8)) (q (floor q 8))
         (slot-kind (mod q 3))
         (mode (if (equal (mod (floor q 3) 2) 0) :eager :lazy))
         (wire (fn-la-payload-wire *lct-payload*))
         (home (fn-lb-log-model-home-frame (lct-held 0)))
         (record (fn-record-make 0 1 0 "<a@x>" *lct-payload* nil "o" "s" "e" 1 5))
         (stored (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                               *fn-frame-store-kind* (fn-record-encode-impl record)))
         (prefix (fn-lg-entry *fn-lg-genesis* (list stored) 1))
         (prev (fn-lg-trailer (fn-lg-frame *fn-lg-genesis* (list stored))))
         (move1 (fn-lc-move-frame prev 0 wire home))
         (move2 (fn-lc-move-frame (fn-lg-trailer move1) 0 wire home))
         (tail (cond ((equal moves 0) nil) ((equal moves 1) move1)
                     (t (append move1 move2))))
         (last (cond ((equal moves 0) prev) ((equal moves 1) (fn-lg-trailer move1))
                     (t (fn-lg-trailer move2))))
         (header (list :lc-header (list 1 (len prefix) 1 1 prev) 2 nil nil
                       (list (list :lc-tail-policy 1 1024))))
         (next (list :lc-header (list 1 (+ (len prefix) (len tail)) (+ 1 moves) 1 last)
                     3 nil nil (list (list :lc-tail-policy 1 1024))))
         (disk (lca-tail-disk header))
         (plan (pgs-plan-commit disk :lc mode (list (cons 0 next)) '(nil 10)))
         (writes (nth 1 plan))
         (keep (list (equal (mod mask 2) 1)
                     (equal (mod (floor mask 2) 2) 1)
                     (equal (mod (floor mask 4) 2) 1)))
         (slot (cond ((equal slot-kind 0) nil) ((equal slot-kind 1) :torn)
                     (t (nth 3 plan))))
         (crashed (pgs-crash disk :lc writes keep (nth 2 plan) slot))
         (opened (pgs-open crashed :lc mode))
         (chosen (fn-lc-header-of-open opened))
         (segs (list (list 1 (append prefix tail) nil)))
         (sel (fn-lc-open-selection crashed :lc mode 3 segs chosen)))
    (list :state (list moves mask slot-kind mode) :selection sel
          :ok (and (equal (car plan) :plan) (equal (len writes) 3)
                   (equal (car sel) :checkpoint)
                   (or (equal chosen header) (equal chosen next))
                   (equal (car opened) :ok)
                   (<= (fn-lc-selection-sequence sel) 3)
                   (fn-lc-segs-retain segs chosen)
                   (equal (fn-lc-selection-S sel) (fn-lc-header-S chosen))
                   (equal (fn-lc-selection-tail sel) (fn-lc-tail-history segs chosen))
                   (<= (len (fn-lc-tail-entries crashed :lc mode segs))
                       (+ 1 (len (fn-lc-selection-tail sel))))))))
(defun lca-publication-check-from (n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (if (zp n) (list :ok 0)
    (let ((one (lca-publication-case (1- n))))
      (if (not (lct-result-field :ok one)) (list :fail one)
        (let ((rest (lca-publication-check-from (1- n))))
          (if (not (equal (car rest) :ok)) rest
            (list :ok (+ 1 (nth 1 rest)))))))))

(with-guard-checking-event :none
  (assert-event (equal (car (lca-unlink-check-from 12000)) :ok)))
(with-guard-checking-event :none
  (assert-event (equal (car (lca-publication-check-from 144)) :ok)))

(include-book "../../books/log-checkpoint-commit")

(defun lca-chain-moves (n prev wire home)
  (declare (xargs :guard t :measure (nfix n) :verify-guards nil))
  (if (zp n) (list nil prev)
    (let* ((frame (fn-lc-move-frame prev 0 wire home))
           (rest (lca-chain-moves (1- n) (fn-lg-trailer frame) wire home)))
      (list (append frame (car rest)) (nth 1 rest)))))

(defun lca-backpressure-case (code fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (natp code) (fn-lbc-p fn-lbc))
                  :verify-guards nil))
  (let* ((k (+ 1 (floor code 3))) (count (+ (- k 1) (mod code 3)))
         (wire (fn-la-payload-wire *lct-payload*))
         (home (fn-lb-log-model-home-frame (lct-held 0)))
         (record (fn-record-make 0 1 0 "<a@x>" *lct-payload* nil "o" "s" "e" 1 5))
         (stored (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                               *fn-frame-store-kind* (fn-record-encode-impl record)))
         (prefix (fn-lg-entry *fn-lg-genesis* (list stored) 1))
         (prev (fn-lg-trailer (fn-lg-frame *fn-lg-genesis* (list stored))))
         (chain (lca-chain-moves count prev wire home))
         (header (list :lc-header (list 1 (len prefix) 1 1 prev) 2 nil nil
                       (list (list :lc-tail-policy 1 1024))))
         (disk (lca-tail-disk header))
         (segs (list (list 1 (append prefix (car chain)) nil)))
         (frame (fn-lc-move-frame (nth 1 chain) 0 wire home))
         (packets (list (list nil frame nil)))
         (before-count (fn-lbc-count fn-lbc)))
    (mv-let (word fn-lbc after) (fn-lc-commit packets segs header k fn-lbc)
      (let* ((refused (<= k count))
             (now (len (fn-lc-tail-history after header)))
             (last (nth 3 (fn-lc-tail-scan after header)))
             (next-header (update-nth 1 (list 1 (len (cadar after)) (+ 1 now) 1 last) header))
             (published (pgs-commit disk :lc :eager (list (cons 0 next-header)) '(nil 10)))
             (adopted (fn-lc-adopted-header published :lc :eager))
             (next-frame (fn-lc-move-frame last 0 wire home)))
        (mv-let (next-word fn-lbc next-segs)
          (fn-lc-commit (list (list nil next-frame nil)) after adopted k fn-lbc)
          (mv (list :state (list k count) :initial-word word :after-word next-word
                    :initial-tail now :after-tail (len (fn-lc-tail-history next-segs adopted))
                    :ok (and (equal count (len (fn-lc-tail-history segs header)))
                             (equal word (if refused :publication-behind :ok))
                             (equal (fn-lbc-count fn-lbc) before-count)
                             (if refused (equal after segs) (<= now k))
                             (equal adopted next-header)
                             (equal (fn-lc-tail-history after adopted) nil)
                             (equal next-word :ok)
                             (equal (len (fn-lc-tail-history next-segs adopted)) 1)))
              fn-lbc))))))

(defun lca-backpressure-check-from (n fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (natp n) (fn-lbc-p fn-lbc))
                  :verify-guards nil))
  (if (zp n) (mv (list :ok 0 0 0) fn-lbc)
    (mv-let (one fn-lbc) (lca-backpressure-case (1- n) fn-lbc)
      (if (not (lct-result-field :ok one)) (mv (list :fail one) fn-lbc)
        (mv-let (rest fn-lbc) (lca-backpressure-check-from (1- n) fn-lbc)
          (mv (if (not (equal (car rest) :ok)) rest
                (list :ok (+ 1 (nth 1 rest))
                      (+ (if (equal (lct-result-field :initial-word one) :publication-behind) 1 0)
                         (nth 2 rest))
                      (+ (if (equal (lct-result-field :after-word one) :ok) 1 0) (nth 3 rest))))
              fn-lbc))))))
(defun lca-backpressure-check ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-lbc
    (mv-let (result fn-lbc) (lca-backpressure-check-from 9 fn-lbc) result)))

(defun lca-backpressure-observation (code)
  (declare (xargs :guard (natp code) :verify-guards nil))
  (with-local-stobj fn-lbc
    (mv-let (result fn-lbc) (lca-backpressure-case code fn-lbc) result)))

(with-guard-checking-event :none
  (assert-event (equal (lca-backpressure-check) '(:ok 9 6 9))))

; A failed assertion is the named STOP; do not continue to crash enumeration.
(with-guard-checking-event
 :none
 (assert-event (lct-result-okp (lct-live-move 1))))

(with-guard-checking-event
 :none
 (assert-event (lct-result-okp (lct-live-move 2))))
