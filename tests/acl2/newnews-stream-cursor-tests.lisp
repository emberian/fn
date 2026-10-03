(in-package "ACL2")
(include-book "../../books/newnews-stream-cursor")
(include-book "newnews-metadata-cursor-tests")

(defthm nnsct-line-wider-than-quantum
  (let* ((cur (fn-sl-start "..abc"))
         (first (fn-sl-step cur 2))
         (next (mv-nth 1 first))
         (last (fn-sl-step next 6)))
    (and (fn-sl-okp cur) (fn-sl-okp next)
         (fn-sl-shapedp cur) (fn-sl-shapedp next)
         (equal (len next) 3)
         (equal (fn-sl-step-cons-cells cur 2) 18)
         (equal (car first) '(46 46))
         (equal (fn-cur-at 0 next) "..abc")
         (equal (fn-cur-at 1 next) 1)
         (not (mv-nth 1 last))
         (equal (append (car first) (car last)) '(46 46 46 97 98 99 13 10))
         (equal (append (car first) (fn-sl-remaining next))
                (fn-sl-remaining cur)))))

(defthm nnsct-render-does-not-revisit-candidate
  (let* ((context (fn-cur-context *nnmt-cur*))
         (cur (fn-cur-make context
                           (fn-nnw-stream-render (fn-sl-start "<a@x>") nil) nil nil))
         (step (fn-nnw-stream-step cur 0 2 nil nil)))
    (and (fn-nnw-stream-okp cur)
         (fn-nnw-stream-outputp (fn-cur-progress cur))
         (equal (car step) '(60 97))
         (equal (mv-nth 2 step) 0)
         (equal (mv-nth 3 step) :output)
         (equal (fn-cur-context (mv-nth 1 step)) context)
         (equal (- (len (fn-nnw-stream-tail (fn-cur-progress cur)))
                   (len (fn-nnw-stream-tail (fn-cur-progress (mv-nth 1 step))))) 0)
         (fn-nnw-meta-livep (mv-nth 1 step))
         (equal (append (car step) (fn-nnw-stream-remaining (mv-nth 1 step) nil nil))
                (fn-nnw-stream-remaining cur nil nil)))))

(defthm nnsct-sparse-scan-retains-renderer
  (let* ((one (fn-nnw-stream-step *nnmt-cur* 1 1 nil nil))
         (two (fn-nnw-stream-step (mv-nth 1 one) 1 1 nil nil)))
    (and (not (car one)) (not (car two))
         (equal (mv-nth 2 one) 1) (equal (mv-nth 2 two) 1)
         (fn-nnw-stream-renderp (fn-cur-progress (mv-nth 1 two)))
         (equal (append (car one) (car two)
                        (fn-nnw-stream-remaining (mv-nth 1 two) nil nil))
                (fn-nnw-stream-remaining *nnmt-cur* nil nil)))))

(defthm nnsct-literal-candidate-progress
  (let* ((progress (fn-cur-progress *nnmt-cur*))
         (next (mv-nth 1 (fn-nnw-stream-one progress 1 nil nil))))
    (and (not (fn-nnw-stream-outputp progress))
         (consp (fn-nnw-tail progress))
         (not (car (fn-nnw-stream-one progress 1 nil nil)))
         (equal (len (fn-nnw-stream-tail next))
                (1- (len (fn-nnw-tail progress))))
         (<= (- (len (fn-nnw-stream-tail progress))
                (len (fn-nnw-stream-tail next))) 1))))

(defconst *nnsct-patterns* (fn-wildmat-result-value
                          (fn-wildmat-parse (fn-nntp-string-octets "fn.*"))))
(defconst *nnsct-select-progress*
  (fn-nnw-stream-select
   (fn-nnm-start *nnsct-patterns* '("fn.test") *nnmt-a*)
   (fn-nnw-stream-scan-cursor
    (fn-nnw-group-source *nnsct-patterns* '("fn.test")) 0 (list *nnmt-a*) 7 t)))

(defthm nnsct-literal-selector-progress
  (let ((next (mv-nth 1 (fn-nnw-stream-one *nnsct-select-progress* 1 nil nil))))
    (and (fn-nnw-stream-selectp *nnsct-select-progress*)
         (fn-nnm-statep (fn-cur-at 1 *nnsct-select-progress*))
         (posp (fn-nnm-group-remaining (fn-cur-at 1 *nnsct-select-progress*)))
         (fn-nnw-stream-progress-okp *nnsct-select-progress*)
         (fn-nnw-stream-selectp next)
         (< (fn-nnm-group-remaining (fn-cur-at 1 next))
            (fn-nnm-group-remaining (fn-cur-at 1 *nnsct-select-progress*)))
         (equal (fn-nnw-stream-tail next) (fn-nnw-stream-tail *nnsct-select-progress*)))))

; Removing positive remaining: an empty but valid selector settles. It
; cannot supply a strict decrease below zero.
(defthm nnsct-selector-progress-needs-positive-remaining
  (let* ((progress (fn-nnw-stream-select
                    (fn-nnm-start *nnsct-patterns* nil *nnmt-a*)
                    (fn-cur-at 2 *nnsct-select-progress*)))
         (next (mv-nth 1 (fn-nnw-stream-one progress 1 nil nil))))
    (and (fn-nnw-stream-selectp progress)
         (fn-nnm-statep (fn-cur-at 1 progress))
         (not (posp (fn-nnm-group-remaining (fn-cur-at 1 progress))))
         (not (< (if (fn-nnw-stream-selectp next)
                     (fn-nnm-group-remaining (fn-cur-at 1 next)) 0)
                 (fn-nnm-group-remaining (fn-cur-at 1 progress)))))))

; Corrupted-capture hypothesis removal: a valid matcher adapter is placed in
; the configured group-source slot. Its positive inner rank and shape hold,
; but starting an entirely new selector may increase the outer rank. The real
; factory always captures a configured source, not this corrupted input.
(defthm nnsct-selector-progress-needs-selection-phase
  (let* ((source (fn-nnm-match (fn-wmc-start *nnsct-patterns* "fn.test")
                               (fn-nnw-select-start *nnsct-patterns* nil *nnmt-a*)))
         (progress (fn-nnw-stream-scan-cursor source 0 (list *nnmt-a*) 7 t))
         (next (mv-nth 1 (fn-nnw-stream-one progress 1 nil nil))))
    (and (not (fn-nnw-stream-selectp progress))
         (fn-nnm-statep (fn-cur-at 1 progress))
         (or (posp (fn-nnm-group-remaining (fn-cur-at 1 progress)))
             (posp (fn-nnm-work-remaining (fn-cur-at 1 progress))))
         (not (or (not (fn-nnw-stream-selectp next))
                  (< (fn-nnm-group-remaining (fn-cur-at 1 next))
                     (fn-nnm-group-remaining (fn-cur-at 1 progress)))
                  (and (equal (fn-nnm-group-remaining (fn-cur-at 1 next))
                              (fn-nnm-group-remaining (fn-cur-at 1 progress)))
                       (< (fn-nnm-work-remaining (fn-cur-at 1 next))
                          (fn-nnm-work-remaining (fn-cur-at 1 progress)))))))))

; Corrupted-state hypothesis removal for the actual stream progress theorem.
; The other literal antecedents hold; a UTF state with a pre-existing frame
; violates the carried matcher state and leaves both ranks unchanged.
(defthm nnsct-selector-progress-needs-carried-state
  (let* ((selector (fn-nnm-match
                    (fn-wmc-state (fn-wmc-node :utf8 nil
                                   (coerce (list (code-char 128)) 'string) 0 nil)
                                  (list (fn-wmc-node :cons 42 nil nil nil)))
                    (fn-nnw-select-start nil nil nil)))
         (progress (fn-nnw-stream-select selector (fn-cur-at 2 *nnsct-select-progress*)))
         (next (mv-nth 1 (fn-nnw-stream-one progress 1 nil nil))))
    (and (fn-nnw-stream-selectp progress)
         (not (fn-nnm-statep (fn-cur-at 1 progress)))
         (or (posp (fn-nnm-group-remaining (fn-cur-at 1 progress)))
             (posp (fn-nnm-work-remaining (fn-cur-at 1 progress))))
         (not (or (not (fn-nnw-stream-selectp next))
                  (< (fn-nnm-group-remaining (fn-cur-at 1 next))
                     (fn-nnm-group-remaining (fn-cur-at 1 progress)))
                  (and (equal (fn-nnm-group-remaining (fn-cur-at 1 next))
                              (fn-nnm-group-remaining (fn-cur-at 1 progress)))
                       (< (fn-nnm-work-remaining (fn-cur-at 1 next))
                          (fn-nnm-work-remaining (fn-cur-at 1 progress)))))))))

; The actual control batch consumes its complete finite visit grant rather
; than paying one scheduler delay for every matcher microstep. It buffers no
; intermediate reply output, and the exact immutable context is retained.
(defthm nnsct-batch-bounds-and-exact-residual
  (let* ((cur (fn-cur-make (fn-cur-context *nnmt-cur*) *nnsct-select-progress* nil nil))
         (one (fn-nnw-stream-step cur 16 2 nil nil))
         (batch (fn-nnw-stream-batch cur 16 2 nil nil)))
    (and (equal (mv-nth 2 one) 1)
         (equal (mv-nth 2 batch) 16)
         (equal (mv-nth 3 batch) :yield)
         (not (car batch))
         (<= (len (car batch)) 2)
         (equal (fn-cur-context (mv-nth 1 batch)) (fn-cur-context cur))
         (true-listp (fn-cur-pending (mv-nth 1 batch)))
         (equal (append (car batch)
                        (fn-nnw-stream-remaining (mv-nth 1 batch) nil nil))
                (fn-nnw-stream-remaining cur nil nil)))))

(defthm nnsct-batch-stops-at-output-and-dependency
  (let* ((cur (fn-cur-make (fn-cur-context *nnmt-cur*)
                          (fn-nnw-stream-render (fn-sl-start "<a@x>") nil) nil nil))
         (batch (fn-nnw-stream-batch cur 16 2 nil nil))
         (held (fn-cur-make (fn-cur-context cur) *nnsct-select-progress* nil '(:resource held)))
         (wait (fn-nnw-stream-batch held 16 2 nil nil))
         (zero (fn-nnw-stream-batch cur 16 0 nil nil)))
    (and (equal (car batch) '(60 97))
         (equal (mv-nth 2 batch) 0)
         (equal (mv-nth 3 batch) :output)
         (equal wait (list nil held 0 :suspended))
         (equal zero (list nil cur 0 :yield)))))
