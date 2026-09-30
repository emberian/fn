(in-package "ACL2")
(include-book "../../books/operator-report-reader")

; Reachable positive full antecedent/conclusion: all four widths, the
; highest scalar, an empty stream, and a valid report beyond token limits.
(defconst *fn-oru-valid-stream*
  '(65 194 128 224 160 128 240 144 128 128 244 143 191 191))
(assert-event
 (let ((c (fn-oru-start)))
   (and (fn-oru-invariant c)
        (fn-wildmat-octet-listp *fn-oru-valid-stream*)
        (equal (car (fn-oru-run c *fn-oru-valid-stream*)) :valid)
        (equal (equal (car (fn-oru-run c *fn-oru-valid-stream*)) :valid)
               (fn-wildmat-result-okp
                (fn-wildmat-decode-aux *fn-oru-valid-stream* nil)))
        (equal (car (fn-oru-run c nil)) :valid))))
(assert-event
 (let ((octets (make-list 600 :initial-element 65)))
   (and (fn-wildmat-octet-listp octets)
        (equal (car (fn-oru-run (fn-oru-start) octets)) :valid)
        (fn-wildmat-result-okp (fn-wildmat-decode-aux octets nil)))))

; Exact complete-prefix theorem: retained full hypotheses and both effect
; projections, with malformed suffix left to the following decoder step.
(assert-event
 (let* ((prefix '(244 143 191 191)) (suffix '(65 255))
        (next (fn-wildmat-utf8-next prefix)))
   (and (true-listp prefix)
        (equal (len prefix) (fn-oru-lead-width (car prefix)))
        (equal (fn-wildmat-utf8-rest next) nil)
        (equal (fn-wildmat-utf8-next (append prefix suffix))
               (if (fn-wildmat-result-okp next)
                   (fn-wildmat-utf8-ok (fn-wildmat-result-value next) suffix)
                 next))
        (equal (fn-wildmat-result-okp
                (fn-wildmat-decode-aux (append prefix suffix) nil))
               (and (fn-wildmat-result-okp next)
                    (fn-wildmat-result-okp (fn-wildmat-decode-aux suffix nil)))))))

; Proper-prefix hypothesis removal: width equality retained, but an
; improper tail becomes the decoder rest and violates the literal result.
(assert-event
 (let ((prefix '(65 . 7)))
   (and (not (true-listp prefix))
        (equal (len prefix) (fn-oru-lead-width (car prefix)))
        (not (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next prefix)) nil)))))
; Width hypothesis removal: properness retained and consumed rest nonempty.
(assert-event
 (let ((prefix '(65 66)))
   (and (true-listp prefix)
        (not (equal (len prefix) (fn-oru-lead-width (car prefix))))
        (not (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next prefix)) nil)))))

; Carried-state step conservation and invariant preservation with a
; complete four-byte scalar. EOF observes only after all bytes are checked.
(assert-event
 (let* ((c (fn-oru-step (fn-oru-step (fn-oru-step (fn-oru-start) 240 nil)
                                              144 nil) 128 nil))
        (next (fn-oru-step c 128 nil)) (rest '(65)))
   (and (fn-oru-invariant c) (equal (car c) :checking)
        (fn-wildmat-octetp 128) (fn-oru-invariant next)
        (equal (fn-oru-denotation c (cons 128 rest))
               (fn-oru-denotation next rest))
        (equal (equal (car (fn-oru-step next 0 t)) :valid)
               (fn-oru-denotation next nil)))))

; Malformed-state invariant hypothesis removal. Guard-ready remains true;
; the carried length/remaining relation fails and the literal preservation
; conclusion fails after one further octet.
(defthm fn-oru-invariant-removal-witness
 (let ((c (fn-oru-cursor :checking '(65 65 65 65) 2)))
   (and (fn-oru-ready-p c) (not (fn-oru-invariant c))
        (fn-wildmat-octetp 65)
        (not (fn-oru-invariant (fn-oru-step c 65 nil)))
        (fn-wildmat-octet-listp nil)
        (not (equal (equal (car (fn-oru-run c nil)) :valid)
                    (fn-oru-denotation c nil)))))
 :rule-classes nil)
; Input-octet hypothesis removal: carried invariant retained; output pending
; ceases to be an octet list. The fresh complete-decoder equality also fails.
(defthm fn-oru-octet-removal-witness
 (and (fn-oru-invariant (fn-oru-start))
      (not (fn-wildmat-octetp 256))
      (not (fn-oru-invariant (fn-oru-step (fn-oru-start) 256 nil)))
      (not (fn-wildmat-octet-listp '(-1)))
      (not (equal (equal (car (fn-oru-run (fn-oru-start) '(-1))) :valid)
                  (fn-wildmat-result-okp (fn-wildmat-decode-aux '(-1) nil)))))
 :rule-classes nil)

; Each malformed encoding is fully consumed by the complete logical fold
; only for the reference test: overlong, surrogate, out-of-range and EOF cut.
(assert-event
 (and (equal (car (fn-oru-run (fn-oru-start) '(192 128))) :invalid)
      (equal (car (fn-oru-run (fn-oru-start) '(224 128 128))) :invalid)
      (equal (car (fn-oru-run (fn-oru-start) '(237 160 128))) :invalid)
      (equal (car (fn-oru-run (fn-oru-start) '(244 144 128 128))) :invalid)
      (equal (car (fn-oru-run (fn-oru-start) '(240 144 128))) :invalid)))

(assert-event
 (let* ((c (fn-oru-start))
        (v (mv-list 3 (fn-oru-reader-step c :validate 65 nil t)))
        (e (mv-list 3 (fn-oru-reader-step (car v) (cadr v) 0 t t)))
        (r (mv-list 3 (fn-oru-reader-step (car e) (cadr e) 0 nil t)))
        (w (mv-list 3 (fn-oru-reader-step (car r) (cadr r) 65 nil t)))
        (d (mv-list 3 (fn-oru-reader-step (car w) (cadr w) 0 t t))))
   (and (fn-oru-reader-invariant c :validate) (fn-wildmat-octetp 65)
        (fn-oru-reader-invariant (car v) (cadr v))
        (equal (caddr v) nil) (equal (caddr e) nil) (equal (caddr r) nil)
        (equal (cadr e) :rewind) (equal (cadr r) :copy)
        (consp (caddr w)) (equal (car (car r)) :valid)
        (equal (cadr r) :copy)
        (equal (caddr w) '(65))
        (equal (cadr d) :done) (equal (caddr d) nil)
        (fn-oru-reader-invariant (car d) (cadr d)))))

(defthm fn-oru-reader-invariant-removal-witness
 (let* ((c (fn-oru-start)) (phase :copy)
        (next (mv-list 3 (fn-oru-reader-step c phase 65 nil t))))
   (and (fn-oru-invariant c) (fn-oru-ready-p c)
        (fn-oru-reader-phasep phase)
        (not (fn-oru-reader-invariant c phase))
        (fn-wildmat-octetp 65)
        (not (fn-oru-reader-invariant (car next) (cadr next)))))
 :rule-classes nil)

(defthm fn-oru-reader-octet-removal-witness
 (let* ((c (fn-oru-start)) (phase :validate)
        (next (mv-list 3 (fn-oru-reader-step c phase 256 nil t))))
   (and (fn-oru-reader-invariant c phase)
        (not (fn-wildmat-octetp 256))
        (not (fn-oru-reader-invariant (car next) (cadr next)))))
 :rule-classes nil)

(defthm fn-oru-conservation-invariant-removal-witness
 (let ((c (fn-oru-cursor :checking '(65 255) 1)))
   (and (fn-oru-ready-p c) (not (fn-oru-invariant c))
        (equal (car c) :checking) (fn-wildmat-octetp 65)
        (not (equal (fn-oru-denotation c '(65))
                    (fn-oru-denotation (fn-oru-step c 65 nil) nil)))))
 :rule-classes nil)
(defthm fn-oru-conservation-octet-removal-witness
 (let ((c (fn-oru-start)))
   (and (fn-oru-invariant c) (equal (car c) :checking)
        (not (fn-wildmat-octetp -1))
        (not (equal (fn-oru-denotation c '(-1))
                    (fn-oru-denotation (fn-oru-step c -1 nil) nil)))))
 :rule-classes nil)
; Conservation also covers stable terminal states; checking status is not
; a theorem hypothesis after proving that weakening.
(defthm fn-oru-output-phase-removal-witness
 (let* ((c (fn-oru-step (fn-oru-start) 0 t))
        (phase :corrupted-phase)
        (output (caddr (mv-list 3 (fn-oru-reader-step c phase 65 nil t)))))
   (and (not (fn-oru-reader-phasep phase)) (consp output)
        (equal (car c) :valid) (not (equal phase :copy))
        (equal output '(65))))
 :rule-classes nil)
(assert-event
 (let* ((c (fn-oru-start)) (phase :validate)
        (output (caddr (mv-list 3 (fn-oru-reader-step c phase 65 nil t)))))
   (and (fn-oru-reader-phasep phase) (not (consp output))
        (not (equal (car c) :valid)) (not (equal phase :copy)))))
