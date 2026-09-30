(in-package "ACL2")
(include-book "../../books/history-record-cursor")

(defun fn-hrcur-test-run (fuel c)
  (declare (xargs :guard (natp fuel)))
  (if (zp fuel) (list :yield c nil)
    (mv-let (verdict octet next) (fn-hrcur-leaf-tick c)
      (cond ((eq verdict :prepared) (list :prepared next nil))
            ((eq verdict :emit)
             (let ((rest (fn-hrcur-test-run (1- fuel) next)))
               (list (car rest) (cadr rest) (cons octet (caddr rest)))))
            ((eq verdict :continue) (fn-hrcur-test-run (1- fuel) next))
            (t (list verdict next nil))))))

(defconst *fn-hrcur-test-leaf* '(0 127 255))
(defconst *fn-hrcur-test-begin*
  (fn-hrcur-leaf-begin *fn-hrcur-test-leaf* '(:captured 31 7) '(:lease 19)))

; PRF-1088 reachable-positive: all literal initial-refinement hypotheses.
(assert-event
 (and (consp *fn-hrcur-test-leaf*)
      (fn-scc-octet-listp *fn-hrcur-test-leaf*)
      (< (+ (len *fn-hrcur-test-leaf*) 2
            (len (fn-scc-le-digits (len *fn-hrcur-test-leaf*))))
         *fn-hrcur-u64-bound*)
      (fn-hrcur-leaf-invariantp *fn-hrcur-test-begin*)
      (equal (fn-hrcur-leaf-rest *fn-hrcur-test-begin*)
             (fn-scc-encode *fn-hrcur-test-leaf*))))

; Every reached count/prefix/body/done state checks the complete invariant,
; byte/refusal verdict and literal exact residual theorem.
(defun fn-hrcur-test-tracep (fuel c)
  (declare (xargs :guard (natp fuel) :verify-guards nil))
  (if (zp fuel) t
    (mv-let (verdict octet next) (fn-hrcur-leaf-tick c)
      (and (fn-hrcur-leaf-invariantp c)
           (fn-hrcur-leaf-invariantp next)
           (member-eq verdict '(:continue :emit :prepared))
           (implies (eq verdict :emit) (fn-scc-octetp octet))
           (equal (fn-hrcur-leaf-rest c)
                  (if (eq verdict :emit)
                      (cons octet (fn-hrcur-leaf-rest next))
                    (fn-hrcur-leaf-rest next)))
           (equal (fn-hrcur-field 5 next) (fn-hrcur-field 5 c))
           (equal (fn-hrcur-field 6 next) (fn-hrcur-field 6 c))
           (fn-hrcur-test-tracep (1- fuel) next)))))

(assert-event (fn-hrcur-test-tracep 15 *fn-hrcur-test-begin*))
(assert-event
 (let ((result (fn-hrcur-test-run 12 *fn-hrcur-test-begin*)))
   (and (equal (car result) :prepared)
        (equal (caddr result) (fn-scc-encode *fn-hrcur-test-leaf*))
        (equal (fn-hrcur-field 5 (cadr result)) '(:captured 31 7))
        (equal (fn-hrcur-field 6 (cadr result)) '(:lease 19)))))

; Yield is resumable; it does not silently truncate the record.
(assert-event
 (let* ((first (fn-hrcur-test-run 7 *fn-hrcur-test-begin*))
        (second (fn-hrcur-test-run 7 (cadr first))))
   (and (equal (car first) :yield) (equal (car second) :prepared)
        (equal (append (caddr first) (caddr second))
               (fn-scc-encode *fn-hrcur-test-leaf*)))))

; Literal hypothesis-removal: sole tick-invariant hypothesis fails,
; as do preservation and its permitted-verdict conjunct. Corrupted state,
; never asserted producer-reachable.
(assert-event
 (let ((bad '(:prefix nil (3) 1 (300) :capture :lease)))
   (mv-let (verdict octet next) (fn-hrcur-leaf-tick bad)
     (declare (ignore octet))
     (and (not (fn-hrcur-leaf-invariantp bad))
          (not (fn-hrcur-leaf-invariantp next))
          (not (member-eq verdict '(:continue :emit :prepared)))))))

; Literal hypothesis-removal for residual refinement: invalid count relation
; reaches the zero-length refusal, losing the nonempty residual.
(assert-event
 (let ((bad '(:count nil (8 9) 0 nil :capture :lease)))
   (mv-let (verdict octet next) (fn-hrcur-leaf-tick bad)
     (and (not (fn-hrcur-leaf-invariantp bad))
          (not (equal (fn-hrcur-leaf-rest bad)
                      (if (eq verdict :emit)
                          (cons octet (fn-hrcur-leaf-rest next))
                        (fn-hrcur-leaf-rest next))))))))

; Existing tree codec treats NIL and a non-octet list differently from an
; opaque leaf. Their positive retained bound hypothesis holds; the omitted
; nonempty / octet hypothesis and the exact encode conclusion fail.
(assert-event
 (let ((x nil))
   (and (fn-scc-octet-listp x) (not (consp x))
        (< (+ (len x) 2 (len (fn-scc-le-digits (len x)))) *fn-hrcur-u64-bound*)
        (not (equal (fn-hrcur-leaf-rest (fn-hrcur-leaf-begin x :c :l))
                    (fn-scc-encode x))))))
(assert-event
 (let ((x '(300)))
   (and (consp x) (not (fn-scc-octet-listp x))
        (< (+ (len x) 2 (len (fn-scc-le-digits (len x)))) *fn-hrcur-u64-bound*)
        (not (equal (fn-hrcur-leaf-rest (fn-hrcur-leaf-begin x :c :l))
                    (fn-scc-encode x))))))

; Word accumulator trace uses the original pack8 as the output oracle.
; All literal preservation and partial/full boundary antecedents are checked.
(defun fn-hrcur-test-word-tracep (xs prefix k w)
  (declare (xargs :guard t :verify-guards nil :measure (len xs)))
  (if (consp xs)
      (mv-let (verdict word k2 w2) (fn-hrcur-word-push (car xs) k w)
        (and (fn-scc-octetp (car xs)) (fn-hrcur-wordp k w)
             (equal k (len prefix)) (equal w (adt-unle k prefix))
             (fn-hrcur-wordp k2 w2)
             (member-eq verdict '(:continue :emit))
             (if (< k 7)
                 (and (equal verdict :continue) (equal k2 (+ 1 k))
                      (equal w2 (adt-unle (+ 1 k) (append prefix (list (car xs)))))
                      (fn-hrcur-test-word-tracep (cdr xs) (append prefix (list (car xs))) k2 w2))
               (and (equal (len prefix) 7) (equal verdict :emit)
                    (unsigned-byte-p 64 word)
                    (equal word (car (fn-hp-pack8 1 (append prefix (list (car xs))))))
                    (equal k2 0) (equal w2 0)
                    (fn-hrcur-test-word-tracep (cdr xs) nil k2 w2)))))
    (mv-let (verdict word k2 w2) (fn-hrcur-word-finish k w)
      (and (equal k (len prefix)) (equal w (adt-unle k prefix))
           (fn-hrcur-wordp k w) (equal k2 0) (equal w2 0)
           (if (< 0 k)
               (and (equal verdict :emit)
                    (equal word (car (fn-hp-pack8 1 (append prefix (adt-zeros (- 8 k)))))))
             (and (equal verdict :prepared) (null word)))))))

(assert-event (fn-hrcur-test-word-tracep '(0 1 127 128 255 64 3 9 255 7 0) nil 0 0))
(assert-event (fn-hrcur-test-word-tracep '(255 255 255 255 255 255 255 255) nil 0 0))

(defun fn-hrcur-test-partial-conclusion (prefix octet k w)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v word k2 w2) (fn-hrcur-word-push octet k w)
    (declare (ignore word))
    (and (equal v :continue) (equal k2 (+ 1 k))
         (equal w2 (adt-unle (+ 1 k) (append prefix (list octet)))))))

; One literal partial-boundary hypothesis is omitted per case. Every other
; hypothesis is checked affirmatively. Corrupted-state/argument mutations,
; not assertions that the composed producer reaches invalid word states.
(assert-event
 (let ((prefix nil) (octet 1) (k 1) (w 0))
   (and (not (equal k (len prefix))) (< k 7)
        (equal w (adt-unle k prefix)) (fn-hrcur-wordp k w) (fn-scc-octetp octet)
        (not (fn-hrcur-test-partial-conclusion prefix octet k w)))))
(assert-event
 (let ((prefix '(0 0 0 0 0 0 0)) (octet 1) (k 7) (w 0))
   (and (equal k (len prefix)) (not (< k 7))
        (equal w (adt-unle k prefix)) (fn-hrcur-wordp k w) (fn-scc-octetp octet)
        (not (fn-hrcur-test-partial-conclusion prefix octet k w)))))
(assert-event
 (let ((prefix '(0)) (octet 1) (k 1) (w 1))
   (and (equal k (len prefix)) (< k 7)
        (not (equal w (adt-unle k prefix))) (fn-hrcur-wordp k w) (fn-scc-octetp octet)
        (not (fn-hrcur-test-partial-conclusion prefix octet k w)))))
(assert-event
 (let ((prefix '(300)) (octet 1) (k 1) (w 300))
   (and (equal k (len prefix)) (< k 7)
        (equal w (adt-unle k prefix)) (not (fn-hrcur-wordp k w)) (fn-scc-octetp octet)
        (not (fn-hrcur-test-partial-conclusion prefix octet k w)))))
(assert-event
 (let ((prefix nil) (octet 300) (k 0) (w 0))
   (and (equal k (len prefix)) (< k 7)
        (equal w (adt-unle k prefix)) (fn-hrcur-wordp k w) (not (fn-scc-octetp octet))
        (not (fn-hrcur-test-partial-conclusion prefix octet k w)))))

(defun fn-hrcur-test-full-conclusion (prefix octet w)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v word k2 w2) (fn-hrcur-word-push octet 7 w)
    (and (equal v :emit)
         (equal word (car (fn-hp-pack8 1 (append prefix (list octet)))))
         (equal k2 0) (equal w2 0))))

(assert-event
 (let ((prefix nil) (octet 1) (w 0))
   (and (not (equal (len prefix) 7)) (equal w (adt-unle 7 prefix))
        (fn-hrcur-wordp 7 w) (fn-scc-octetp octet)
        (not (fn-hrcur-test-full-conclusion prefix octet w)))))
(assert-event
 (let ((prefix '(0 0 0 0 0 0 0)) (octet 1) (w 1))
   (and (equal (len prefix) 7) (not (equal w (adt-unle 7 prefix)))
        (fn-hrcur-wordp 7 w) (fn-scc-octetp octet)
        (not (fn-hrcur-test-full-conclusion prefix octet w)))))
(assert-event
 (let* ((prefix '(0 0 0 0 0 0 300)) (octet 1) (w (adt-unle 7 prefix)))
   (and (equal (len prefix) 7) (equal w (adt-unle 7 prefix))
        (not (fn-hrcur-wordp 7 w)) (fn-scc-octetp octet)
        (not (fn-hrcur-test-full-conclusion prefix octet w)))))
(assert-event
 (let ((prefix '(0 0 0 0 0 0 0)) (octet 300) (w 0))
   (and (equal (len prefix) 7) (equal w (adt-unle 7 prefix))
        (fn-hrcur-wordp 7 w) (not (fn-scc-octetp octet))
        (not (fn-hrcur-test-full-conclusion prefix octet w)))))

(defun fn-hrcur-test-pad-conclusion (prefix k w)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v word k2 w2) (fn-hrcur-word-finish k w)
    (and (equal v :emit)
         (equal word (car (fn-hp-pack8 1 (append prefix (adt-zeros (- 8 k))))))
         (equal k2 0) (equal w2 0))))

(assert-event
 (let ((prefix '(1 2)) (k 1) (w 1))
   (and (not (equal k (len prefix))) (< 0 k)
        (equal w (adt-unle k prefix)) (fn-hrcur-wordp k w)
        (not (fn-hrcur-test-pad-conclusion prefix k w)))))
(assert-event
 (let ((prefix nil) (k 0) (w 0))
   (and (equal k (len prefix)) (not (< 0 k))
        (equal w (adt-unle k prefix)) (fn-hrcur-wordp k w)
        (not (fn-hrcur-test-pad-conclusion prefix k w)))))
(assert-event
 (let ((prefix '(0)) (k 1) (w 1))
   (and (equal k (len prefix)) (< 0 k)
        (not (equal w (adt-unle k prefix))) (fn-hrcur-wordp k w)
        (not (fn-hrcur-test-pad-conclusion prefix k w)))))
(assert-event
 (let ((prefix '(300)) (k 1) (w 300))
   (and (equal k (len prefix)) (< 0 k)
        (equal w (adt-unle k prefix)) (not (fn-hrcur-wordp k w))
        (not (fn-hrcur-test-pad-conclusion prefix k w)))))

; Word-state and octet-domain hypotheses are both necessary to the permitted
; verdict part of the preservation theorem. Other hypothesis stays true.
(assert-event
 (let ((octet 300) (k 0) (w 0))
   (mv-let (v word k2 w2) (fn-hrcur-word-push octet k w)
     (declare (ignore word k2 w2))
     (and (not (fn-scc-octetp octet)) (fn-hrcur-wordp k w)
          (not (member-eq v '(:continue :emit)))))))
(assert-event
 (let ((octet 0) (k 0) (w 1))
   (mv-let (v word k2 w2) (fn-hrcur-word-push octet k w)
     (declare (ignore word k2 w2))
     (and (fn-scc-octetp octet) (not (fn-hrcur-wordp k w))
          (not (member-eq v '(:continue :emit)))))))

; Tree descriptor interpreter is an oracle used only by this test. Production
; passes at most one pending descriptor to a byte cursor, not this flattening.
(defun fn-hrcur-test-tree-tracep (fuel c)
  (declare (xargs :guard (natp fuel) :verify-guards nil))
  (if (zp fuel) t
    (mv-let (v descriptor next) (fn-hrcur-tree-tick c)
      (and (fn-hrcur-tree-invariantp c)
           (fn-hrcur-tree-invariantp next)
           (member-eq v '(:continue :emit :prepared))
           (implies (eq v :emit) (fn-hrcur-descriptorp descriptor))
           (equal (fn-hrcur-tree-rest (fn-hrcur-field 0 c))
                  (if (eq v :emit)
                      (append (fn-hrcur-descriptor-octets descriptor)
                              (fn-hrcur-tree-rest (fn-hrcur-field 0 next)))
                    (fn-hrcur-tree-rest (fn-hrcur-field 0 next))))
           (equal (fn-hrcur-field 1 next) (fn-hrcur-field 1 c))
           (equal (fn-hrcur-field 2 next) (fn-hrcur-field 2 c))
           (fn-hrcur-test-tree-tracep (1- fuel) next)))))

(defun fn-hrcur-test-tree-run (fuel c)
  (declare (xargs :guard (natp fuel) :verify-guards nil))
  (if (zp fuel) (list :yield c nil)
    (mv-let (v descriptor next) (fn-hrcur-tree-tick c)
      (cond ((eq v :prepared) (list :prepared next nil))
            ((eq v :continue) (fn-hrcur-test-tree-run (1- fuel) next))
            ((eq v :emit)
             (let ((rest (fn-hrcur-test-tree-run (1- fuel) next)))
               (list (car rest) (cadr rest)
                     (append (fn-hrcur-descriptor-octets descriptor) (caddr rest)))))
            (t (list v next nil))))))

(defconst *fn-hrcur-test-tree*
  '(:article 17 (0 127 255) "subject" (:groups "fn.test") (:alpha . :beta) nil -9 #\A))
(defconst *fn-hrcur-test-tree-begin*
  (fn-hrcur-tree-begin *fn-hrcur-test-tree* '(:captured 37 4) '(:lease 61)))

; Complete literal initial-refinement hypothesis and both conclusions.
(assert-event
 (and (fn-hrcur-tree-domainp *fn-hrcur-test-tree*)
      (fn-hrcur-tree-invariantp *fn-hrcur-test-tree-begin*)
      (equal (fn-hrcur-tree-rest (fn-hrcur-field 0 *fn-hrcur-test-tree-begin*))
             (fn-scc-encode *fn-hrcur-test-tree*))))

; Nonempty composite trace exercises repeated prefix scanning, opaque leaf,
; non-octet/dotted-tail descent, atom descriptors and CONS byte descriptors.
(assert-event (fn-hrcur-test-tree-tracep 150 *fn-hrcur-test-tree-begin*))
(assert-event
 (let ((result (fn-hrcur-test-tree-run 150 *fn-hrcur-test-tree-begin*)))
   (and (equal (car result) :prepared)
        (equal (caddr result) (fn-scc-encode *fn-hrcur-test-tree*)))))

; Stop before tree/atom completion, then resume exactly the retained task stack.
(assert-event
 (let* ((first (fn-hrcur-test-tree-run 13 *fn-hrcur-test-tree-begin*))
        (second (fn-hrcur-test-tree-run 150 (cadr first))))
   (and (equal (car first) :yield) (equal (car second) :prepared)
        (equal (append (caddr first) (caddr second))
               (fn-scc-encode *fn-hrcur-test-tree*)))))

; Literal sole-hypothesis removal, corrupted scan state: fake complete count
; does not equal the immutable source length. Both emitted descriptor validity
; and the exact residual conclusion fail, with no other hypotheses to omit.
(assert-event
 (let ((bad '(((:scan (1 2) nil 0)) :capture :lease)))
   (mv-let (v descriptor next) (fn-hrcur-tree-tick bad)
     (and (not (fn-hrcur-tree-invariantp bad))
          (eq v :emit) (not (fn-hrcur-descriptorp descriptor))
          (not (equal (fn-hrcur-tree-rest (fn-hrcur-field 0 bad))
                      (append (fn-hrcur-descriptor-octets descriptor)
                              (fn-hrcur-tree-rest (fn-hrcur-field 0 next)))))))))

; Initial-domain hypothesis is material: the current scalar format represents
; fewer than256 length digits. This 2056-bit argument is not a producer state.
(assert-event
 (let* ((x (expt 256 256)) (c (fn-hrcur-tree-begin x :capture :lease)))
   (and (not (fn-hrcur-tree-domainp x))
        (not (fn-hrcur-tree-invariantp c)))))

; A non-octet after a long byte prefix is discovered once. The carried
; :non-octets task prevents rescanning the same shrinking suffix each time.
(assert-event
 (let* ((x (append (fn-scc-repeat 200 9) (list :x)))
        (c (fn-hrcur-tree-begin x :capture :lease))
        (result (fn-hrcur-test-tree-run 810 c)))
   (and (fn-hrcur-tree-domainp x)
        (equal (car result) :prepared)
        (equal (caddr result) (fn-scc-encode x)))))
