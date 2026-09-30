; Bounded validation for the actual offline retire-report reader. Each input
; quantum supplies one observed octet or EOF; no report-length array exists.
; RFC 3629 sections 3/4 restrict the scalar encodings. This uses the actual
; shared fn-wildmat-utf8-next, not the 497-octet command-token preflight.
; CLI decode/reencode refinement, FD immutability, I/O effects and runtime
; buffer/lifetime grants remain separate before replacing the real caller.
(in-package "ACL2")
(include-book "utf8")

(defun fn-oru-lead-width (byte)
  (declare (xargs :guard (fn-wildmat-octetp byte)))
  (cond ((< byte 128) 1)
        ((and (<= 194 byte) (<= byte 223)) 2)
        ((and (<= 224 byte) (<= byte 239)) 3)
        ((and (<= 240 byte) (<= byte 244)) 4)
        (t 0)))

(defun fn-oru-cursor (status pending remaining)
  (declare (xargs :guard t))
  (list status pending remaining))

(defun fn-oru-ready-p (cursor)
  (declare (xargs :guard t))
  (and (consp cursor) (consp (cdr cursor)) (consp (cddr cursor))
       (null (cdddr cursor))
       (member-eq (car cursor) '(:checking :valid :invalid))
       ; Short-circuit before the octet predicate: at most four cells ever
       ; reach that predicate, even for a deliberately corrupted argument.
       (fn-wildmat-at-mostp (cadr cursor) 4)
       (fn-wildmat-octet-listp (cadr cursor))
       (natp (caddr cursor)) (<= (caddr cursor) 3)))

(defun fn-oru-start ()
  (declare (xargs :guard t))
  (fn-oru-cursor :checking nil 0))

(defun fn-oru-invariant (cursor)
  (declare (xargs :guard t))
  (and (fn-oru-ready-p cursor)
       (if (equal (car cursor) :checking)
           (if (equal (caddr cursor) 0)
               (equal (cadr cursor) nil)
             (and (consp (cadr cursor))
                  (< (len (cadr cursor)) 4)
                  (equal (+ (len (cadr cursor)) (caddr cursor))
                         (fn-oru-lead-width (car (cadr cursor))))))
         (if (equal (car cursor) :valid)
             (and (equal (cadr cursor) nil) (equal (caddr cursor) 0))
           t))))

(defun fn-oru-step (cursor byte eofp)
  (declare (xargs :guard (and (fn-oru-ready-p cursor)
                              (fn-wildmat-octetp byte))
                  :verify-guards nil))
  (let ((status (car cursor)) (pending (cadr cursor))
        (remaining (caddr cursor)))
    (cond ((not (equal status :checking)) cursor)
          (eofp (fn-oru-cursor (if (equal remaining 0) :valid :invalid)
                               pending remaining))
          ((equal remaining 0)
           (let ((width (fn-oru-lead-width byte)))
             (cond ((equal width 0) (fn-oru-cursor :invalid (list byte) 0))
                   ((equal width 1) (fn-oru-start))
                   (t (fn-oru-cursor :checking (list byte) (1- width))))))
          ((equal remaining 1)
           (let ((next (fn-wildmat-utf8-next (append pending (list byte)))))
             (if (fn-wildmat-result-okp next)
                 (fn-oru-start)
               (fn-oru-cursor :invalid (append pending (list byte)) 0))))
          (t (fn-oru-cursor :checking (append pending (list byte))
                            (1- remaining))))))

(defthm fn-oru-start-establishes-invariant
  (fn-oru-invariant (fn-oru-start))
  :hints (("Goal" :in-theory (enable fn-oru-invariant fn-oru-ready-p fn-oru-start
                                    fn-oru-cursor fn-wildmat-at-mostp))))

(defthm fn-oru-lead-width-range
  (implies (fn-wildmat-octetp byte)
           (and (natp (fn-oru-lead-width byte))
                (<= (fn-oru-lead-width byte) 4)))
  :hints (("Goal" :in-theory (enable fn-oru-lead-width fn-wildmat-octetp))))

(local
 (defthm fn-oru-octet-listp-append-one
   (implies (and (fn-wildmat-octet-listp xs) (fn-wildmat-octetp byte))
            (fn-wildmat-octet-listp (append xs (list byte))))
   :hints (("Goal" :induct (len xs)
            :in-theory (enable fn-wildmat-octet-listp fn-wildmat-octetp
                               fn-cbor-octet-listp)))))

(local
 (defthm fn-oru-at-mostp-is-len
   (implies (natp bound)
            (equal (fn-cbor-at-mostp xs bound) (<= (len xs) bound)))
   :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
            :in-theory (enable fn-wildmat-at-mostp fn-cbor-at-mostp)))))

(local
 (defthm fn-oru-len-append-one
   (equal (len (append xs (list byte))) (+ 1 (len xs)))
   :hints (("Goal" :induct (len xs)))))

(defthm fn-oru-step-preserves-invariant
  (implies (and (fn-oru-invariant cursor) (fn-wildmat-octetp byte))
           (fn-oru-invariant (fn-oru-step cursor byte eofp)))
  :hints (("Goal" :in-theory (enable fn-oru-step fn-oru-invariant fn-oru-ready-p
                                    fn-oru-cursor fn-oru-start fn-oru-lead-width
                                    fn-wildmat-at-mostp))))

(defthm fn-oru-terminal-step-is-stable
  (implies (not (equal (car cursor) :checking))
           (equal (fn-oru-step cursor byte eofp) cursor))
  :hints (("Goal" :in-theory (enable fn-oru-step))))

; The executable ready guard is shorter than the carried relation. Runtime
; invokes it only on established/preserved cursors, never scans the file.
(verify-guards fn-oru-step
  :hints (("Goal" :in-theory (enable fn-oru-ready-p fn-oru-lead-width))))

; Reference/complete-input fold is logical only, never the executable CLI
; read loop. The actual CLI will submit one observed octet/EOF at a time.
(defun fn-oru-run (cursor octets)
  (declare (xargs :measure (len octets)
                  :guard (and (fn-oru-invariant cursor)
                              (fn-wildmat-octet-listp octets))
                  :verify-guards nil))
  (if (not (equal (car cursor) :checking))
      cursor
    (if (consp octets)
        (fn-oru-run (fn-oru-step cursor (car octets) nil) (cdr octets))
      (fn-oru-step cursor 0 t))))

(defthm fn-oru-run-preserves-invariant
  (implies (and (fn-oru-invariant cursor) (fn-wildmat-octet-listp octets))
           (fn-oru-invariant (fn-oru-run cursor octets)))
  :hints (("Goal" :induct (fn-oru-run cursor octets)
           :in-theory (e/d (fn-oru-run fn-wildmat-octet-listp)
                           (fn-oru-invariant fn-oru-step fn-wildmat-utf8-next)))))

(local
 (defthm fn-oru-invariant-ready-by-definition
   (implies (fn-oru-invariant cursor)
            (and (consp cursor) (fn-oru-ready-p cursor)))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-oru-invariant fn-oru-ready-p)))))

(verify-guards fn-oru-run
  :hints (("Goal" :in-theory (e/d (fn-wildmat-octet-listp)
                                   (fn-oru-invariant fn-oru-ready-p fn-oru-step)))))

(local
 (defthm fn-oru-zero-len-append
   (implies (equal (len xs) 0) (equal (append xs ys) ys))
   :hints (("Goal" :cases ((consp xs)) :in-theory (enable len)))))

; A complete code-unit prefix has the width of its leading octet. Additional
; input cannot change either its scalar/error or exact consumed prefix.
(local
 (defthm fn-oru-next-prefix-1
   (implies (equal (fn-oru-lead-width a) 1)
            (equal (fn-wildmat-utf8-next (list* a suffix))
                   (let ((next (fn-wildmat-utf8-next (list a))))
                     (if (fn-wildmat-result-okp next)
                         (fn-wildmat-utf8-ok (fn-wildmat-result-value next) suffix)
                       next))))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable fn-oru-lead-width fn-wildmat-utf8-next
                    fn-wildmat-octetp fn-wildmat-result-okp
                    fn-wildmat-result-value fn-wildmat-utf8-ok
                    fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                    fn-wildmat-utf8-4-tailsp fn-wildmat-utf8-2-value
                    fn-wildmat-utf8-3-value fn-wildmat-utf8-4-value)))))

(local
 (defthm fn-oru-next-prefix-2
   (implies (equal (fn-oru-lead-width a) 2)
            (equal (fn-wildmat-utf8-next (list* a b suffix))
                   (let ((next (fn-wildmat-utf8-next (list a b))))
                     (if (fn-wildmat-result-okp next)
                         (fn-wildmat-utf8-ok (fn-wildmat-result-value next) suffix)
                       next))))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable fn-oru-lead-width fn-wildmat-utf8-next
                    fn-wildmat-octetp fn-wildmat-result-okp
                    fn-wildmat-result-value fn-wildmat-utf8-ok
                    fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                    fn-wildmat-utf8-4-tailsp fn-wildmat-utf8-2-value
                    fn-wildmat-utf8-3-value fn-wildmat-utf8-4-value)))))

(local
 (defthm fn-oru-next-prefix-3
   (implies (equal (fn-oru-lead-width a) 3)
            (equal (fn-wildmat-utf8-next (list* a b c suffix))
                   (let ((next (fn-wildmat-utf8-next (list a b c))))
                     (if (fn-wildmat-result-okp next)
                         (fn-wildmat-utf8-ok (fn-wildmat-result-value next) suffix)
                       next))))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable fn-oru-lead-width fn-wildmat-utf8-next
                    fn-wildmat-octetp fn-wildmat-result-okp
                    fn-wildmat-result-value fn-wildmat-utf8-ok
                    fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                    fn-wildmat-utf8-4-tailsp fn-wildmat-utf8-2-value
                    fn-wildmat-utf8-3-value fn-wildmat-utf8-4-value)))))

(local
 (defthm fn-oru-next-prefix-4
   (implies (equal (fn-oru-lead-width a) 4)
            (equal (fn-wildmat-utf8-next (list* a b c d suffix))
                   (let ((next (fn-wildmat-utf8-next (list a b c d))))
                     (if (fn-wildmat-result-okp next)
                         (fn-wildmat-utf8-ok (fn-wildmat-result-value next) suffix)
                       next))))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable fn-oru-lead-width fn-wildmat-utf8-next
                    fn-wildmat-octetp fn-wildmat-result-okp
                    fn-wildmat-result-value fn-wildmat-utf8-ok
                    fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                    fn-wildmat-utf8-4-tailsp fn-wildmat-utf8-2-value
                    fn-wildmat-utf8-3-value fn-wildmat-utf8-4-value)))))

(local
 (defthm fn-oru-proper-zero-length-by-definition
   (implies (and (true-listp xs) (equal (len xs) 0)) (equal xs nil))
   :rule-classes nil
   :hints (("Goal" :cases ((consp xs)) :in-theory (enable len true-listp)))))

(local
 (defthm fn-oru-proper-spine-1-by-definition
   (implies (and (true-listp xs) (equal (len xs) 1))
            (and (consp xs) (equal (cdr xs) nil)))
   :rule-classes nil
   :hints (("Goal" :cases ((consp xs))
            :expand ((true-listp xs) (len xs))
            :use ((:instance fn-oru-proper-zero-length-by-definition (xs (cdr xs))))
            :in-theory (disable len true-listp)))))

(local
 (defthm fn-oru-proper-spine-2-by-definition
   (implies (and (true-listp xs) (equal (len xs) 2))
            (and (consp xs) (consp (cdr xs)) (equal (cdr (cdr xs)) nil)))
   :rule-classes nil
   :hints (("Goal" :cases ((consp xs))
            :expand ((true-listp xs) (len xs))
            :use ((:instance fn-oru-proper-spine-1-by-definition (xs (cdr xs))))
            :in-theory (disable len true-listp)))))

(local
 (defthm fn-oru-proper-spine-3-by-definition
   (implies (and (true-listp xs) (equal (len xs) 3))
            (and (consp xs) (consp (cdr xs)) (consp (cdr (cdr xs))) (equal (cdr (cdr (cdr xs))) nil)))
   :rule-classes nil
   :hints (("Goal" :cases ((consp xs))
            :expand ((true-listp xs) (len xs))
            :use ((:instance fn-oru-proper-spine-2-by-definition (xs (cdr xs))))
            :in-theory (disable len true-listp)))))

(local
 (defthm fn-oru-proper-spine-4-by-definition
   (implies (and (true-listp xs) (equal (len xs) 4))
            (and (consp xs) (consp (cdr xs)) (consp (cdr (cdr xs))) (consp (cdr (cdr (cdr xs)))) (equal (cdr (cdr (cdr (cdr xs)))) nil)))
   :rule-classes nil
   :hints (("Goal" :cases ((consp xs))
            :expand ((true-listp xs) (len xs))
            :use ((:instance fn-oru-proper-spine-3-by-definition (xs (cdr xs))))
            :in-theory (disable len true-listp)))))

(local
 (defthm fn-oru-next-rest-1
   (implies (equal (fn-oru-lead-width a) 1)
            (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next (list a))) nil))
   :hints (("Goal" :in-theory
            (e/d (fn-oru-lead-width fn-wildmat-utf8-next fn-wildmat-utf8-rest
                    fn-wildmat-octetp fn-wildmat-utf8-ok fn-wildmat-error
                    fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                    fn-wildmat-utf8-4-tailsp)
                 nil)))))

(local
 (defthm fn-oru-next-rest-2
   (implies (equal (fn-oru-lead-width a) 2)
            (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next (list a b))) nil))
   :hints (("Goal" :in-theory
            (e/d (fn-oru-lead-width fn-wildmat-utf8-next fn-wildmat-utf8-rest
                    fn-wildmat-octetp fn-wildmat-utf8-ok fn-wildmat-error
                    fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                    fn-wildmat-utf8-4-tailsp)
                 nil)))))

(local
 (defthm fn-oru-next-rest-3
   (implies (equal (fn-oru-lead-width a) 3)
            (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next (list a b c))) nil))
   :hints (("Goal" :in-theory
            (e/d (fn-oru-lead-width fn-wildmat-utf8-next fn-wildmat-utf8-rest
                    fn-wildmat-octetp fn-wildmat-utf8-ok fn-wildmat-error
                    fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                    fn-wildmat-utf8-4-tailsp)
                 nil)))))

(local
 (defthm fn-oru-next-rest-4
   (implies (equal (fn-oru-lead-width a) 4)
            (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next (list a b c d))) nil))
   :hints (("Goal" :in-theory
            (e/d (fn-oru-lead-width fn-wildmat-utf8-next fn-wildmat-utf8-rest
                    fn-wildmat-octetp fn-wildmat-utf8-ok fn-wildmat-error
                    fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                    fn-wildmat-utf8-4-tailsp)
                 nil)))))

(local
 (defthm fn-oru-lead-width-unconditional-range
   (and (natp (fn-oru-lead-width byte))
        (<= (fn-oru-lead-width byte) 4))
   :hints (("Goal" :in-theory (enable fn-oru-lead-width)))))

(defthm fn-oru-complete-prefix-is-actual-next
  (implies (and (true-listp prefix)
                (equal (len prefix) (fn-oru-lead-width (car prefix))))
           (and (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next prefix)) nil)
                (equal (fn-wildmat-utf8-next (append prefix suffix))
                       (let ((next (fn-wildmat-utf8-next prefix)))
                         (if (fn-wildmat-result-okp next)
                             (fn-wildmat-utf8-ok (fn-wildmat-result-value next) suffix)
                           next)))))
  :hints (("Goal" :cases ((equal (fn-oru-lead-width (car prefix)) 1)
                         (equal (fn-oru-lead-width (car prefix)) 2)
                         (equal (fn-oru-lead-width (car prefix)) 3)
                         (equal (fn-oru-lead-width (car prefix)) 4))
           :use ((:instance fn-oru-lead-width-unconditional-range (byte (car prefix)))
                 (:instance fn-oru-proper-spine-1-by-definition (xs prefix)) (:instance fn-oru-proper-spine-2-by-definition (xs prefix)) (:instance fn-oru-proper-spine-3-by-definition (xs prefix)) (:instance fn-oru-proper-spine-4-by-definition (xs prefix))
                 (:instance fn-oru-proper-zero-length-by-definition (xs prefix))
                 (:instance fn-oru-next-prefix-1 (a (car prefix)))
                 (:instance fn-oru-next-rest-1 (a (car prefix)))
                 (:instance fn-oru-next-prefix-2 (a (car prefix)) (b (cadr prefix)))
                 (:instance fn-oru-next-rest-2 (a (car prefix)) (b (cadr prefix)))
                 (:instance fn-oru-next-prefix-3 (a (car prefix)) (b (cadr prefix)) (c (caddr prefix)))
                 (:instance fn-oru-next-rest-3 (a (car prefix)) (b (cadr prefix)) (c (caddr prefix)))
                 (:instance fn-oru-next-prefix-4 (a (car prefix)) (b (cadr prefix)) (c (caddr prefix)) (d (cadddr prefix)))
                 (:instance fn-oru-next-rest-4 (a (car prefix)) (b (cadr prefix)) (c (caddr prefix)) (d (cadddr prefix))))
           :in-theory (disable fn-wildmat-utf8-next fn-oru-lead-width
                               len true-listp fn-wildmat-utf8-rest))))

; Decoder acceptance does not depend on the already-decoded accumulator.
; This is a projection of the actual shared uncapped decoder, not a second
; executable report parser.
(local
 (defthm fn-oru-decode-acceptance-accumulator-independent
   (equal (fn-wildmat-result-okp (fn-wildmat-decode-aux octets acc))
          (fn-wildmat-result-okp (fn-wildmat-decode-aux octets other)))
   :rule-classes nil
   :hints (("Goal" :induct (list (fn-wildmat-decode-aux octets acc)
                          (fn-wildmat-decode-aux octets other))
            :in-theory (e/d (fn-wildmat-decode-aux fn-wildmat-result-okp
                             fn-wildmat-ok fn-wildmat-error)
                            (fn-wildmat-utf8-next fn-wildmat-result-value
                             fn-wildmat-utf8-rest))))))

(defthm fn-oru-complete-prefix-decoder-acceptance
  (implies (and (true-listp prefix)
                (equal (len prefix) (fn-oru-lead-width (car prefix))))
           (equal (fn-wildmat-result-okp
                   (fn-wildmat-decode-aux (append prefix suffix) nil))
                  (and (fn-wildmat-result-okp (fn-wildmat-utf8-next prefix))
                       (fn-wildmat-result-okp
                        (fn-wildmat-decode-aux suffix nil)))))
  :hints (("Goal"
           :use ((:instance fn-oru-complete-prefix-is-actual-next)
                 (:instance fn-oru-lead-width-unconditional-range (byte (car prefix)))
                 (:instance fn-oru-proper-zero-length-by-definition (xs prefix))
                 (:instance fn-oru-decode-acceptance-accumulator-independent
                            (octets suffix)
                            (acc (list (fn-wildmat-result-value
                                        (fn-wildmat-utf8-next prefix))))
                            (other nil)))
           :expand ((fn-wildmat-decode-aux (append prefix suffix) nil))
           :in-theory (e/d (fn-wildmat-result-okp fn-wildmat-utf8-ok
                            fn-wildmat-result-value fn-wildmat-utf8-rest)
                           (fn-wildmat-decode-aux fn-wildmat-utf8-next
                            fn-oru-lead-width len true-listp
                            fn-oru-complete-prefix-is-actual-next)))))

(local
 (defthm fn-oru-incomplete-prefix-is-actual-error
   (implies (and (true-listp prefix)
                 (< (len prefix) (fn-oru-lead-width (car prefix))))
            (not (fn-wildmat-result-okp (fn-wildmat-utf8-next prefix))))
   :hints (("Goal" :cases ((equal (len prefix) 0) (equal (len prefix) 1)
                           (equal (len prefix) 2) (equal (len prefix) 3))
            :use ((:instance fn-oru-lead-width-unconditional-range (byte (car prefix)))
                  (:instance fn-oru-proper-zero-length-by-definition (xs prefix))
                  (:instance fn-oru-proper-spine-1-by-definition (xs prefix))
                  (:instance fn-oru-proper-spine-2-by-definition (xs prefix))
                  (:instance fn-oru-proper-spine-3-by-definition (xs prefix)))
            :in-theory (e/d (fn-oru-lead-width fn-wildmat-utf8-next
                             fn-wildmat-result-okp fn-wildmat-utf8-ok
                             fn-wildmat-error fn-wildmat-octetp
                             fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                             fn-wildmat-utf8-4-tailsp)
                            (len true-listp))))))

(local
 (defthm fn-oru-invalid-lead-is-actual-error
   (implies (and (fn-wildmat-octetp byte)
                 (equal (fn-oru-lead-width byte) 0))
            (not (fn-wildmat-result-okp
                  (fn-wildmat-decode-aux (cons byte rest) nil))))
   :hints (("Goal" :expand ((fn-wildmat-decode-aux (cons byte rest) nil))
            :in-theory (e/d (fn-oru-lead-width fn-wildmat-utf8-next
                             fn-wildmat-result-okp fn-wildmat-error
                             fn-wildmat-octetp fn-wildmat-utf8-2p
                             fn-wildmat-utf8-3-tailsp fn-wildmat-utf8-4-tailsp)
                            (fn-wildmat-decode-aux))))))

; Ghost acceptance of the unread stream; executable STEP never traverses it.
(defun fn-oru-denotation (cursor rest)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car cursor) :checking)
      (fn-wildmat-result-okp
       (fn-wildmat-decode-aux (append (cadr cursor) rest) nil))
    (equal (car cursor) :valid)))

(local
 (defthm fn-oru-append-one-rest-by-definition
   (equal (append (append xs (list byte)) rest)
          (append xs (cons byte rest)))
   :hints (("Goal" :induct (len xs)))))

(local
 (defthm fn-oru-car-append-by-definition
   (implies (consp xs) (equal (car (append xs ys)) (car xs)))))

(local
 (defthm fn-oru-ascii-next-is-accepted
   (implies (and (fn-wildmat-octetp byte)
                 (equal (fn-oru-lead-width byte) 1))
            (fn-wildmat-result-okp (fn-wildmat-utf8-next (list byte))))
   :hints (("Goal" :in-theory (enable fn-oru-lead-width fn-wildmat-utf8-next
                                     fn-wildmat-octetp fn-wildmat-result-okp
                                     fn-wildmat-utf8-ok fn-wildmat-error
                                     fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                                     fn-wildmat-utf8-4-tailsp)))))

(defthm fn-oru-step-conserves-decoder-acceptance
  (implies (and (fn-oru-invariant cursor)
                (fn-wildmat-octetp byte))
           (equal (fn-oru-denotation cursor (cons byte rest))
                  (fn-oru-denotation (fn-oru-step cursor byte nil) rest)))
  :hints (("Goal"
           :use ((:instance fn-oru-complete-prefix-decoder-acceptance
                            (prefix (append (cadr cursor) (list byte))) (suffix rest))
                 (:instance fn-oru-complete-prefix-decoder-acceptance
                            (prefix (list byte)) (suffix rest)))
           :in-theory (e/d (fn-oru-step fn-oru-denotation fn-oru-invariant
                            fn-oru-ready-p fn-oru-cursor fn-oru-start)
                           (fn-oru-lead-width fn-wildmat-utf8-next
                            fn-wildmat-decode-aux fn-wildmat-result-okp
                            fn-oru-complete-prefix-decoder-acceptance)))))

(local
 (defthm fn-oru-octet-list-is-proper-by-definition
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :hints (("Goal" :induct (len xs) :in-theory (enable fn-cbor-octet-listp)))))

(defthm fn-oru-eof-conserves-decoder-acceptance
  (implies (fn-oru-invariant cursor)
           (equal (equal (car (fn-oru-step cursor 0 t)) :valid)
                  (fn-oru-denotation cursor nil)))
  :hints (("Goal"
           :use ((:instance fn-oru-incomplete-prefix-is-actual-error
                            (prefix (cadr cursor))))
           :expand ((fn-wildmat-decode-aux (cadr cursor) nil))
           :in-theory (e/d (fn-oru-invariant fn-oru-ready-p fn-oru-step
                            fn-oru-cursor fn-oru-denotation fn-wildmat-octet-listp
                            fn-wildmat-result-okp fn-wildmat-ok)
                           (fn-wildmat-decode-aux fn-wildmat-utf8-next
                            fn-oru-lead-width fn-oru-incomplete-prefix-is-actual-error)))))

; Complete logical fold only. The CLI reads one octet per executable STEP.
(defthm fn-oru-run-complete-decoder-acceptance
  (implies (and (fn-oru-invariant cursor)
                (fn-wildmat-octet-listp octets))
           (equal (equal (car (fn-oru-run cursor octets)) :valid)
                  (fn-oru-denotation cursor octets)))
  :hints (("Goal" :induct (fn-oru-run cursor octets)
           :in-theory (e/d (fn-oru-run fn-wildmat-octet-listp fn-cbor-octet-listp)
                           (fn-oru-step fn-oru-invariant fn-oru-denotation)))
          ("Subgoal *1/3" :use ((:instance fn-oru-eof-conserves-decoder-acceptance)))
          ("Subgoal *1/1" :in-theory (enable fn-oru-denotation))))

(defthm fn-oru-fresh-run-refines-actual-uncapped-decoder
  (implies (fn-wildmat-octet-listp octets)
           (equal (equal (car (fn-oru-run (fn-oru-start) octets)) :valid)
                  (fn-wildmat-result-okp (fn-wildmat-decode-aux octets nil))))
  :hints (("Goal" :use ((:instance fn-oru-run-complete-decoder-acceptance
                                   (cursor (fn-oru-start))))
           :in-theory (e/d (fn-oru-denotation fn-oru-start fn-oru-cursor)
                           (fn-oru-run fn-oru-run-complete-decoder-acceptance)))))

; Fixed controller ABI for the actual two-pass CLI reader. Observations are
; obtained from one opened immutable report descriptor. No output is issued
; during validation or rewind; the host must retain that descriptor until
; completion/error close returns. Library/canonical-byte and lifetime funding
; remain prerequisites for selecting this controller in the public caller.
(defun fn-oru-reader-phasep (phase)
  (declare (xargs :guard t))
  (member-eq phase '(:validate :rewind :copy :done :invalid :error)))

(defun fn-oru-reader-action (cursor phase)
  (declare (xargs :guard (and (fn-oru-ready-p cursor) (fn-oru-reader-phasep phase))))
  (case phase
    (:validate :read-validate)
    (:rewind :rewind)
    (:copy (if (equal (car cursor) :valid) :read-copy :close-invalid))
    (:done :close-valid)
    (:invalid :close-invalid)
    (otherwise :close-error)))

(defun fn-oru-reader-step (cursor phase byte eofp io-okp)
  (declare (xargs :guard (and (fn-oru-ready-p cursor)
                              (fn-oru-reader-phasep phase)
                              (fn-wildmat-octetp byte))
                  :verify-guards nil))
  (cond ((member-eq phase '(:done :invalid :error)) (mv cursor phase nil))
        ((not io-okp) (mv cursor :error nil))
        ((equal phase :validate)
         (let ((next (fn-oru-step cursor byte eofp)))
           (mv next (case (car next) (:valid :rewind) (:invalid :invalid)
                                      (otherwise :validate)) nil)))
        ((not (equal (car cursor) :valid)) (mv cursor :invalid nil))
        ((equal phase :rewind) (mv cursor :copy nil))
        (eofp (mv cursor :done nil))
        (t (mv cursor :copy (list byte)))))

(defun fn-oru-reader-invariant (cursor phase)
  (declare (xargs :guard t))
  (and (fn-oru-invariant cursor) (fn-oru-reader-phasep phase)
       (case phase
         (:validate (equal (car cursor) :checking))
         ((:rewind :copy :done) (equal (car cursor) :valid))
         (:invalid (equal (car cursor) :invalid))
         (otherwise t))))

(local
 (defthm fn-oru-invariant-status-by-definition
   (implies (fn-oru-invariant cursor)
            (or (equal (car cursor) :checking)
                (equal (car cursor) :valid)
                (equal (car cursor) :invalid)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-oru-invariant fn-oru-ready-p)))))

(defthm fn-oru-reader-step-preserves-invariant
  (implies (and (fn-oru-reader-invariant cursor phase)
                (fn-wildmat-octetp byte))
           (fn-oru-reader-invariant
            (mv-nth 0 (fn-oru-reader-step cursor phase byte eofp io-okp))
            (mv-nth 1 (fn-oru-reader-step cursor phase byte eofp io-okp))))
  :hints (("Goal" :use ((:instance fn-oru-invariant-status-by-definition
                                              (cursor (fn-oru-step cursor byte eofp))))
           :in-theory (e/d (fn-oru-reader-step fn-oru-reader-invariant
                                   fn-oru-reader-phasep)
                                  (fn-oru-invariant fn-oru-step)))))

(defthm fn-oru-reader-output-needs-validation-and-rewind
  (implies (and (fn-oru-reader-phasep phase)
                (consp (mv-nth 2 (fn-oru-reader-step cursor phase byte eofp io-okp))))
           (and (equal (car cursor) :valid) (equal phase :copy) io-okp
                (not eofp)
                (equal (mv-nth 2 (fn-oru-reader-step cursor phase byte eofp io-okp))
                       (list byte))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oru-reader-step fn-oru-reader-phasep))))

(verify-guards fn-oru-reader-step)
