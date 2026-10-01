; Enrollment comparison consumes borrowed same-parse spans, never reparses.
; The parser/source producer establishes span provenance outside this step.
; No allocation authority follows from a span shape or this continuation.
(in-package "ACL2")
(include-book "replay-snapshot-cursor")

(defun fn-rse-span-length (span)
 (declare (xargs :guard t))
 (nfix (fn-rsc-at 2 span)))
(defun fn-rse-span-tail (span)
 (declare (xargs :guard t))
 (fn-rsc-at 3 span))
(defun fn-rse-span-shapep (span)
 (declare (xargs :guard t))
 (and (fn-rsc-widthp 4 span) (eq (fn-rsc-at 0 span) :bytes)
      (natp (fn-rsc-at 1 span)) (natp (fn-rsc-at 2 span))))
(defun fn-rse-keys-shapep (keys)
 (declare (xargs :guard t))
 (and (fn-rsc-widthp 2 keys) (consp (fn-rsc-at 0 keys))
      (consp (fn-rsc-at 1 keys))
      (eq (car (fn-rsc-at 0 keys)) :ed25519)
      (eq (car (fn-rsc-at 1 keys)) :ml-dsa-65)))

(defun fn-rse-key-bytes (n keys)
 (declare (xargs :guard (natp n)))
 (let ((entry (fn-rsc-at n keys)))
  (if (consp entry) (cdr entry) nil)))

; Eight cells: phase, borrowed query keys, borrowed span triple, current
; borrowed source tail, current query tail, remaining octets, source, answer.
(defun fn-rse-equality-state (phase keys spans left right remaining source answer)
 (declare (xargs :guard t))
 (list phase keys spans left right remaining source answer))
(defun fn-rse-equality-start-field (phase keys spans span query source)
 (declare (xargs :guard t))
 (if (fn-rse-span-shapep span)
  (fn-rse-equality-state phase keys spans (fn-rse-span-tail span) query
                         (fn-rse-span-length span) source nil)
  (fn-rse-equality-state :refused keys spans nil nil 0 source nil)))
(defun fn-rse-equality-begin (principal keys spans source)
 (declare (xargs :guard t))
 (if (and (fn-rse-keys-shapep keys) (fn-rsc-widthp 3 spans))
  (fn-rse-equality-start-field :principal keys spans (fn-rsc-at 0 spans)
                                principal source)
  (fn-rse-equality-state :done keys spans nil nil 0 source nil)))
 ; The revoked tombstone/detail comparison has no supplied length. It uses
; the SAME equality continuation with two borrowed resident tails.
(defun fn-rse-equality-begin-tails (left right source)
 (declare (xargs :guard t))
 (fn-rse-equality-state :tails '((:ed25519) (:ml-dsa-65))
  '((:bytes 0 0 nil) (:bytes 0 0 nil) (:bytes 0 0 nil))
  left right 0 source nil))
(defun fn-rse-equality-step (s)
 (declare (xargs :guard t))
 (if (not (fn-rsc-widthp 8 s)) (mv :refused s)
  (let ((phase (fn-rsc-at 0 s)) (keys (fn-rsc-at 1 s))
        (spans (fn-rsc-at 2 s)) (left (fn-rsc-at 3 s))
        (right (fn-rsc-at 4 s)) (remaining (fn-rsc-at 5 s))
        (source (fn-rsc-at 6 s)))
   (cond
    ((eq phase :done) (mv :done s))
    ((eq phase :tails)
     (cond
      ((and (null left) (null right))
       (mv :done (fn-rse-equality-state :done keys spans nil nil 0 source t)))
      ((not (and (consp left) (consp right)
                  (integerp (car left)) (<= 0 (car left)) (< (car left) 256)
                  (integerp (car right)) (<= 0 (car right)) (< (car right) 256)))
       (mv :done (fn-rse-equality-state :done keys spans nil nil 0 source nil)))
      ((not (eql (car left) (car right)))
       (mv :done (fn-rse-equality-state :done keys spans nil nil 0 source nil)))
      (t (mv :working (fn-rse-equality-state :tails keys spans (cdr left) (cdr right)
                       0 source nil)))))
    ((not (and (member-eq phase '(:principal :ed25519 :ml-dsa-65))
                (natp remaining) (fn-rse-keys-shapep keys)
                (fn-rsc-widthp 3 spans))) (mv :refused s))
    ((zp remaining)
     (cond
      ((not (null right))
       (mv :done (fn-rse-equality-state :done keys spans nil nil 0 source nil)))
      ((eq phase :principal)
       (mv :working (fn-rse-equality-start-field :ed25519 keys spans
        (fn-rsc-at 1 spans) (fn-rse-key-bytes 0 keys) source)))
      ((eq phase :ed25519)
       (mv :working (fn-rse-equality-start-field :ml-dsa-65 keys spans
        (fn-rsc-at 2 spans) (fn-rse-key-bytes 1 keys) source)))
      (t (mv :done (fn-rse-equality-state :done keys spans nil nil 0 source t)))))
    ((not (and (consp left) (consp right)
                (integerp (car left)) (<= 0 (car left)) (< (car left) 256)
                (integerp (car right)) (<= 0 (car right)) (< (car right) 256)))
     (mv :done (fn-rse-equality-state :done keys spans nil nil 0 source nil)))
    ((not (eql (car left) (car right)))
     (mv :done (fn-rse-equality-state :done keys spans nil nil 0 source nil)))
    (t (mv :working (fn-rse-equality-state phase keys spans (cdr left) (cdr right)
                     (1- remaining) source nil)))))))

; Logical abstraction only: allocation and traversal here never execute in
; the semantic scheduler or served guards.
(defun fn-rse-span-model (n tail)
 (declare (xargs :guard t :measure (nfix n)))
 (if (zp (nfix n)) nil
  (cons (if (consp tail) (car tail) nil)
        (fn-rse-span-model (1- (nfix n)) (if (consp tail) (cdr tail) nil)))))
(defun fn-rse-enrollment-model (spans)
 (declare (xargs :guard t))
 (list (fn-rse-span-model (fn-rse-span-length (fn-rsc-at 0 spans))
                          (fn-rse-span-tail (fn-rsc-at 0 spans)))
       (list (cons :ed25519
              (fn-rse-span-model (fn-rse-span-length (fn-rsc-at 1 spans))
                                (fn-rse-span-tail (fn-rsc-at 1 spans))))
             (cons :ml-dsa-65
              (fn-rse-span-model (fn-rse-span-length (fn-rsc-at 2 spans))
                                (fn-rse-span-tail (fn-rsc-at 2 spans)))))))

(defun fn-rse-octet-prefixp (n xs)
 (declare (xargs :guard t :measure (nfix n)))
 (if (zp (nfix n)) t
  (and (consp xs) (integerp (car xs)) (<= 0 (car xs)) (< (car xs) 256)
       (fn-rse-octet-prefixp (1- (nfix n)) (cdr xs)))))
(defun fn-rse-span-provenance-shapep (span)
 (declare (xargs :guard t))
 (and (fn-rse-span-shapep span)
      (fn-rse-octet-prefixp (fn-rse-span-length span) (fn-rse-span-tail span))))
(defun fn-rse-spans-provenance-shapep (spans)
 (declare (xargs :guard t))
 (and (fn-rsc-widthp 3 spans)
      (fn-rse-span-provenance-shapep (fn-rsc-at 0 spans))
      (fn-rse-span-provenance-shapep (fn-rsc-at 1 spans))
      (fn-rse-span-provenance-shapep (fn-rsc-at 2 spans))))
(defun fn-rse-equality-invariantp (s)
 (declare (xargs :guard t))
 (and (fn-rsc-widthp 8 s) (fn-rse-keys-shapep (fn-rsc-at 1 s))
      (fn-rse-spans-provenance-shapep (fn-rsc-at 2 s))
      (natp (fn-rsc-at 5 s))
      (member-eq (fn-rsc-at 0 s) '(:principal :ed25519 :ml-dsa-65 :tails :done))
      (fn-rse-octet-prefixp (fn-rsc-at 5 s) (fn-rsc-at 3 s))
      (if (eq (fn-rsc-at 0 s) :tails)
       (and (equal (fn-rsc-at 5 s) 0) (true-listp (fn-rsc-at 3 s))
            (fn-rse-octet-prefixp (len (fn-rsc-at 3 s)) (fn-rsc-at 3 s))) t)))
(defun fn-rse-equality-outcome (s)
 (declare (xargs :guard t))
 (let ((phase (fn-rsc-at 0 s)) (keys (fn-rsc-at 1 s))
       (spans (fn-rsc-at 2 s)))
  (if (eq phase :done) (fn-rsc-at 7 s)
   (if (eq phase :tails) (equal (fn-rsc-at 3 s) (fn-rsc-at 4 s))
   (and (equal (fn-rse-span-model (fn-rsc-at 5 s) (fn-rsc-at 3 s))
               (fn-rsc-at 4 s))
        (or (not (eq phase :principal))
         (equal (fn-rse-span-model (fn-rse-span-length (fn-rsc-at 1 spans))
                                   (fn-rse-span-tail (fn-rsc-at 1 spans)))
                (fn-rse-key-bytes 0 keys)))
        (or (eq phase :ml-dsa-65)
         (equal (fn-rse-span-model (fn-rse-span-length (fn-rsc-at 2 spans))
                                   (fn-rse-span-tail (fn-rsc-at 2 spans)))
                (fn-rse-key-bytes 1 keys))))))))
(defun fn-rse-equality-workleft (s)
 (declare (xargs :guard t))
 (let ((phase (fn-rsc-at 0 s)) (spans (fn-rsc-at 2 s)))
  (cond ((eq phase :tails) (+ 1 (len (fn-rsc-at 3 s))))
        ((eq phase :principal)
         (+ 3 (nfix (fn-rsc-at 5 s))
              (fn-rse-span-length (fn-rsc-at 1 spans))
              (fn-rse-span-length (fn-rsc-at 2 spans))))
        ((eq phase :ed25519)
         (+ 2 (nfix (fn-rsc-at 5 s))
              (fn-rse-span-length (fn-rsc-at 2 spans))))
        ((eq phase :ml-dsa-65) (+ 1 (nfix (fn-rsc-at 5 s))))
        (t 0))))

(local (defthm fn-rse-zero-octet-prefix-unfolds
 (fn-rse-octet-prefixp 0 xs)
 :hints (("Goal" :expand ((fn-rse-octet-prefixp 0 xs))
          :in-theory (disable fn-rse-octet-prefixp)))))
(local (defthm fn-rse-positive-octet-prefix-unfolds
 (implies (and (natp n) (< 0 n) (fn-rse-octet-prefixp n xs))
  (and (consp xs) (integerp (car xs)) (<= 0 (car xs)) (< (car xs) 256)
       (fn-rse-octet-prefixp (1- n) (cdr xs))))
 :hints (("Goal" :expand ((fn-rse-octet-prefixp n xs))
          :in-theory (disable fn-rse-octet-prefixp)))))
(local (defthm fn-rse-positive-span-model-unfolds
 (implies (and (natp n) (< 0 n) (consp xs))
  (equal (fn-rse-span-model n xs)
         (cons (car xs) (fn-rse-span-model (1- n) (cdr xs)))))
 :hints (("Goal" :expand ((fn-rse-span-model n xs))
          :in-theory (disable fn-rse-span-model)))))

(local (defthm fn-rse-keys-reconstruct
 (implies (fn-rse-keys-shapep keys)
  (equal keys (list (cons :ed25519 (fn-rse-key-bytes 0 keys))
                    (cons :ml-dsa-65 (fn-rse-key-bytes 1 keys)))))
 :rule-classes nil
 :hints (("Goal" :expand ((fn-rsc-widthp 2 keys)
                          (fn-rsc-widthp 1 (cdr keys))
                          (fn-rsc-widthp 0 (cddr keys)))
          :in-theory (enable fn-rse-keys-shapep fn-rse-key-bytes fn-rsc-at)))))

; Source-only proof targets. These ghost predicates are not served guards.
(defthm fn-rse-equality-begin-has-exact-public-value-comparison
 (implies (and (fn-rse-keys-shapep keys) (fn-rse-spans-provenance-shapep spans))
  (and (fn-rse-equality-invariantp (fn-rse-equality-begin principal keys spans source))
       (equal (fn-rse-equality-outcome
                (fn-rse-equality-begin principal keys spans source))
              (equal (list principal keys) (fn-rse-enrollment-model spans)))))
 :rule-classes nil
 :hints (("Goal" :use fn-rse-keys-reconstruct
 :in-theory (enable fn-rse-equality-begin fn-rse-equality-start-field
  fn-rse-equality-state fn-rse-equality-outcome fn-rse-equality-invariantp
  fn-rse-spans-provenance-shapep fn-rse-span-provenance-shapep
  fn-rse-enrollment-model fn-rsc-at fn-rsc-widthp fn-rse-keys-shapep fn-rse-key-bytes))))
(defthm fn-rse-tails-begin-has-exact-resident-comparison
 (implies (and (true-listp left) (fn-rse-octet-prefixp (len left) left))
  (and (fn-rse-equality-invariantp (fn-rse-equality-begin-tails left right source))
       (equal (fn-rse-equality-outcome (fn-rse-equality-begin-tails left right source))
              (equal left right))
       (equal (fn-rsc-at 6 (fn-rse-equality-begin-tails left right source)) source)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rse-equality-begin-tails fn-rse-equality-state fn-rse-equality-invariantp
        fn-rse-equality-outcome fn-rse-keys-shapep fn-rse-spans-provenance-shapep
        fn-rse-span-provenance-shapep fn-rse-span-shapep fn-rse-span-length
        fn-rse-span-tail fn-rsc-at fn-rsc-widthp)
       (fn-rse-octet-prefixp fn-rse-span-model)))))
(defthm fn-rse-equality-step-preserves-complete-comparison
 (implies (fn-rse-equality-invariantp s)
  (and (fn-rse-equality-invariantp (mv-nth 1 (fn-rse-equality-step s)))
       (equal (fn-rse-equality-outcome (mv-nth 1 (fn-rse-equality-step s)))
              (fn-rse-equality-outcome s))
       (equal (fn-rsc-at 6 (mv-nth 1 (fn-rse-equality-step s))) (fn-rsc-at 6 s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-rse-equality-step fn-rse-equality-start-field
  fn-rse-equality-state fn-rse-equality-outcome fn-rse-equality-invariantp
  fn-rse-spans-provenance-shapep fn-rse-span-provenance-shapep
  fn-rse-span-shapep fn-rse-span-length fn-rse-span-tail
  fn-rse-keys-shapep fn-rse-key-bytes fn-rsc-at fn-rsc-widthp)
  :use ((:instance fn-rse-positive-octet-prefix-unfolds
           (n (fn-rsc-at 5 s)) (xs (fn-rsc-at 3 s)))
        (:instance fn-rse-positive-span-model-unfolds
           (n (fn-rsc-at 5 s)) (xs (fn-rsc-at 3 s)))
        (:instance fn-rse-positive-octet-prefix-unfolds
           (n (len (fn-rsc-at 3 s))) (xs (fn-rsc-at 3 s)))))))
(defthm fn-rse-equality-working-step-spends-one-quantum
 (implies (and (fn-rse-equality-invariantp s)
               (eq (mv-nth 0 (fn-rse-equality-step s)) :working))
          (< (fn-rse-equality-workleft (mv-nth 1 (fn-rse-equality-step s)))
             (fn-rse-equality-workleft s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-rse-equality-step fn-rse-equality-start-field
  fn-rse-equality-state fn-rse-equality-invariantp fn-rse-equality-workleft
  fn-rse-spans-provenance-shapep fn-rse-span-provenance-shapep
  fn-rse-span-shapep fn-rse-span-length fn-rse-span-tail fn-rse-keys-shapep fn-rse-key-bytes
  fn-rsc-at fn-rsc-widthp))))

; Proof scheduling vocabulary only; the host calls STEP, never this loop.
(defun fn-rse-equality-run (fuel s)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp (nfix fuel)) (mv :yield s)
  (mv-let (status next) (fn-rse-equality-step s)
   (if (eq status :working) (fn-rse-equality-run (1- (nfix fuel)) next)
    (mv status next)))))
(local (defthm fn-rse-step-invariant-rewrite
 (implies (fn-rse-equality-invariantp s)
  (fn-rse-equality-invariantp (mv-nth 1 (fn-rse-equality-step s))))
 :hints (("Goal" :use fn-rse-equality-step-preserves-complete-comparison
  :in-theory (disable fn-rse-equality-step fn-rse-equality-invariantp
                       fn-rse-equality-outcome fn-rsc-at)))))
(local (defthm fn-rse-step-outcome-rewrite
 (implies (fn-rse-equality-invariantp s)
  (equal (fn-rse-equality-outcome (mv-nth 1 (fn-rse-equality-step s)))
         (fn-rse-equality-outcome s)))
 :hints (("Goal" :use fn-rse-equality-step-preserves-complete-comparison
  :in-theory (disable fn-rse-equality-step fn-rse-equality-invariantp
                       fn-rse-equality-outcome fn-rsc-at)))))
(local (defthm fn-rse-step-source-rewrite
 (implies (fn-rse-equality-invariantp s)
  (equal (fn-rsc-at 6 (mv-nth 1 (fn-rse-equality-step s))) (fn-rsc-at 6 s)))
 :hints (("Goal" :use fn-rse-equality-step-preserves-complete-comparison
  :in-theory (disable fn-rse-equality-step fn-rse-equality-invariantp
                       fn-rse-equality-outcome fn-rsc-at)))))
(defthm fn-rse-arbitrary-budget-preserves-comparison-and-borrow
 (implies (fn-rse-equality-invariantp s)
  (and (fn-rse-equality-invariantp (mv-nth 1 (fn-rse-equality-run fuel s)))
       (equal (fn-rse-equality-outcome (mv-nth 1 (fn-rse-equality-run fuel s)))
              (fn-rse-equality-outcome s))
       (equal (fn-rsc-at 6 (mv-nth 1 (fn-rse-equality-run fuel s))) (fn-rsc-at 6 s))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-rse-equality-run fuel s)
  :in-theory (e/d (fn-rse-equality-run)
   (fn-rse-equality-step fn-rse-equality-invariantp fn-rse-equality-outcome fn-rsc-at)))))
(defthm fn-rse-completed-step-exposes-exact-comparison
 (implies (eq (mv-nth 0 (fn-rse-equality-step s)) :done)
  (and (eq (fn-rsc-at 0 (mv-nth 1 (fn-rse-equality-step s))) :done)
       (equal (fn-rse-equality-outcome (mv-nth 1 (fn-rse-equality-step s)))
              (fn-rsc-at 7 (mv-nth 1 (fn-rse-equality-step s))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rse-equality-step fn-rse-equality-state fn-rse-equality-outcome
        fn-rsc-at fn-rsc-widthp)
       (fn-rse-equality-start-field fn-rse-keys-shapep fn-rse-span-model
        fn-rse-span-length fn-rse-span-tail fn-rse-key-bytes)))))
