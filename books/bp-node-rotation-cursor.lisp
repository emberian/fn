; PRF-1137 planned boundary: exact FNBR payload codec, one bounded turn.
; A resident checkpoint capture owns the referenced source. This library does
; not borrow an arena payload view and is not yet activated by the host.
(in-package "ACL2")
(include-book "bp-node-rotation-codec")
(set-verify-guards-eagerness 0)

(defun fn-bpnrc-begin (x depth)
  (declare (xargs :guard t))
  (list (list :value x depth)))

(defun fn-bpnrc-answer (status bytes tasks)
  (declare (xargs :guard t))
  (list status bytes tasks))

; Prefix chunks never exceed nine octets. Text/octet bodies are carried as
; source references and advance by one cell/character, never copied whole.
(defun fn-bpnrc-counted-start (tag size body rest)
  (declare (xargs :guard t))
  (if (and (natp size) (<= size *fn-bpc-max-uint*))
      (fn-bpnrc-answer :continue
                       (cons tag (fn-bpc-u64-bytes size))
                       (cons body rest))
    (fn-bpnrc-answer :refused nil nil)))

(defun fn-bpnrc-step (tasks)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom tasks)
      (fn-bpnrc-answer :done nil nil)
    (let* ((task (car tasks)) (rest (cdr tasks))
           (kind (fn-bpn-nth 0 task))
           (x (fn-bpn-nth 1 task)))
      (cond
       ((equal kind :value)
        (let ((d (fn-bpn-nth 2 task)))
          (cond
           ((or (not (natp d)) (zp d))
            (fn-bpnrc-answer :refused nil nil))
           ((and (symbolp x) x (not (equal x t)))
            (let ((tag (fn-bpnr-symbol-tag x)) (name (symbol-name x)))
              (if tag
                  (fn-bpnrc-counted-start tag (length name)
                                         (list :text name 0) rest)
                (fn-bpnrc-answer :refused nil nil))))
           ((stringp x)
            (fn-bpnrc-counted-start 7 (length x) (list :text x 0) rest))
           ((consp x)
            (fn-bpnrc-answer :continue nil
                             (cons (list :scan x d x 0) rest)))
           (t
            (let ((bytes (fn-bpnr-enc-leaf x d)))
              (if bytes (fn-bpnrc-answer :continue bytes rest)
                (fn-bpnrc-answer :refused nil nil)))))))
       ((equal kind :scan)
        (let ((d (fn-bpn-nth 2 task)) (cursor (fn-bpn-nth 3 task))
              (count (fn-bpn-nth 4 task)))
          (cond
           ((or (not (natp d)) (zp d) (not (natp count)))
            (fn-bpnrc-answer :refused nil nil))
           ((and (consp cursor) (fn-cbor-octetp (car cursor)))
            (fn-bpnrc-answer :continue nil
                             (cons (list :scan x d (cdr cursor) (1+ count)) rest)))
           ((null cursor)
            (fn-bpnrc-counted-start 9 count (list :octets x) rest))
           ((consp x)
            (fn-bpnrc-answer
             :continue '(10)
             (cons (list :value (car x) (1- d))
                   (cons (list :value (cdr x) (1- d)) rest))))
           (t (fn-bpnrc-answer :refused nil nil)))))
       ((equal kind :octets)
        (if (consp x)
            (if (fn-cbor-octetp (car x))
                (fn-bpnrc-answer :continue (list (car x))
                                 (cons (list :octets (cdr x)) rest))
              (fn-bpnrc-answer :refused nil nil))
          (if (null x) (fn-bpnrc-answer :continue nil rest)
            (fn-bpnrc-answer :refused nil nil))))
       ((equal kind :text)
        (let ((i (fn-bpn-nth 2 task)))
          (if (not (and (stringp x) (natp i) (<= i (length x))))
              (fn-bpnrc-answer :refused nil nil)
            (if (equal i (length x))
                (fn-bpnrc-answer :continue nil rest)
              (let ((code (char-code (char x i))))
                (if (fn-cbor-octetp code)
                    (fn-bpnrc-answer :continue (list code)
                                     (cons (list :text x (1+ i)) rest))
                  (fn-bpnrc-answer :refused nil nil)))))))
       (t (fn-bpnrc-answer :refused nil nil))))))

; This is a scheduling quantum, not an admission ceiling. Its continuation
; keeps source references; a depleted quantum yields without truncation.
(defun fn-bpnrc-run (tasks quantum acc)
  (declare (xargs :guard t :measure (nfix quantum) :verify-guards nil))
  (if (zp (nfix quantum))
      (fn-bpnrc-answer :yield (fn-ag-rev-onto acc nil) tasks)
    (let* ((answer (fn-bpnrc-step tasks))
           (status (fn-bpn-nth 0 answer))
           (bytes (fn-bpn-nth 1 answer))
           (next (fn-bpn-nth 2 answer)))
      (if (equal status :continue)
          (fn-bpnrc-run next (1- (nfix quantum)) (fn-ag-rev-onto bytes acc))
        (fn-bpnrc-answer status (fn-ag-rev-onto acc nil) next)))))

; Census uses the same bounded producer, discarding each bounded chunk.
; It allocates no list of the whole encoded payload.
(defun fn-bpnrc-census-run (tasks quantum count)
  (declare (xargs :guard t :measure (nfix quantum) :verify-guards nil))
  (if (zp (nfix quantum)) (list :yield (nfix count) tasks)
    (let* ((answer (fn-bpnrc-step tasks))
           (status (fn-bpn-nth 0 answer))
           (bytes (fn-bpn-nth 1 answer))
           (next (fn-bpn-nth 2 answer)))
      (if (equal status :continue)
          (fn-bpnrc-census-run next (1- (nfix quantum)) (+ (nfix count) (len bytes)))
        (list status (nfix count) next)))))

(verify-guards fn-bpnrc-begin)
(verify-guards fn-bpnrc-answer)
(verify-guards fn-bpnrc-counted-start)
(verify-guards fn-bpnrc-step)
(verify-guards fn-bpnrc-run)
(verify-guards fn-bpnrc-census-run)

; Logical abstraction only: these walkers are never called on a served tick.
(defun fn-bpnrc-task-residual (task)
  (declare (xargs :guard t :verify-guards nil))
  (let ((kind (fn-bpn-nth 0 task)) (x (fn-bpn-nth 1 task))
        (d (fn-bpn-nth 2 task)))
    (cond ((member-equal kind '(:value :scan))
           (and (natp d) (fn-bpnr-enc x d)))
          ((equal kind :octets) x)
          ((equal kind :text)
           (and (stringp x) (natp d)
                (fn-bpnr-codes (nthcdr d (coerce x 'list)))))
          (t nil))))

(defun fn-bpnrc-residual (tasks)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom tasks) nil
    (append (fn-bpnrc-task-residual (car tasks))
            (fn-bpnrc-residual (cdr tasks)))))

(defun fn-bpnrc-suffix (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp (nfix n)) xs
    (if (consp xs) (fn-bpnrc-suffix (1- (nfix n)) (cdr xs)) nil)))

(defthm fn-bpnrc-suffix-is-nthcdr
  (equal (fn-bpnrc-suffix n xs) (nthcdr (nfix n) xs))
  :hints (("Goal" :induct (fn-bpnrc-suffix n xs)
           :in-theory (enable fn-bpnrc-suffix))))

(defun fn-bpnrc-prefix (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp (nfix n)) nil
    (cons (fn-cbor-ag-car xs)
          (fn-bpnrc-prefix (1- (nfix n)) (fn-cbor-ag-cdr xs)))))

(defthm fn-bpnrc-prefix-is-take
  (equal (fn-bpnrc-prefix n xs) (take (nfix n) xs))
  :hints (("Goal" :induct (fn-bpnrc-prefix n xs)
           :in-theory (enable fn-bpnrc-prefix fn-cbor-ag-car fn-cbor-ag-cdr))))

(defun fn-bpnrc-task-validp (task)
  (declare (xargs :guard t :verify-guards nil))
  (let ((kind (fn-bpn-nth 0 task)) (x (fn-bpn-nth 1 task))
        (d (fn-bpn-nth 2 task)))
    (cond
     ((equal kind :value) (and (natp d) (fn-bpnr-enc x d)))
     ((equal kind :scan)
      (let ((cursor (fn-bpn-nth 3 task)) (count (fn-bpn-nth 4 task)))
        (and (consp x) (natp d) (fn-bpnr-enc x d) (natp count)
             (<= count (len x))
             (equal cursor (fn-bpnrc-suffix count x))
             (fn-cbor-octet-listp (fn-bpnrc-prefix count x)))))
     ((equal kind :octets) (fn-cbor-octet-listp x))
     ((equal kind :text)
      (and (stringp x) (natp d) (<= d (length x))
           (fn-cbor-octet-listp (fn-bpnr-codes (coerce x 'list)))))
     (t nil))))

(defun fn-bpnrc-tasks-validp (tasks)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom tasks) (null tasks)
    (and (fn-bpnrc-task-validp (car tasks))
         (fn-bpnrc-tasks-validp (cdr tasks)))))

(defthm fn-bpnrc-begin-residual-is-exact-encoder-by-definition
  (implies (natp depth)
           (equal (fn-bpnrc-residual (fn-bpnrc-begin x depth))
                  (fn-bpnr-enc x depth)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bpnrc-begin fn-bpnrc-residual
                                     fn-bpnrc-task-residual fn-bpn-nth))))

(local
 (defthm fn-bpnrc-codes-end
   (implies (and (natp i) (<= (len xs) i))
            (equal (fn-bpnr-codes (nthcdr i xs)) nil))
   :hints (("Goal" :induct (nthcdr i xs)
            :in-theory (enable fn-bpnr-codes)))))

(local
 (defthm fn-bpnrc-codes-step
   (implies (and (natp i) (< i (len xs)))
            (equal (fn-bpnr-codes (nthcdr i xs))
                   (cons (if (characterp (nth i xs))
                             (char-code (nth i xs)) 0)
                         (fn-bpnr-codes (nthcdr (+ 1 i) xs)))))
   :hints (("Goal" :induct (nthcdr i xs)
            :in-theory (enable fn-bpnr-codes)))))

(local
 (defthm fn-bpnrc-nthcdr-step
   (implies (natp n)
            (equal (nthcdr (+ 1 n) xs) (cdr (nthcdr n xs))))
   :hints (("Goal" :induct (nthcdr n xs)))))

(local
 (defthm fn-bpnrc-prefix-octets-step
   (implies (and (natp n) (< n (len xs))
                 (fn-cbor-octet-listp (take n xs))
                 (fn-cbor-octetp (car (nthcdr n xs))))
            (fn-cbor-octet-listp (take (+ 1 n) xs)))
   :hints (("Goal" :induct (nthcdr n xs)
            :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-bpnrc-scan-complete
   (implies (and (natp n) (<= n (len xs))
                 (equal (nthcdr n xs) nil)
                 (fn-cbor-octet-listp (take n xs)))
            (and (equal (len xs) n) (fn-cbor-octet-listp xs)))
   :rule-classes nil
   :hints (("Goal" :induct (nthcdr n xs)
            :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-bpnrc-nthcdr-consp-length
   (implies (and (natp n) (consp (nthcdr n xs)))
            (< n (len xs)))
   :hints (("Goal" :induct (nthcdr n xs)))))

(local
 (defthm fn-bpnrc-code-at-is-octet
   (implies (and (natp i) (< i (len xs)) (character-listp xs)
                 (fn-cbor-octet-listp (fn-bpnr-codes xs)))
            (and (characterp (nth i xs))
                 (fn-cbor-octetp (char-code (nth i xs)))))
   :hints (("Goal" :induct (nthcdr i xs)
            :in-theory (enable fn-bpnr-codes fn-cbor-octet-listp)))))

(local
 (defthm fn-bpnrc-codes-length
   (equal (len (fn-bpnr-codes xs)) (len xs))
   :hints (("Goal" :induct (len xs) :in-theory (enable fn-bpnr-codes)))))
(local
 (defthm fn-bpnrc-append-assoc
   (equal (append (append x y) z) (append x y z))
   :hints (("Goal" :induct (len x)))))
(local (defthm fn-bpnrc-nthcdr-zero (equal (nthcdr 0 xs) xs)))

(local
 (defthm fn-bpnrc-octet-suffix-shape
   (implies (and (natp n) (fn-cbor-octet-listp xs))
            (or (null (nthcdr n xs))
                (and (consp (nthcdr n xs))
                     (fn-cbor-octetp (car (nthcdr n xs))))))
   :rule-classes nil
   :hints (("Goal" :induct (nthcdr n xs)
            :in-theory (enable fn-cbor-octet-listp)))))

(defthm fn-bpnrc-step-preserves-exact-residual
  (implies (fn-bpnrc-tasks-validp tasks)
           (let ((answer (fn-bpnrc-step tasks)))
             (and (member-equal (fn-bpn-nth 0 answer) '(:continue :done))
                  (equal (fn-bpnrc-residual tasks)
                         (append (fn-bpn-nth 1 answer)
                                 (fn-bpnrc-residual (fn-bpn-nth 2 answer))))
                  (fn-bpnrc-tasks-validp (fn-bpn-nth 2 answer)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-bpnrc-tasks-validp tasks))
           :use ((:instance fn-bpnrc-octet-suffix-shape
                            (xs (fn-bpn-nth 1 (car tasks)))
                            (n (fn-bpn-nth 4 (car tasks))))
                 (:instance fn-bpnrc-scan-complete
                            (xs (fn-bpn-nth 1 (car tasks)))
                            (n (fn-bpn-nth 4 (car tasks))))
                 (:instance fn-bpnrc-prefix-octets-step
                            (xs (fn-bpn-nth 1 (car tasks)))
                            (n (fn-bpn-nth 4 (car tasks))))
                 (:instance fn-bpnrc-nthcdr-consp-length
                            (xs (fn-bpn-nth 1 (car tasks)))
                            (n (fn-bpn-nth 4 (car tasks)))))
           :in-theory (union-theories
                        '(fn-bpnrc-step fn-bpnrc-counted-start fn-bpnrc-answer
                          fn-bpnrc-tasks-validp fn-bpnrc-task-validp
                          fn-bpnrc-suffix-is-nthcdr fn-bpnrc-prefix-is-take nfix
                          fn-bpnrc-residual fn-bpnrc-task-residual
                          fn-cbor-octet-listp
                          fn-bpnr-enc fn-bpnr-enc-leaf fn-bpnr-counted
                          fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr member-equal
                          (:type-prescription len) take append zp natp length char fn-bpnrc-codes-length fn-bpnrc-append-assoc fn-bpnrc-nthcdr-zero
                          fn-bpnrc-code-at-is-octet character-listp-coerce
                          fn-bpnrc-codes-end fn-bpnrc-codes-step
                          fn-bpnrc-nthcdr-step
                          (:e append) car-cons cdr-cons (:e natp) (:e equal)
                          (:e zp) (:e binary-+) (:e member-equal))
                        (theory 'minimal-theory)))))

(local
 (defthm fn-bpnrc-append-rev-onto
   (equal (append (fn-ag-rev-onto xs acc) tail)
          (fn-ag-rev-onto xs (append acc tail)))
   :hints (("Goal" :induct (fn-ag-rev-onto xs acc)
            :in-theory (enable fn-ag-rev-onto)))))
(local
 (defthm fn-bpnrc-rev-onto-twice
   (equal (fn-ag-rev-onto (fn-ag-rev-onto bytes acc) tail)
          (fn-ag-rev-onto acc (append bytes tail)))))

(local
 (defthm fn-bpnrc-rev-onto-compose
   (equal (fn-ag-rev-onto (fn-ag-rev-onto bytes acc) tail)
          (append (fn-ag-rev-onto acc nil) bytes tail))
   :hints (("Goal" :induct (fn-ag-rev-onto bytes acc)
            :in-theory (enable fn-ag-rev-onto)))))

(local
 (defthm fn-bpnrc-done-emits-no-bytes
   (implies (equal (fn-bpn-nth 0 (fn-bpnrc-step tasks)) :done)
            (equal (fn-bpn-nth 1 (fn-bpnrc-step tasks)) nil))
   :hints (("Goal" :in-theory (union-theories
                                     '(fn-bpnrc-step fn-bpnrc-counted-start
                                       fn-bpnrc-answer fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr
                                       car-cons cdr-cons (:e equal) (:e natp) (:e zp) (:e binary-+))
                                     (theory 'minimal-theory))))))

(defthm fn-bpnrc-quantum-preserves-exact-residual
  (implies (fn-bpnrc-tasks-validp tasks)
           (let ((answer (fn-bpnrc-run tasks quantum acc)))
             (and (member-equal (fn-bpn-nth 0 answer) '(:yield :done))
                  (equal (append (fn-bpn-nth 1 answer)
                                 (fn-bpnrc-residual (fn-bpn-nth 2 answer)))
                         (append (fn-ag-rev-onto acc nil)
                                 (fn-bpnrc-residual tasks)))
                  (fn-bpnrc-tasks-validp (fn-bpn-nth 2 answer)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bpnrc-run tasks quantum acc)
           :in-theory (disable fn-bpnrc-step fn-bpnrc-residual
                               fn-bpnrc-tasks-validp fn-bpnr-enc))
          ("Subgoal *1/3" :use ((:instance fn-bpnrc-step-preserves-exact-residual)))
          ("Subgoal *1/2" :use ((:instance fn-bpnrc-step-preserves-exact-residual)))
          ("Subgoal *1/1" :use ((:instance fn-bpnrc-step-preserves-exact-residual)))))

(local
 (defthm fn-bpnrc-length-of-append
   (equal (len (append x y)) (+ (len x) (len y)))
   :hints (("Goal" :induct (len x)))))

(defthm fn-bpnrc-census-preserves-exact-length
  (implies (fn-bpnrc-tasks-validp tasks)
           (let ((answer (fn-bpnrc-census-run tasks quantum count)))
             (and (member-equal (fn-bpn-nth 0 answer) '(:yield :done))
                  (equal (+ (fn-bpn-nth 1 answer)
                            (len (fn-bpnrc-residual (fn-bpn-nth 2 answer))))
                         (+ (nfix count) (len (fn-bpnrc-residual tasks))))
                  (fn-bpnrc-tasks-validp (fn-bpn-nth 2 answer)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bpnrc-census-run tasks quantum count)
           :in-theory (disable fn-bpnrc-step fn-bpnrc-residual
                               fn-bpnrc-tasks-validp fn-bpnr-enc))
          ("Subgoal *1/3" :use ((:instance fn-bpnrc-step-preserves-exact-residual)))
          ("Subgoal *1/2" :use ((:instance fn-bpnrc-step-preserves-exact-residual)))
          ("Subgoal *1/1" :use ((:instance fn-bpnrc-step-preserves-exact-residual)))))

(defthm fn-bpnrc-step-emits-at-most-nine-bytes
  (<= (len (fn-bpn-nth 1 (fn-bpnrc-step tasks))) 9)
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                        '(fn-bpnrc-step fn-bpnrc-answer fn-bpnrc-counted-start
                          fn-bpnr-enc-leaf fn-bpnr-counted
                          fn-bpc-u64-bytes-have-eight-octets
                          fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr
                          len natp zp car-cons cdr-cons (:e equal) (:e binary-+)
                          (:type-prescription len))
                        (theory 'minimal-theory)))))

(verify-guards fn-bpnrc-prefix)
(verify-guards fn-bpnrc-suffix)
