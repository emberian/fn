; Representation refinement of the actual byte-fed history decoder.
; This book is proof vocabulary. No served path evaluates an abstraction.
(in-package "ACL2")
(include-book "history-decode-lineage-model")
(local (include-book "arithmetic/top" :dir :system))

(defun-nx fn-hdc-stack-abstract (stack pool)
  (if (consp stack)
      (cons (fn-hdc-abstract (car stack) pool)
            (fn-hdc-stack-abstract (cdr stack) pool))
    nil))

; Actual NIL and CONS byte transitions agree with the existing decoder's
; complete stack effect. Other opcodes suspend in their explicit substates;
; their instruction refinements are proved separately.
(defthm fn-hdc-simple-op-refines-current-step
  (implies (and (eq (nth 0 s) :op)
                (< (nth 7 s) (nth 8 s))
                (member-equal byte '(0 5))
                (or (equal byte 0)
                    (and (consp (nth 9 s)) (consp (cdr (nth 9 s))))))
           (and (equal (nth 7 (fn-hdc-feed byte s)) (+ 1 (nth 7 s)))
                (equal (fn-hdc-stack-abstract (nth 9 (fn-hdc-feed byte s)) pool)
                       (car (fn-scc-step (cons byte rest)
                                         (fn-hdc-stack-abstract (nth 9 s) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((equal byte 0) (equal byte 5))
           :in-theory (enable fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                              fn-hdc-stack-abstract fn-hdc-abstract fn-scc-step))))

(defthm fn-hdc-char-op-refines-current-step
  (implies (and (eq (nth 0 s) :op)
                (< (+ 1 (nth 7 s)) (nth 8 s))
                (fn-scc-octetp byte))
           (and (equal (nth 7 (fn-hdc-feed byte (fn-hdc-feed 7 s)))
                       (+ 2 (nth 7 s)))
                (equal (fn-hdc-stack-abstract
                        (nth 9 (fn-hdc-feed byte (fn-hdc-feed 7 s))) pool)
                       (car (fn-scc-step (cons 7 (cons byte rest))
                                         (fn-hdc-stack-abstract (nth 9 s) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                              fn-hdc-stack-abstract fn-hdc-abstract fn-scc-step
                              fn-scc-octetp))))

; The pending-instruction interpretation uses the old codec's execution,
; not a second executable decoder. No host may call these ghost functions.
(defun-nx fn-hdc-model-done (stack)
  (if (and (consp stack) (null (cdr stack)))
      (list :ok (car stack))
    (list :refused :tree)))

(defun-nx fn-hdc-model-tail (bytes stack)
  (fn-hdc-model-done (fn-scc-run bytes stack)))

(defun-nx fn-hdc-model-payload (op pkg bytes)
  (cond ((equal op 6) bytes)
        ((equal op 3) (coerce (fn-scc-octets-chars bytes) 'string))
        ((equal op 4) (fn-scc-intern pkg (coerce (fn-scc-octets-chars bytes) 'string)))
        (t nil)))

(defun-nx fn-hdc-model-number (op pkg value bytes stack)
  (cond ((equal op 1) (fn-hdc-model-tail bytes (cons value stack)))
        ((equal op 2) (fn-hdc-model-tail bytes (cons (- -1 value) stack)))
        ((and (member-equal op '(3 4 6)) (natp value) (<= value (len bytes)))
         (fn-hdc-model-tail
          (nthcdr value bytes)
          (cons (fn-hdc-model-payload op pkg (take value bytes)) stack)))
        (t (list :refused :tree))))

(defun-nx fn-hdc-model-length (op pkg bytes stack)
  (let ((read (fn-scc-read-nat bytes)))
    (if (consp read)
        (fn-hdc-model-number op pkg (car read) (cdr read) stack)
      (list :refused :tree))))

(defun-nx fn-hdc-denote (s pool)
  (let* ((mode (nth 0 s)) (op (nth 1 s)) (pkg (nth 2 s))
         (number (nth 3 s)) (start (nth 4 s)) (count (nth 5 s))
         (left (nth 6 s)) (pos (nth 7 s)) (end (nth 8 s))
         (stack (fn-hdc-stack-abstract (nth 9 s) pool))
         (bytes (take (nfix (- (nfix end) (nfix pos)))
                      (nthcdr (nfix pos) pool))))
    (cond ((eq mode :op) (fn-hdc-model-tail bytes stack))
          ((eq mode :done) (fn-hdc-model-done stack))
          ((eq mode :char)
           (if (consp bytes)
               (fn-hdc-model-tail (cdr bytes) (cons (code-char (car bytes)) stack))
             (list :refused :tree)))
          ((eq mode :package)
           (if (and (consp bytes) (natp (car bytes)) (< (car bytes) 3))
               (fn-hdc-model-length 4 (car bytes) (cdr bytes) stack)
             (list :refused :tree)))
          ((eq mode :length) (fn-hdc-model-length op pkg bytes stack))
          ((eq mode :digits)
           (if (and (natp (car number)) (<= (car number) (len bytes)))
               (fn-hdc-model-number
                op pkg (fn-hdc-number-value number (take (car number) bytes))
                (nthcdr (car number) bytes) stack)
             (list :refused :tree)))
          ((eq mode :payload)
           (if (and (natp left) (<= left (len bytes)))
               (fn-hdc-model-tail
                (nthcdr left bytes)
                (cons (fn-hdc-model-payload op pkg
                        (take (nfix count) (nthcdr (nfix start) pool))) stack))
             (list :refused :tree)))
          (t (list :refused :tree)))))

(defthm fn-hdc-initial-denotes-current-decoder
  (implies (and (natp offset) (natp count))
           (equal (fn-hdc-denote (fn-hdc-begin offset count epoch lease) pool)
                  (fn-scc-decode-tree (take count (nthcdr offset pool)))))
  :hints (("Goal" :in-theory (enable fn-hdc-begin fn-hdc-state
                                      fn-scc-decode-tree fn-scc-run))))

(local
 (defthm fn-hdc-nth-after-offset
   (implies (and (natp i) (natp j))
            (equal (nth i (nthcdr j pool)) (nth (+ i j) pool)))
   :hints (("Goal" :induct (nthcdr j pool) :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-hdc-take-next
   (implies (natp n)
            (equal (take (+ 1 n) bytes)
                   (append (take n bytes) (list (nth n bytes)))))
   :hints (("Goal" :induct (take n bytes) :in-theory (enable take nth)))))

(local
 (defthm fn-hdc-five-known-octets
   (implies (and (equal (take 4 bytes) '(72 83 84 88))
                 (equal (nth 4 bytes) 65))
            (equal (take 5 bytes) '(72 83 84 88 65)))
   :hints (("Goal" :use ((:instance fn-hdc-take-next (n 4)))
            :in-theory (disable fn-hdc-take-next)))))

; The optimization is a cached comparison with one pre-existing keyword,
; not an assumption that every symbol belongs to a small vocabulary.
(defthm fn-hdc-known-tag-finishes-as-the-source-symbol
  (implies (and (natp start)
                (equal byte (nth (+ 4 start) pool))
                (equal (equal (cadr number) 0)
                       (equal (take 4 (nthcdr start pool)) '(72 83 84 88))))
           (equal (fn-hdc-abstract
                   (fn-hdc-payload-node 4 0 start 5
                     (fn-hdc-tag-byte 4 0 5 1 byte number)) pool)
                  (fn-hdc-model-payload 4 0 (take 5 (nthcdr start pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdc-five-known-octets (bytes (nthcdr start pool)))
                 (:instance fn-hdc-nth-after-offset (i 4) (j start)))
           :in-theory (enable fn-hdc-payload-node fn-hdc-tag-byte fn-hdc-abstract
                              fn-hdc-span fn-hdc-model-payload))))

(defthm fn-hdc-feed-preserves-stack-spine
  (implies (true-listp (nth 9 s))
           (true-listp (nth 9 (fn-hdc-feed byte s))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                              fn-hdc-finish-number))))

(defthm fn-hdc-stack-abstract-singleton-iff
  (implies (true-listp stack)
           (equal (and (consp (fn-hdc-stack-abstract stack pool))
                        (null (cdr (fn-hdc-stack-abstract stack pool))))
                  (and (consp stack) (null (cdr stack)))))
  :hints (("Goal" :in-theory (enable fn-hdc-stack-abstract))))


(local
 (defthm fn-hdc-cdr-after-offset
   (implies (natp i)
            (equal (cdr (nthcdr i pool)) (nthcdr (+ 1 i) pool)))
   :hints (("Goal" :induct (nthcdr i pool) :in-theory (enable nthcdr)))))

(local
 (defthm fn-hdc-source-window-step
   (implies (and (natp pos) (natp end) (< pos end))
            (equal (take (- end pos) (nthcdr pos pool))
                   (cons (nth pos pool)
                         (take (- end (+ 1 pos)) (nthcdr (+ 1 pos) pool)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hdc-nth-after-offset (i 0) (j pos)))
            :expand ((take (- end pos) (nthcdr pos pool)))
            :in-theory (disable fn-hdc-nth-after-offset take nthcdr)))))

(local
 (defthm fn-hdc-window-length
   (equal (len (take n bytes)) (nfix n))
   :hints (("Goal" :induct (take n bytes) :in-theory (enable take)))))

(local
 (defthm fn-hdc-drop-cons-window
   (implies (and (posp n) (equal window (cons byte rest)))
            (equal (nthcdr n window) (nthcdr (1- n) rest)))
   :hints (("Goal" :expand ((nthcdr n (cons byte rest)))
            :in-theory (enable nthcdr)))))

; While a payload has more than one byte left, advancing the actual parser
; changes neither the borrowed complete value nor its following program.
; Source-byte agreement is separately required to preserve the cached tag
; comparison invariant; it is unnecessary to this interior denotation lemma.
(defthm fn-hdc-payload-interior-preserves-denotation
  (implies (and (fn-hdc-statep s) (eq (nth 0 s) :payload)
                (member-equal (nth 1 s) '(3 4 6))
                (< 1 (nth 6 s))
                (<= (nth 6 s) (- (nth 8 s) (nth 7 s))))
           (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdc-source-window-step
                            (pos (nth 7 s)) (end (nth 8 s)))
                 (:instance fn-hdc-drop-cons-window
                            (n (nth 6 s))
                            (window (take (- (nth 8 s) (nth 7 s))
                                          (nthcdr (nth 7 s) pool)))
                            (byte (nth (nth 7 s) pool))
                            (rest (take (- (nth 8 s) (+ 1 (nth 7 s)))
                                        (nthcdr (+ 1 (nth 7 s)) pool)))))
           :in-theory (e/d (fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                                       fn-hdc-denote)
                           (fn-hdc-model-tail fn-hdc-model-payload
                            fn-hdc-model-done fn-hdc-model-length fn-hdc-model-number
                            fn-hdc-source-window-step take nthcdr fn-scc-run)))))

(defun-nx fn-hdc-tag-prefixp (op pkg start count consumed number pool)
  (if (and (equal op 4) (equal pkg 0) (equal count 5))
      (equal (equal (cadr number) 0)
             (equal (take (nfix consumed) (nthcdr (nfix start) pool))
                    (take (nfix consumed) '(72 83 84 88 65))))
    t))

(defthm fn-hdc-payload-node-final-refines
  (implies (and (member-equal op '(3 4 6)) (natp start) (natp count)
                (fn-hdc-tag-prefixp op pkg start count (- count 1) number pool)
                (equal byte (nth (+ start count -1) pool)))
           (equal (fn-hdc-abstract
                   (fn-hdc-payload-node op pkg start count
                     (fn-hdc-tag-byte op pkg count 1 byte number)) pool)
                  (fn-hdc-model-payload op pkg (take count (nthcdr start pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((and (equal op 4) (equal pkg 0) (equal count 5)))
           :use ((:instance fn-hdc-known-tag-finishes-as-the-source-symbol))
           :in-theory (enable fn-hdc-payload-node fn-hdc-tag-byte fn-hdc-abstract
                              fn-hdc-span fn-hdc-model-payload fn-hdc-tag-prefixp))))

(local
 (defthm fn-hdc-model-tail-empty
   (equal (fn-hdc-model-tail nil stack) (fn-hdc-model-done stack))
   :hints (("Goal" :in-theory (enable fn-hdc-model-tail fn-scc-run)))))

(local
 (defthm fn-hdc-nthcdr-zero
   (equal (nthcdr 0 xs) xs)
   :hints (("Goal" :in-theory (enable nthcdr)))))
(local
 (defthm fn-hdc-take-zero
   (equal (take 0 xs) nil)
   :hints (("Goal" :in-theory (enable take)))))
(local
 (defthm fn-hdc-end-distance-one
   (implies (and (natp pos) (equal (+ 1 pos) end))
            (equal (+ -1 (- pos) end) 0))))
(local
 (defthm fn-hdc-stack-abstract-consp
   (equal (consp (fn-hdc-stack-abstract stack pool)) (consp stack))
   :hints (("Goal" :in-theory (enable fn-hdc-stack-abstract)))))
(local
 (defthm fn-hdc-stack-abstract-nonnil-iff
   (implies (true-listp stack)
            (iff (fn-hdc-stack-abstract stack pool) stack))
   :hints (("Goal" :in-theory (enable fn-hdc-stack-abstract)))))

(defthm fn-hdc-final-payload-preserves-denotation
  (implies (and (fn-hdc-statep s) (eq (nth 0 s) :payload)
                (member-equal (nth 1 s) '(3 4 6))
                (equal (nth 6 s) 1) (< 0 (nth 5 s))
                (equal (nth 7 s) (+ (nth 4 s) (nth 5 s) -1))
                (<= (+ (nth 4 s) (nth 5 s)) (nth 8 s))
                (true-listp (nth 9 s))
                (fn-hdc-tag-prefixp (nth 1 s) (nth 2 s) (nth 4 s) (nth 5 s)
                                    (- (nth 5 s) 1) (nth 3 s) pool)
                (equal byte (nth (nth 7 s) pool)))
           (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdc-source-window-step
                            (pos (nth 7 s)) (end (nth 8 s)))
                 (:instance fn-hdc-drop-cons-window
                            (n 1)
                            (window (take (- (nth 8 s) (nth 7 s))
                                          (nthcdr (nth 7 s) pool)))
                            (byte (nth (nth 7 s) pool))
                            (rest (take (- (nth 8 s) (+ 1 (nth 7 s)))
                                        (nthcdr (+ 1 (nth 7 s)) pool))))
                 (:instance fn-hdc-payload-node-final-refines
                            (op (nth 1 s)) (pkg (nth 2 s)) (start (nth 4 s))
                            (count (nth 5 s)) (number (nth 3 s))))
           :in-theory (e/d (fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                                       fn-hdc-denote fn-hdc-stack-abstract fn-hdc-model-done)
                           (fn-hdc-model-tail fn-hdc-model-payload fn-hdc-tag-prefixp
                            fn-hdc-model-length fn-hdc-model-number
                            fn-hdc-source-window-step take nthcdr fn-scc-run)))))

(defthm fn-hdc-char-preserves-denotation
  (implies (and (fn-hdc-statep s) (eq (nth 0 s) :char)
                (< (nth 7 s) (nth 8 s))
                (true-listp (nth 9 s))
                (fn-scc-octetp byte)
                (equal byte (nth (nth 7 s) pool)))
           (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdc-source-window-step
                            (pos (nth 7 s)) (end (nth 8 s))))
           :in-theory (e/d (fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                                       fn-hdc-denote fn-hdc-stack-abstract
                                       fn-hdc-abstract fn-hdc-atom fn-hdc-model-done)
                           (fn-hdc-model-tail fn-hdc-model-payload fn-hdc-tag-prefixp
                            fn-hdc-model-length fn-hdc-model-number
                            fn-hdc-source-window-step take nthcdr fn-scc-run)))))

(defthm fn-hdc-package-preserves-denotation
  (implies (and (fn-hdc-statep s) (eq (nth 0 s) :package)
                (equal (nth 1 s) 4)
                (< (nth 7 s) (nth 8 s))
                (fn-scc-octetp byte)
                (equal byte (nth (nth 7 s) pool)))
           (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdc-source-window-step
                            (pos (nth 7 s)) (end (nth 8 s))))
           :in-theory (e/d (fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                                       fn-hdc-denote fn-scc-octetp
                                       fn-hdc-model-length fn-scc-read-nat)
                           (fn-hdc-model-tail fn-hdc-model-payload fn-hdc-tag-prefixp
                            fn-hdc-model-number
                            fn-hdc-source-window-step take nthcdr fn-scc-run)))))

(local
 (defun fn-hdc-two-take-ind (n m xs)
   (if (zp n) (list m xs)
     (fn-hdc-two-take-ind (1- n) (1- m) (cdr xs)))))

(local
 (defthm fn-hdc-take-shorter-window
   (implies (and (natp n) (natp m) (<= n m))
            (equal (take n (take m xs)) (take n xs)))
   :hints (("Goal" :induct (fn-hdc-two-take-ind n m xs)
            :in-theory (enable take)))))

(defthm fn-hdc-finish-number-denotation
  (implies (and (fn-hdc-statep s) (natp value) (natp pos)
                (<= pos (nth 8 s))
                (member-equal op '(1 2 3 4 6)))
           (equal (fn-hdc-denote (fn-hdc-finish-number value op pkg pos stack s) pool)
                  (fn-hdc-model-number
                   op pkg value (take (- (nth 8 s) pos) (nthcdr pos pool))
                   (fn-hdc-stack-abstract stack pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hdc-finish-number fn-hdc-move fn-hdc-state fn-hdc-denote
                            fn-hdc-stack-abstract fn-hdc-abstract fn-hdc-span fn-hdc-atom
                            fn-hdc-model-number fn-hdc-model-payload)
                           (fn-hdc-model-tail fn-hdc-model-done
                            fn-hdc-model-length fn-hdc-source-window-step
                            take nthcdr fn-scc-run)))))

(local
 (defthm fn-hdc-long-enough-is-length
   (implies (natp n)
            (equal (fn-scc-long-enoughp n bytes) (<= n (len bytes))))
   :hints (("Goal" :induct (fn-scc-long-enoughp n bytes)
            :in-theory (enable fn-scc-long-enoughp len)))))

(local
 (defthm fn-hdc-window-head
   (implies (and (natp pos) (natp end) (< pos end))
            (equal (car (take (- end pos) (nthcdr pos pool))) (nth pos pool)))
   :hints (("Goal" :use fn-hdc-source-window-step
            :in-theory (disable fn-hdc-source-window-step take nthcdr)))))
(local
 (defthm fn-hdc-window-tail
   (implies (and (natp pos) (natp end) (< pos end))
            (equal (cdr (take (- end pos) (nthcdr pos pool)))
                   (take (- end (+ 1 pos)) (nthcdr (+ 1 pos) pool))))
   :hints (("Goal" :use fn-hdc-source-window-step
            :in-theory (disable fn-hdc-source-window-step take nthcdr)))))

(defthm fn-hdc-length-preserves-denotation
  (implies (and (fn-hdc-statep s) (eq (nth 0 s) :length)
                (member-equal (nth 1 s) '(1 2 3 4 6))
                (< (nth 7 s) (nth 8 s))
                (true-listp (nth 9 s))
                (fn-scc-octetp byte)
                (equal byte (nth (nth 7 s) pool)))
           (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdc-window-head
                            (pos (nth 7 s)) (end (nth 8 s)))
                 (:instance fn-hdc-window-tail
                            (pos (nth 7 s)) (end (nth 8 s))))
           :in-theory (e/d (fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                            fn-hdc-denote fn-hdc-finish-number fn-hdc-model-length
                            fn-hdc-model-number fn-hdc-model-payload
                            fn-hdc-number-begin fn-hdc-number-value
                            fn-scc-read-nat fn-scc-octetp fn-hdc-stack-abstract
                            fn-hdc-abstract fn-hdc-span fn-hdc-atom fn-hdc-model-done)
                           (fn-hdc-model-tail fn-hdc-tag-prefixp
                            fn-scc-le-value fn-scc-long-enoughp
                            fn-hdc-window-head fn-hdc-window-tail
                            fn-hdc-source-window-step take nthcdr fn-scc-run)))))

(local
 (defthm fn-hdc-take-cons-window
   (implies (and (posp n) (equal window (cons byte rest)))
            (equal (take n window) (cons byte (take (1- n) rest))))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-hdc-window-tail-length
   (equal (len (cdr (take n xs))) (if (posp n) (1- n) 0))
   :hints (("Goal" :expand ((take n xs)) :in-theory (enable take)))))
(local
 (defthm fn-hdc-window-consp
   (equal (consp (take n xs)) (posp n))
   :hints (("Goal" :expand ((take n xs)) :in-theory (enable take)))))
(local
 (defthm fn-hdc-numeric-fields
   (implies (fn-hdc-numberp number)
            (and (natp (car number)) (natp (cadr number)) (posp (caddr number))))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-hdc-numberp)))))

(defthm fn-hdc-digits-preserves-denotation
  (implies (and (fn-hdc-statep s) (eq (nth 0 s) :digits)
                (member-equal (nth 1 s) '(1 2 3 4 6))
                (posp (car (nth 3 s)))
                (< (nth 7 s) (nth 8 s))
                (true-listp (nth 9 s))
                (fn-scc-octetp byte)
                (equal byte (nth (nth 7 s) pool)))
           (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdc-take-shorter-window
                            (n (+ (cadr (nth 3 s)) (* (caddr (nth 3 s)) byte)))
                            (m (- (nth 8 s) (+ 1 (nth 7 s))))
                            (xs (nthcdr (+ 1 (nth 7 s)) pool)))
                 (:instance fn-hdc-window-head
                            (pos (nth 7 s)) (end (nth 8 s)))
                 (:instance fn-hdc-window-tail
                            (pos (nth 7 s)) (end (nth 8 s)))
                 (:instance fn-hdc-source-window-step
                            (pos (nth 7 s)) (end (nth 8 s)))
                 (:instance fn-hdc-number-feed-preserves-value
                            (c (nth 3 s))
                            (suffix (take (1- (car (nth 3 s)))
                                      (take (- (nth 8 s) (+ 1 (nth 7 s)))
                                            (nthcdr (+ 1 (nth 7 s)) pool))))))
           :in-theory (e/d (fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                            fn-hdc-denote fn-hdc-finish-number fn-hdc-number-feed
                            fn-hdc-numberp fn-hdc-number-value fn-hdc-model-number
                            fn-hdc-model-payload fn-scc-octetp fn-hdc-stack-abstract
                            fn-hdc-abstract fn-hdc-span fn-hdc-atom fn-hdc-model-done)
                           (fn-hdc-model-tail fn-hdc-tag-prefixp fn-scc-le-value
                            fn-hdc-take-shorter-window
                            fn-hdc-source-window-step fn-hdc-window-head fn-hdc-window-tail
                            len take nthcdr fn-scc-run)))))

(defun-nx fn-hdc-model-op (byte bytes stack)
  (cond ((equal byte 0) (fn-hdc-model-tail bytes (cons nil stack)))
        ((member-equal byte '(1 2 3 6)) (fn-hdc-model-length byte 0 bytes stack))
        ((equal byte 4)
         (if (and (consp bytes) (natp (car bytes)) (< (car bytes) 3))
             (fn-hdc-model-length 4 (car bytes) (cdr bytes) stack)
           '(:refused :tree)))
        ((equal byte 7)
         (if (consp bytes)
             (fn-hdc-model-tail (cdr bytes) (cons (code-char (car bytes)) stack))
           '(:refused :tree)))
        ((and (equal byte 5) (consp stack) (consp (cdr stack)))
         (fn-hdc-model-tail bytes (cons (cons (cadr stack) (car stack)) (cddr stack))))
        (t '(:refused :tree))))

(local
 (defthm fn-hdc-package-selection
   (implies (natp n)
            (iff (fn-scc-package-index (nth n *fn-scc-packages*)) (< n 3)))
   :hints (("Goal" :cases ((equal n 0) (equal n 1) (equal n 2))
            :in-theory (enable nth fn-scc-package-index)))))

(local
 (defthm fn-hdc-run-empty
   (equal (fn-scc-run nil stack) stack)
   :hints (("Goal" :in-theory (enable fn-scc-run)))))

(defthm fn-hdc-model-op-is-current-run
  (implies (and (fn-scc-octetp byte) (fn-scc-octet-listp bytes))
           (equal (fn-hdc-model-op byte bytes stack)
                  (fn-hdc-model-tail (cons byte bytes) stack)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-step-shrinks (xs (cons byte bytes)))
                 (:instance fn-scc-read-nat-facts (xs bytes))
                 (:instance fn-scc-read-nat-facts (xs (cdr bytes))))
           :expand ((:free (b rest st) (fn-scc-run (cons b rest) st)))
           :in-theory (e/d (fn-hdc-model-op fn-hdc-model-tail fn-hdc-model-done
                            fn-hdc-model-length fn-hdc-model-number fn-hdc-model-payload
                            fn-scc-step fn-scc-read-string fn-scc-octetp)
                           (fn-scc-run fn-scc-read-nat fn-scc-intern
                            fn-scc-octets-chars fn-scc-long-enoughp take nthcdr)))))

(defthm fn-hdc-op-feed-denotes-model-op
  (implies (and (fn-hdc-statep s) (eq (nth 0 s) :op)
                (< (nth 7 s) (nth 8 s))
                (true-listp (nth 9 s)) (fn-scc-octetp byte))
           (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                  (fn-hdc-model-op
                   byte (take (- (nth 8 s) (+ 1 (nth 7 s)))
                              (nthcdr (+ 1 (nth 7 s)) pool))
                   (fn-hdc-stack-abstract (nth 9 s) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-state
                            fn-hdc-denote fn-hdc-model-op fn-hdc-stack-abstract
                            fn-hdc-abstract fn-hdc-atom fn-hdc-pair fn-hdc-model-done
                            fn-hdc-model-length fn-scc-read-nat fn-scc-octetp)
                           (fn-hdc-model-tail fn-hdc-model-number fn-hdc-model-payload
                            fn-scc-run take nthcdr fn-scc-long-enoughp)))))

(defthm fn-hdc-op-preserves-denotation
  (implies (and (fn-hdc-statep s) (eq (nth 0 s) :op)
                (< (nth 7 s) (nth 8 s))
                (true-listp (nth 9 s)) (fn-scc-octetp byte)
                (equal byte (nth (nth 7 s) pool))
                (fn-scc-octet-listp
                 (take (- (nth 8 s) (+ 1 (nth 7 s)))
                       (nthcdr (+ 1 (nth 7 s)) pool))))
           (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdc-op-feed-denotes-model-op)
                 (:instance fn-hdc-model-op-is-current-run
                            (bytes (take (- (nth 8 s) (+ 1 (nth 7 s)))
                                         (nthcdr (+ 1 (nth 7 s)) pool)))
                            (stack (fn-hdc-stack-abstract (nth 9 s) pool)))
                 (:instance fn-hdc-source-window-step
                            (pos (nth 7 s)) (end (nth 8 s))))
           :in-theory (e/d (fn-hdc-denote)
                           (fn-hdc-model-tail fn-hdc-model-op fn-hdc-stack-abstract
                            fn-hdc-feed fn-hdc-source-window-step
                            take nthcdr fn-scc-run)))))

(defthm fn-hdc-tag-prefix-advances
  (implies (and (natp start) (natp count) (posp left) (<= left count)
                (fn-hdc-tag-prefixp op pkg start count (- count left) number pool)
                (equal byte (nth (+ start count (- left)) pool)))
           (fn-hdc-tag-prefixp op pkg start count (+ 1 count (- left))
                               (fn-hdc-tag-byte op pkg count left byte number) pool))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((not (and (equal op 4) (equal pkg 0) (equal count 5)))
                   (equal left 1) (equal left 2) (equal left 3)
                   (equal left 4) (equal left 5))
           :expand ((:free (xs) (take 1 xs)) (:free (xs) (take 2 xs))
                    (:free (xs) (take 3 xs)) (:free (xs) (take 4 xs))
                    (:free (xs) (take 5 xs)))
           :use ((:instance fn-hdc-take-next
                            (n (- count left)) (bytes (nthcdr start pool)))
                 (:instance fn-hdc-nth-after-offset (i (- count left)) (j start)))
           :in-theory (e/d (fn-hdc-tag-prefixp fn-hdc-tag-byte take nth)
                           (fn-hdc-take-next fn-hdc-nth-after-offset nthcdr)))))

(defun-nx fn-hdc-coherent (s pool)
  (and (fn-hdc-statep s) (true-listp (nth 9 s))
       (or (member-eq (nth 0 s) '(:done :refused)) (< (nth 7 s) (nth 8 s)))
       (cond ((eq (nth 0 s) :package) (equal (nth 1 s) 4))
             ((eq (nth 0 s) :length) (member-equal (nth 1 s) '(1 2 3 4 6)))
             ((eq (nth 0 s) :digits)
              (and (member-equal (nth 1 s) '(1 2 3 4 6)) (posp (car (nth 3 s)))))
             ((eq (nth 0 s) :payload)
              (and (member-equal (nth 1 s) '(3 4 6))
                   (posp (nth 6 s)) (<= (nth 6 s) (nth 5 s))
                   (equal (nth 7 s) (+ (nth 4 s) (nth 5 s) (- (nth 6 s))))
                   (<= (+ (nth 4 s) (nth 5 s)) (nth 8 s))
                   (fn-hdc-tag-prefixp (nth 1 s) (nth 2 s) (nth 4 s) (nth 5 s)
                                       (- (nth 5 s) (nth 6 s)) (nth 3 s) pool)))
             (t t))))

(defthm fn-hdc-begin-coherent
  (implies (and (natp offset) (natp count))
           (fn-hdc-coherent (fn-hdc-begin offset count epoch lease) pool))
  :hints (("Goal" :in-theory (enable fn-hdc-coherent fn-hdc-begin fn-hdc-state
                                      fn-hdc-statep fn-hdc-numberp fn-hdc-number-begin))))

(local
 (defthm fn-hdc-empty-tag-prefix
   (fn-hdc-tag-prefixp op pkg start count 0 '(0 0 1) pool)
   :hints (("Goal" :in-theory (enable fn-hdc-tag-prefixp)))))

(defthm fn-hdc-feed-preserves-coherence
  (implies (and (fn-hdc-coherent s pool) (fn-scc-octetp byte)
                (equal byte (nth (nth 7 s) pool)))
           (fn-hdc-coherent (fn-hdc-feed byte s) pool))
  :hints (("Goal" :do-not-induct t
           :use (fn-hdc-feed-valid fn-hdc-feed-preserves-stack-spine
                 (:instance fn-hdc-tag-prefix-advances
                            (op (nth 1 s)) (pkg (nth 2 s)) (start (nth 4 s))
                            (count (nth 5 s)) (left (nth 6 s)) (number (nth 3 s))))
           :in-theory (e/d (fn-hdc-coherent fn-hdc-feed fn-hdc-feed-raw
                            fn-hdc-move fn-hdc-state fn-hdc-finish-number
                            fn-hdc-number-feed fn-hdc-number-begin fn-scc-octetp)
                           (fn-hdc-feed-valid fn-hdc-feed-preserves-stack-spine
                            fn-hdc-tag-prefixp fn-hdc-statep fn-hdc-tag-byte
                            fn-hdc-payload-node)))))

(local
 (defthm fn-hdc-nthcdr-length
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))
   :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr len)))))

(local
 (defthm fn-hdc-source-window-octets
   (implies (and (fn-scc-octet-listp pool) (natp pos) (natp end)
                 (<= pos end) (<= end (len pool)))
            (fn-scc-octet-listp (take (- end pos) (nthcdr pos pool))))
   :hints (("Goal" :in-theory (disable take nthcdr fn-scc-octet-listp)))))

(local
 (defthm fn-hdc-terminal-feed-unchanged
   (implies (member-eq (nth 0 s) '(:done :refused))
            (equal (fn-hdc-feed byte s) s))
   :hints (("Goal" :in-theory (enable fn-hdc-feed fn-hdc-feed-raw)))))

(defthm fn-hdc-feed-preserves-denotation
  (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
                (<= (nth 8 s) (len pool))
                (fn-scc-octetp byte) (equal byte (nth (nth 7 s) pool)))
           (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((eq (nth 0 s) :op) (eq (nth 0 s) :length)
                   (eq (nth 0 s) :digits) (eq (nth 0 s) :package)
                   (eq (nth 0 s) :char) (eq (nth 0 s) :payload)
                   (eq (nth 0 s) :done) (eq (nth 0 s) :refused))
           :use (fn-hdc-op-preserves-denotation fn-hdc-length-preserves-denotation
                 fn-hdc-digits-preserves-denotation fn-hdc-package-preserves-denotation
                 fn-hdc-char-preserves-denotation fn-hdc-payload-interior-preserves-denotation
                 fn-hdc-final-payload-preserves-denotation
                 (:instance fn-hdc-source-window-octets
                            (pos (+ 1 (nth 7 s))) (end (nth 8 s))))
           :in-theory (e/d (fn-hdc-coherent)
                           (fn-hdc-denote fn-hdc-feed fn-hdc-source-window-octets
                            fn-hdc-tag-prefixp fn-scc-octet-listp)) )
          ("Subgoal 9" :in-theory (e/d (fn-hdc-coherent fn-hdc-statep)
                                       (fn-hdc-feed fn-hdc-denote fn-hdc-tag-prefixp)))))

(defthm fn-hdc-coherent-fields
  (implies (fn-hdc-coherent s pool)
           (and (fn-hdc-statep s) (true-listp (nth 9 s))
                (or (member-eq (nth 0 s) '(:done :refused))
                    (< (nth 7 s) (nth 8 s)))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-hdc-coherent))))

(local
 (defthm fn-hdc-source-octet
   (implies (and (fn-scc-octet-listp pool) (natp pos) (< pos (len pool)))
            (fn-scc-octetp (nth pos pool)))
   :hints (("Goal" :induct (nth pos pool)
            :in-theory (enable nth fn-scc-octet-listp fn-scc-octetp)))))

; Proof-only traversal of repeated public feed calls. No host executes this
; whole-source driver; host scheduling remains one fn-hdc-feed per source byte.
; Exact model definition is supplied by history-decode-lineage-model.


; Exact model definition is supplied by history-decode-lineage-model.


(local
 (defthm fn-hdc-active-source-octet
   (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
                 (<= (nth 8 s) (len pool))
                 (not (member-eq (nth 0 s) '(:done :refused))))
            (fn-scc-octetp (nth (nth 7 s) pool)))
   :hints (("Goal" :use ((:instance fn-hdc-source-octet (pos (nth 7 s))))
            :in-theory (e/d (fn-hdc-coherent)
                            (fn-hdc-source-octet fn-hdc-statep fn-hdc-tag-prefixp
                             fn-scc-octet-listp fn-scc-octetp))))))

(defthm fn-hdc-model-run-coherent
  (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
                (<= (nth 8 s) (len pool)))
           (fn-hdc-coherent (fn-hdc-model-run fuel s pool) pool))
  :hints (("Goal" :induct (fn-hdc-model-run fuel s pool)
           :in-theory (e/d (fn-hdc-model-run)
                           (fn-hdc-feed fn-hdc-coherent fn-scc-octet-listp)))))

(defthm fn-hdc-model-run-preserves-denotation
  (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
                (<= (nth 8 s) (len pool)))
           (equal (fn-hdc-denote (fn-hdc-model-run fuel s pool) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hdc-model-run fuel s pool)
           :in-theory (e/d (fn-hdc-model-run)
                           (fn-hdc-feed fn-hdc-coherent fn-scc-octet-listp fn-hdc-denote)))
          ("Subgoal *1/2" :use ((:instance fn-hdc-feed-preserves-denotation
                                         (byte (nth (nth 7 s) pool)))))))

(local
 (defthm fn-hdc-active-feed-advances
   (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
                 (<= (nth 8 s) (len pool))
                 (not (member-eq (nth 0 s) '(:done :refused))))
            (equal (nth 7 (fn-hdc-feed (nth (nth 7 s) pool) s)) (+ 1 (nth 7 s))))
   :hints (("Goal" :use ((:instance fn-hdc-feed-advances-one-byte
                                   (byte (nth (nth 7 s) pool))))
            :in-theory (e/d (fn-hdc-coherent)
                            (fn-hdc-feed fn-hdc-feed-advances-one-byte fn-scc-octet-listp
                             fn-scc-octetp fn-hdc-tag-prefixp))))))
(local
 (defthm fn-hdc-coherent-at-end-terminal
   (implies (and (fn-hdc-coherent s pool) (equal (nth 7 s) (nth 8 s)))
            (member-equal (nth 0 s) '(:done :refused)))
   :hints (("Goal" :in-theory (enable fn-hdc-coherent)))))

(defthm fn-hdc-model-run-completes
  (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
                (<= (nth 8 s) (len pool))
                (natp fuel) (<= (- (nth 8 s) (nth 7 s)) fuel))
           (member-eq (nth 0 (fn-hdc-model-run fuel s pool)) '(:done :refused)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hdc-model-run fuel s pool)
           :in-theory (e/d (fn-hdc-model-run)
                           (fn-hdc-feed fn-hdc-coherent fn-scc-octet-listp)))
          ("Subgoal *1/1" :use fn-hdc-coherent-at-end-terminal
           :in-theory (e/d (fn-hdc-model-run)
                           (fn-hdc-feed fn-hdc-coherent fn-hdc-coherent-at-end-terminal
                            fn-scc-octet-listp)))
          ("Subgoal *1/2" :use ((:instance fn-hdc-feed-advances-one-byte
                                         (byte (nth (nth 7 s) pool)))))))

(defun-nx fn-hdc-abstract-result (result pool)
  (if (eq (car result) :ok)
      (list :ok (fn-hdc-abstract (cadr result) pool))
    result))

(defthm fn-hdc-terminal-result-is-denotation
  (implies (and (true-listp (nth 9 s))
                (member-eq (nth 0 s) '(:done :refused)))
           (equal (fn-hdc-abstract-result (fn-hdc-result s) pool)
                  (fn-hdc-denote s pool)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-result fn-hdc-abstract-result fn-hdc-denote
                                      fn-hdc-model-done fn-hdc-stack-abstract))))

; Complete arbitrary current-format byte slice, including malformed programs
; and accepted nonminimal scalar spellings. Source I/O/authentication and row
; metadata checks are outside this byte/tree representation boundary.
(local
 (defthm fn-hdc-begin-coordinates-unfolds
   (and (equal (nth 7 (fn-hdc-begin offset count epoch lease)) offset)
        (equal (nth 8 (fn-hdc-begin offset count epoch lease)) (+ offset count)))
   :hints (("Goal" :in-theory (enable fn-hdc-begin fn-hdc-state)))))

(defthm fn-hdc-current-codec-refinement
  (implies (and (fn-scc-octet-listp pool) (natp offset) (natp count)
                (<= (+ offset count) (len pool)))
           (equal
            (fn-hdc-abstract-result
             (fn-hdc-result
              (fn-hdc-model-run count (fn-hdc-begin offset count epoch lease) pool)) pool)
            (fn-scc-decode-tree (take count (nthcdr offset pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-hdc-begin-coherent
                 (:instance fn-hdc-model-run-coherent
                            (fuel count) (s (fn-hdc-begin offset count epoch lease)))
                 (:instance fn-hdc-model-run-preserves-denotation
                            (fuel count) (s (fn-hdc-begin offset count epoch lease)))
                 (:instance fn-hdc-model-run-completes
                            (fuel count) (s (fn-hdc-begin offset count epoch lease)))
                 (:instance fn-hdc-terminal-result-is-denotation
                            (s (fn-hdc-model-run count
                                 (fn-hdc-begin offset count epoch lease) pool))))
           :in-theory (e/d ()
                           (fn-hdc-begin-coherent fn-hdc-model-run-coherent
                            fn-hdc-begin fn-hdc-state fn-hdc-model-run fn-hdc-result fn-hdc-denote
                            fn-hdc-abstract-result fn-scc-decode-tree
                            fn-hdc-coherent take nthcdr)))))

; Scheduler quantum partition and opaque source ownership survive arbitrary
; runs, including an early malformed-program refusal.
(defthm fn-hdc-model-run-preserves-lifetime
  (and (equal (nth 10 (fn-hdc-model-run fuel s pool)) (nth 10 s))
       (equal (nth 11 (fn-hdc-model-run fuel s pool)) (nth 11 s)))
  :hints (("Goal" :induct (fn-hdc-model-run fuel s pool)
           :in-theory (e/d (fn-hdc-model-run) (fn-hdc-feed)))))

(defthm fn-hdc-model-run-fuel-partition
  (implies (and (natp first) (natp second))
           (equal (fn-hdc-model-run second (fn-hdc-model-run first s pool) pool)
                  (fn-hdc-model-run (+ first second) s pool)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hdc-model-run first s pool)
           :in-theory (e/d (fn-hdc-model-run) (fn-hdc-feed)))))

; Carried borrowed-node representation validity; never rescanned at runtime.
; Exact model definition is supplied by history-decode-lineage-model.

; Exact model definition is supplied by history-decode-lineage-model.

(defthm fn-hdc-feed-preserves-borrowed-node-bounds
 (implies (and (fn-hdc-coherent s pool) (fn-scc-octetp byte)
               (fn-hdc-stack-in-poolp (nth 9 s) (nth 8 s)))
          (fn-hdc-stack-in-poolp (nth 9 (fn-hdc-feed byte s)) (nth 8 s)))
 :hints (("Goal" :do-not-induct t
          :in-theory (enable fn-hdc-coherent fn-hdc-feed fn-hdc-feed-raw
                             fn-hdc-move fn-hdc-finish-number fn-hdc-state
                             fn-hdc-stack-in-poolp fn-hdc-node-in-poolp
                             fn-hdc-atom fn-hdc-pair fn-hdc-span
                             fn-hdc-payload-node))))
