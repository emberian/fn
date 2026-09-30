; Byte-fed current history tree decoder. Spans borrow payload; no interning,
; string coercion, list reversal, suffix validation or eager pgsmem exists here.
(in-package "ACL2")
(include-book "history-decode-cursor")
(include-book "history-decode-nodes")
(local (include-book "arithmetic/top" :dir :system))

; Twelve constant-sized fields. STACK and decoded nodes are opaque here:
; their invariant is established and carried, never rescanned by a tick.
; MODE OP PKG NUMBER START COUNT LEFT POSITION END STACK EPOCH LEASE.
(defun fn-hdc-state (mode op pkg number start count left pos end stack epoch lease)
  (declare (xargs :guard t))
  (list mode op pkg number start count left pos end stack epoch lease))

(defun fn-hdc-statep (s)
  (declare (xargs :guard t))
  (and (consp s) (consp (cdr s)) (consp (cddr s))
       (consp (cdddr s)) (consp (cddddr s)) (consp (cdr (cddddr s)))
       (consp (cddr (cddddr s))) (consp (cdddr (cddddr s))) (consp (cddddr (cddddr s)))
       (consp (cdr (cddddr (cddddr s)))) (consp (cddr (cddddr (cddddr s)))) (consp (cdddr (cddddr (cddddr s))))
       (null (cddddr (cddddr (cddddr s))))
       (member-eq (nth 0 s) '(:op :length :digits :package :char :payload :done :refused))
       (natp (nth 1 s)) (< (nth 1 s) 8)
       (natp (nth 2 s)) (< (nth 2 s) 3)
       (fn-hdc-numberp (nth 3 s))
       (natp (nth 4 s)) (natp (nth 5 s)) (natp (nth 6 s))
       (natp (nth 7 s)) (natp (nth 8 s)) (<= (nth 7 s) (nth 8 s))))

(defthm fn-hdc-state-constructor
  (equal (fn-hdc-statep (fn-hdc-state mode op pkg number start count left pos end stack epoch lease))
         (and (member-eq mode '(:op :length :digits :package :char :payload :done :refused))
              (natp op) (< op 8) (natp pkg) (< pkg 3) (fn-hdc-numberp number)
              (natp start) (natp count) (natp left) (natp pos) (natp end) (<= pos end))))

(defthm fn-hdc-state-fields
  (implies (fn-hdc-statep s)
           (and (true-listp s) (consp s) (equal (len s) 12)
                (member-eq (nth 0 s) '(:op :length :digits :package :char :payload :done :refused))
                (natp (nth 1 s)) (< (nth 1 s) 8)
                (natp (nth 2 s)) (< (nth 2 s) 3)
                (fn-hdc-numberp (nth 3 s))
                (natp (nth 4 s)) (natp (nth 5 s)) (natp (nth 6 s))
                (natp (nth 7 s)) (natp (nth 8 s)) (<= (nth 7 s) (nth 8 s))))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable fn-hdc-statep fn-hdc-state))

(defun fn-hdc-begin (offset length epoch lease)
  (declare (xargs :guard (and (natp offset) (natp length))))
  (fn-hdc-state (if (zp length) :refused :op) 0 0
                (fn-hdc-number-begin 0) 0 0 0 offset (+ offset length)
                nil epoch lease))

; All internal moves preserve the source coordinate and lifetime tokens.
(defun fn-hdc-move (mode op pkg number start count left pos stack s)
  (declare (xargs :guard (fn-hdc-statep s)))
  (fn-hdc-state mode op pkg number start count left pos (nth 8 s)
                stack (nth 10 s) (nth 11 s)))

(defthm fn-hdc-move-valid
  (implies (and (fn-hdc-statep s)
                (member-eq mode '(:op :length :digits :package :char :payload :done :refused))
                (natp op) (< op 8) (natp pkg) (< pkg 3) (fn-hdc-numberp number)
                (natp start) (natp count) (natp left) (natp pos) (<= pos (nth 8 s)))
           (fn-hdc-statep (fn-hdc-move mode op pkg number start count left pos stack s))))

(defun fn-hdc-finish-number (value op pkg pos stack s)
  (declare (xargs :guard (and (natp value) (natp op) (< op 8)
                              (natp pkg) (< pkg 3) (natp pos)
                              (fn-hdc-statep s))))
  (cond ((or (equal op 1) (equal op 2))
         (fn-hdc-move :op op pkg (fn-hdc-number-begin 0) 0 0 0 pos
                       (cons (fn-hdc-atom (if (equal op 1) value (- -1 value))) stack) s))
        ((not (member-equal op '(3 4 6)))
         (fn-hdc-move :refused op pkg (fn-hdc-number-begin 0) 0 0 0 pos stack s))
        ((> value (- (nth 8 s) pos))
         (fn-hdc-move :refused op pkg (fn-hdc-number-begin 0) 0 0 0 pos stack s))
        ((zp value)
         (fn-hdc-move :op op pkg (fn-hdc-number-begin 0) pos 0 0 pos
                       (cons (fn-hdc-span op pkg pos 0) stack) s))
        (t (fn-hdc-move :payload op pkg (fn-hdc-number-begin 0) pos value value pos stack s))))

(defthm fn-hdc-finish-number-valid
  (implies (and (fn-hdc-statep s) (natp value) (natp op) (< op 8)
                (natp pkg) (< pkg 3) (natp pos) (<= pos (nth 8 s)))
           (fn-hdc-statep (fn-hdc-finish-number value op pkg pos stack s)))
  :hints (("Goal" :in-theory (disable fn-hdc-move))))

(in-theory (disable fn-hdc-move fn-hdc-finish-number))

 ; A fixed existing keyword may be recognized while its bytes pass. Other
; symbols retain borrowed spans; no intern or symbol vocabulary restriction.
(defun fn-hdc-tag-byte (op pkg count left byte number)
  (declare (xargs :guard (and (natp op) (natp pkg) (natp count) (natp left)
                              (fn-scc-octetp byte) (fn-hdc-numberp number))
                  :guard-hints (("Goal" :in-theory (enable fn-hdc-numberp)))))
  (if (and (equal op 4) (equal pkg 0) (equal count 5))
      (list 0 (if (and (equal (cadr number) 0) (< 0 left) (<= left 5)
                        (equal byte (nth (nfix (- 5 left)) '(72 83 84 88 65))))
                   0 1) 1)
    number))

(defthm fn-hdc-tag-byte-valid
  (implies (fn-hdc-numberp number)
           (fn-hdc-numberp (fn-hdc-tag-byte op pkg count left byte number)))
  :hints (("Goal" :in-theory (enable fn-hdc-numberp))))

(defun fn-hdc-payload-node (op pkg start count number)
  (declare (xargs :guard (and (member-equal op '(3 4 6))
                              (natp pkg) (< pkg 3) (natp start) (natp count)
                              (fn-hdc-numberp number))
                  :guard-hints (("Goal" :in-theory (enable fn-hdc-numberp)))))
  (if (and (equal op 4) (equal pkg 0) (equal count 5)
           (equal (cadr number) 0))
      (fn-hdc-atom :hstxa)
    (fn-hdc-span op pkg start count)))

(in-theory (disable fn-hdc-tag-byte fn-hdc-payload-node))

(defun fn-hdc-feed-raw (byte s)
  (declare (xargs :guard (and (fn-scc-octetp byte) (fn-hdc-statep s))
                  :verify-guards nil))
  (let* ((mode (nth 0 s)) (op (nth 1 s)) (pkg (nth 2 s))
         (num (nth 3 s)) (start (nth 4 s)) (count (nth 5 s))
         (left (nth 6 s)) (pos (nth 7 s)) (end (nth 8 s))
         (stack (nth 9 s)))
    (if (or (member-eq mode '(:done :refused)) (>= pos end)) s
      (let ((next (+ 1 pos)))
        (cond
         ((eq mode :op)
          (cond
           ((equal byte 0)
            (fn-hdc-move :op 0 0 num 0 0 0 next (cons (fn-hdc-atom nil) stack) s))
           ((member-equal byte '(1 2 3 6))
            (fn-hdc-move :length byte 0 num 0 0 0 next stack s))
           ((equal byte 4) (fn-hdc-move :package 4 0 num 0 0 0 next stack s))
           ((equal byte 7) (fn-hdc-move :char 7 0 num 0 0 0 next stack s))
           ((and (equal byte 5) (consp stack) (consp (cdr stack)))
            (fn-hdc-move :op 5 0 num 0 0 0 next
                          (cons (fn-hdc-pair (cadr stack) (car stack)) (cddr stack)) s))
           (t (fn-hdc-move :refused op pkg num start count left next stack s))))
         ((eq mode :package)
          (fn-hdc-move (if (< byte 3) :length :refused) op
                        (if (< byte 3) byte pkg) num start count left next stack s))
         ((eq mode :char)
          (fn-hdc-move :op op pkg num 0 0 0 next
                        (cons (fn-hdc-atom (code-char byte)) stack) s))
         ((eq mode :length)
          (if (zp byte) (fn-hdc-finish-number 0 op pkg next stack s)
            (fn-hdc-move :digits op pkg (fn-hdc-number-begin byte)
                          0 0 0 next stack s)))
         ((eq mode :digits)
          (let ((n (fn-hdc-number-feed byte num)))
            (if (zp (car n)) (fn-hdc-finish-number (cadr n) op pkg next stack s)
              (fn-hdc-move :digits op pkg n 0 0 0 next stack s))))
         ((and (eq mode :payload) (member-equal op '(3 4 6)) (< 0 left))
          (let ((num (fn-hdc-tag-byte op pkg count left byte num)))
            (if (equal left 1)
                (fn-hdc-move :op op pkg num start count 0 next
                              (cons (fn-hdc-payload-node op pkg start count num) stack) s)
              (fn-hdc-move :payload op pkg num start count (1- left) next stack s))))
         (t (fn-hdc-move :refused op pkg num start count left next stack s)))))))

(defthm fn-hdc-begin-valid
  (implies (and (natp offset) (natp length))
           (fn-hdc-statep (fn-hdc-begin offset length epoch lease)))
  :hints (("Goal" :in-theory (enable fn-hdc-numberp fn-hdc-number-begin))))

(local
 (defthm fn-hdc-number-feed-fields
   (implies (and (fn-hdc-numberp c) (fn-scc-octetp byte))
            (and (true-listp (fn-hdc-number-feed byte c))
                 (natp (car (fn-hdc-number-feed byte c)))
                 (natp (cadr (fn-hdc-number-feed byte c)))))
   :hints (("Goal" :use fn-hdc-number-feed-valid
            :in-theory (enable fn-hdc-numberp fn-hdc-number-feed fn-scc-octetp)))))

(defthm fn-hdc-feed-raw-valid
  (implies (and (fn-hdc-statep s) (fn-scc-octetp byte))
           (fn-hdc-statep (fn-hdc-feed-raw byte s)))
  :hints (("Goal" :in-theory (enable fn-scc-octetp)
           :use ((:instance fn-hdc-number-feed-fields (c (nth 3 s))))
           :do-not-induct t)))

(verify-guards fn-hdc-feed-raw
  :hints (("Goal" :use ((:instance fn-hdc-number-feed-fields (c (nth 3 s))))
           :in-theory (e/d (fn-scc-octetp) (fn-hdc-number-feed-fields))
           :do-not-induct t)))

(defun fn-hdc-feed (byte s)
  (declare (xargs :guard (and (fn-scc-octetp byte) (fn-hdc-statep s))))
  (let ((s (fn-hdc-feed-raw byte s)))
    (if (and (equal (nth 7 s) (nth 8 s))
             (not (member-eq (nth 0 s) '(:done :refused))))
        (cons (if (and (eq (nth 0 s) :op)
                        (consp (nth 9 s)) (null (cdr (nth 9 s))))
                   :done :refused) (cdr s))
      s)))

(defthm fn-hdc-new-mode-valid
  (implies (and (fn-hdc-statep s)
                (member-eq mode '(:op :length :digits :package :char :payload :done :refused)))
           (fn-hdc-statep (cons mode (cdr s))))
  :hints (("Goal" :in-theory (enable fn-hdc-statep))))

(defthm fn-hdc-feed-valid
  (implies (and (fn-hdc-statep s) (fn-scc-octetp byte))
           (fn-hdc-statep (fn-hdc-feed byte s)))
  :hints (("Goal" :in-theory (disable fn-hdc-feed-raw fn-hdc-statep) :do-not-induct t)))

(defthm fn-hdc-feed-preserves-lifetime
  (and (equal (nth 8 (fn-hdc-feed byte s)) (nth 8 s))
       (equal (nth 10 (fn-hdc-feed byte s)) (nth 10 s))
       (equal (nth 11 (fn-hdc-feed byte s)) (nth 11 s)))
  :hints (("Goal" :in-theory (enable fn-hdc-move fn-hdc-finish-number fn-hdc-state))))

(defthm fn-hdc-feed-advances-one-byte
  (implies (and (fn-hdc-statep s) (fn-scc-octetp byte)
                (not (member-eq (nth 0 s) '(:done :refused)))
                (< (nth 7 s) (nth 8 s)))
           (equal (nth 7 (fn-hdc-feed byte s)) (+ 1 (nth 7 s))))
  :hints (("Goal" :in-theory (enable fn-hdc-move fn-hdc-finish-number fn-hdc-state) :do-not-induct t)))
