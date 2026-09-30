; Bounded normalization of names accepted by the current history codec.
; Only the existing package import table is inspected. Arbitrary source names
; remain borrowed spans; execution never interns or assembles a source name.
(in-package "ACL2")
(include-book "store-tree-codec")
(local (include-book "arithmetic/top" :dir :system))

(defconst *fn-hdsn-acl2-imports* (pkg-imports "ACL2"))

(defun fn-hdsn-imports-p (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (symbolp (car xs))
           (equal (symbol-package-name (car xs)) "COMMON-LISP")
           (fn-hdsn-imports-p (cdr xs)))
    (null xs)))

(defthm fn-hdsn-selected-package-contract
  (and (fn-hdsn-imports-p *fn-hdsn-acl2-imports*)
       (equal (pkg-imports "COMMON-LISP") nil)
       (equal (pkg-imports "KEYWORD") nil)))

(defthm fn-hdsn-member-import-home
  (implies (and (fn-hdsn-imports-p imports)
                (member-symbol-name name imports))
           (and (symbolp (car (member-symbol-name name imports)))
                (equal (symbol-package-name (car (member-symbol-name name imports)))
                       "COMMON-LISP")))
  :hints (("Goal" :induct (member-symbol-name name imports)
           :in-theory (enable member-symbol-name fn-hdsn-imports-p))))

(defun-nx fn-hdsn-classify-name (pkg name)
  (cond ((and (member-equal pkg '(1 2)) (equal name "NIL")) '(0 0))
        ((and (equal pkg 1) (member-symbol-name name *fn-hdsn-acl2-imports*)) '(4 2))
        (t (list 4 pkg))))

(defthm fn-hdsn-intern-name
  (implies (and (member-equal pkg '(0 1 2)) (stringp name))
           (equal (symbol-name (fn-scc-intern pkg name)) name))
  :hints (("Goal" :in-theory (enable fn-scc-intern))))

(defthm fn-hdsn-intern-nil
  (implies (and (member-equal pkg '(0 1 2)) (stringp name))
           (equal (equal (fn-scc-intern pkg name) nil)
                  (and (member-equal pkg '(1 2)) (equal name "NIL") t)))
  :hints (("Goal" :use fn-hdsn-intern-name
           :cases ((equal name "NIL"))
           :in-theory (enable fn-scc-intern))))

(local
 (defthm fn-hdsn-member-empty
   (equal (member-symbol-name name nil) nil)
   :hints (("Goal" :in-theory (enable member-symbol-name)))))

(defthm fn-hdsn-classify-matches-current-intern
  (implies (and (member-equal pkg '(0 1 2)) (stringp name))
           (equal (fn-hdsn-classify-name pkg name)
                  (if (equal (fn-scc-intern pkg name) nil) '(0 0)
                    (list 4 (fn-scc-package-index
                             (symbol-package-name (fn-scc-intern pkg name)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-hdsn-intern-nil
                 (:instance intern-in-package-of-symbol-is-identity
                            (x name) (y 'fn-scc-intern))
                 (:instance fn-hdsn-member-import-home
                            (imports *fn-hdsn-acl2-imports*)))
           :in-theory (e/d (fn-hdsn-classify-name fn-scc-intern fn-scc-package-index)
                           (member-symbol-name fn-hdsn-imports-p)))))

; Seven cells: package, source offset, source name length, remaining fixed
; import candidates, candidate character index, request serial, result.
; The candidate suffix is carried, not validated by walking it on each tick.
(defun fn-hdsn-state (pkg offset count candidates index serial result)
  (declare (xargs :guard t))
  (list pkg offset count candidates index serial result))

(defun fn-hdsn-statep (c)
  (declare (xargs :guard t))
  (and (consp c) (consp (cdr c)) (consp (cddr c)) (consp (cdddr c))
       (consp (cddddr c)) (consp (cdr (cddddr c))) (consp (cddr (cddddr c)))
       (null (cdddr (cddddr c)))
       (member-equal (nth 0 c) '(0 1 2))
       (natp (nth 1 c)) (natp (nth 2 c))
       (natp (nth 4 c)) (<= (nth 4 c) (nth 2 c)) (natp (nth 5 c))))

(defthm fn-hdsn-state-fields
  (implies (fn-hdsn-statep c)
           (and (true-listp c) (member-equal (nth 0 c) '(0 1 2))
                (natp (nth 1 c)) (natp (nth 2 c))
                (natp (nth 4 c)) (<= (nth 4 c) (nth 2 c)) (natp (nth 5 c))))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-hdsn-state-constructor
  (equal (fn-hdsn-statep (fn-hdsn-state pkg offset count candidates index serial result))
         (and (member-equal pkg '(0 1 2)) (natp offset) (natp count)
              (natp index) (<= index count) (natp serial))))

(in-theory (disable fn-hdsn-statep fn-hdsn-state))

(defun fn-hdsn-begin (pkg offset count)
  (declare (xargs :guard (and (member-equal pkg '(0 1 2)) (natp offset) (natp count))))
  (fn-hdsn-state pkg offset count
    (cond ((equal pkg 1) *fn-hdsn-acl2-imports*) ((equal pkg 2) '(nil)) (t nil))
    0 0 nil))

(defun fn-hdsn-next-candidate (c)
  (declare (xargs :guard (fn-hdsn-statep c)
                  :guard-hints (("Goal" :in-theory (enable fn-hdsn-statep)))))
  (fn-hdsn-state (nth 0 c) (nth 1 c) (nth 2 c) (if (consp (nth 3 c)) (cdr (nth 3 c)) nil)
                  0 (+ 1 (nth 5 c)) nil))

; Result is (:done (opcode package)), (:need-byte offset serial), :continue
; or :refused. A read does not move state; its matching supply does.
(defun fn-hdsn-tick (c)
  (declare (xargs :guard (fn-hdsn-statep c)
                  :guard-hints (("Goal" :in-theory (enable fn-hdsn-statep)))))
  (let* ((candidates (nth 3 c)) (symbol (if (consp candidates) (car candidates) nil))
         (index (nth 4 c)) (count (nth 2 c)))
    (cond
     ((nth 6 c) (mv (list :done (nth 6 c)) c))
     ((not (consp candidates))
      (let ((r (list 4 (nth 0 c))))
        (mv (list :done r)
            (fn-hdsn-state (nth 0 c) (nth 1 c) count candidates index (nth 5 c) r))))
     ((not (symbolp symbol)) (mv :refused c))
     ((not (equal (length (symbol-name symbol)) count))
      (mv :continue (fn-hdsn-next-candidate c)))
     ((equal index count)
      (let ((r (if (null symbol) '(0 0) '(4 2))))
        (mv (list :done r)
            (fn-hdsn-state (nth 0 c) (nth 1 c) count candidates index (nth 5 c) r))))
     (t (mv (list :need-byte (+ (nth 1 c) index) (nth 5 c)) c)))))

(defun fn-hdsn-supply (offset serial byte c)
  (declare (xargs :guard (and (fn-hdsn-statep c) (natp offset) (natp serial)
                              (fn-scc-octetp byte))
                  :guard-hints (("Goal" :in-theory (enable fn-hdsn-statep)))))
  (let* ((candidates (nth 3 c)) (symbol (if (consp candidates) (car candidates) nil))
         (index (nth 4 c)) (count (nth 2 c)))
    (if (and (not (nth 6 c)) (consp candidates) (symbolp symbol)
             (equal (length (symbol-name symbol)) count) (< index count)
             (equal offset (+ (nth 1 c) index)) (equal serial (nth 5 c)))
        (mv :continue
            (if (equal byte (char-code (char (symbol-name symbol) index)))
                (fn-hdsn-state (nth 0 c) (nth 1 c) count candidates (+ 1 index)
                                (+ 1 (nth 5 c)) nil)
              (fn-hdsn-next-candidate c)))
      (mv :refused c))))

(defthm fn-hdsn-begin-valid
  (implies (and (member-equal pkg '(0 1 2)) (natp offset) (natp count))
           (fn-hdsn-statep (fn-hdsn-begin pkg offset count)))
  :hints (("Goal" :in-theory (enable fn-hdsn-begin))))

(defthm fn-hdsn-tick-valid
  (implies (fn-hdsn-statep c)
           (fn-hdsn-statep (mv-nth 1 (fn-hdsn-tick c))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-hdsn-statep fn-hdsn-tick fn-hdsn-next-candidate))))

(defthm fn-hdsn-supply-valid
  (implies (fn-hdsn-statep c)
           (fn-hdsn-statep (mv-nth 1 (fn-hdsn-supply offset serial byte c))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-hdsn-statep fn-hdsn-supply fn-hdsn-next-candidate))))

(defthm fn-hdsn-stale-supply-does-not-advance
  (implies (or (not (equal offset (+ (nth 1 c) (nth 4 c))))
               (not (equal serial (nth 5 c))))
           (equal (fn-hdsn-supply offset serial byte c) (mv :refused c))))

(defthm fn-hdsn-supply-advances-serial
  (implies (equal (mv-nth 0 (fn-hdsn-supply offset serial byte c)) :continue)
           (equal (nth 5 (mv-nth 1 (fn-hdsn-supply offset serial byte c)))
                  (+ 1 (nth 5 c))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-hdsn-state fn-hdsn-next-candidate))))

; Proof-only residual search. Its whole-name operations do not execute in the
; host-called tick or supply functions.
(defun-nx fn-hdsn-find (name candidates index)
  (if (consp candidates)
      (if (and (symbolp (car candidates))
               (equal (length name) (length (symbol-name (car candidates))))
               (equal (nthcdr (nfix index) (coerce name 'list))
                      (nthcdr (nfix index) (coerce (symbol-name (car candidates)) 'list))))
          (cons t (car candidates))
        (fn-hdsn-find name (cdr candidates) 0))
    nil))

(defun-nx fn-hdsn-denote (c name)
  (if (nth 6 c) (nth 6 c)
    (let ((found (fn-hdsn-find name (nth 3 c) (nth 4 c))))
      (if found (if (null (cdr found)) '(0 0) '(4 2))
        (list 4 (nth 0 c))))))

(local
 (defthm fn-hdsn-nthcdr-zero
   (equal (nthcdr 0 xs) xs)
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-hdsn-string-chars-injective
   (implies (and (stringp x) (stringp y))
            (equal (equal (coerce x 'list) (coerce y 'list)) (equal x y)))
   :hints (("Goal" :use ((:instance coerce-inverse-2 (x x))
                         (:instance coerce-inverse-2 (x y)))
            :in-theory (disable coerce-inverse-2)))))

(defthm fn-hdsn-find-from-zero
  (implies (and (stringp name) (fn-hdsn-imports-p candidates))
           (equal (fn-hdsn-find name candidates 0)
                  (if (member-symbol-name name candidates)
                      (cons t (car (member-symbol-name name candidates))) nil)))
  :hints (("Goal" :induct (fn-hdsn-find name candidates 0)
           :in-theory (enable fn-hdsn-find fn-hdsn-imports-p member-symbol-name))))

(local
 (defthm fn-hdsn-member-name
   (implies (and (fn-hdsn-imports-p imports) (member-symbol-name name imports))
            (equal (symbol-name (car (member-symbol-name name imports))) name))
   :hints (("Goal" :induct (member-symbol-name name imports)
            :in-theory (enable member-symbol-name fn-hdsn-imports-p)))))

(local
 (defthm fn-hdsn-member-single-nil
   (equal (member-symbol-name name '(nil)) (if (equal name "NIL") '(nil) nil))
   :hints (("Goal" :in-theory (enable member-symbol-name)))))

(defthm fn-hdsn-begin-denotes-canonical-classification
  (implies (and (member-equal pkg '(0 1 2)) (stringp name))
           (equal (fn-hdsn-denote (fn-hdsn-begin pkg offset count) name)
                  (fn-hdsn-classify-name pkg name)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdsn-member-name (imports *fn-hdsn-acl2-imports*)))
           :cases ((equal name "NIL"))
           :in-theory (e/d (fn-hdsn-denote fn-hdsn-begin fn-hdsn-state
                            fn-hdsn-classify-name)
                           (fn-hdsn-find member-symbol-name fn-hdsn-imports-p fn-hdsn-member-name)))))

(local
 (defthm fn-hdsn-nthcdr-length
   (implies (and (true-listp xs) (equal n (len xs)))
            (equal (nthcdr n xs) nil))
   :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr len)))))

(local
 (defthm fn-hdsn-find-mismatched-length-unfolds
  (implies (and (consp candidates)
                (not (equal (length name)
                            (length (symbol-name (car candidates))))))
           (equal (fn-hdsn-find name candidates index)
                  (fn-hdsn-find name (cdr candidates) 0)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-hdsn-find name candidates index))
           :in-theory (disable fn-hdsn-find)))))

(local
 (defthm fn-hdsn-find-unfolds
  (equal (fn-hdsn-find name candidates index)
         (if (consp candidates)
             (if (and (symbolp (car candidates))
                      (equal (length name) (length (symbol-name (car candidates))))
                      (equal (nthcdr (nfix index) (coerce name 'list))
                             (nthcdr (nfix index)
                                     (coerce (symbol-name (car candidates)) 'list))))
                 (cons t (car candidates))
               (fn-hdsn-find name (cdr candidates) 0))
           nil))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-hdsn-find name candidates index))
           :in-theory (disable fn-hdsn-find)))))

(defthm fn-hdsn-tick-preserves-denotation
  (implies (and (fn-hdsn-statep c) (stringp name)
                (equal (length name) (nth 2 c)))
           (equal (fn-hdsn-denote (mv-nth 1 (fn-hdsn-tick c)) name)
                  (fn-hdsn-denote c name)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-hdsn-state-fields
                 (:instance fn-hdsn-find-unfolds
                            (candidates (nth 3 c)) (index (nth 4 c)))
                 (:instance fn-hdsn-find-mismatched-length-unfolds
                            (candidates (nth 3 c)) (index (nth 4 c)))
                 (:instance fn-hdsn-nthcdr-length (xs (coerce name 'list)) (n (nth 2 c)))
                 (:instance fn-hdsn-nthcdr-length
                            (xs (coerce (symbol-name (car (nth 3 c))) 'list)) (n (nth 2 c))))
           :expand ((fn-hdsn-find name (nth 3 c) (nth 4 c)))
           :in-theory (e/d (fn-hdsn-tick fn-hdsn-next-candidate fn-hdsn-state
                            fn-hdsn-denote)
                           (fn-hdsn-find member-symbol-name fn-hdsn-nthcdr-length fn-hdsn-state-fields)))))

(defthm fn-hdsn-done-is-denotation
  (implies (and (fn-hdsn-statep c) (stringp name)
                (equal (length name) (nth 2 c))
                (equal (car (mv-nth 0 (fn-hdsn-tick c))) :done))
           (equal (cadr (mv-nth 0 (fn-hdsn-tick c))) (fn-hdsn-denote c name)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-hdsn-state-fields
                 (:instance fn-hdsn-find-unfolds
                            (candidates (nth 3 c)) (index (nth 4 c)))
                 (:instance fn-hdsn-find-mismatched-length-unfolds
                            (candidates (nth 3 c)) (index (nth 4 c)))
                 (:instance fn-hdsn-nthcdr-length (xs (coerce name 'list)) (n (nth 2 c)))
                 (:instance fn-hdsn-nthcdr-length
                            (xs (coerce (symbol-name (car (nth 3 c))) 'list)) (n (nth 2 c))))
           :expand ((fn-hdsn-find name (nth 3 c) (nth 4 c)))
           :in-theory (e/d (fn-hdsn-tick fn-hdsn-next-candidate fn-hdsn-state
                            fn-hdsn-denote)
                           (fn-hdsn-find member-symbol-name fn-hdsn-nthcdr-length fn-hdsn-state-fields)))))

(local
 (defthm fn-hdsn-tail-step
   (implies (and (natp index) (< index (len xs)))
            (equal (nthcdr index xs)
                   (cons (nth index xs) (nthcdr (+ 1 index) xs))))
   :hints (("Goal" :induct (nthcdr index xs)
            :in-theory (enable nthcdr nth len)))))

(local
 (defthm fn-hdsn-character-codes-injective
   (implies (and (characterp x) (characterp y))
            (equal (equal (char-code x) (char-code y)) (equal x y)))
   :hints (("Goal" :use ((:instance code-char-char-code-is-identity (c x))
                         (:instance code-char-char-code-is-identity (c y)))
            :in-theory (disable code-char-char-code-is-identity)))))

(local
 (defthm fn-hdsn-car-of-tail-unfolds
  (equal (car (nthcdr n xs)) (nth n xs))
  :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-hdsn-equal-tails-have-equal-heads
  (implies (equal (nthcdr n xs) (nthcdr n ys))
           (equal (nth n xs) (nth n ys)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdsn-car-of-tail-unfolds)
                 (:instance fn-hdsn-car-of-tail-unfolds (xs ys)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (executable-counterpart-theory :here))))))

(defthm fn-hdsn-supply-preserves-denotation
  (implies (and (fn-hdsn-statep c) (stringp name)
                (equal (length name) (nth 2 c))
                (< (nth 4 c) (nth 2 c))
                (equal byte (char-code (char name (nth 4 c)))))
           (equal (fn-hdsn-denote
                   (mv-nth 1 (fn-hdsn-supply offset serial byte c)) name)
                  (fn-hdsn-denote c name)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-hdsn-state-fields
                 (:instance fn-hdsn-equal-tails-have-equal-heads
                            (n (nth 4 c)) (xs (coerce name 'list))
                            (ys (coerce (symbol-name (car (nth 3 c))) 'list)))
                 (:instance fn-hdsn-find-unfolds
                            (candidates (nth 3 c)) (index (nth 4 c)))
                 (:instance fn-hdsn-find-unfolds
                            (candidates (nth 3 c)) (index (+ 1 (nth 4 c))))
                 (:instance fn-hdsn-tail-step
                            (index (nth 4 c)) (xs (coerce name 'list)))
                 (:instance fn-hdsn-tail-step
                            (index (nth 4 c))
                            (xs (coerce (symbol-name (car (nth 3 c))) 'list))))
           :expand ((fn-hdsn-find name (nth 3 c) (nth 4 c))
                    (fn-hdsn-find name (nth 3 c) (+ 1 (nth 4 c))))
           :in-theory (e/d (fn-hdsn-supply fn-hdsn-next-candidate fn-hdsn-state
                            fn-hdsn-denote)
                           (fn-hdsn-find member-symbol-name fn-hdsn-tail-step fn-hdsn-state-fields)))))

(defun-nx fn-hdsn-coherent (c)
  (and (fn-hdsn-statep c) (fn-hdsn-imports-p (nth 3 c))
       (or (equal (nth 4 c) 0)
           (and (consp (nth 3 c))
                (equal (length (symbol-name (car (nth 3 c)))) (nth 2 c))))))

(defthm fn-hdsn-begin-coherent
  (implies (and (member-equal pkg '(0 1 2)) (natp offset) (natp count))
           (fn-hdsn-coherent (fn-hdsn-begin pkg offset count)))
  :hints (("Goal" :in-theory (enable fn-hdsn-statep fn-hdsn-coherent fn-hdsn-state fn-hdsn-begin))))

(defthm fn-hdsn-tick-coherent
  (implies (fn-hdsn-coherent c)
           (fn-hdsn-coherent (mv-nth 1 (fn-hdsn-tick c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdsn-statep fn-hdsn-coherent fn-hdsn-tick fn-hdsn-next-candidate
                              fn-hdsn-state fn-hdsn-imports-p))))

(defthm fn-hdsn-supply-coherent
  (implies (fn-hdsn-coherent c)
           (fn-hdsn-coherent (mv-nth 1 (fn-hdsn-supply offset serial byte c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdsn-statep fn-hdsn-coherent fn-hdsn-supply fn-hdsn-next-candidate
                              fn-hdsn-state fn-hdsn-imports-p))))

(defun fn-hdsn-candidate-work (candidates)
  (declare (xargs :guard (fn-hdsn-imports-p candidates)))
  (if (consp candidates)
      (+ 1 (length (symbol-name (car candidates)))
         (fn-hdsn-candidate-work (cdr candidates)))
    0))

(defun-nx fn-hdsn-work (c)
  (if (nth 6 c) 0
    (+ 1 (nfix (- (fn-hdsn-candidate-work (nth 3 c)) (nfix (nth 4 c)))))))

(defthm fn-hdsn-tick-progress
  (implies (and (fn-hdsn-coherent c)
                (equal (mv-nth 0 (fn-hdsn-tick c)) :continue))
           (< (fn-hdsn-work (mv-nth 1 (fn-hdsn-tick c))) (fn-hdsn-work c)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-hdsn-candidate-work (nth 3 c)))
           :in-theory (enable fn-hdsn-statep fn-hdsn-coherent fn-hdsn-tick fn-hdsn-next-candidate
                              fn-hdsn-state fn-hdsn-work))))

(defthm fn-hdsn-supply-progress
  (implies (and (fn-hdsn-coherent c)
                (equal (mv-nth 0 (fn-hdsn-supply offset serial byte c)) :continue))
           (< (fn-hdsn-work (mv-nth 1 (fn-hdsn-supply offset serial byte c)))
              (fn-hdsn-work c)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-hdsn-candidate-work (nth 3 c)))
           :in-theory (enable fn-hdsn-statep fn-hdsn-coherent fn-hdsn-supply fn-hdsn-next-candidate
                              fn-hdsn-state fn-hdsn-work))))

(defthm fn-hdsn-selected-table-work
  (equal (fn-hdsn-candidate-work *fn-hdsn-acl2-imports*) 12249)
  :hints (("Goal" :in-theory (enable fn-hdsn-candidate-work))))

(defthm fn-hdsn-initial-work-bound
  (implies (member-equal pkg '(0 1 2))
           (<= (fn-hdsn-work (fn-hdsn-begin pkg offset count)) 12250))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdsn-work fn-hdsn-begin fn-hdsn-state))))

(defthm fn-hdsn-source-coordinate-preserved
  (and (equal (nth 0 (mv-nth 1 (fn-hdsn-tick c))) (nth 0 c))
       (equal (nth 1 (mv-nth 1 (fn-hdsn-tick c))) (nth 1 c))
       (equal (nth 2 (mv-nth 1 (fn-hdsn-tick c))) (nth 2 c))
       (equal (nth 0 (mv-nth 1 (fn-hdsn-supply offset serial byte c))) (nth 0 c))
       (equal (nth 1 (mv-nth 1 (fn-hdsn-supply offset serial byte c))) (nth 1 c))
       (equal (nth 2 (mv-nth 1 (fn-hdsn-supply offset serial byte c))) (nth 2 c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdsn-state fn-hdsn-next-candidate fn-hdsn-tick fn-hdsn-supply))))
