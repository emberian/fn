; Teeth for the linear :exec paths of the whole-node recognizer's list checks
; (checkpoint-cost, PKT-142): fn-no-duplicatesp, fn-subsetp
; (books/acceptance-alloc.lisp), fn-article-listp (books/acceptance.lisp),
; fn-retain-no-duplicatesp (books/retention.lisp) and fn-node-binding-listp
; (books/node.lisp).
;
; Every equality here is hypothesis-free, so the teeth are witnesses: each
; recognizer, evaluated (its guard-verified :exec path, the hash set for a
; list of eight or more), agrees with a quadratic reference that is the
; :logic body copied with guards unverified (evaluated in the logic), on a
; long list that passes and on the same list with one duplicate far from its
; twin, which fails.
(in-package "ACL2")
(include-book "../../books/node")

(defun lrt-nodupp (xs)
  (declare (xargs :verify-guards nil))
  (if (consp xs)
      (and (not (member-equal (car xs) (cdr xs))) (lrt-nodupp (cdr xs)))
    t))

(defun lrt-subsetp (xs ys)
  (declare (xargs :verify-guards nil))
  (if (consp xs)
      (and (member-equal (car xs) ys) (lrt-subsetp (cdr xs) ys))
    t))

(defun lrt-article-listp (configured xs)
  (declare (xargs :verify-guards nil))
  (if (consp xs)
      (and (fn-articlep configured (car xs))
           (not (member-equal (fn-article-msgid (car xs))
                              (fn-article-msgids (cdr xs))))
           (lrt-article-listp configured (cdr xs)))
    (null xs)))

(defconst *lrt-keys* '("a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k" "l"))
(defconst *lrt-keys-dup* (append *lrt-keys* '("b")))

; The hash path is the one these lists take.
(assert-event (fn-ks-longp *lrt-keys*))
(assert-event (equal (fn-no-duplicatesp *lrt-keys*) t))
(assert-event (equal (fn-no-duplicatesp *lrt-keys*) (lrt-nodupp *lrt-keys*)))
(assert-event (equal (fn-no-duplicatesp *lrt-keys-dup*) nil))
(assert-event (equal (fn-no-duplicatesp *lrt-keys-dup*) (lrt-nodupp *lrt-keys-dup*)))
(assert-event (equal (fn-retain-no-duplicatesp *lrt-keys-dup*) nil))
(assert-event (equal (fn-retain-no-duplicatesp *lrt-keys*) t))
(assert-event (equal (fn-subsetp '("l" "a" "e") *lrt-keys*) t))
(assert-event (equal (fn-subsetp '("l" "a" "e") *lrt-keys*)
                     (lrt-subsetp '("l" "a" "e") *lrt-keys*)))
(assert-event (equal (fn-subsetp '("l" "z" "e") *lrt-keys*) nil))
(assert-event (equal (fn-subsetp '("l" "z" "e") *lrt-keys*)
                     (lrt-subsetp '("l" "z" "e") *lrt-keys*)))
; Keys that are not strings: pairs, as memberships are.
(assert-event (equal (fn-no-duplicatesp (append (pairlis$ *lrt-keys* *lrt-keys*)
                                                (list (cons "c" "c"))))
                     nil))

; Articles: one committed article, cloned under twelve Message-IDs.
(defconst *lrt-groups* '("fn.letters" "fn.test"))
(defconst *lrt-committed*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *lrt-groups*) 7 "<a@example.invalid>"
                      '(72 105 13 10) *lrt-groups* 841000000)
   0 7 :durable))
(defconst *lrt-article* (car (fn-state-articles *lrt-committed*)))
(assert-event (fn-articlep *lrt-groups* *lrt-article*))

(defun lrt-clones (ids)
  (declare (xargs :verify-guards nil))
  (if (consp ids)
      (cons (cons (concatenate 'string "<" (car ids) "@example.invalid>")
                  (cdr *lrt-article*))
            (lrt-clones (cdr ids)))
    nil))

(defconst *lrt-articles* (lrt-clones *lrt-keys*))
(defconst *lrt-articles-dup* (lrt-clones *lrt-keys-dup*))
(assert-event (equal (fn-article-msgid (car *lrt-articles*)) "<a@example.invalid>"))
(assert-event (equal (fn-article-listp *lrt-groups* *lrt-articles*) t))
(assert-event (equal (fn-article-listp *lrt-groups* *lrt-articles*)
                     (lrt-article-listp *lrt-groups* *lrt-articles*)))
(assert-event (equal (fn-article-listp *lrt-groups* *lrt-articles-dup*) nil))
(assert-event (equal (fn-article-listp *lrt-groups* *lrt-articles-dup*)
                     (lrt-article-listp *lrt-groups* *lrt-articles-dup*)))
; A non-article element and a dotted tail fail on both paths.
(assert-event (equal (fn-article-listp *lrt-groups* (cons 7 *lrt-articles*)) nil))
(assert-event (equal (fn-article-listp *lrt-groups* (append *lrt-articles* 'tail)) nil))
(assert-event (equal (lrt-article-listp *lrt-groups* (append *lrt-articles* 'tail)) nil))

; Bindings: twelve bindings with distinct message IDs and identities pass; a
; repeated identity under a fresh message ID fails.
(defun lrt-bindings (ids)
  (declare (xargs :verify-guards nil))
  (if (consp ids)
      (cons (fn-node-make-binding (car ids) "subject" (concatenate 'string "id-" (car ids)))
            (lrt-bindings (cdr ids)))
    nil))
(defconst *lrt-bindings* (lrt-bindings *lrt-keys*))
(assert-event (equal (fn-node-binding-listp *lrt-bindings*) t))
(assert-event (equal (fn-node-binding-listp
                      (append *lrt-bindings*
                              (list (fn-node-make-binding "z" "subject" "id-c"))))
                     nil))
(assert-event (equal (fn-node-binding-listp
                      (append *lrt-bindings*
                              (list (fn-node-make-binding "c" "subject" "id-z"))))
                     nil))
