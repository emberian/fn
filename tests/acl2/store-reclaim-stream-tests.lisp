; fn: witnesses and teeth for books/store-reclaim-stream.lisp (PKT-686 item
; 2): the reclaim decision folded one record at a time answers what
; `fn-rclp-decide' answers over the history, on each of its reachable
; answers over store-reclaim-pack-tests' owner fixture; per hypothesis a
; counterexample and the must-fail of the keystone without it.
(in-package "ACL2")
(include-book "../../books/store-reclaim-stream")
(include-book "must-fail-checked")
(include-book "owner-served-invariants-tests")

(defconst *rst-s* (fn-own-store (cdr (osi-finish *osi-completing* *osi-cfg* *osi-completing-prior*))))
(defun rst-encode-all (rs)
  (declare (xargs :mode :program))
  (if (consp rs) (cons (fn-store-event-encode (car rs)) (rst-encode-all (cdr rs))) nil))
(defconst *rst-wire* (fn-hrt-wire-of *osi-completing-prior* (fn-sf-records (fn-sn-files *rst-s*))))
(defmacro rst-events () '(rst-encode-all *rst-wire*))
(defconst *rst-rule* '(:released-by-all-holders))
(defconst *rst-ctx* (fn-rclp-ctx *rst-rule* 0 *rst-s*))
(defconst *rst-profile* *fn-bs-profile-development*)
(defmacro rst-n () '(len (rst-events)))
(defmacro rst-long () '(append (rst-events) (make-list 4096 :initial-element '(1 2 3))))

(defun rst-acc (events)
  (declare (xargs :mode :program))
  (fn-rcls-fold events *rst-ctx* (fn-rcls-init)))

(defmacro rst-both (events lower gens selected disk dry)
  `(list (fn-rcls-decide *rst-profile* *rst-rule* 0 *rst-s* (rst-acc ,events)
                         (len ,events) ,lower nil ,gens ,selected ,disk ,dry)
         (fn-rclp-decide *rst-profile* *rst-rule* 0 *rst-s* ,events
                         (len ,events) ,lower nil ,gens ,selected ,disk ,dry)))

; The witnesses: every reachable answer agrees -- the reclaim (with the
; summary it publishes), the dry run, compact-first, the named spans-links
; refusal of a history past one link, the temporary-space refusal, and
; keep-forever's none.
(assert-event (let ((b (rst-both (rst-events) (rst-n) '(0) 0 1000000 nil)))
                (and (equal (car (first b)) :reclaim) (equal (first b) (second b)))))
(assert-event (let ((b (rst-both (rst-events) (rst-n) '(0) 0 1000000 t)))
                (and (equal (car (first b)) :dry-run) (equal (first b) (second b)))))
(assert-event (let ((b (rst-both (rst-events) 0 nil nil 1000000 nil)))
                (and (equal (first b) '(:compact-first)) (equal (first b) (second b)))))
(assert-event (let ((b (rst-both (rst-long) (len (rst-long)) '(0) 0 1000000 nil)))
                (and (equal (first b) '(:refused :spans-links)) (equal (first b) (second b)))))
(assert-event (let ((b (rst-both (rst-events) (rst-n) '(0) 0 10 nil)))
                (and (equal (first b) '(:refused :temporary-space)) (equal (first b) (second b)))))
(assert-event (equal (fn-rcls-decide *rst-profile* '(:keep-forever) 0 *rst-s*
                                     (fn-rcls-fold (rst-events)
                                                   (fn-rclp-ctx '(:keep-forever) 0 *rst-s*)
                                                   (fn-rcls-init))
                                     (rst-n) (rst-n) nil '(0) 0 1000000 nil)
                     (fn-rclp-decide *rst-profile* '(:keep-forever) 0 *rst-s* (rst-events)
                                     (rst-n) (rst-n) nil '(0) 0 1000000 nil)))
; The fold keeps no rewritten history past one link: the long history's
; accumulator holds none.
(assert-event (and (nth 5 (rst-acc (rst-long))) (null (nth 3 (rst-acc (rst-long))))))

; Without ACC the fold of the records: the empty history's fold (nothing to
; rewrite) answers :none where the history reclaims.
(assert-event (not (equal (fn-rcls-decide *rst-profile* *rst-rule* 0 *rst-s* (fn-rcls-init)
                                          (rst-n) (rst-n) nil '(0) 0 1000000 nil)
                          (fn-rclp-decide *rst-profile* *rst-rule* 0 *rst-s* (rst-events)
                                          (rst-n) (rst-n) nil '(0) 0 1000000 nil))))
(must-fail-checked
 (defthm rst-without-fold
   (implies (true-listp records)
            (equal (fn-rcls-decide profile rule now s acc frontier lower names generations
                                   selected disk-free dry)
                   (fn-rclp-decide profile rule now s records frontier lower names
                                   generations selected disk-free dry)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-rcls-decide fn-rclp-decide)
                                       (theory 'minimal-theory))))))

; Without a true list of records: the history ending in an atom.  The fold
; reads the same records; the whole-history decision captures the dotted
; rewritten list and answers otherwise.
(defmacro rst-dotted () '(append (rst-events) 7))
(assert-event (not (true-listp (rst-dotted))))
(assert-event (not (equal (fn-rcls-decide *rst-profile* *rst-rule* 0 *rst-s*
                                          (rst-acc (rst-dotted))
                                          (rst-n) (rst-n) nil '(0) 0 1000000 nil)
                          (fn-rclp-decide *rst-profile* *rst-rule* 0 *rst-s* (rst-dotted)
                                          (rst-n) (rst-n) nil '(0) 0 1000000 nil))))
(must-fail-checked
 (defthm rst-without-true-list
   (implies (equal acc (fn-rcls-fold records (fn-rclp-ctx rule now s) (fn-rcls-init)))
            (equal (fn-rcls-decide profile rule now s acc frontier lower names generations
                                   selected disk-free dry)
                   (fn-rclp-decide profile rule now s records frontier lower names
                                   generations selected disk-free dry)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-rcls-fold-of-init (ctx (fn-rclp-ctx rule now s))))
            :in-theory (union-theories '(fn-rcls-decide fn-rclp-decide)
                                       (theory 'minimal-theory))))))
