; LB append-only record layout: owner C; adapter retires with LB-LOG-MODEL.
; The recognizer checks ordered physical record intervals and range containment,
; not uniqueness itself. Trailer widths come from the digest boundary.
(in-package "ACL2")
(include-book "lb-log-model")
(include-book "crypto-attach")
(local (include-book "arithmetic-5/top" :dir :system))


(defun fn-lb-log-entries-layoutp (entries lower upper)
 (declare (xargs :guard (and (true-list-listp entries) (natp lower) (natp upper)) :verify-guards nil))
 (if (consp entries)
  (let ((e (car entries)))
   (and (true-listp e) (equal (len e) 9)
        (natp (nth 1 e)) (natp (nth 2 e)) (natp (nth 3 e)) (natp (nth 4 e))
        (<= lower (nth 1 e)) (<= (nth 1 e) (nth 3 e))
        (<= (+ (nth 3 e) (nth 4 e)) (+ (nth 1 e) (nth 2 e)))
        (<= (+ (nth 1 e) (nth 2 e) 32) upper)
        (fn-lb-log-entries-layoutp (cdr entries) (+ (nth 1 e) (nth 2 e) 32) upper)))
  (null entries)))

(defun fn-lb-log-segment-layoutp (segment)
 (declare (xargs :guard (true-listp segment) :verify-guards nil))
 (and (equal (len segment) 3) (true-listp (cadr segment))
      (true-list-listp (caddr segment))
      (fn-lb-log-entries-layoutp (caddr segment) 0 (len (cadr segment)))))

(defun fn-lb-log-layout-ids (log)
 (declare (xargs :guard (true-list-listp log) :verify-guards nil))
 (if (consp log) (cons (caar log) (fn-lb-log-layout-ids (cdr log))) nil))

(defun fn-lb-log-layoutp (log)
 (declare (xargs :guard (true-list-listp log) :verify-guards nil))
 (if (consp log)
  (and (fn-lb-log-segment-layoutp (car log))
       (not (member-equal (caar log) (fn-lb-log-layout-ids (cdr log))))
       (fn-lb-log-layoutp (cdr log)))
  (null log)))

(defun fn-lb-log-served-offsets (entries)
 (declare (xargs :guard (true-list-listp entries) :verify-guards nil))
 (if (consp entries) (cons (nth 3 (car entries)) (fn-lb-log-served-offsets (cdr entries))) nil))

(verify-guards fn-lb-log-entries-layoutp)

(verify-guards fn-lb-log-segment-layoutp)

(verify-guards fn-lb-log-layout-ids)

(verify-guards fn-lb-log-layoutp)

(verify-guards fn-lb-log-served-offsets)

(local (defthm fn-lb-layout-offset-member-bound
 (implies (and (natp lower) (natp upper) (fn-lb-log-entries-layoutp entries lower upper)
               (member-equal off (fn-lb-log-served-offsets entries)))
  (and (natp off) (<= lower off)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower upper)
  :in-theory (e/d (fn-lb-log-entries-layoutp fn-lb-log-served-offsets member-equal)
                 (nth true-listp))))))

(defthm fn-lb-layout-entries-have-unique-served-offsets
 (implies (and (natp lower) (natp upper) (fn-lb-log-entries-layoutp entries lower upper))
  (no-duplicatesp-equal (fn-lb-log-served-offsets entries)))
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower upper)
  :in-theory (e/d (fn-lb-log-entries-layoutp fn-lb-log-served-offsets no-duplicatesp-equal)
                 (nth true-listp)))
 ("Subgoal *1/1" :use ((:instance fn-lb-layout-offset-member-bound
   (entries (cdr entries)) (lower (+ (nth 1 (car entries)) (nth 2 (car entries)) 32))
   (off (nth 3 (car entries))))))))

(defthm fn-lb-log-layout-implies-unique-served-offsets
 (implies (and (fn-lb-log-layoutp log) (member-equal segment log))
  (no-duplicatesp-equal (fn-lb-log-served-offsets (caddr segment))))
 :hints (("Goal" :induct (fn-lb-log-layoutp log)
  :in-theory (e/d (fn-lb-log-layoutp fn-lb-log-segment-layoutp member-equal)
                 (fn-lb-log-entries-layoutp fn-lb-log-served-offsets nth fn-lb-layout-entries-have-unique-served-offsets)))
 ("Subgoal *1/1" :use ((:instance fn-lb-layout-entries-have-unique-served-offsets
 (entries (caddr (car log))) (lower 0) (upper (len (cadr (car log)))))))))

(local (defthm fn-lb-layout-entries-shape
 (implies (fn-lb-log-entries-layoutp entries lower upper) (true-list-listp entries))
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower upper)
  :in-theory (e/d (fn-lb-log-entries-layoutp true-list-listp) (nth true-listp))))))

(local (defthm fn-lb-layout-upper-weaken
 (implies (and (fn-lb-log-entries-layoutp entries lower upper) (natp upper) (natp newupper) (<= upper newupper))
  (fn-lb-log-entries-layoutp entries lower newupper))
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower upper)
  :in-theory (e/d (fn-lb-log-entries-layoutp) (nth true-listp))))))

(local (defthm fn-lb-layout-empty-by-definition
 (fn-lb-log-entries-layoutp nil lower upper)
 :hints (("Goal" :in-theory (enable fn-lb-log-entries-layoutp)))))

(local (defthm fn-lb-layout-lower-weaken
 (implies (and (fn-lb-log-entries-layoutp entries lower upper) (natp lower) (natp newlower) (<= newlower lower))
  (fn-lb-log-entries-layoutp entries newlower upper))
 :hints (("Goal" :expand ((fn-lb-log-entries-layoutp entries lower upper)
                          (fn-lb-log-entries-layoutp entries newlower upper))
  :in-theory (disable fn-lb-log-entries-layoutp nth true-listp)))))

(local (defthm fn-lb-layout-concatenate
 (implies (and (fn-lb-log-entries-layoutp entries lower middle)
               (fn-lb-log-entries-layoutp tail middle upper)
               (natp lower) (natp middle) (natp upper) (<= lower middle) (<= middle upper))
  (fn-lb-log-entries-layoutp (append entries tail) lower upper))
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower middle)
  :in-theory (e/d (fn-lb-log-entries-layoutp append) (nth true-listp))))))

(local (defthm fn-lb-layout-cbor-true-list
 (implies (fn-cbor-octet-listp x) (true-listp x))
 :hints (("Goal" :induct (fn-cbor-octet-listp x) :in-theory (enable fn-cbor-octet-listp)))))

(local (defthm fn-lb-layout-digest-true-list
 (true-listp (fn-blake3-stobj prefix))
 :hints (("Goal" :use ((:instance fn-blake3-stobj-satisfies-fn-frame-digest-octet-listp (octets prefix)))
  :in-theory (disable fn-blake3-stobj fn-cbor-octet-listp)))))

(local (defthm fn-lb-layout-singleton-unfolds
 (equal (fn-lb-log-entries-layoutp (list e) lower upper)
  (and (true-listp e) (equal (len e) 9)
       (natp (nth 1 e)) (natp (nth 2 e)) (natp (nth 3 e)) (natp (nth 4 e))
       (<= lower (nth 1 e)) (<= (nth 1 e) (nth 3 e))
       (<= (+ (nth 3 e) (nth 4 e)) (+ (nth 1 e) (nth 2 e)))
       (<= (+ (nth 1 e) (nth 2 e) 32) upper)))
 :hints (("Goal" :expand ((fn-lb-log-entries-layoutp (list e) lower upper))
  :in-theory (disable fn-lb-log-entries-layoutp nth true-listp)))))

(local (defthm fn-lb-layout-len-append
 (equal (len (append x y)) (+ (len x) (len y)))
 :hints (("Goal" :induct (append x y) :in-theory (enable append len)))))

(local (defthm fn-lb-layout-list-list-append
 (implies (and (true-list-listp x) (true-list-listp y))
  (true-list-listp (append x y)))
 :hints (("Goal" :induct (append x y) :in-theory (enable append true-list-listp)))))

(defthm fn-lb-log-model-append-to-segment-preserves-layout
 (implies (fn-lb-log-segment-layoutp segment)
  (fn-lb-log-segment-layoutp (fn-lb-log-model-append-to-segment row payload segment)))
 :hints (("Goal" :in-theory
  (e/d (fn-lb-log-segment-layoutp fn-lb-log-model-append-to-segment)
       (fn-lb-log-entries-layoutp fn-lb-log-model-pre fn-la-tombstone-raw
        fn-la-payload-wire fn-lb-log-model-home-frame fn-lb-log-model-homes
        fn-record-payload fn-record-sequence fn-blake3-stobj nth)))))

(local (defthm fn-lb-log-append-to-segment-id-frame-by-definition
 (equal (car (fn-lb-log-model-append-to-segment row payload segment)) (car segment))
 :hints (("Goal" :in-theory (e/d (fn-lb-log-model-append-to-segment)
  (fn-lb-log-model-pre fn-la-tombstone-raw fn-la-payload-wire fn-lb-log-model-home-frame
   fn-lb-log-model-homes fn-record-payload fn-record-sequence fn-blake3-stobj))))))

(local (defthm fn-lb-layout-member-append
 (iff (member-equal a (append x y)) (or (member-equal a x) (member-equal a y)))
 :hints (("Goal" :induct (append x y) :in-theory (enable append member-equal)))))

(defthm fn-lb-log-layout-ids-of-append
 (equal (fn-lb-log-layout-ids (fn-lb-log-model-append row payload id log))
  (if (member-equal id (fn-lb-log-layout-ids log))
      (fn-lb-log-layout-ids log) (append (fn-lb-log-layout-ids log) (list id))))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload id log)
  :in-theory (e/d (fn-lb-log-model-append fn-lb-log-layout-ids member-equal)
   (fn-lb-log-model-append-to-segment fn-lb-log-segment-layoutp fn-lb-log-entries-layoutp)))))

(local (defthm fn-lb-layout-empty-segment-by-definition
 (fn-lb-log-segment-layoutp (list id nil nil))
 :hints (("Goal" :in-theory (enable fn-lb-log-segment-layoutp)))))

(defthm fn-lb-log-model-append-preserves-layout
 (implies (fn-lb-log-layoutp log)
  (fn-lb-log-layoutp (fn-lb-log-model-append row payload id log)))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload id log)
  :in-theory (e/d (fn-lb-log-model-append fn-lb-log-layoutp fn-lb-log-layout-ids)
    (fn-lb-log-model-append-to-segment fn-lb-log-segment-layoutp fn-lb-log-entries-layoutp)))))

(defthm fn-lb-log-layout-offset-upper-bound
 (implies (and (fn-lb-log-entries-layoutp entries lower upper) (natp lower) (natp upper)
               (member-equal off (fn-lb-log-served-offsets entries)))
  (and (natp off) (< off upper)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower upper)
  :in-theory (e/d (fn-lb-log-entries-layoutp fn-lb-log-served-offsets member-equal) (nth true-listp)))))

(local (defthm fn-lb-log-offset-projection-member
 (implies (member-equal e entries) (member-equal (nth 3 e) (fn-lb-log-served-offsets entries)))
 :hints (("Goal" :induct (fn-lb-log-served-offsets entries)
  :in-theory (e/d (fn-lb-log-served-offsets member-equal) (nth))))))

(local (defthm fn-lb-log-last-appended-entry
 (equal (car (last (append entries (list e)))) e)
 :hints (("Goal" :induct (append entries (list e)) :in-theory (enable append last)))))

(local (defthm fn-lb-log-appended-offset-by-definition
 (equal (nth 3 (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment)))))
        (+ (len (cadr segment)) (len (fn-lb-log-model-pre row payload))))
 :hints (("Goal" :in-theory (e/d (fn-lb-log-model-append-to-segment)
  (fn-lb-log-model-pre fn-la-tombstone-raw fn-la-payload-wire fn-lb-log-model-home-frame
   fn-lb-log-model-homes fn-record-payload fn-record-sequence fn-blake3-stobj last))))))

(defthm fn-lb-log-append-cannot-reuse-old-served-offset
 (implies (and (fn-lb-log-segment-layoutp segment) (member-equal e (caddr segment)))
  (not (equal (nth 3 e)
   (nth 3 (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment))))))))
 :hints (("Goal" :use ((:instance fn-lb-log-layout-offset-upper-bound
                       (entries (caddr segment)) (lower 0) (upper (len (cadr segment))) (off (nth 3 e)))
                      (:instance fn-lb-log-offset-projection-member (entries (caddr segment))))
  :in-theory (e/d (fn-lb-log-segment-layoutp)
   (fn-lb-log-entries-layoutp fn-lb-log-served-offsets fn-lb-log-model-append-to-segment
    fn-lb-log-model-pre nth)))))

(defthm fn-lb-log-existing-range-entry-survives-append
 (implies (fn-lb-log-model-range-entry off entries)
  (equal (fn-lb-log-model-range-entry off (append entries tail))
         (fn-lb-log-model-range-entry off entries)))
 :hints (("Goal" :induct (fn-lb-log-model-range-entry off entries)
  :in-theory (e/d (fn-lb-log-model-range-entry append) (nth)))))
