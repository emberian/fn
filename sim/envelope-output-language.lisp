; Semantic proof boundary for the runtime row machine. No served-path validator.
(in-package "ACL2")
(include-book "envelope-output")

(defun fn2-eo-octets-p (xs)
 (declare (xargs :guard t))
 (if (atom xs) (equal xs nil)
   (and (unsigned-byte-p 8 (car xs)) (fn2-eo-octets-p (cdr xs)))))

(defun fn2-eo-segments-p (segments)
 (declare (xargs :guard t))
 (if (atom segments) (equal segments nil)
   (and (consp (car segments))
        (or (eq (caar segments) :exact) (eq (caar segments) :prefix))
        (fn2-eo-octets-p (cdar segments))
        (fn2-eo-segments-p (cdr segments)))))

; The raw language is intentionally permissive outside its mathematical domain.
; Keep domain rejection separate from the recurrence and runtime validation proof.
(defun fn2-eo-language-p (segments peer)
 (declare (xargs :verify-guards nil))
 (and (fn2-eo-segments-p segments) (fn2-eo-octets-p peer)
      (fn2-envelope-output-language-p segments peer)))

(defthm fn2-eo-language-rejects-malformed-by-definition
 (implies (or (not (fn2-eo-segments-p segments))
              (not (fn2-eo-octets-p peer)))
          (not (fn2-eo-language-p segments peer)))
 :hints (("Goal" :in-theory (enable fn2-eo-language-p))))

; A row contains one membership bit for every peer suffix, including empty.
(defun fn2-eo-language-row (segments peer)
 (declare (xargs :verify-guards nil))
 (if (consp peer)
     (cons (fn2-envelope-output-language-p segments peer)
           (fn2-eo-language-row segments (cdr peer)))
   (list (fn2-envelope-output-language-p segments nil))))

(defthm fn2-eo-language-row-head-unfolds
 (implies (true-listp peer)
  (equal (car (fn2-eo-language-row segments peer))
         (fn2-envelope-output-language-p segments peer)))
 :hints (("Goal" :in-theory (enable fn2-eo-language-row))))

(defthm fn2-eo-language-row-tail-unfolds
 (implies (consp peer)
  (equal (cdr (fn2-eo-language-row segments peer))
         (fn2-eo-language-row segments (cdr peer))))
 :hints (("Goal" :in-theory (enable fn2-eo-language-row))))

(defthm fn2-eo-octets-implies-true-list
 (implies (fn2-eo-octets-p peer) (true-listp peer))
 :hints (("Goal" :induct (fn2-eo-octets-p peer))))

; These are semantic recurrences, not yet a refinement of a runtime phase.
; The prefix RHS uses two DIFFERENT rows: following segments and current rest.
(defthm fn2-eo-exact-row-cell-unfolds
 (implies (and (unsigned-byte-p 8 byte) (fn2-eo-octets-p rest)
               (fn2-eo-segments-p following) (fn2-eo-octets-p peer))
  (equal
   (car (fn2-eo-language-row (cons (cons :exact (cons byte rest)) following) peer))
   (and (consp peer) (equal byte (car peer))
        (cadr (fn2-eo-language-row (cons (cons :exact rest) following) peer)))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-language-p
                                    fn2-eo-language-row))))

(defthm fn2-eo-prefix-row-cell-unfolds
 (implies (and (unsigned-byte-p 8 byte) (fn2-eo-octets-p rest)
               (fn2-eo-segments-p following) (fn2-eo-octets-p peer))
  (equal
   (car (fn2-eo-language-row (cons (cons :prefix (cons byte rest)) following) peer))
   (or (car (fn2-eo-language-row following peer))
       (and (consp peer) (equal byte (car peer))
            (cadr (fn2-eo-language-row (cons (cons :prefix rest) following) peer))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-language-p
                                    fn2-eo-language-row))))
(defthm fn2-eo-phase8-acc-refines-language
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 8)
       (consp (fn2-eo-scan fn2-envelope-output-state))
       (fn2-eo-octets-p (fn2-eo-scan fn2-envelope-output-state))
       (unsigned-byte-p 8 (fn2-eo-byte fn2-envelope-output-state))
       (fn2-eo-octets-p rest) (fn2-eo-segments-p following)
       (equal (fn2-eo-suffix-scan fn2-envelope-output-state)
              (fn2-eo-language-row following (fn2-eo-scan fn2-envelope-output-state)))
       (equal (fn2-eo-shifted fn2-envelope-output-state)
        (cdr (fn2-eo-language-row
         (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact) rest) following)
         (fn2-eo-scan fn2-envelope-output-state)))))
  (equal
   (fn2-eo-acc (fn2-envelope-output-step fn2-envelope-output-state))
   (cons (fn2-envelope-output-language-p
    (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact)
                (cons (fn2-eo-byte fn2-envelope-output-state) rest)) following)
    (fn2-eo-scan fn2-envelope-output-state))
    (fn2-eo-acc fn2-envelope-output-state))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step fn2-eo-language-row
                                    fn2-envelope-output-language-p))))
