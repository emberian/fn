(in-package "ACL2")
(include-book "article-stream")
(include-book "served-catalog")
(in-theory (disable fn-scat-membership-number-is-number-in))

(defun-nx fn-asx-prefix-equalp (group row-group at)
  (if (zp at)
      t
    (and (equal (char group (+ -1 at)) (char row-group (+ -1 at)))
         (fn-asx-prefix-equalp group row-group (+ -1 at)))))

(defun-nx fn-asx-hitp (mode group number article)
  (and (equal (fn-nntp-membership-number group (fn-article-memberships article)) number)
       (or (not (eq mode :current)) (fn-nntp-article-idp article))))

(defun-nx fn-asx-first (mode group number articles)
  (cond ((atom articles) nil)
        ((fn-asx-hitp mode group number (car articles)) (car articles))
        (t (fn-asx-first mode group number (cdr articles)))))

(defun-nx fn-asx-spec (it)
  (let ((mode (fn-ast-at 1 it)) (group (fn-ast-at 2 it)) (number (fn-ast-at 3 it))
        (remaining (fn-ast-at 4 it)) (article (fn-ast-at 5 it))
        (members (fn-ast-at 6 it)) (phase (fn-ast-at 9 it)))
    (case phase
      (:next (fn-asx-first mode group number remaining))
      ((:members :compare)
       (if (and (equal (fn-nntp-membership-number group members) number)
                (or (not (eq mode :current)) (fn-nntp-article-idp article)))
           article
         (fn-asx-first mode group number (cdr remaining))))
      (:selected article)
      (t nil))))

(defun-nx fn-asx-goodp (it)
  (let ((mode (fn-ast-at 1 it)) (group (fn-ast-at 2 it)) (number (fn-ast-at 3 it))
        (remaining (fn-ast-at 4 it)) (article (fn-ast-at 5 it))
        (members (fn-ast-at 6 it)) (row (fn-ast-at 7 it))
        (at (fn-ast-at 8 it)) (phase (fn-ast-at 9 it)))
    (and (member-eq mode '(:number :current))
         (stringp group) (posp number)
         (case phase
           (:next t)
           (:members (and (consp remaining) (equal article (car remaining))
                          (or (atom members) (consp article))))
           (:compare (and (consp remaining) (equal article (car remaining)) (consp article)
                          (consp members) (equal row (car members))
                          (consp row) (stringp (car row))
                          (equal (length (car row)) (length group))
                          (natp at) (<= at (length group))
                          (fn-asx-prefix-equalp group (car row) at)))
           (:selected (and (consp article)
                           (or (not (eq mode :current)) (fn-nntp-article-idp article))))
           (:missing t)
           (t nil)))))

(defun-nx fn-asx-meas (it)
  (let ((phase (fn-ast-at 9 it)) (remaining (fn-ast-at 4 it))
        (members (fn-ast-at 6 it)) (group (fn-ast-at 2 it)) (at (fn-ast-at 8 it)))
    (make-ord 3 (+ 1 (* 2 (len remaining)) (if (eq phase :next) 1 0))
              (make-ord 2 (+ 1 (len members))
                        (make-ord 1 (if (eq phase :members) 2 1)
                                  (if (stringp group) (nfix (- (length group) (nfix at))) 0))))))

(defun fn-asx-lp (x y at)
  (declare (xargs :measure (nfix at)))
  (if (zp at)
      t
    (and (equal (car x) (car y))
         (fn-asx-lp (cdr x) (cdr y) (+ -1 at)))))

(local
 (defthm fn-asx-lp-snoc
   (implies (natp at)
            (equal (fn-asx-lp x y (+ 1 at))
                   (and (fn-asx-lp x y at)
                        (equal (nth at x) (nth at y)))))
   :hints (("Goal" :induct (fn-asx-lp x y at)
                   :in-theory (enable fn-asx-lp)))))

(local
 (defun fn-asx-pair-ind (x y)
   (if (and (consp x) (consp y)) (fn-asx-pair-ind (cdr x) (cdr y)) (list x y))))

(local
 (defthm fn-asx-lp-equal
   (implies (and (true-listp x) (true-listp y) (equal (len x) (len y))
                 (fn-asx-lp x y (len x)))
            (equal x y))
   :rule-classes nil
   :hints (("Goal" :induct (fn-asx-pair-ind x y)
                   :in-theory (enable fn-asx-lp)))))

(local
 (defthm fn-asx-lp-zero
   (fn-asx-lp x y 0)
   :hints (("Goal" :in-theory (enable fn-asx-lp)))))

(local
 (defthm fn-asx-lp-pred
   (implies (posp at)
            (equal (fn-asx-lp x y at)
                   (and (fn-asx-lp x y (+ -1 at))
                        (equal (nth (+ -1 at) x) (nth (+ -1 at) y)))))
   :hints (("Goal" :use ((:instance fn-asx-lp-snoc (at (+ -1 at))))))))

(local
 (defthm fn-asx-prefix-is-lp
   (implies (natp at)
            (equal (fn-asx-prefix-equalp a b at)
                   (fn-asx-lp (coerce a 'list) (coerce b 'list) at)))
   :hints (("Goal" :in-theory (e/d (fn-asx-prefix-equalp char (:executable-counterpart fn-asx-lp)) (fn-asx-lp))
                   :induct (fn-asx-prefix-equalp a b at)))))

(defthm fn-asx-prefix-equalp-full
  (implies (and (stringp a) (stringp b) (equal (length a) (length b))
                (equal at (length a)) (fn-asx-prefix-equalp a b at))
           (equal a b))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-asx-lp-equal (x (coerce a 'list)) (y (coerce b 'list)))))))

; the one-step lemmas
(defthm fn-asx-select-one-good
  (implies (and (fn-asx-goodp it) (not (fn-ast-select-donep it)))
           (fn-asx-goodp (fn-ast-select-one it)))
  :hints (("Goal" :in-theory (enable fn-ast-select-one fn-asx-goodp fn-ast-select-state fn-ast-at fn-ast-select-donep fn-article-memberships))))

(defthm fn-asx-select-one-meas
  (implies (and (fn-asx-goodp it) (not (fn-ast-select-donep it))
                (not (fn-ast-select-donep (fn-ast-select-one it))))
           (o< (fn-asx-meas (fn-ast-select-one it)) (fn-asx-meas it)))
  :hints (("Goal" :in-theory (enable fn-ast-select-one fn-asx-goodp fn-ast-select-state fn-ast-at fn-ast-select-donep fn-asx-meas))))

(local
 (defthm fn-asx-unequal-by-char
   (implies (not (equal (char a i) (char b i))) (not (equal a b)))))

(local
 (defthm fn-asx-unequal-by-length
   (implies (not (equal (length a) (length b))) (not (equal a b)))))

(local
 (defthm fn-asx-compare-end-group
   (implies (and (fn-asx-goodp it) (equal (fn-ast-at 9 it) :compare)
                 (<= (length (fn-ast-at 2 it)) (fn-ast-at 8 it)))
            (equal (car (fn-ast-at 7 it)) (fn-ast-at 2 it)))
   :hints (("Goal" :use ((:instance fn-asx-prefix-equalp-full
                                    (a (fn-ast-at 2 it)) (b (car (fn-ast-at 7 it)))
                                    (at (fn-ast-at 8 it))))
                   :in-theory (enable fn-asx-goodp)))))

(defthm fn-asx-select-one-spec
  (implies (and (fn-asx-goodp it) (not (fn-ast-select-donep it)))
           (equal (fn-asx-spec (fn-ast-select-one it)) (fn-asx-spec it)))
  :hints (("Goal" :in-theory (enable fn-ast-select-one fn-asx-goodp fn-ast-select-state fn-ast-at fn-ast-select-donep fn-asx-spec fn-asx-first fn-asx-hitp fn-nntp-membership-number))))

(defun-nx fn-asx-need (it)
  (declare (xargs :measure (fn-asx-meas it) :well-founded-relation o<
                  :hints (("Goal" :use fn-asx-select-one-meas))))
  (if (or (not (fn-asx-goodp it)) (fn-ast-select-donep it))
      0
    (if (fn-ast-select-donep (fn-ast-select-one it))
        1
      (+ 1 (fn-asx-need (fn-ast-select-one it))))))

(defthm fn-asx-select-one-fields
  (implies (and (fn-asx-goodp it) (not (fn-ast-select-donep it)))
           (and (equal (fn-ast-at 1 (fn-ast-select-one it)) (fn-ast-at 1 it))
                (equal (fn-ast-at 2 (fn-ast-select-one it)) (fn-ast-at 2 it))
                (equal (fn-ast-at 3 (fn-ast-select-one it)) (fn-ast-at 3 it))))
  :hints (("Goal" :in-theory (enable fn-ast-select-one fn-asx-goodp fn-ast-select-state fn-ast-at fn-ast-select-donep))))

;; The induction runs on the work still needed, with the slack held fixed.
(local
 (defthm fn-asx-step-reaches-spec-extra
   (implies (and (fn-asx-goodp it) (natp extra))
            (let ((r (fn-ast-select-step it (+ (fn-asx-need it) extra))))
              (and (fn-ast-select-donep r)
                   (equal (fn-asx-spec r) (fn-asx-spec it))
                   (equal (fn-ast-at 1 r) (fn-ast-at 1 it))
                   (equal (fn-ast-at 2 r) (fn-ast-at 2 it))
                   (equal (fn-ast-at 3 r) (fn-ast-at 3 it)))))
   :hints (("Goal" :induct (fn-asx-need it)
                   :in-theory (e/d (fn-asx-need)
                                   (fn-ast-select-one fn-ast-select-donep fn-asx-spec fn-asx-goodp)))
           ("Subgoal *1/3" :use ((:instance fn-asx-select-one-good)
                                 (:instance fn-asx-select-one-spec)
                                 (:instance fn-asx-select-one-fields))
            :in-theory (e/d (fn-asx-need)
                            (fn-ast-select-one fn-asx-spec fn-asx-goodp))))))

; KEYSTONE: running the retained selection with enough work reaches a done
; state whose outcome is the specification's, with mode, group and number kept.
(defthm fn-asx-step-reaches-spec
  (implies (and (fn-asx-goodp it) (natp fuel) (<= (fn-asx-need it) fuel))
           (let ((r (fn-ast-select-step it fuel)))
             (and (fn-ast-select-donep r)
                  (equal (fn-asx-spec r) (fn-asx-spec it))
                  (equal (fn-ast-at 1 r) (fn-ast-at 1 it))
                  (equal (fn-ast-at 2 r) (fn-ast-at 2 it))
                  (equal (fn-ast-at 3 r) (fn-ast-at 3 it)))))
  :hints (("Goal" :use ((:instance fn-asx-step-reaches-spec-extra
                                   (extra (- fuel (fn-asx-need it))))))))

; -----------------------------------------------------------------------------
; The specification is the archive-list reads the old selection computed.

(defthm fn-asx-first-number-is-find-group-number
  (equal (fn-asx-first :number group number articles)
         (fn-nntp-find-group-number group number articles))
  :hints (("Goal" :in-theory (enable fn-asx-first fn-asx-hitp fn-nntp-find-group-number))))

(defthm fn-asx-start-good
  (implies (and (member-eq mode '(:number :current)) (stringp group) (posp number))
           (fn-asx-goodp (fn-ast-select-state mode group number articles nil nil nil 0 :next)))
  :hints (("Goal" :in-theory (enable fn-asx-goodp fn-ast-select-state fn-ast-at))))

(defthm fn-asx-start-spec
  (equal (fn-asx-spec (fn-ast-select-state mode group number articles nil nil nil 0 :next))
         (fn-asx-first mode group number articles))
  :hints (("Goal" :in-theory (enable fn-asx-spec fn-ast-select-state fn-ast-at))))


; With each number carried once (the view's articles, fn-scat-uniq), the first
; article with the number and a renderable id is the number's article when that
; one has an id.
(defthm fn-asx-first-current-is-found
  (implies (and (fn-scat-uniq group articles) (posp number))
           (equal (fn-asx-first :current group number articles)
                  (let ((a (fn-nntp-find-group-number group number articles)))
                    (if (fn-nntp-article-idp a) a nil))))
  :hints (("Goal" :induct (fn-scat-uniq group articles)
           :in-theory (enable fn-scat-uniq fn-asx-first fn-asx-hitp fn-nntp-find-group-number))))

; -----------------------------------------------------------------------------
; The routed selection: a catalog lookup answers the retained selection's
; question at once, in the state the walk reaches.

(defun fn-asx-done-state (mode group number article)
  (declare (xargs :guard t))
  (if (and (consp article)
           (or (not (eq mode :current)) (fn-nntp-article-idp article)))
      (fn-ast-select-state mode group number nil article nil nil 0 :selected)
    (fn-ast-select-state mode group number nil nil nil nil 0 :missing)))

; What a selection answers: its mode, group and number, whether it found an
; article, and which.
(defun fn-asx-outcome (it)
  (declare (xargs :guard t))
  (list (fn-ast-at 1 it) (fn-ast-at 2 it) (fn-ast-at 3 it) (fn-ast-at 9 it)
        (if (eq (fn-ast-at 9 it) :selected) (fn-ast-at 5 it) nil)))

(defthm fn-asx-outcome-of-done-state
  (equal (fn-asx-outcome (fn-asx-done-state mode group number article))
         (list mode group number
               (if (and (consp article)
                        (or (not (eq mode :current)) (fn-nntp-article-idp article)))
                   :selected :missing)
               (if (and (consp article)
                        (or (not (eq mode :current)) (fn-nntp-article-idp article)))
                   article nil)))
  :hints (("Goal" :in-theory (enable fn-asx-done-state fn-asx-outcome fn-ast-select-state fn-ast-at))))

; A good done state's outcome is its done-state of the specification's article.
(defthm fn-asx-done-outcome-is-done-state
  (implies (and (fn-asx-goodp r) (fn-ast-select-donep r))
           (equal (fn-asx-outcome r)
                  (fn-asx-outcome (fn-asx-done-state (fn-ast-at 1 r) (fn-ast-at 2 r)
                                                     (fn-ast-at 3 r) (fn-asx-spec r)))))
  :hints (("Goal" :in-theory (enable fn-asx-goodp fn-asx-spec fn-asx-outcome fn-ast-select-donep
                                     fn-asx-done-state fn-ast-select-state fn-ast-at))))

(defthm fn-asx-step-good
  (implies (fn-asx-goodp it)
           (fn-asx-goodp (fn-ast-select-step it fuel)))
  :hints (("Goal" :induct (fn-ast-select-step it fuel)
                  :in-theory (e/d (fn-ast-select-step) (fn-ast-select-one fn-ast-select-donep fn-asx-goodp)))))

; KEYSTONE: whatever the walk reaches with enough work, the lookup states at once.
(defthm fn-asx-walk-is-lookup
  (implies (and (member-eq mode '(:number :current)) (stringp group) (posp number)
                (natp fuel)
                (<= (fn-asx-need (fn-ast-select-state mode group number articles nil nil nil 0 :next))
                    fuel))
           (equal (fn-asx-outcome
                   (fn-ast-select-step
                    (fn-ast-select-state mode group number articles nil nil nil 0 :next) fuel))
                  (fn-asx-outcome
                   (fn-asx-done-state mode group number
                                      (fn-asx-first mode group number articles)))))
  :hints (("Goal" :use ((:instance fn-asx-start-good (articles articles))
                        (:instance fn-asx-start-spec (articles articles))
                        (:instance fn-asx-step-reaches-spec
                                   (it (fn-ast-select-state mode group number articles nil nil nil 0 :next)))
                        (:instance fn-asx-step-good
                                   (it (fn-ast-select-state mode group number articles nil nil nil 0 :next)))
                        (:instance fn-asx-done-outcome-is-done-state
                                   (r (fn-ast-select-step
                                       (fn-ast-select-state mode group number articles nil nil nil 0 :next)
                                       fuel))))
           :in-theory (disable fn-asx-step-reaches-spec fn-asx-done-outcome-is-done-state fn-asx-step-good
                               fn-asx-start-good fn-asx-start-spec
                               fn-asx-need fn-ast-select-step fn-asx-outcome fn-asx-done-state
                               fn-asx-first fn-asx-spec fn-asx-goodp fn-ast-select-donep))))
