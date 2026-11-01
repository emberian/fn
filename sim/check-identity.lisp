; Layer C: the IDENTITY checker (EXECUTION-MODEL-ROUND2-ASTRA F.1). An
; independent list interpreter over an identity trace. It keeps its own
; Binding (Message-ID -> the contents recorded for it, in record order) and
; judges each event at its own point in the trace. No identity book is
; included: the contract is restated here (UC 4.3 decision 3, STORAGE 4
; decision 6). The decision for (mid, c) is :duplicate iff c is recorded
; for mid as its accepted content (the first recorded), :evidence iff c is
; recorded only as conflict evidence, :conflict iff another content is,
; else :stored. A record
; (outcome :ok) of a stored offer adds the accepted content; of a
; conflicting one adds evidence, however many contents mid holds (no
; per-name ceiling: IDENTITY-ACROSS-PEERS ruling 7, C §4a). A duplicate
; or an :evidence records nothing. :stale records nothing and constrains
; nothing (the offer was decided around a later record of its bucket and is
; decided again);
; every other outcome is judged against the Binding at the record, its
; linearization point. Queries are judged at their point; seals and
; reclaims (staged bodies, journal placements) change nothing a query may
; observe; a :binding event (a node's scanned facts, each (mid c state))
; must equal the checker's Binding as a set, states included: the first
; content recorded for a Message-ID is :accepted, the rest :conflict (the
; served choice a peer's node must reproduce, REVIEW-20261030).
;
; Events: (:offer mid c answer outcome) (:query mid c answer) (:seal n)
; (:reclaim what) (:binding facts), facts a list of (mid c).
; Result: (:ok facts seals reclaims stales) or (:identity-error i name ...).
(in-package "ACL2")
(include-book "../books/declare")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :c)

(defun fn2-ci-contents (mid binding)
 (declare (xargs :guard t))
 (cond ((atom binding) nil)
       ((and (consp (car binding)) (equal (caar binding) mid)) (cdar binding))
       (t (fn2-ci-contents mid (cdr binding)))))
(defun fn2-ci-add (mid c binding)
 (declare (xargs :guard t))
 (cond ((atom binding) (list (list mid c)))
       ((and (consp (car binding)) (equal (caar binding) mid))
        (cons (cons mid (append (true-list-fix (cdar binding)) (list c))) (cdr binding)))
       (t (cons (car binding) (fn2-ci-add mid c (cdr binding))))))
(defun fn2-ci-decide (mid c binding)
 (declare (xargs :guard t))
 (let ((cs (fn2-ci-contents mid binding)))
  (cond ((and (consp cs) (equal c (car cs))) :duplicate)
        ((member-equal c (true-list-fix cs)) :evidence)
        ((consp cs) :conflict) (t :stored))))
(defun fn2-ci-facts-of (mid cs st)
 (declare (xargs :guard t))
 (if (atom cs) nil (cons (list mid (car cs) st) (fn2-ci-facts-of mid (cdr cs) :conflict))))
(defun fn2-ci-facts (binding)
 (declare (xargs :guard t))
 (cond ((atom binding) nil)
       ((consp (car binding)) (append (fn2-ci-facts-of (caar binding) (cdar binding) :accepted) (fn2-ci-facts (cdr binding))))
       (t (fn2-ci-facts (cdr binding)))))
(defun fn2-ci-same-set (a b)
 (declare (xargs :guard (and (true-listp a) (true-listp b))))
 (and (subsetp-equal a b) (subsetp-equal b a)))
; The outcome a correct engine reports for an offer whose decision was
; EXPECTED.
(defun fn2-ci-outcome-ok (expected outcome)
 (declare (xargs :guard t))
 (case expected
  (:duplicate (member-eq outcome '(:duplicate :none)))
  (:evidence (member-eq outcome '(:evidence :none)))
  (otherwise (eq outcome :ok))))

(defun fn2-ci-loop (events i binding seals reclaims stales)
 (declare (xargs :guard (and (natp i) (natp seals) (natp reclaims) (natp stales))))
 (if (atom events) (list :ok (fn2-ci-facts binding) seals reclaims stales)
  (let ((e (car events)))
   (case (and (consp e) (car e))
    (:offer
     (b* (((unless (and (true-listp e) (equal (len e) 5))) (list :identity-error i :malformed e))
          (mid (nth 1 e)) (c (nth 2 e)) (answer (nth 3 e)) (outcome (nth 4 e))
          ((when (eq outcome :stale)) (fn2-ci-loop (cdr events) (+ 1 i) binding seals reclaims (+ 1 stales)))
          (expected (fn2-ci-decide mid c binding))
          ((unless (eq answer expected)) (list :identity-error i :answer mid c expected answer))
          ((unless (fn2-ci-outcome-ok expected outcome)) (list :identity-error i :outcome mid c expected outcome)))
      (fn2-ci-loop (cdr events) (+ 1 i) (if (eq outcome :ok) (fn2-ci-add mid c binding) binding) seals reclaims stales)))
    (:query
     (b* (((unless (and (true-listp e) (equal (len e) 4))) (list :identity-error i :malformed e))
          (expected (fn2-ci-decide (nth 1 e) (nth 2 e) binding))
          ((unless (eq (nth 3 e) expected)) (list :identity-error i :query (nth 1 e) (nth 2 e) expected (nth 3 e))))
      (fn2-ci-loop (cdr events) (+ 1 i) binding seals reclaims stales)))
    (:seal (fn2-ci-loop (cdr events) (+ 1 i) binding (+ 1 seals) reclaims stales))
    (:reclaim (fn2-ci-loop (cdr events) (+ 1 i) binding seals (+ 1 reclaims) stales))
    (:binding
     (b* (((unless (and (true-listp e) (equal (len e) 2) (true-listp (nth 1 e)))) (list :identity-error i :malformed e))
          ((unless (fn2-ci-same-set (nth 1 e) (fn2-ci-facts binding))) (list :identity-error i :binding (fn2-ci-facts binding) (nth 1 e))))
      (fn2-ci-loop (cdr events) (+ 1 i) binding seals reclaims stales)))
    (otherwise (list :identity-error i :unknown e))))))
(defun fn2-check-identity (events)
 (declare (xargs :guard t))
 (fn2-ci-loop events 0 nil 0 0 0))

; Controls (the checker's own teeth): a correct trace passes (a third
; content of one Message-ID recorded as evidence: no ceiling); a flipped
; answer, evidence answered as accepted content, a dropped conflict record,
; a binding missing a fact, and an accepted second content are refused.
(defconst *fn2-ci-good*
 '((:offer m1 a :stored :ok) (:offer m1 a :duplicate :duplicate) (:offer m1 b :conflict :ok)
   (:offer m2 a :stored :stale) (:offer m2 a :stored :ok) (:seal 1) (:reclaim :bodies)
   (:offer m1 c :conflict :ok)
   (:query m1 b :evidence) (:query m1 a :duplicate) (:query m1 z :conflict) (:query m3 a :stored)
   (:binding ((m2 a :accepted) (m1 c :conflict) (m1 b :conflict) (m1 a :accepted)))))
(assert-event (equal (fn2-check-identity *fn2-ci-good*)
                     '(:ok ((m1 a :accepted) (m1 b :conflict) (m1 c :conflict) (m2 a :accepted)) 1 1 1)))
;; The same facts with the accepted and an evidence content exchanged (a
;; node that served the other choice) are refused.
(assert-event (equal (car (fn2-check-identity (append (butlast *fn2-ci-good* 1)
                                                      '((:binding ((m2 a :accepted) (m1 c :conflict) (m1 b :accepted) (m1 a :conflict)))))))
                     :identity-error))
(assert-event (equal (car (fn2-check-identity (cons '(:offer m9 a :conflict :ok) *fn2-ci-good*))) :identity-error))
(assert-event (equal (fn2-check-identity '((:offer m1 a :stored :ok) (:offer m1 b :conflict :none)))
                     '(:identity-error 1 :outcome m1 b :conflict :none)))
(assert-event (equal (car (fn2-check-identity (append (butlast *fn2-ci-good* 1) '((:binding ((m1 a) (m1 b))))))) :identity-error))
(assert-event (equal (fn2-check-identity '((:offer m1 a :stored :ok) (:offer m1 b :conflict :ok) (:query m1 b :duplicate)))
                     '(:identity-error 2 :query m1 b :evidence :duplicate)))
(assert-event (equal (fn2-check-identity '((:offer m1 a :stored :ok) (:offer m1 b :stored :ok)))
                     '(:identity-error 1 :answer m1 b :conflict :stored)))
