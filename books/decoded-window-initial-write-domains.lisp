; Actual initializer updater arguments for selected-runtime family joining.
; No setter/compiled-frame/allocation/INITIAL adequacy is inferred.
(in-package "ACL2")
(include-book "decoded-window-initial-source-counts")
(include-book "decoded-window-initial-retained-state")
(defun-nx fn-piw-register-write-roster (trace)
 (if (atom trace) nil
  (if (and (consp (car trace)) (equal (caar trace) :borrow)
           (equal (cadar trace) 'fn-zin-set))
    (cons (list (car (caddr (car trace))) (cadr (caddr (car trace))))
          (fn-piw-register-write-roster (cdr trace)))
    (fn-piw-register-write-roster (cdr trace)))))
(defthm fn-piw-register-write-roster-of-append
 (equal (fn-piw-register-write-roster (append a b))
        (append (fn-piw-register-write-roster a) (fn-piw-register-write-roster b)))
 :hints (("Goal" :induct (append a b))))
(defun fn-piw-reset-register-roster (i)
 (declare (xargs :guard (natp i) :measure (nfix (- 18 (nfix i)))))
 (if (and (natp i) (< i 18))
   (cons (list i 0) (fn-piw-reset-register-roster (+ i 1))) nil))
(defthm fn-piw-reset-loop-exact-register-write-roster
 (equal (fn-piw-register-write-roster (cdr (fn-piw-zin-reset-loop i fn-zin-st)))
        (fn-piw-reset-register-roster i))
 :rule-classes nil
 :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
  :in-theory (e/d (fn-piw-register-write-roster fn-piw-reset-register-roster
                    fn-piw-zin-reset-loop)
                  (fn-zin-set fn-zin-set$inline)))))
(defthm fn-piw-reset-exact-register-write-roster
 (equal (fn-piw-register-write-roster (cdr (fn-piw-zin-reset fn-zin-st)))
        (append (fn-piw-reset-register-roster 0) '((19 0) (11 1))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-reset-loop-exact-register-write-roster (i 0))
  :in-theory (e/d (fn-piw-register-write-roster fn-piw-zin-reset)
                 (fn-piw-zin-reset-loop fn-zin-set fn-zin-set$inline)))))
(defthm fn-piw-no-register-writes-means-empty-roster
 (implies (equal (fn-piw-borrow-count 'fn-zin-set trace) 0)
          (equal (fn-piw-register-write-roster trace) nil))
 :hints (("Goal" :induct (fn-piw-borrow-count 'fn-zin-set trace)
  :in-theory (enable fn-piw-register-write-roster fn-piw-borrow-count))))
(local (defthm fn-piw-actual-payload-ready-preset-value
 (equal (mv-nth 0 (fn-zin-payload-ready dict fn-zin-win fn-zin-tab))
        (min (len dict) 32768))
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-zin-payload-ready)
    (fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back
     fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back nthcdr len min))))))
(defthm fn-piw-initialize-exact-register-write-roster
 (equal (fn-piw-register-write-roster
            (cdr (fn-piw-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
        (append (fn-piw-reset-register-roster 0)
                (list '(19 0) '(11 1) (list 18 (min (len dict) 32768)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use fn-piw-reset-exact-register-write-roster
  :in-theory (e/d (fn-piw-pzw-initialize fn-piw-register-write-roster)
    (fn-piw-zin-reset fn-piw-zin-payload-ready fn-zin-set fn-zin-set$inline
     fn-zin-out-clear fn-zin-out-reserve min len)))))
(defthm fn-piw-ewz-begin-exact-register-write-roster
 (equal (fn-piw-register-write-roster
            (cdr (fn-piw-ewz-begin file eoff elen poff compressed decoded offset
                   ticket incarnation lease expected dict hash zin win tab out)))
        (append (fn-piw-reset-register-roster 0)
                (list '(19 0) '(11 1) (list 18 (min (len dict) 32768)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-initialize-exact-register-write-roster
          (fn-zin-st zin) (fn-zin-win win) (fn-zin-tab tab) (fn-zin-out out))
  :in-theory (e/d (fn-piw-ewz-begin fn-piw-register-write-roster)
    (fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-pzt-pzd-budget
     fn-pzt-pzw-stored-admissiblep nfix min len)))))
(defthm fn-piw-begin-exact-register-write-roster
 (equal (fn-piw-register-write-roster
            (cdr (fn-piw-pwz-begin token incarnation hash zin win tab out)))
        (append (fn-piw-reset-register-roster 0)
                (list '(19 0) '(11 1) (list 18 (min (len (fn-pwz-dictionary token)) 32768)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-ewz-begin-exact-register-write-roster
    (dict (fn-pwz-dictionary token))
    (file (nfix (fn-pwz-nth 2 token))) (eoff (nfix (fn-pwz-nth 3 token)))
    (elen (nfix (fn-pwz-nth 4 token))) (poff (nfix (fn-pwz-nth 5 token)))
    (compressed (nfix (fn-pwz-nth 6 token))) (decoded (nfix (fn-pwz-nth 9 token)))
    (offset (nfix (fn-pwz-nth 7 token))) (ticket (fn-pwz-nth 1 token))
    (lease token) (expected (nfix (fn-pwz-nth 8 token))))
  :in-theory (e/d (fn-piw-pwz-begin fn-piw-register-write-roster)
    (fn-piw-ewz-begin fn-pwz-nth fn-pwz-dictionary nfix min len
     (:e fn-pwz-dictionary))))))
(defun fn-piw-register-write-domainp (roster)
 (declare (xargs :guard t))
 (if (atom roster) (equal roster nil)
  (and (true-listp (car roster)) (equal (len (car roster)) 2)
       (natp (caar roster)) (< (caar roster) 20)
       (natp (cadar roster)) (<= (cadar roster) 32768)
       (fn-piw-register-write-domainp (cdr roster)))))
(defthm fn-piw-register-write-domainp-of-append
 (implies (and (fn-piw-register-write-domainp a) (fn-piw-register-write-domainp b))
          (fn-piw-register-write-domainp (append a b)))
 :hints (("Goal" :induct (append a b))))
(defthm fn-piw-reset-roster-establishes-register-write-domain
 (fn-piw-register-write-domainp (fn-piw-reset-register-roster i))
 :hints (("Goal" :induct (fn-piw-reset-register-roster i)
  :in-theory (enable fn-piw-reset-register-roster fn-piw-register-write-domainp))))
(defthm fn-piw-actual-begin-register-write-domain
 (fn-piw-register-write-domainp
   (fn-piw-register-write-roster
     (cdr (fn-piw-pwz-begin token incarnation hash zin win tab out))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use fn-piw-begin-exact-register-write-roster
  :in-theory (e/d (fn-piw-register-write-domainp)
    (fn-piw-pwz-begin fn-piw-register-write-roster fn-piw-reset-register-roster
     fn-pwz-dictionary (:e fn-pwz-dictionary))))))
(defconst *fn-piw-digest-setters*
 '(update-pgs-dc-mode update-pgs-dc-sel update-pgs-dc-base update-pgs-dc-total
   update-pgs-dc-start update-pgs-dc-end update-pgs-dc-pos update-pgs-dc-counter
   update-pgs-dc-power update-pgs-dc-depth update-pgs-dc-cv update-pgs-dc-output
   update-pgs-dc-capture update-pgs-dc-lease update-pgs-dc-answer))
(defun-nx fn-piw-digest-write-roster (trace)
 (if (atom trace) nil
  (if (and (consp (car trace)) (equal (caar trace) :borrow)
           (member-equal (cadar trace) *fn-piw-digest-setters*))
    (cons (list (cadar trace) (car (caddr (car trace))))
          (fn-piw-digest-write-roster (cdr trace)))
    (fn-piw-digest-write-roster (cdr trace)))))
(defthm fn-piw-digest-write-roster-of-append
 (equal (fn-piw-digest-write-roster (append a b))
        (append (fn-piw-digest-write-roster a) (fn-piw-digest-write-roster b)))
 :hints (("Goal" :induct (append a b))))
(defun-nx fn-piw-digest-begin-inputs (sel base nb capture lease)
 (list '(update-pgs-dc-mode :node) (list 'update-pgs-dc-sel sel)
       (list 'update-pgs-dc-base base) (list 'update-pgs-dc-total (* 8 nb))
       '(update-pgs-dc-start 0) (list 'update-pgs-dc-end (* 8 nb))
       '(update-pgs-dc-pos 0) '(update-pgs-dc-counter 0)
       '(update-pgs-dc-power 1) '(update-pgs-dc-depth 0)
       (list 'update-pgs-dc-cv *fn-b3-iv*) '(update-pgs-dc-output nil)
       (list 'update-pgs-dc-capture capture) (list 'update-pgs-dc-lease lease)
       '(update-pgs-dc-answer 0)))
(defthm fn-piw-dc-begin-exact-digest-write-roster
 (equal (fn-piw-digest-write-roster
          (cdr (fn-piw-pgs-dc-begin sel base nb capture lease hash)))
        (fn-piw-digest-begin-inputs sel base nb capture lease))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-piw-pgs-dc-begin fn-piw-digest-write-roster fn-piw-digest-begin-inputs)
 (update-pgs-dc-mode update-pgs-dc-sel update-pgs-dc-base update-pgs-dc-total
  update-pgs-dc-start update-pgs-dc-end update-pgs-dc-pos update-pgs-dc-counter
  update-pgs-dc-power update-pgs-dc-depth update-pgs-dc-cv update-pgs-dc-output
  update-pgs-dc-capture update-pgs-dc-lease update-pgs-dc-answer)))))
(defthm fn-piw-dcb-begin-exact-digest-write-roster
 (equal (fn-piw-digest-write-roster
          (cdr (fn-piw-pgs-dcb-begin sel base byte-total capture lease hash)))
        (append (fn-piw-digest-begin-inputs sel base (ceiling byte-total 64) capture lease)
                (list (list 'update-pgs-dc-total (ceiling byte-total 8))
                      (list 'update-pgs-dc-end (ceiling byte-total 8)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-dc-begin-exact-digest-write-roster
          (nb (ceiling byte-total 64)))
  :in-theory (e/d (fn-piw-pgs-dcb-begin fn-piw-pgs-dcb-word-count fn-piw-digest-write-roster)
    (fn-piw-pgs-dc-begin fn-piw-digest-begin-inputs pgs-dcb-word-count ceiling nfix
     update-pgs-dc-total update-pgs-dc-end)))))

(local (defthm fn-piw-zin-reset-loop-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-piw-zin-reset-loop i fn-zin-st))) nil)
 :hints (("Goal"  :induct (fn-zin-reset-loop i fn-zin-st)
  :in-theory (e/d (fn-piw-zin-reset-loop fn-piw-digest-write-roster)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset
     fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewp-state
     fn-piw-ewp-begin fn-piw-ews-capture fn-piw-ewz-state
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))

(local (defthm fn-piw-zin-reset-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-piw-zin-reset fn-zin-st))) nil)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-piw-zin-reset fn-piw-digest-write-roster)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset-loop 
     fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewp-state
     fn-piw-ewp-begin fn-piw-ews-capture fn-piw-ewz-state
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))

(local (defthm fn-piw-zin-payload-ready-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-piw-zin-payload-ready dict fn-zin-win fn-zin-tab))) nil)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-piw-zin-payload-ready fn-piw-digest-write-roster)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset-loop fn-piw-zin-reset
     fn-piw-pzw-initialize fn-piw-ewp-state
     fn-piw-ewp-begin fn-piw-ews-capture fn-piw-ewz-state
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))

(local (defthm fn-piw-pzw-initialize-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-piw-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) nil)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-piw-pzw-initialize fn-piw-digest-write-roster)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset-loop fn-piw-zin-reset
     fn-piw-zin-payload-ready fn-piw-ewp-state
     fn-piw-ewp-begin fn-piw-ews-capture fn-piw-ewz-state
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))

(local (defthm fn-pzt-pzd-budget-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-pzt-pzd-budget clen n))) nil)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-pzt-pzd-budget fn-piw-digest-write-roster)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset-loop fn-piw-zin-reset
     fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewp-state
     fn-piw-ewp-begin fn-piw-ews-capture fn-piw-ewz-state
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))

(local (defthm fn-pzt-pzw-stored-admissiblep-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-pzt-pzw-stored-admissiblep compressed expected))) nil)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-pzt-pzw-stored-admissiblep fn-piw-digest-write-roster fn-pzt-pzw-stored-allowance fn-pzt-zin-stored-allowance)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset-loop fn-piw-zin-reset
     fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewp-state
     fn-piw-ewp-begin fn-piw-ews-capture fn-piw-ewz-state
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))

(local (defthm fn-piw-ewp-state-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-piw-ewp-state phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset))) nil)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-piw-ewp-state fn-piw-digest-write-roster)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset-loop fn-piw-zin-reset
     fn-piw-zin-payload-ready fn-piw-pzw-initialize 
     fn-piw-ewp-begin fn-piw-ews-capture fn-piw-ewz-state
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))

(local (defthm fn-piw-ewp-begin-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-piw-ewp-begin file eoff elen poff plen offset ticket incarnation lease expected))) nil)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-piw-ewp-begin fn-piw-digest-write-roster)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset-loop fn-piw-zin-reset
     fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewp-state
     fn-piw-ews-capture fn-piw-ewz-state
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))

(local (defthm fn-piw-ews-capture-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-piw-ews-capture s))) nil)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-piw-ews-capture fn-piw-digest-write-roster)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset-loop fn-piw-zin-reset
     fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewp-state
     fn-piw-ewp-begin fn-piw-ewz-state
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))

(local (defthm fn-piw-ewz-state-has-no-digest-setter-inputs
 (equal (fn-piw-digest-write-roster (cdr (fn-piw-ewz-state mode plan n offset wanted budget ip end status))) nil)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-piw-ewz-state fn-piw-digest-write-roster)
    (fn-zin-set fn-zin-set$inline fn-piw-zin-reset-loop fn-piw-zin-reset
     fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewp-state
     fn-piw-ewp-begin fn-piw-ews-capture 
     nfix natp min len fn-zin-win-clear fn-zin-win-reserve
     fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list
     fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
     fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve))))))
(defun-nx fn-piw-byte-digest-inputs (byte-total capture lease)
 (append (fn-piw-digest-begin-inputs 0 0 (ceiling byte-total 64) capture lease)
         (list (list 'update-pgs-dc-total (ceiling byte-total 8))
               (list 'update-pgs-dc-end (ceiling byte-total 8)))))
(defthm fn-piw-ews-begin-exact-digest-write-roster
 (equal (fn-piw-digest-write-roster
          (cdr (fn-piw-ews-begin file eoff elen poff plen offset
                  ticket incarnation lease expected hash)))
        (fn-piw-byte-digest-inputs elen
          (fn-ews-capture (fn-ewp-begin file eoff elen poff plen offset
                             ticket incarnation lease expected)) lease))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-dcb-begin-exact-digest-write-roster
    (sel 0) (base 0) (byte-total elen)
    (capture (fn-ews-capture (fn-ewp-begin file eoff elen poff plen offset
                                 ticket incarnation lease expected))))
  :in-theory (e/d (fn-piw-ews-begin fn-piw-digest-write-roster fn-piw-byte-digest-inputs)
    (fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dcb-begin
     fn-piw-digest-begin-inputs fn-ews-capture fn-ewp-begin ceiling)))))
(defthm fn-piw-ewz-begin-exact-digest-write-roster
 (equal (fn-piw-digest-write-roster
          (cdr (fn-piw-ewz-begin file eoff elen poff compressed decoded offset
                  ticket incarnation lease expected dict hash zin win tab out)))
        (fn-piw-byte-digest-inputs elen
          (fn-ews-capture (fn-ewp-begin file eoff elen poff compressed compressed
                             ticket incarnation lease expected)) lease))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-ews-begin-exact-digest-write-roster
           (plen compressed) (offset compressed))
  :in-theory (e/d (fn-piw-ewz-begin fn-piw-digest-write-roster)
    (fn-piw-ews-begin fn-piw-pzw-initialize fn-pzt-pzd-budget
     fn-pzt-pzw-stored-admissiblep fn-piw-ewz-state fn-piw-byte-digest-inputs
     fn-ews-capture fn-ewp-begin nfix min)))))
(defthm fn-piw-begin-exact-digest-write-roster
 (equal (fn-piw-digest-write-roster
          (cdr (fn-piw-pwz-begin token incarnation hash zin win tab out)))
        (fn-piw-byte-digest-inputs (nfix (fn-pwz-nth 4 token))
          (fn-ews-capture (fn-ewp-begin
           (nfix (fn-pwz-nth 2 token)) (nfix (fn-pwz-nth 3 token))
           (nfix (fn-pwz-nth 4 token)) (nfix (fn-pwz-nth 5 token))
           (nfix (fn-pwz-nth 6 token)) (nfix (fn-pwz-nth 6 token))
           (fn-pwz-nth 1 token) incarnation token (nfix (fn-pwz-nth 8 token)))) token))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use (:instance fn-piw-ewz-begin-exact-digest-write-roster
    (dict (fn-pwz-dictionary token))
    (file (nfix (fn-pwz-nth 2 token))) (eoff (nfix (fn-pwz-nth 3 token)))
    (elen (nfix (fn-pwz-nth 4 token))) (poff (nfix (fn-pwz-nth 5 token)))
    (compressed (nfix (fn-pwz-nth 6 token))) (decoded (nfix (fn-pwz-nth 9 token)))
    (offset (nfix (fn-pwz-nth 7 token))) (ticket (fn-pwz-nth 1 token))
    (lease token) (expected (nfix (fn-pwz-nth 8 token))))
 :in-theory (e/d (fn-piw-pwz-begin fn-piw-digest-write-roster)
    (fn-piw-ewz-begin fn-pwz-nth fn-pwz-dictionary nfix fn-piw-byte-digest-inputs
     fn-ews-capture fn-ewp-begin (:e fn-pwz-dictionary))))))
(defconst *fn-piw-digest-natural-setters*
 '(update-pgs-dc-sel update-pgs-dc-base update-pgs-dc-total update-pgs-dc-start
   update-pgs-dc-end update-pgs-dc-pos update-pgs-dc-counter update-pgs-dc-power
   update-pgs-dc-depth update-pgs-dc-answer))
(defun fn-piw-digest-write-domainp (roster)
 (declare (xargs :guard t))
 (if (atom roster) (equal roster nil)
  (and (true-listp (car roster)) (equal (len (car roster)) 2)
       (member-equal (caar roster) *fn-piw-digest-setters*)
       (if (member-equal (caar roster) *fn-piw-digest-natural-setters*)
           (and (natp (cadar roster)) (<= (cadar roster) 1152921504606846976))
         (cond ((equal (caar roster) 'update-pgs-dc-mode) (equal (cadar roster) :node))
               ((equal (caar roster) 'update-pgs-dc-cv) (equal (cadar roster) *fn-b3-iv*))
               ((equal (caar roster) 'update-pgs-dc-output) (equal (cadar roster) nil))
               ((equal (caar roster) 'update-pgs-dc-capture)
                (and (true-listp (cadar roster)) (equal (len (cadar roster)) 12)))
               (t t)))
       (fn-piw-digest-write-domainp (cdr roster)))))
(defthm fn-piw-digest-write-domainp-of-append
 (implies (and (fn-piw-digest-write-domainp a) (fn-piw-digest-write-domainp b))
          (fn-piw-digest-write-domainp (append a b)))
 :hints (("Goal" :induct (append a b))))
(local (defthm fn-piw-capture-twelve-reference-fields
 (and (true-listp (fn-ews-capture s)) (equal (len (fn-ews-capture s)) 12))
 :hints (("Goal" :in-theory (enable fn-ews-capture)))))
(defthm fn-piw-byte-digest-inputs-establish-source-domains
 (implies (and (natp (ceiling b 64))
               (<= (* 8 (ceiling b 64)) 1152921504606846976)
               (natp (ceiling b 8)) (<= (ceiling b 8) 1152921504606846976)
               (true-listp capture) (equal (len capture) 12))
  (fn-piw-digest-write-domainp (fn-piw-byte-digest-inputs b capture lease)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-piw-byte-digest-inputs fn-piw-digest-begin-inputs
                                fn-piw-digest-write-domainp) (ceiling)))))
(defthm fn-piw-actual-begin-digest-write-domain
 (implies (fn-pwz-native-offsetp (cddr token))
  (fn-piw-digest-write-domainp
    (fn-piw-digest-write-roster
      (cdr (fn-piw-pwz-begin token incarnation hash zin win tab out)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-piw-begin-exact-digest-write-roster
        (:instance fn-pwz-actual-begin-establishes-digest-source-widths
          (pgs-digest-state hash) (fn-zin-st zin) (fn-zin-win win) (fn-zin-tab tab) (fn-zin-out out))
        (:instance fn-piw-byte-digest-inputs-establish-source-domains
          (b (nfix (fn-pwz-nth 4 token))) (lease token)
          (capture (fn-ews-capture (fn-ewp-begin
           (nfix (fn-pwz-nth 2 token)) (nfix (fn-pwz-nth 3 token))
           (nfix (fn-pwz-nth 4 token)) (nfix (fn-pwz-nth 5 token))
           (nfix (fn-pwz-nth 6 token)) (nfix (fn-pwz-nth 6 token))
           (fn-pwz-nth 1 token) incarnation token (nfix (fn-pwz-nth 8 token)))))))
  :in-theory (disable fn-piw-pwz-begin fn-piw-digest-write-roster
     fn-piw-byte-digest-inputs fn-piw-digest-write-domainp fn-pwz-begin
     fn-ews-capture fn-ewp-begin fn-pwz-native-offsetp fn-pwz-nth nfix ceiling
     (:e fn-piw-pwz-begin) (:e fn-pwz-begin)))))
(defun-nx fn-piw-token-digest-inputs (token incarnation)
 (fn-piw-byte-digest-inputs (nfix (fn-pwz-nth 4 token))
  (fn-ews-capture (fn-ewp-begin
   (nfix (fn-pwz-nth 2 token)) (nfix (fn-pwz-nth 3 token))
   (nfix (fn-pwz-nth 4 token)) (nfix (fn-pwz-nth 5 token))
   (nfix (fn-pwz-nth 6 token)) (nfix (fn-pwz-nth 6 token))
   (fn-pwz-nth 1 token) incarnation token (nfix (fn-pwz-nth 8 token)))) token))
(defthm fn-piw-actual-begin-updater-source-boundary
 (implies (fn-pwz-native-offsetp (cddr token))
  (let* ((o (fn-piw-pwz-begin token incarnation hash zin win tab out))
         (trace (cdr o)))
   (and (equal (car o) (fn-pwz-begin token incarnation hash zin win tab out))
        (equal (fn-piw-register-write-roster trace)
          (append (fn-piw-reset-register-roster 0)
            (list '(19 0) '(11 1) (list 18 (min (len (fn-pwz-dictionary token)) 32768)))))
        (fn-piw-register-write-domainp (fn-piw-register-write-roster trace))
        (equal (fn-piw-digest-write-roster trace) (fn-piw-token-digest-inputs token incarnation))
        (fn-piw-digest-write-domainp (fn-piw-digest-write-roster trace)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use (fn-piw-begin-exact-register-write-roster fn-piw-actual-begin-register-write-domain
       fn-piw-begin-exact-digest-write-roster fn-piw-actual-begin-digest-write-domain)
 :in-theory (e/d (fn-piw-token-digest-inputs)
   (fn-piw-pwz-begin fn-pwz-begin fn-piw-register-write-roster fn-piw-digest-write-roster
    fn-piw-register-write-domainp fn-piw-digest-write-domainp fn-piw-byte-digest-inputs
    fn-pwz-native-offsetp fn-pwz-nth fn-pwz-dictionary fn-piw-reset-register-roster nfix
    fn-ews-capture fn-ewp-begin (:e fn-piw-pwz-begin) (:e fn-pwz-begin))))))
