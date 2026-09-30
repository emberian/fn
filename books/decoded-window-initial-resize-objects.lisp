; Conditional success primary-object composition, not INITIAL admission.
(in-package "ACL2")
(include-book "decoded-window-initial-resize-roster")
(include-book "assumptions-selected-runtime-octets-resize")
(defun-nx fn-pibr-roster-object-octets (roster coordinate)
 (if (atom roster) 0
  (+ (fn-assume-sror-success-object-octets (caar roster) (cadar roster) coordinate)
     (fn-pibr-roster-object-octets (cdr roster) coordinate))))
(defun-nx fn-pibr-roster-primary-requests (roster)
 (if (atom roster) 0
  (+ (fn-sror-primary-request (caar roster))
     (fn-pibr-roster-primary-requests (cdr roster)))))
(defthm fn-pibr-roster-object-family-bound
 (implies (and (fn-pibr-fixed-resize-rosterp roster)
               (equal coordinate *fn-sror-coordinate*))
  (<= (fn-pibr-roster-object-octets roster coordinate)
      (fn-pibr-roster-primary-requests roster)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pibr-roster-object-octets roster coordinate)
  :in-theory (enable fn-pibr-roster-object-octets fn-pibr-roster-primary-requests
                     fn-pibr-fixed-resize-rosterp fn-sror-resize-domain-p))
 ("Subgoal *1/2" :use ((:instance fn-assume-sror-success-primary-object-bound
          (request (caar roster)) (old (cadar roster)))))))
(defun fn-pibr-initial-primary-object-octets (wc tc oc)
 (declare (xargs :guard t))
 (+ (if (<= 64 (nfix oc)) 0 80)
    (if (<= 65536 (nfix wc)) 0 65552)
    (if (<= 3494 (nfix tc)) 0 3520)))
(defthm fn-pibr-initial-primary-object-bound
 (and (natp (fn-pibr-initial-primary-object-octets wc tc oc))
      (<= (fn-pibr-initial-primary-object-octets wc tc oc) 69152))
 :hints (("Goal" :in-theory (enable fn-pibr-initial-primary-object-octets))))
(defthm fn-pibr-initial-roster-primary-requests
 (equal (fn-pibr-roster-primary-requests (fn-pibr-initial-request-roster wc tc oc))
        (fn-pibr-initial-primary-object-octets wc tc oc))
 :hints (("Goal" :in-theory (enable fn-pibr-roster-primary-requests
      fn-pibr-initial-request-roster fn-pibr-initial-primary-object-octets fn-sror-primary-request))))
; The named coordinate requires genuine backing and installed HONS NIL;
; comparing a literal coordinate does not install those runtime facts.
(defun fn-pibr-initial-primary-object-component (wc tc oc coordinate)
 (declare (xargs :guard t))
 (if (equal coordinate *fn-sror-coordinate*)
   (mv :primary-object (fn-pibr-initial-primary-object-octets wc tc oc)
       (len (fn-pibr-initial-request-roster wc tc oc)))
   (mv :unavailable nil nil)))
(defthm fn-pibr-actual-begin-primary-objects-conditional-bound
 (implies (equal coordinate *fn-sror-coordinate*)
  (<= (fn-pibr-roster-object-octets
        (fn-pibr-request-roster
          (cdr (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout))) coordinate)
      (fn-pibr-initial-primary-object-octets (fn-octets$c-buf-length cwin)
          (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-pibr-begin-exact-request-roster
        (:instance fn-pibr-roster-object-family-bound
          (roster (fn-pibr-initial-request-roster (fn-octets$c-buf-length cwin)
                    (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))))
  :in-theory (disable fn-pib-piwc-begin fn-pibr-request-roster fn-pibr-roster-object-octets
       fn-pibr-initial-request-roster fn-pibr-fixed-resize-rosterp
       fn-pibr-roster-primary-requests fn-pibr-initial-primary-object-octets
       fn-octets$c-buf-length (:e fn-pib-piwc-begin)))))

(defthm fn-pibr-actual-begin-primary-object-boundary
 (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-octets$cp cout))
  (let* ((o (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout))
         (rc (car o)) (ra (fn-pwz-begin token incarnation hash zin awin atab aout))
         (roster (fn-pibr-request-roster (cdr o))))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (equal (mv-nth 1 rc) (mv-nth 1 ra))
        (equal (mv-nth 2 rc) (mv-nth 2 ra))
        (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
        (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
        (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra))
        (equal roster (fn-pibr-initial-request-roster (fn-octets$c-buf-length cwin)
               (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
        (fn-pibr-fixed-resize-rosterp roster)
        (implies (equal coordinate *fn-sror-coordinate*)
          (<= (fn-pibr-roster-object-octets roster coordinate)
              (fn-pibr-initial-primary-object-octets (fn-octets$c-buf-length cwin)
               (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-pibr-actual-begin-resize-roster-boundary
        fn-pibr-actual-begin-primary-objects-conditional-bound)
  :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin
   fn-pibr-request-roster fn-pibr-initial-request-roster fn-pibr-fixed-resize-rosterp
   fn-pibr-roster-object-octets fn-pibr-initial-primary-object-octets
   fn-octets$cp fn-octets$corr fn-octets$c-buf-length
   (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))
