; Exact actual selected resize arguments, for runtime family composition.
(in-package "ACL2")
(include-book "decoded-window-initial-array-payload")
(defun-nx fn-pibr-request-roster (trace)
 (if (atom trace) nil
  (if (and (consp (car trace)) (equal (caar trace) :array-resize))
    (cons (list (nfix (car (caddr (car trace))))
                (fn-octets$c-buf-length (cadr (caddr (car trace)))))
          (fn-pibr-request-roster (cdr trace)))
    (fn-pibr-request-roster (cdr trace)))))
(defthm fn-pibr-request-roster-of-append
 (equal (fn-pibr-request-roster (append a b))
        (append (fn-pibr-request-roster a) (fn-pibr-request-roster b)))
 :hints (("Goal" :induct (append a b))))
(defthm fn-pibr-no-resize-means-no-roster
 (implies (equal (fn-pib-event-count :array-resize trace) 0)
          (equal (fn-pibr-request-roster trace) nil))
 :hints (("Goal" :induct (fn-pib-event-count :array-resize trace)
  :in-theory (enable fn-pibr-request-roster fn-pib-event-count))))
(defthm fn-pibr-reserve-request-roster
 (implies (natp n)
  (equal (fn-pibr-request-roster (cdr (fn-pib-octets$c-reserve n c)))
         (if (<= n (fn-octets$c-buf-length c)) nil
           (list (list n (fn-octets$c-buf-length c))))))
 :hints (("Goal" :in-theory (enable fn-pibr-request-roster fn-pib-octets$c-reserve))))
(local (defthm fn-pibrp-clear-capacity-and-fill
 (and (equal (fn-octets$c-buf-length (fn-octets$c-clear b)) (fn-octets$c-buf-length b))
      (equal (fn-octets$c-fill (fn-octets$c-clear b)) 0))
 :hints (("Goal" :in-theory (enable fn-octets$c-clear)))))
(local (defthm fn-pibrp-reserve-capacity-and-fill
 (implies (natp n)
  (and (equal (fn-octets$c-buf-length (fn-octets$c-reserve n b))
              (max n (fn-octets$c-buf-length b)))
       (equal (fn-octets$c-fill (fn-octets$c-reserve n b)) (fn-octets$c-fill b))))
 :hints (("Goal" :in-theory (enable fn-octets$c-reserve)))))
(local (defthm fn-pibrp-len-nthcdr
 (equal (len (nthcdr n xs)) (nfix (- (len xs) (nfix n))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr)))))

(local (defthm fn-pibrp-append-octet-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-octet o b))
        (+ 1 (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet)))))
(local (defthm fn-pibrp-append-back-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-back off n b))
        (+ n (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-append-back) (fn-oct-back-loop))))))
(local (defthm fn-pibrp-write-list-fill
 (implies (acl2-numberp (fn-octets$c-fill b))
  (equal (fn-octets$c-fill (fn-oct-write-list xs b))
         (+ (len xs) (fn-octets$c-fill b))))
 :hints (("Goal" :induct (fn-oct-write-list xs b)
            :in-theory (e/d (fn-oct-write-list) (fn-octets$c-append-octet))))))

(local (defthm fn-pibrp-ready-prefix-capacity-and-fill
 (let ((b (fn-octets$c-append-back 1 32767
             (fn-octets$c-append-octet 0
               (fn-octets$c-reserve 65536 (fn-octets$c-clear c))))))
  (and (equal (fn-octets$c-fill b) 32768)
       (equal (fn-octets$c-buf-length b) (max 65536 (fn-octets$c-buf-length c)))))
 :hints (("Goal" :in-theory (disable fn-octets$c-clear fn-octets$c-reserve
   fn-octets$c-append-octet fn-octets$c-append-back fn-octets$c-fill fn-octets$c-buf-length)))))


(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pibr-payload-ready-exact-request-roster
  (equal (fn-pibr-request-roster (cdr (fn-pib-piwc-payload-ready dict cwin ctab)))
   (append (if (<= 65536 (fn-octets$c-buf-length cwin)) nil
               (list (list 65536 (fn-octets$c-buf-length cwin))))
           (if (<= 3494 (fn-octets$c-buf-length ctab)) nil
               (list (list 3494 (fn-octets$c-buf-length ctab))))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use (fn-pib-prefilled-dict-source-counts fn-pib-prefilled-dict-capacity-and-fill)
 :in-theory (e/d (fn-pib-piwc-payload-ready fn-pibr-request-roster)
   (fn-pib-prefilled-dict-source-counts fn-pib-prefilled-dict-capacity-and-fill
    fn-pib-octets$c-clear fn-pib-octets$c-reserve fn-pib-octets$c-append-octet
    fn-pib-octets$c-append-back fn-pib-oct-write-list fn-pib-oct-back-loop
    fn-octets$c-clear fn-octets$c-reserve fn-octets$c-append-octet
    fn-octets$c-append-back fn-oct-write-list fn-oct-back-loop fn-pib-event-count
    fn-octets$c-fill fn-octets$c-buf-length nthcdr (:e fn-octets$c-append-back)))))))
(defun fn-pibr-initial-request-roster (wc tc oc)
 (declare (xargs :guard t))
 (append (if (<= 64 (nfix oc)) nil (list (list 64 (nfix oc))))
         (if (<= 65536 (nfix wc)) nil (list (list 65536 (nfix wc))))
         (if (<= 3494 (nfix tc)) nil (list (list 3494 (nfix tc))))))
(defthm fn-pibr-initialize-exact-request-roster
 (equal (fn-pibr-request-roster
          (cdr (fn-pib-piwc-initialize dict zin cwin ctab cout)))
   (fn-pibr-initial-request-roster (fn-octets$c-buf-length cwin)
           (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use fn-pibr-payload-ready-exact-request-roster
 :in-theory (e/d (fn-pib-piwc-initialize fn-pibr-initial-request-roster fn-pibr-request-roster)
    (fn-pib-piwc-payload-ready fn-piwc-payload-ready fn-octets$c-clear
     fn-octets$c-reserve fn-octets$c-buf-length fn-octets$c-fill
     fn-pib-octets$c-clear fn-pib-octets$c-reserve fn-pib-event-count fn-zin-reset fn-zin-set)))))
(defthm fn-pibr-ewz-begin-exact-request-roster
 (equal (fn-pibr-request-roster
         (cdr (fn-pib-piwc-ewz-begin file eoff elen poff compressed decoded offset
                    ticket incarnation lease expected dict hash zin cwin ctab cout)))
   (fn-pibr-initial-request-roster (fn-octets$c-buf-length cwin)
           (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use fn-pibr-initialize-exact-request-roster
 :in-theory (e/d (fn-pib-piwc-ewz-begin fn-pibr-request-roster)
    (fn-pib-piwc-initialize fn-piwc-initialize fn-pibr-initial-request-roster
     fn-ews-begin fn-ewz-state fn-pzd-budget fn-pzw-stored-admissiblep nfix natp nth
     fn-pib-event-count fn-octets$c-buf-length fn-octets$c-fill)))))
(defthm fn-pibr-begin-exact-request-roster
 (equal (fn-pibr-request-roster
         (cdr (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout)))
   (fn-pibr-initial-request-roster (fn-octets$c-buf-length cwin)
           (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pibr-ewz-begin-exact-request-roster (dict (fn-pwz-dictionary token))
    (file (nfix (fn-pwz-nth 2 token))) (eoff (nfix (fn-pwz-nth 3 token)))
    (elen (nfix (fn-pwz-nth 4 token))) (poff (nfix (fn-pwz-nth 5 token)))
    (compressed (nfix (fn-pwz-nth 6 token))) (decoded (nfix (fn-pwz-nth 9 token)))
    (offset (nfix (fn-pwz-nth 7 token))) (ticket (fn-pwz-nth 1 token))
    (lease token) (expected (nfix (fn-pwz-nth 8 token)))))
 :in-theory (e/d (fn-pib-piwc-begin fn-pibr-request-roster)
    (fn-pib-piwc-ewz-begin fn-piwc-ewz-begin fn-pib-piwc-initialize fn-piwc-initialize
     fn-pibr-initial-request-roster fn-pwz-nth fn-pwz-dictionary fn-pib-event-count
     fn-octets$c-buf-length fn-octets$c-fill fn-ews-begin fn-ewz-state fn-pzd-budget
     fn-pzw-stored-admissiblep nfix natp nth (:e fn-pwz-dictionary))))))


; Domain of reviewed literal success resize families; logical roster itself
; does not assert compiled-body qualification or allocator adequacy.
(defun fn-pibr-fixed-resize-rosterp (roster)
 (declare (xargs :guard t))
 (if (atom roster) (equal roster nil)
  (and (true-listp (car roster)) (equal (len (car roster)) 2)
       (member-equal (caar roster) '(64 3494 65536))
       (natp (cadar roster)) (< (cadar roster) (caar roster))
       (fn-pibr-fixed-resize-rosterp (cdr roster)))))
(defthm fn-pibr-initial-roster-is-fixed-success-domain
 (fn-pibr-fixed-resize-rosterp (fn-pibr-initial-request-roster wc tc oc))
 :hints (("Goal" :in-theory (enable fn-pibr-fixed-resize-rosterp fn-pibr-initial-request-roster))))
(defthm fn-pibr-begin-all-resize-arguments-in-fixed-success-domain
 (fn-pibr-fixed-resize-rosterp
   (fn-pibr-request-roster
     (cdr (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use fn-pibr-begin-exact-request-roster
  :in-theory (disable fn-pib-piwc-begin fn-pibr-request-roster
    fn-pibr-initial-request-roster fn-pibr-fixed-resize-rosterp
    fn-octets$c-buf-length (:e fn-pib-piwc-begin)))))

(defthm fn-pibr-actual-begin-resize-roster-boundary
 (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-octets$cp cout))
  (let* ((o (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout))
         (rc (car o)) (ra (fn-pwz-begin token incarnation hash zin awin atab aout)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (equal (mv-nth 1 rc) (mv-nth 1 ra))
        (equal (mv-nth 2 rc) (mv-nth 2 ra))
        (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
        (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
        (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra))
        (equal (fn-pibr-request-roster (cdr o))
          (fn-pibr-initial-request-roster (fn-octets$c-buf-length cwin)
            (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
        (fn-pibr-fixed-resize-rosterp (fn-pibr-request-roster (cdr o))))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use (fn-pibr-begin-exact-request-roster
       fn-pibr-begin-all-resize-arguments-in-fixed-success-domain
       (:instance fn-piwc-begin-refines-actual-begin-from-typed-arrays
         (pgs-digest-state hash) (fn-zin-st zin)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin
  fn-pibr-request-roster fn-pibr-initial-request-roster fn-pibr-fixed-resize-rosterp
  fn-octets$cp fn-octets$corr fn-octets$c-buf-length
  (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))
