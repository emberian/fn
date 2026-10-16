; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-cell-decoder")

(defthm fn-lbc-row-flags-nov-ok-bit
 (equal (logbitp 0 (nfix (fn-lbc-row-flags nov withdrawn escaped verified reclaimed)))
        (if (and (fn-hnov-p nov) (fn-hnov-ok nov)) t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-flags (:executable-counterpart logbitp)
     (:executable-counterpart nfix) (:executable-counterpart binary-+))))))

(defthm fn-lbc-row-flags-nov-tomb-bit
 (equal (logbitp 1 (nfix (fn-lbc-row-flags nov withdrawn escaped verified reclaimed)))
        (if (and (fn-hnov-p nov) (fn-hnov-tomb nov)) t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-flags (:executable-counterpart logbitp)
     (:executable-counterpart nfix) (:executable-counterpart binary-+))))))

(defthm fn-lbc-row-flags-withdrawn-bit
 (equal (logbitp 2 (nfix (fn-lbc-row-flags nov withdrawn escaped verified reclaimed)))
        (if withdrawn t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-flags (:executable-counterpart logbitp)
     (:executable-counterpart nfix) (:executable-counterpart binary-+))))))

(defthm fn-lbc-row-flags-escaped-bit
 (equal (logbitp 3 (nfix (fn-lbc-row-flags nov withdrawn escaped verified reclaimed)))
        (if escaped t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-flags (:executable-counterpart logbitp)
     (:executable-counterpart nfix) (:executable-counterpart binary-+))))))

(defthm fn-lbc-row-flags-ingest-verified-bit
 (equal (logbitp 4 (nfix (fn-lbc-row-flags nov withdrawn escaped verified reclaimed)))
        (if verified t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-flags (:executable-counterpart logbitp)
     (:executable-counterpart nfix) (:executable-counterpart binary-+))))))

(defthm fn-lbc-row-flags-reclaimed-bit
 (equal (logbitp 5 (nfix (fn-lbc-row-flags nov withdrawn escaped verified reclaimed)))
        (if reclaimed t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-flags (:executable-counterpart logbitp)
     (:executable-counterpart nfix) (:executable-counterpart binary-+))))))
