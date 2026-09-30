; PRF-1107: canonical word stream bridges for the bounded source scanner.
(in-package "ACL2")
(include-book "history-page-reader")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (in-theory (disable floor mod)))

; Logical vocabulary only: no directory suffix is checked by a runtime guard.
(defun fn-hsr-zero-wordsp (words)
  (declare (xargs :guard t))
  (if (consp words)
      (and (equal (car words) 0) (fn-hsr-zero-wordsp (cdr words)))
    t))

(local
 (defthm fn-hsr-words-okp-padding
   (implies (and (natp i) (natp count) (<= (* 6 count) i))
            (equal (fn-hsr-words-okp i count txid words)
                   (fn-hsr-zero-wordsp words)))
   :hints (("Goal" :induct (fn-hsr-words-okp i count txid words)
            :in-theory (enable fn-hsr-words-okp fn-hsr-word-okp)))))

(local
 (defun fn-hsr-canonical-ind (base count words)
   (declare (xargs :measure (nfix count) :verify-guards nil))
   (if (zp count) (list base words)
     (fn-hsr-canonical-ind (+ 1 base) (1- count) (nthcdr 6 words)))))

(local
 (defthm fn-hsr-nat-listp-nthcdr
   (implies (nat-listp words) (nat-listp (nthcdr n words)))
   :hints (("Goal" :induct (nthcdr n words) :in-theory (enable nthcdr nat-listp)))))
(local
 (defthm fn-hsr-natp-nth
   (implies (and (nat-listp words) (natp n) (< n (len words)))
            (natp (nth n words)))
   :hints (("Goal" :induct (nth n words) :in-theory (enable nth nat-listp)))))
(local
 (defthm fn-hsr-nthcdr-add-canonical
   (implies (and (natp a) (natp b))
            (equal (nthcdr a (nthcdr b words)) (nthcdr (+ a b) words)))
   :hints (("Goal" :induct (nthcdr b words) :in-theory (enable nthcdr)))))
(local
 (defthm fn-hsr-empty-words-okp
   (equal (fn-hsr-words-okp i count txid nil) t)
   :hints (("Goal" :in-theory (enable fn-hsr-words-okp)))))
(local
 (defthm fn-hsr-six-words-step
   (implies (and (natp base) (posp count) (natp txid) (nat-listp words))
            (equal (fn-hsr-words-okp (* 6 base) (+ base count) txid words)
                   (and (<= (nfix (nth 1 words)) txid)
                        (fn-hsr-words-okp (* 6 (+ 1 base)) (+ base count)
                                           txid (nthcdr 6 words)))))
   :hints (("Goal" :do-not-induct t
            :expand ((nthcdr 6 words)
                     (fn-hsr-words-okp (* 6 base) (+ base count) txid words)
                     (fn-hsr-words-okp (+ 1 (* 6 base)) (+ base count) txid (cdr words))
                     (fn-hsr-words-okp (+ 2 (* 6 base)) (+ base count) txid (cddr words))
                     (fn-hsr-words-okp (+ 3 (* 6 base)) (+ base count) txid (cdddr words))
                     (fn-hsr-words-okp (+ 4 (* 6 base)) (+ base count) txid (cddddr words))
                     (fn-hsr-words-okp (+ 5 (* 6 base)) (+ base count) txid (cdr (cddddr words))))
            :in-theory (e/d (fn-hsr-word-okp nth nthcdr len nat-listp)
                            (fn-hsr-words-okp))))))

(local
 (defthm fn-hsr-canonical-words-bridge
   (implies (and (natp base) (natp count) (natp txid)
                 (nat-listp words))
            (equal (fn-hsr-words-okp (* 6 base) (+ base count) txid words)
                   (and (pgs-ptab-txids-ok (pgs-decode-table words count) txid)
                        (fn-hsr-zero-wordsp (nthcdr (* 6 count) words)))))
   :hints (("Goal" :induct (fn-hsr-canonical-ind base count words)
            :expand ((nthcdr 0 words))
            :in-theory (e/d (pgs-decode-table pgs-decode-entry pgs-ptab-txids-ok)
                            (fn-hsr-words-okp fn-hsr-word-okp nthcdr))))))

(defthm fn-hsr-stream-shape-refines-current-txids-and-padding
  (implies (and (natp count) (natp txid) (nat-listp words))
           (equal (fn-hsr-words-okp 0 count txid words)
                  (and (pgs-ptab-txids-ok (pgs-decode-table words count) txid)
                       (fn-hsr-zero-wordsp (nthcdr (* 6 count) words)))))
  :hints (("Goal" :use ((:instance fn-hsr-canonical-words-bridge (base 0)))
           :in-theory (disable fn-hsr-words-okp fn-hsr-zero-wordsp
                               pgs-decode-table pgs-ptab-txids-ok))))

(defun fn-hsr-page-verdict (phase ordinal physical expected observed bad)
  (declare (xargs :guard t))
  (cond ((equal phase :directory)
         (cond ((not (equal observed expected)) (list :dir-damaged physical))
               (bad (list :dir-malformed physical))
               (t nil)))
        ((equal phase :table)
         (cond ((not (equal observed expected)) (list :table-damaged ordinal physical))
               (bad (list :table-malformed ordinal))
               (t nil)))
        ((equal phase :data)
         (if (equal observed expected) nil (list :page-damaged ordinal physical)))
        (t '(:reader-phase))))

(local
 (defthm fn-hsr-decoded-entry-shapep
   (pgs-entry-p (pgs-decode-entry words))
   :hints (("Goal" :in-theory (enable pgs-entry-p pgs-decode-entry pgs-h64)))))
(local
 (defthm fn-hsr-decoded-table-shapep
   (pgs-ptab-p (pgs-decode-table words count))
   :hints (("Goal" :induct (pgs-decode-table words count)
            :in-theory (enable pgs-ptab-p pgs-decode-table)))))
(local
 (defthm fn-hsr-decoded-table-length
   (equal (len (pgs-decode-table words count)) (nfix count))
   :hints (("Goal" :induct (pgs-decode-table words count)
            :in-theory (enable pgs-decode-table)))))

(defthm fn-hsr-directory-verdict-refines-current-format
  (let ((nt (pgs-x-ntables (pgs-rec-npages rec))))
    (implies (nat-listp words)
             (equal (fn-hsr-page-verdict
                     :directory 0 (pgs-rec-dir-addr rec) (pgs-rec-dir-digest rec)
                     observed (not (fn-hsr-words-okp 0 nt (pgs-rec-txid rec) words)))
                    (or (pgs-dir-verdict rec (pgs-decode-table words nt) observed)
                        (if (fn-hsr-zero-wordsp (nthcdr (* 6 nt) words)) nil
                          (list :dir-malformed (pgs-rec-dir-addr rec)))))))
  :hints (("Goal" :in-theory (e/d (fn-hsr-page-verdict pgs-dir-verdict pgs-x-ntables)
                                 (pgs-ntables pgs-decode-table pgs-ptab-txids-ok
                                  fn-hsr-words-okp fn-hsr-zero-wordsp)))))

(defthm fn-hsr-table-verdict-refines-current-format
  (let ((count (min 341 (nfix rem))))
    (implies (and (natp txid) (nat-listp words))
             (equal (fn-hsr-page-verdict
                     :table tp (first entry) (third entry) observed
                     (not (fn-hsr-words-okp 0 count txid words)))
                    (cond ((equal (pgs-entry-verdict entry txid :eager observed) :damaged)
                           (list :table-damaged tp (first entry)))
                          ((not (fn-hsr-zero-wordsp (nthcdr (* 6 count) words)))
                           (list :table-malformed tp))
                          ((not (pgs-table-ok (pgs-decode-table words count) rem txid))
                           (list :table-malformed tp))
                          (t nil)))))
  :hints (("Goal" :in-theory (e/d (fn-hsr-page-verdict pgs-table-ok
                                  pgs-entry-verdict pgs-entry-checked-p)
                                 (pgs-decode-table pgs-ptab-txids-ok
                                  fn-hsr-words-okp fn-hsr-zero-wordsp)))))

(defthm fn-hsr-data-verdict-unfolds
  (equal (fn-hsr-page-verdict :data ordinal (first entry) (third entry) observed bad)
         (if (equal (pgs-entry-verdict entry txid :eager observed) :damaged)
             (list :page-damaged ordinal (first entry)) nil))
  :hints (("Goal" :in-theory (enable fn-hsr-page-verdict pgs-entry-verdict
                                    pgs-entry-checked-p))))

(in-theory (disable fn-hsr-zero-wordsp fn-hsr-page-verdict))
