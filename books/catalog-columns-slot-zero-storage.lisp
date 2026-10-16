; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-empty-metadata")

(defun-nx fn-lb-zero-slot-records (n)
 (declare (xargs :measure (nfix n)))
 (if (zp n) nil (cons '(0) (fn-lb-zero-slot-records (- n 1)))))

(local (defthm fn-lbszs-append-associative
 (equal (append (append a b) c) (append a (append b c)))
 :hints (("Goal" :induct (len a) :in-theory (enable len binary-append)))))

(local (defthm fn-lbszs-append-nil
 (implies (true-listp a) (equal (append a nil) a))
 :hints (("Goal" :induct (len a) :in-theory (enable len binary-append true-listp)))))

(local (defthm fn-lbszs-append-proper
 (implies (and (true-listp a) (true-listp b)) (true-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (enable len binary-append true-listp)))))

(defthm fn-lb-slot-store-model-of-native-append
 (equal (fn-lb-slot-store-model (update-fn-lbc-slot-store
          (fn-lbc-msgid-slots-append rec (fn-lbc-slot-store fn-lbc)) fn-lbc))
        (append (fn-lb-slot-store-model fn-lbc) (list rec)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-slot-store-model update-fn-lbc-slot-store fn-lbc-slot-store
 fn-lbc-msgid-slots-append-is-append fn-dm-nth-update-nth
 (:executable-counterpart nfix) (:executable-counterpart equal))))))

(defthm fn-lb-slot-store-model-of-reserve-slots
 (implies (and (natp n) (true-listp (fn-lb-slot-store-model fn-lbc)))
 (equal (fn-lb-slot-store-model (fn-lbc-reserve-slots n fn-lbc))
        (append (fn-lb-slot-store-model fn-lbc) (fn-lb-zero-slot-records n))))
 :hints (("Goal" :induct (fn-lbc-reserve-slots n fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-reserve-slots fn-lb-slot-store-model-of-native-append fn-lb-zero-slot-records
 fn-lbszs-append-associative fn-lbszs-append-nil fn-lbszs-append-proper binary-append true-listp natp zp)))))

(defthm fn-lb-zero-slot-records-length
 (equal (len (fn-lb-zero-slot-records n)) (nfix n))
 :hints (("Goal" :induct (fn-lb-zero-slot-records n)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-zero-slot-records len nfix zp)))))

(local (defun-nx fn-lbszs-index-induct (n query)
 (declare (xargs :measure (nfix n)))
 (if (and (not (zp n)) (not (zp query)))
 (fn-lbszs-index-induct (- n 1) (- query 1)) (list n query))))

(local (defthm fn-lbszs-zero-record-word
 (implies (and (natp query) (< query (nfix n)))
 (equal (nth 0 (nth query (fn-lb-zero-slot-records n))) 0))
 :hints (("Goal" :induct (fn-lbszs-index-induct n query) :expand ((fn-lb-zero-slot-records n))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbszs-index-induct fn-lb-zero-slot-records nth nfix natp zp))))))

(defthm fn-lb-slot-raw-word-of-zero-records
 (implies (equal (fn-lb-slot-store-model fn-lbc) (fn-lb-zero-slot-records n))
 (equal (fn-lb-slot-raw-word query fn-lbc) 0))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-slot-raw-word fn-lb-slot-store-model fn-lb-zero-slot-records-length fn-lbszs-zero-record-word)))))

(defthm fn-lbc-slot-word-of-zero-records
 (implies (equal (fn-lb-slot-store-model fn-lbc) (fn-lb-zero-slot-records n))
 (equal (fn-lbc-slot-word query fn-lbc) 0))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-word-by-raw-word fn-lb-slot-raw-word-of-zero-records)))))

(local (defthm fn-lbszs-zero-cells-with-accumulator
 (implies (and (natp base) (equal (fn-lb-slot-store-model fn-lbc) (fn-lb-zero-slot-records capacity)))
 (equal (fn-lbc-slot-cells-corr (make-list-ac n 0 tail) base fn-lbc)
        (fn-lbc-slot-cells-corr tail (+ base (nfix n)) fn-lbc)))
 :hints (("Goal" :induct (make-list-ac n 0 tail)
 :in-theory (union-theories (theory 'ground-zero)
 '(make-list-ac fn-lbc-slot-cells-corr fn-lbc-slot-word-of-zero-records natp nfix zp))))))

(defthm fn-lbc-slot-cells-corr-of-zero-records
 (implies (equal (fn-lb-slot-store-model fn-lbc) (fn-lb-zero-slot-records capacity))
 (fn-lbc-slot-cells-corr (make-list n :initial-element 0) 0 fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbszs-zero-cells-with-accumulator (base 0) (tail nil)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-slot-cells-corr)))))

(local (defthm fn-lbszs-make-list-ac-length
 (equal (len (make-list-ac n value tail)) (+ (nfix n) (len tail)))
 :hints (("Goal" :induct (make-list-ac n value tail)
 :in-theory (union-theories (theory 'ground-zero) '(make-list-ac len nfix zp))))))

(local (defthm fn-lbszs-make-list-ac-proper
 (implies (true-listp tail) (true-listp (make-list-ac n value tail)))
 :hints (("Goal" :induct (make-list-ac n value tail)
 :in-theory (union-theories (theory 'ground-zero) '(make-list-ac true-listp))))))

(defthm fn-lb-slot-zero-table-shape
 (implies (posp n)
 (and (consp (make-list n :initial-element 0))
      (true-listp (make-list n :initial-element 0))
      (equal (len (make-list n :initial-element 0)) n)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbszs-make-list-ac-length (value 0) (tail nil)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbszs-make-list-ac-proper len posp nfix)))))
