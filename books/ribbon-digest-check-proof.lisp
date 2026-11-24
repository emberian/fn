(in-package "ACL2")
(include-book "ribbon")

; The computed digest and the parent digest are each read as 32 octets.
(defun-nx fn2-ribbon-digest-suffix (pos row ds)
  (declare (xargs :measure (nfix (- 32 (nfix pos)))))
  (if (or (not (natp pos)) (<= 32 pos)) nil
    (cons (fn2-fc-word-byte (fn2-digest-word row (floor pos 4) ds) (mod pos 4))
          (fn2-ribbon-digest-suffix (1+ pos) row ds))))

(defmacro fn2-ribbon-check-page-call (op)
   `(,op fuel 0 :page nil slot gen 0 *fn2-run-page-size* 0 9 0 1
         fc ctx b3 fields pool ds))

(local
 (defthm fn2-ribbon-checks-one-digest-octet
   (let ((pos (fn2-fc-pos 0 fc)))
     (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-digest*)
                   (natp pos) (< pos 32))
              (equal (fn2-ribbon-check-page-call fn2-fc-advance)
                     (if (equal (fn2-fc-word-byte (fn2-digest-word 125 (floor pos 4) ds) (mod pos 4))
                                (fn2-fc-word-byte (fn2-digest-word (fn2-fc-context-hash 0 ctx) (floor pos 4) ds) (mod pos 4)))
                         (list (if (equal pos 31) :ok :more) 1 (fn2-fc-set-pos 0 (1+ pos) fc) b3 pool ds)
                       (list :bad-hash 1 fc b3 pool ds)))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-byte fn2-fc-advance fn2-fc-context-hash-word fn2-fc-digest-byte)
                                   (fn2-fc-phase fn2-fc-pos fn2-fc-set-pos fn2-fc-context-hash
                                    fn2-fc-word-byte fn2-digest-word floor mod))))))

(local
 (defthm fn2-ribbon-digest-next-position
   (and (equal (fn2-fc-pos 0 (fn2-fc-set-pos 0 i fc)) i)
        (equal (fn2-fc-phase 0 (fn2-fc-set-pos 0 i fc)) (fn2-fc-phase 0 fc)))
   :hints (("Goal" :in-theory (e/d (fn2-fc-pos fn2-fc-phase fn2-fc-set-pos update-fn2-fc-pos$ai)
                                   (nth update-nth))))))

(local
 (defun-nx fn2-ribbon-digest-walk (fuel fc)
   (if (zp fuel) fc
     (fn2-ribbon-digest-walk (1- fuel) (fn2-fc-set-pos 0 (1+ (fn2-fc-pos 0 fc)) fc)))))

(defthm fn2-ribbon-page-check-decides-digest
  (let ((pos (fn2-fc-pos 0 fc)))
    (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-digest*)
                  (natp pos) (< pos 32) (natp fuel) (<= (- 32 pos) fuel))
             (equal (car (fn2-ribbon-check-page-call fn2-fc-run-bytes))
                    (if (equal (fn2-ribbon-digest-suffix pos 125 ds)
                               (fn2-ribbon-digest-suffix pos (fn2-fc-context-hash 0 ctx) ds))
                        :ok :bad-hash))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ribbon-digest-walk fuel fc)
           :expand ((fn2-ribbon-check-page-call fn2-fc-run-bytes)
                    (:free (row) (fn2-ribbon-digest-suffix (fn2-fc-pos 0 fc) row ds))
                    (:free (row) (fn2-ribbon-digest-suffix 32 row ds)))
           :in-theory (disable fn2-fc-phase fn2-fc-pos fn2-fc-set-pos fn2-digest-word
                               fn2-fc-word-byte fn2-fc-context-hash fn2-fc-advance
                               fn2-fc-run-bytes fn2-ribbon-digest-suffix floor mod))))
