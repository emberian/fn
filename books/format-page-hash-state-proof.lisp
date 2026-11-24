; The remaining hash input in each state of the physical page checker.
(in-package "ACL2")
(include-book "format-page-hash-progress-proof")

(local (in-theory (current-theory 'fc-u32-reconstruct)))

(defun-nx fn2-page-hash-statep (bytes ans fc ds b3)
  (let ((phase (fn2-fc-phase 0 fc)) (pos (fn2-fc-pos 0 fc)))
    (cond ((equal phase *fn2-fc-phase-decode*) (fc-g (fn2-fc-covered :page bytes nil) ans ds b3))
          ((equal phase *fn2-fc-phase-prefix*)
           (and (natp pos) (<= pos 20)
                (fc-g (append (fn2-fc-string-bytes (fn2-fc-domain :page) pos) bytes) ans ds b3)))
          ((equal phase *fn2-fc-phase-hash*)
           (and (natp pos) (<= pos 65536)
                (fc-g (fn-b3-nthcdrx pos bytes) ans ds b3)))
          ((equal phase *fn2-fc-phase-digest*) (equal (fn2-digest-list 125 ds) ans))
          (t t))))

(defthmd fn2-page-prefix-advances
  (implies (and (natp pos) (< pos 20))
           (equal (fn2-fc-string-bytes (fn2-fc-domain :page) pos)
                  (cons (fn2-fc-prefix-byte 0 :page pos ctx)
                        (fn2-fc-string-bytes (fn2-fc-domain :page) (1+ pos)))))
  :hints (("Goal" :expand ((fn2-fc-string-bytes (fn2-fc-domain :page) pos))
           :in-theory (e/d (fn2-fc-prefix-byte fn2-fc-domain) (char-code char)))))

(defthmd fn2-page-covered-bytes
  (equal (fn2-fc-covered :page bytes nil)
         (append (fn2-fc-string-bytes (fn2-fc-domain :page) 0) bytes))
  :hints (("Goal" :in-theory (enable fn2-fc-covered))))

(defmacro fn2-page-check-call (op &rest prefix)
  `(,op ,@prefix 0 :page nil 0 1 0 65536 0 9 0 1 fc ctx b3 f pool ds))

(defmacro fn2-page-hash-effect (call fi bi di)
  `(let ((r ,call))
     (implies (and (fn2-page-hash-statep bytes ans fc ds b3)
                   (fn2-hash-page-windowp pool)
                   (fn-b3-octet-listp bytes) (equal (len bytes) 65536)
                   (fn2-b3-covers bytes 0 pool))
              (and (implies (member-eq (car r) '(:more :yield))
                            (fn2-page-hash-statep bytes ans (mv-nth ,fi r) (mv-nth ,di r) (mv-nth ,bi r)))
                   (implies (equal (car r) :ok) (equal (fn2-digest-list 125 (mv-nth ,di r)) ans))))))

(defthm fn2-page-hash-prefix-step
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-prefix*)
           (fn2-page-hash-effect (fn2-page-check-call fn2-fc-byte) 1 2 4))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fc-g-byte (b (fn2-fc-prefix-byte 0 :page (fn2-fc-pos 0 fc) ctx))
                            (xs (append (fn2-fc-string-bytes (fn2-fc-domain :page) (1+ (fn2-fc-pos 0 fc))) bytes)))
                 (:instance fn2-page-prefix-advances (pos (fn2-fc-pos 0 fc))))
           :in-theory (e/d (fn2-fc-byte fn2-page-hash-statep fc-phase-pos-updates fn2-b3-drop-zero)
                           (fn2-fc-string-bytes fn2-fc-prefix-byte fn2-fc-pos fn2-fc-phase fn2-fc-set-pos
                            fn2-fc-set-phase fn2-b3-byte fn2-hash-page-windowp mv-nth)))))

(local
 (defthm fn2-page-suffix-at-octet
   (implies (and (natp pos) (< pos (len bytes)))
            (equal (fn-b3-nthcdrx pos bytes)
                   (cons (fn-b3-nthx pos bytes) (fn-b3-nthcdrx (1+ pos) bytes))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-b3-nthcdrx pos bytes)
            :expand ((fn-b3-nthcdrx (1+ pos) bytes))
            :in-theory (enable fn-b3-nthcdrx fn-b3-nthx)))))

(defthm fn2-page-hash-next-octet
  (implies (and (natp pos) (< pos (len bytes)) (fn2-b3-covers bytes 0 pool)
                (fn2-hash-page-windowp pool) (equal (len bytes) 65536))
           (let ((read (fn2-b3-read 0 1 pos 9 0 1 pool)))
             (and (equal (car read) :ok)
                  (equal (fn-b3-nthcdrx pos bytes)
                         (cons (mv-nth 1 read) (fn-b3-nthcdrx (1+ pos) bytes))))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-page-suffix-at-octet (:instance fn2-hash-page-window-read (off pos))
                        (:instance fn2-b3-covered-byte (i pos) (off 0) (xs bytes) (fn2-pool pool)))
           :in-theory (union-theories (theory 'minimal-theory) '(natp commutativity-of-+ fc-zero-plus-len car-cons cdr-cons fc-mv-cons (:e mv-nth) (:e <) (:e equal))))))

(defthmd fn2-page-feed-checked-byte
  (let* ((read (fn2-b3-read 0 1 pos 9 0 1 pool))
         (step (fn2-b3-byte 0 (mv-nth 1 read) ds b3)))
    (implies (and (natp pos) (< pos 65536) (equal (len bytes) 65536)
                  (fn2-hash-page-windowp pool) (fn2-b3-covers bytes 0 pool)
                  (fc-g (fn-b3-nthcdrx pos bytes) ans ds b3))
             (fc-g (fn-b3-nthcdrx (1+ pos) bytes) ans (mv-nth 0 step) (mv-nth 1 step))))
  :hints (("Goal" :use (fn2-page-hash-next-octet
                        (:instance fc-g-byte (b (mv-nth 1 (fn2-b3-read 0 1 pos 9 0 1 pool)))
                                   (xs (fn-b3-nthcdrx (1+ pos) bytes))))
           :in-theory (theory 'minimal-theory))))

(defthmd fn2-page-hash-finished-at-end
  (implies (and (fn-b3-octet-listp bytes) (equal (len bytes) 65536)
                (fc-g (fn-b3-nthcdrx 65536 bytes) ans ds b3))
           (equal (fn2-digest-list 125 (fn2-b3-finalize 125 0 ds b3)) ans))
  :hints (("Goal" :use ((:instance fc-g-finish (dst 125))
                        (:instance fn2-b3-drop-end (n 65536) (xs bytes)))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-b3-finalize fn2-b3-octets-true-list (:e nfix) (:e natp) (:e <))))))

(defthm fn2-page-hash-byte-step
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*)
           (fn2-page-hash-effect (fn2-page-check-call fn2-fc-byte) 1 2 4))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :cases ((equal (fn2-fc-pos 0 fc) 65536))
           :use ((:instance fn2-page-feed-checked-byte (pos (fn2-fc-pos 0 fc)))
                 fn2-page-hash-finished-at-end)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-fc-byte fn2-page-hash-statep fc-phase-pos-updates
                          fc-zero-plus-len commutativity-of-+ fc-mv-cons fc-mv-zero
                          natp member-equal car-cons cdr-cons eql eq not
                          (:t fn2-b3-byte) (:e fn2-fc-domain) (:e length) (:e fn2-digest-slot)
                          (:e member-equal) (:e mv-nth) (:e binary-+) (:e <)
                          (:e equal) (:e not) (:e natp) (:e integerp))))))

(defthm fn2-page-hash-one-byte
  (fn2-page-hash-effect (fn2-page-check-call fn2-fc-byte) 1 2 4)
  :rule-classes nil
  :hints (("Goal" :use (fn2-page-hash-prefix-step fn2-page-hash-byte-step)
           :in-theory (e/d (fn2-fc-byte fn2-page-hash-statep fc-phase-pos-updates)
                           (fn2-fc-prefix-byte fn2-fc-phase fn2-fc-pos fn2-fc-set-pos fn2-fc-set-phase
                            fn2-b3-finalize fn2-fc-context-hash-word fn2-fc-digest-byte fn2-fc-word-byte
                            fn2-fc-string-bytes fn2-hash-page-windowp mv-nth)))))
