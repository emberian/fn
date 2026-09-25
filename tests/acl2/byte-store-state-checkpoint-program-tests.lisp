; Teeth for books/byte-store-state-checkpoint-program and
; books/byte-store-range-read.
(in-package "ACL2")
(include-book "../../books/byte-store-state-checkpoint-program")
(include-book "../../books/byte-store-range-read")

; fn-bs-scp-program-crash-is-old-or-new, a reachable run: a quiet store with
; an old checkpoint at inode 3, next inode 5.
(defconst *scp-t-bs*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3)))
                    (cons :staging nil))
              nil 5))
(defconst *scp-t-run*
  (fn-bs-run *scp-t-bs* nil (fn-bs-scp-program ".stage-state-checkpoint-1" '(1 2 3))
             nil nil 0))
(assert-event (fn-bs-scp-inputp *scp-t-bs* ".stage-state-checkpoint-1" 3))
(assert-event (equal (len *scp-t-run*) 10))
(defconst *scp-t-renamed* (car (nth 7 *scp-t-run*)))
(assert-event (equal (fn-bs-durable-entry (fn-bs-crash *scp-t-renamed* '(:drop :drop :drop))
                                          :root "store-checkpoint.fnsc")
                     3))
(assert-event (equal (fn-bs-durable-entry (fn-bs-crash *scp-t-renamed* '(:drop :apply :drop))
                                          :root "store-checkpoint.fnsc")
                     5))
(assert-event (fn-bs-scp-old-or-newp
               (fn-bs-crash *scp-t-renamed* '(:drop :drop :drop)) *scp-t-bs* 3 '(1 2 3)))
(assert-event (fn-bs-scp-old-or-newp
               (fn-bs-crash *scp-t-renamed* '(:drop :apply :drop)) *scp-t-bs* 3 '(1 2 3)))
; The first publish: no old checkpoint, the name is absent or new.
(defconst *scp-t-fresh*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root nil) (cons :staging nil))
              nil 5))
(assert-event (fn-bs-scp-inputp *scp-t-fresh* ".stage-state-checkpoint-1" nil))
(defconst *scp-t-fresh-run*
  (fn-bs-run *scp-t-fresh* nil (fn-bs-scp-program ".stage-state-checkpoint-1" '(1 2 3))
             nil nil 0))
(assert-event (fn-bs-scp-old-or-newp
               (fn-bs-crash (car (nth 7 *scp-t-fresh-run*)) '(:drop :drop :drop))
               *scp-t-fresh* nil '(1 2 3)))
; Without a quiet store (a pending write to the old inode), a crash image
; holds a third content.
(defconst *scp-t-busy*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3)))
                    (cons :staging nil))
              (list (list :write 3 0 '(9 9)))
              5))
(defconst *scp-t-busy-run*
  (fn-bs-run *scp-t-busy* nil (fn-bs-scp-program ".stage-state-checkpoint-1" '(1 2 3))
             nil nil 0))
(must-fail
 (defthm scp-t-crash-without-quiet-store
   (fn-bs-scp-old-or-newp (fn-bs-crash (car (nth 0 *scp-t-busy-run*)) '((:new) :drop))
                          *scp-t-busy* 3 '(1 2 3))))

; fn-bs-read-ranges-concatenate: two ranges of inode 3 read in one state are
; the one range.  Without A-HOST-EXCLUSIVE-READ (a later state whose inode 3
; holds other octets) the second range comes from other content.
(defconst *scp-t-file*
  (fn-bs-make 4 (list (cons 3 '(1 2 3 4 5 6)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3))))
              nil 5))
(defconst *scp-t-changed*
  (fn-bs-make 4 (list (cons 3 '(1 2 3 9 9 9)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3))))
              nil 5))
(assert-event (equal (append (fn-bs-read-range *scp-t-file* 3 0 2)
                             (fn-bs-read-range *scp-t-file* 3 2 4))
                     (fn-bs-read-range *scp-t-file* 3 0 6)))
(assert-event (equal (append (fn-bs-read-range *scp-t-file* 3 0 2)
                             (fn-bs-read-range *scp-t-file* 3 2 4))
                     (fn-bs-read *scp-t-file* 3)))
(assert-event (not (equal (append (fn-bs-read-range *scp-t-file* 3 0 2)
                                  (fn-bs-read-range *scp-t-changed* 3 2 4))
                          (fn-bs-read-range *scp-t-file* 3 0 6))))
(must-fail
 (defthm scp-t-ranges-without-exclusive-read
   (implies (and (natp off) (natp n) (natp m)
                 (<= (+ off n) (len (fn-bs-content s0 ino))))
            (equal (append (fn-bs-read-range s0 ino off n)
                           (fn-bs-read-range s1 ino (+ off n) m))
                   (fn-bs-read-range s0 ino off (+ n m))))
   :hints (("Goal" :do-not-induct t))))
