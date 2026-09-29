; Tests for books/extent-retire.lisp (lane online-reclaim-2, PRF-930).
;
; 1. The functions the host calls are guard-verified.
; 2. A checkpoint frame on the live stobjs: the step's handles, the reseat of
;    a frame whose chunk holds handle 0's payload (done), a torn chunk (not
;    done) and the quiet files.
; 3. Teeth for the keystones: a positive witness per keystone asserting its
;    whole antecedent and conclusion, and a failing proof per hypothesis.

(in-package "ACL2")
(include-book "../../books/extent-retire")
(include-book "must-fail-checked")

(assert-event
 (and (eq (symbol-class 'fn-xrt-step-handles (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-xrt-reseat-one (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-xrt-reseat-frame (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-xrt-reseat-checkpoint-frame (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-xrt-quiet-files (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The step's handles: step 0 (the head) none; step 1 the first K sources, a
; source that is an octet list as NIL.
(assert-event
 (and (equal (fn-xrt-step-handles (list 0 '(4 (9 9) 6) '(2 1) nil 0)) nil)
      (equal (fn-xrt-step-handles (list 1 '(4 (9 9) 6) '(2 1) nil 0)) '(4 nil))
      (equal (fn-xrt-step-handles (list 2 '(6) '(1) nil 0)) '(6))))

; A frame at file offset 100 (the buffer's cell 0 is the frame start less
; 32): 32 octets of the previous trailer, the 37-octet header, then the
; chunk: handle 0's payload (1 2 3) as its length (one digit, 3) and its
; octets.  The prefix is 74 octets.
(defconst *xrt-buf* (append (make-list 69 :initial-element 0) '(1 3 1 2 3)))

(defconst *xrt-pos* '(100 106 171 3))

; The member the frame gives handle 0 is the commit's extent at the payload.
(assert-event
 (let ((fn-arena (fn-arena-clear fn-arena)))
   (let ((fn-arena (fn-arena-seal-list '(1 2 3) fn-arena)))
     (mv (and (equal (fn-arx-commit-extent 0 5 *xrt-pos* '(1 2 3) fn-arena)
                     '(5 100 74 171 3 0))
              ; another payload is not reseated there
              (null (fn-arx-commit-extent 0 5 *xrt-pos* '(1 2 4) fn-arena)))
         fn-arena)))
 :stobjs-out '(nil fn-arena))

; The frame's reseat on the live buffer: a chunk torn before the payload's
; end is not done (and reseats nothing, so the payload still reads from the
; arena's own copy); the whole chunk is parsed (done) -- here with a source
; that is not a handle, since a successful reseat's extent needs the host's
; realizer, which this session does not have (the keystone's witness below
; covers the reseat).
(assert-event
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list '(1 2 3) fn-arena))
        (fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list *xrt-buf* fn-octets)))
   (mv-let (torn fn-arena)
     (fn-xrt-reseat-checkpoint-frame '(0) 5 100 73 fn-octets fn-arena)
     (mv (and (null torn) (equal (fn-arena-payload 0 fn-arena) '(1 2 3)))
         fn-arena fn-octets)))
 :stobjs-out '(nil fn-arena fn-octets))

(assert-event
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list '(1 2 3) fn-arena))
        (fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list *xrt-buf* fn-octets)))
   (mv-let (done fn-arena)
     (fn-xrt-reseat-checkpoint-frame '(nil) 5 100 74 fn-octets fn-arena)
     (mv (and (eq done t) (equal (fn-arena-payload 0 fn-arena) '(1 2 3)))
         fn-arena fn-octets)))
 :stobjs-out '(nil fn-arena fn-octets))

; -----------------------------------------------------------------------------
; Teeth: fn-xrt-reseat-frame-keeps-the-arena.

(defthm xrt-keeps-witness
  (implies (equal (fn-durable-octets 5 100 74) (fn-oct-slice-list 0 74 *xrt-buf*))
           (and (fn-arena-p '((1 2 3)))
                (natp 5) (natp 100) (natp 69) (natp 74)
                (equal (mv-nth 1 (fn-xrt-reseat-frame '(0) 5 100 69 74 *xrt-buf* '((1 2 3))))
                       '((1 2 3)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-xrt-reseat-frame-keeps-the-arena
                                   (handles '(0)) (file 5) (start 100) (i 69) (end 74)
                                   (fn-octets *xrt-buf*) (fn-arena '((1 2 3)))))
           :in-theory (disable (:e fn-xrt-reseat-frame) fn-xrt-reseat-frame-keeps-the-arena
                               (:e fn-oct-slice-list)))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-keeps-without-durable
    (implies (and (fn-arena-p fn-arena) (natp file) (natp start) (natp i) (natp end))
             (equal (mv-nth 1 (fn-xrt-reseat-frame handles file start i end fn-octets fn-arena))
                    fn-arena))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-keeps-without-arena-p
    (implies (and (natp file) (natp start) (natp i) (natp end)
                  (equal (fn-durable-octets file start end)
                         (fn-oct-slice-list 0 end fn-octets)))
             (equal (mv-nth 1 (fn-xrt-reseat-frame handles file start i end fn-octets fn-arena))
                    fn-arena))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-keeps-without-natp-file
    (implies (and (fn-arena-p fn-arena) (natp start) (natp i) (natp end)
                  (equal (fn-durable-octets file start end)
                         (fn-oct-slice-list 0 end fn-octets)))
             (equal (mv-nth 1 (fn-xrt-reseat-frame handles file start i end fn-octets fn-arena))
                    fn-arena))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-keeps-without-natp-start
    (implies (and (fn-arena-p fn-arena) (natp file) (natp i) (natp end)
                  (equal (fn-durable-octets file start end)
                         (fn-oct-slice-list 0 end fn-octets)))
             (equal (mv-nth 1 (fn-xrt-reseat-frame handles file start i end fn-octets fn-arena))
                    fn-arena))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-keeps-without-natp-i
    (implies (and (fn-arena-p fn-arena) (natp file) (natp start) (natp end)
                  (equal (fn-durable-octets file start end)
                         (fn-oct-slice-list 0 end fn-octets)))
             (equal (mv-nth 1 (fn-xrt-reseat-frame handles file start i end fn-octets fn-arena))
                    fn-arena))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-keeps-without-natp-end
    (implies (and (fn-arena-p fn-arena) (natp file) (natp start) (natp i)
                  (equal (fn-durable-octets file start end)
                         (fn-oct-slice-list 0 end fn-octets)))
             (equal (mv-nth 1 (fn-xrt-reseat-frame handles file start i end fn-octets fn-arena))
                    fn-arena))))))

; -----------------------------------------------------------------------------
; Teeth: KEYSTONE fn-xrt-quiet-files-are-unnamed.  A run reached through the
; exports alone (so it corresponds): an extent on file 7 at handle 0, a
; resident handle 1, then handle 0 reseated onto file 9.  File 7's count is
; 0, file 9's 1.

(defun-nx xrt-x3 ()
  (fn-arena$x-reseat-extent 0 9 0 50 10 20 5
    (fn-arena$x-seal-list '(1 2)
      (fn-arena$x-seal-extent 7 100 100 120 20 99
        (fn-arena$x-clear (create-fn-arena$x))))))

(defun xrt-a3 ()
  (fn-arena$a-reseat-extent 0 9 0 50 10 20 5
    (fn-arena$a-seal-list '(1 2)
      (fn-arena$a-seal-extent 7 100 100 120 20 99
        (fn-arena$a-clear (create-fn-arena$a))))))

(defthm xrt-x3-corresponds
  (fn-arena$xcorr (xrt-x3) (xrt-a3))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-arena$xcorr fn-arena$x-clear fn-arena$x-seal-extent
                               fn-arena$x-seal-list fn-arena$x-reseat-extent create-fn-arena$x
                               (:e fn-arena$x-clear) (:e fn-arena$x-seal-extent)
                               (:e fn-arena$x-seal-list) (:e fn-arena$x-reseat-extent)
                               (:e create-fn-arena$x))
           :use ((:instance create-fn-arena-extent{correspondence})
                 (:instance fn-arena-extent-clear{correspondence}
                            (fn-arena$x (create-fn-arena$x)) (fn-arena-extent (create-fn-arena$a)))
                 (:instance fn-arena-extent-seal-extent{correspondence}
                            (file 7) (eoff 100) (elen 100) (poff 120) (plen 20) (trailer 99)
                            (fn-arena$x (fn-arena$x-clear (create-fn-arena$x)))
                            (fn-arena-extent (fn-arena$a-clear (create-fn-arena$a))))
                 (:instance fn-arena-extent-seal-list{correspondence} (xs '(1 2))
                            (fn-arena$x (fn-arena$x-seal-extent 7 100 100 120 20 99
                                          (fn-arena$x-clear (create-fn-arena$x))))
                            (fn-arena-extent (fn-arena$a-seal-extent 7 100 100 120 20 99
                                               (fn-arena$a-clear (create-fn-arena$a)))))
                 (:instance fn-arena-extent-reseat-extent{correspondence}
                            (h 0) (file 9) (eoff 0) (elen 50) (poff 10) (plen 20) (trailer 5)
                            (fn-arena$x (fn-arena$x-seal-list '(1 2)
                                          (fn-arena$x-seal-extent 7 100 100 120 20 99
                                            (fn-arena$x-clear (create-fn-arena$x)))))
                            (fn-arena-extent (fn-arena$a-seal-list '(1 2)
                                               (fn-arena$a-seal-extent 7 100 100 120 20 99
                                                 (fn-arena$a-clear (create-fn-arena$a))))))))))

; The run on the live stobj: 7 retired and quiet; 9 retired and still named
; by handle 0; 5 retired but named by a log member in flight.
(defun xrt-quiet-run (fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :verify-guards nil))
  (let* ((fn-arena$x (fn-arena$x-clear fn-arena$x))
         (fn-arena$x (fn-arena$x-seal-extent 7 100 100 120 20 99 fn-arena$x))
         (fn-arena$x (fn-arena$x-seal-list '(1 2) fn-arena$x))
         (fn-arena$x (fn-arena$x-reseat-extent 0 9 0 50 10 20 5 fn-arena$x)))
    (mv (fn-xrt-quiet-files '(5 7 9) '(5) fn-arena$x) fn-arena$x)))

(defun xrt-quiet-run-result ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena$x
    (mv-let (r fn-arena$x) (xrt-quiet-run fn-arena$x) r)))

(assert-event (equal (xrt-quiet-run-result) '(7)))

; Reachable positive witness: the complete antecedent and the conclusion, at
; both handles.
(defthm xrt-quiet-positive
  (and (fn-arena$xcorr (xrt-x3) (xrt-a3))
       (nat-listp '(5 7 9))
       (member 7 (fn-xrt-quiet-files '(5 7 9) '(5) (xrt-x3)))
       (member 7 '(5 7 9))
       (not (member 7 '(5)))
       (not (equal (fn-arx-entry-file (nth 0 (nth *fn-arena$x-exti* (xrt-x3)))) 7))
       (not (equal (fn-arx-entry-file (nth 1 (nth *fn-arena$x-exti* (xrt-x3)))) 7)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance xrt-x3-corresponds))
           :in-theory (disable fn-arena$xcorr fn-xrt-quiet-files-are-unnamed))))

; Each file the check keeps out fails a conjunct of the conclusion: 9 is
; named at handle 0, 5 by a member in flight.
(defthm xrt-quiet-keeps-out-named
  (and (not (member 9 (fn-xrt-quiet-files '(5 7 9) '(5) (xrt-x3))))
       (equal (fn-arx-entry-file (nth 0 (nth *fn-arena$x-exti* (xrt-x3)))) 9)
       (not (member 5 (fn-xrt-quiet-files '(5 7 9) '(5) (xrt-x3))))
       (member 5 '(5)))
  :rule-classes nil)

;; Without nat-listp: a non-file id NIL is "quiet" (its count reads file 0's)
;; and the resident handle 1 names it (fn-arx-entry-file answers NIL).
(defthm xrt-quiet-without-nat-listp
  (and (fn-arena$xcorr (xrt-x3) (xrt-a3))
       (not (nat-listp '(nil)))
       (member nil (fn-xrt-quiet-files '(nil) nil (xrt-x3)))
       (equal (fn-arx-entry-file (nth 1 (nth *fn-arena$x-exti* (xrt-x3)))) nil))
  :rule-classes nil
  :hints (("Goal" :use ((:instance xrt-x3-corresponds))
           :in-theory (disable fn-arena$xcorr))))

; Without the correspondence (CORRUPTED-STATE witness): an extent column
; naming file 7 beside an empty count column.  The other hypotheses hold,
; the correspondence fails for every abstract value, and so does the
; conclusion (entry 0 names 7).
(defthm xrt-quiet-without-corr-corrupted-state
  (let ((x (list nil '((7 100 100 120 20 99)) nil nil)))
    (and (not (fn-arx-files-agree (nth *fn-arena$x-exti* x) (nth *fn-arena$x-filesi* x)))
         (not (fn-arena$xcorr x a))
         (nat-listp '(7))
         (member 7 (fn-xrt-quiet-files '(7) nil x))
         (equal (fn-arx-entry-file (nth 0 (nth *fn-arena$x-exti* x))) 7)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arx-files-agree-necc (f 7)
                                   (ext '((7 100 100 120 20 99))) (files nil)))
           :in-theory (e/d (fn-arx-files-get fn-arx-entry-file) (fn-arx-files-agree-necc)))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-quiet-keystone-without-corr
    (implies (and (nat-listp retired)
                  (member f (fn-xrt-quiet-files retired named fn-arena$x)))
             (not (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x)))
                         f)))))))

; Teeth: KEYSTONE fn-xrt-dropped-file-is-released (section 3).  The
; publication's own pin at 2, nobody else pinned, the pending stamp 3.
(defconst *xrt-st-own* (list 3 '((2 . 1)) nil))
(defconst *xrt-st-other* (list 3 '((1 . 1) (2 . 1)) nil))
(defconst *xrt-st-none* (list 3 nil nil))

; Reachable positive witness: the complete antecedent and the conclusion.
(defthm xrt-released-positive
  (and (member 7 '(5 7 9))
       (not (member 7 '(5)))
       (equal (fn-arx-file-count 7 (xrt-x3)) 0)
       (natp 3) (natp 2)
       (fn-arpn-held-p 2 (second *xrt-st-own*))
       (atom (fn-arpn-unpin-at 2 (second *xrt-st-own*)))
       (member 7 (fn-xrt-quiet-files '(5 7 9) '(5) (xrt-x3)))
       (equal (mv-nth 1 (fn-arpn-step *xrt-st-own* (list :clear-except 3 2))) t))
  :rule-classes nil)

; Hypothesis removal: another reader pinned at 1 (at or below the stamp).
; Every retained hypothesis holds, the omitted one fails, the conclusion
; fails (the group waits).
(defthm xrt-released-without-no-other-pin
  (and (member 7 '(5 7 9))
       (not (member 7 '(5)))
       (equal (fn-arx-file-count 7 (xrt-x3)) 0)
       (natp 3) (natp 2)
       (fn-arpn-held-p 2 (second *xrt-st-other*))
       (not (atom (fn-arpn-unpin-at 2 (second *xrt-st-other*))))
       (not (equal (mv-nth 1 (fn-arpn-step *xrt-st-other* (list :clear-except 3 2))) t)))
  :rule-classes nil)

; Hypothesis removal: the asking reader holds no pin (the step refuses).
(defthm xrt-released-without-own-pin
  (and (member 7 '(5 7 9))
       (not (member 7 '(5)))
       (equal (fn-arx-file-count 7 (xrt-x3)) 0)
       (natp 3) (natp 2)
       (not (fn-arpn-held-p 2 (second *xrt-st-none*)))
       (atom (fn-arpn-unpin-at 2 (second *xrt-st-none*)))
       (equal (mv-nth 1 (fn-arpn-step *xrt-st-none* (list :clear-except 3 2))) :refused))
  :rule-classes nil)

; Hypothesis removal: a file a log member names (5), and a file an extent
; entry still counts (9): each is kept out of the quiet set.
(defthm xrt-released-without-unnamed
  (and (member 5 '(5 7 9))
       (member 5 '(5))
       (not (member 5 (fn-xrt-quiet-files '(5 7 9) '(5) (xrt-x3))))
       (member 9 '(5 7 9))
       (not (member 9 '(5)))
       (not (equal (fn-arx-file-count 9 (xrt-x3)) 0))
       (not (member 9 (fn-xrt-quiet-files '(5 7 9) '(5) (xrt-x3)))))
  :rule-classes nil)
