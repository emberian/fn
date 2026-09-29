; Tests for books/extent-retire.lisp (lane online-reclaim-2, PRF-930).
;
; 1. The functions the host calls are guard-verified.
; 2. A checkpoint frame on the live stobjs: the step's handles, the reseat of
;    a frame whose chunk holds handle 0's payload (done), a torn chunk (not
;    done), the scan and the close decision.
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
      (eq (symbol-class 'fn-xrt-scan (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-xrt-scan-may-start (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-xrt-close-set (w state)) :common-lisp-compliant)))

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

; The close decision.
(assert-event
 (and (fn-xrt-scan-may-start '(3 4) '(5))
      (not (fn-xrt-scan-may-start '(3 4) '(4)))
      (equal (fn-xrt-close-set '(3 4) t '(4) 0) '(3))
      (null (fn-xrt-close-set '(3 4) nil nil 0))
      (null (fn-xrt-close-set '(3 4) t nil 1))))

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
; Teeth: the scan.  A ground concrete arena: entry 1 an extent in file 5,
; entry 2 an lz extent in file 7, entries 0 and 3 resident.

(defconst *xrt-x*
  (list nil
        (list 0 '(5 0 10 0 3 0) '(7 0 10 0 3 0 3 nil) 0)
        nil))

(defthm xrt-scan-ground
  (and (equal (fn-xrt-first-naming '(5) 0 4 *xrt-x*) 1)
       (equal (fn-xrt-first-naming '(7) 0 4 *xrt-x*) 2)
       (null (fn-xrt-first-naming '(9) 0 4 *xrt-x*))
       (null (fn-xrt-first-naming '(5) 2 4 *xrt-x*))
       (equal (fn-xrt-scan '(5) 0 1 *xrt-x*) '(:next 1))
       (equal (fn-xrt-scan '(5) 1 1 *xrt-x*) '(:found 1))
       (equal (fn-xrt-scan '(5) 2 8 *xrt-x*) :done))
  :rule-classes nil)

(defthm xrt-none-witness
  (and (not (fn-xrt-first-naming '(5) 2 4 *xrt-x*))
       (natp 2) (natp 4) (natp 3) (<= 2 3) (< 3 4)
       (not (fn-xrt-entry-names (fn-arena$x-exti 3 *xrt-x*) '(5))))
  :rule-classes nil)

; Each hypothesis removed: a handle before LO, at or past END, or a scan that
; found one, names the file.
(defthm xrt-none-needs-lo
  (and (not (fn-xrt-first-naming '(5) 2 4 *xrt-x*))
       (not (<= 2 1))
       (fn-xrt-entry-names (fn-arena$x-exti 1 *xrt-x*) '(5)))
  :rule-classes nil)

(defthm xrt-none-needs-end
  (and (not (fn-xrt-first-naming '(5) 0 1 *xrt-x*))
       (not (< 1 1))
       (fn-xrt-entry-names (fn-arena$x-exti 1 *xrt-x*) '(5)))
  :rule-classes nil)

(defthm xrt-none-needs-no-find
  (and (fn-xrt-first-naming '(5) 0 4 *xrt-x*)
       (fn-xrt-entry-names (fn-arena$x-exti 1 *xrt-x*) '(5)))
  :rule-classes nil)

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-none-without-natp-end
    (implies (and (not (fn-xrt-first-naming files lo end fn-arena$x))
                  (natp lo) (natp k) (<= lo k) (< k end))
             (not (fn-xrt-entry-names (fn-arena$x-exti k fn-arena$x) files)))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-none-without-natp-lo
    (implies (and (not (fn-xrt-first-naming files lo end fn-arena$x))
                  (natp end) (natp k) (<= lo k) (< k end))
             (not (fn-xrt-entry-names (fn-arena$x-exti k fn-arena$x) files)))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm xrt-none-without-natp-k
    (implies (and (not (fn-xrt-first-naming files lo end fn-arena$x))
                  (natp lo) (natp end) (<= lo k) (< k end))
             (not (fn-xrt-entry-names (fn-arena$x-exti k fn-arena$x) files)))))))

; The close set: each conjunct of the conclusion fails without its gate.
(defthm xrt-close-witness
  (and (member 3 (fn-xrt-close-set '(3 4) t '(4) 0))
       (member 3 '(3 4)) (not (member 3 '(4))))
  :rule-classes nil)

(assert-event
 (and (not (member 4 (fn-xrt-close-set '(3 4) t '(4) 0)))
      (not (member 3 (fn-xrt-close-set '(3 4) nil '(4) 0)))
      (not (member 3 (fn-xrt-close-set '(3 4) t '(4) 2)))
      (not (member 9 (fn-xrt-close-set '(3 4) t nil 0)))))
