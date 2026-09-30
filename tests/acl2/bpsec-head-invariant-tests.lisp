(in-package "ACL2")
(include-book "../../books/bpsec-asb-head-invariant")

(defconst *fn-bpshi-head* (fn-bps-head-start))
(defconst *fn-bpshi-ready* '(2 4))
(defconst *fn-bpshi-wide* '(27 255 255 255 255 255 255 255 255 99))
(defconst *fn-bpshi-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpshi-bib*
  (fn-bps-asb-make 11 '(0 1) 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
                         (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bpshi-wire* (fn-bps-asb-encode *fn-bpshi-bib*))
(defconst *fn-bpshi-start* (fn-bps-asb-start 11 :head-invariant 0 (len *fn-bpshi-wire*) *fn-bpshi-limits*))

(assert-event
 (and (eq (symbol-class 'fn-bps-head-profilep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-ready-headp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-head-profilep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))
(assert-event (fn-bps-head-profilep *fn-bpshi-head*))
(assert-event (fn-bps-ready-headp *fn-bpshi-ready*))
(assert-event (fn-bps-asb-head-profilep *fn-bpshi-start*))

; Reachable uint64 boundary, complete typed-ready and carried-profile facts.
(assert-event
 (let ((drive (fn-bps-head-drive *fn-bpshi-head* *fn-bpshi-wide* 9)))
   (and (fn-bps-head-profilep *fn-bpshi-head*)
        (eq (fn-bps-field 0 drive) :ready)
        (fn-bps-ready-headp (fn-bps-field 1 drive))
        (equal (fn-bps-field 1 drive) (list 0 *fn-bpc-max-uint*))
        (fn-bps-head-profilep (fn-bps-field 2 drive))
        (equal (fn-bps-field 3 drive) 9) (equal (fn-bps-field 4 drive) '(99)))))
(assert-event
 (let* ((first (fn-bps-head-drive *fn-bpshi-head* *fn-bpshi-wide* 3))
        (held (fn-bps-field 2 first))
        (second (fn-bps-head-drive held (fn-bps-field 4 first) 6)))
   (and (fn-bps-head-profilep *fn-bpshi-head*) (eq (fn-bps-field 0 first) :more)
        (fn-bps-head-profilep held) (eq (fn-bps-field 0 second) :ready)
        (fn-bps-ready-headp (fn-bps-field 1 second))
        (fn-bps-head-profilep (fn-bps-field 2 second)))))
(assert-event
 (let ((one (fn-bps-head-feed *fn-bpshi-head* 68)))
   (and (fn-bps-head-profilep *fn-bpshi-head*) (eq (fn-bps-field 0 one) :ready)
        (fn-bps-ready-headp (fn-bps-field 1 one)) (equal (fn-bps-field 1 one) '(2 4))
        (fn-bps-head-profilep (fn-bps-field 2 one)))))
(assert-event
 (let ((one (fn-bps-head-feed *fn-bpshi-head* 256)))
   (and (fn-bps-head-profilep *fn-bpshi-head*) (eq (fn-bps-field 0 one) :refused)
        (fn-bps-head-profilep (fn-bps-field 2 one)))))
(assert-event
 (let ((drive (fn-bps-head-drive *fn-bpshi-head* '(24 23) 2)))
   (and (fn-bps-head-profilep *fn-bpshi-head*) (eq (fn-bps-field 0 drive) :refused)
        (eq (fn-bps-field 1 drive) :nonminimal-head)
        (fn-bps-head-profilep (fn-bps-field 2 drive)))))
(assert-event
 (let ((one (fn-bps-head-feed *fn-bpshi-head* 32)))
   (and (fn-bps-head-profilep *fn-bpshi-head*) (eq (fn-bps-field 0 one) :unsupported)
        (fn-bps-head-profilep (fn-bps-field 2 one)))))

(defun fn-bpshi-run (cursor remaining fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))))
  (if (zp (nfix fuel)) :test-fuel
    (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :head-invariant (fn-bps-get :offset cursor)
                                      (if (consp remaining) (list (car remaining)) nil)) 1))
           (next (fn-bps-field 2 step)))
      (if (not (and (fn-bps-asb-head-profilep cursor) (fn-bps-asb-head-profilep next))) :broken-head
        (if (or (eq (fn-bps-field 0 step) :more) (eq (fn-bps-field 0 step) :need-input))
            (fn-bpshi-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                                  (cdr remaining) remaining) (1- (nfix fuel)))
          (list (fn-bps-field 0 step) next))))))
(assert-event
 (let* ((run (fn-bpshi-run *fn-bpshi-start* *fn-bpshi-wire* 1024)) (next (fn-bps-field 1 run)))
   (and (fn-bps-asb-head-profilep *fn-bpshi-start*) (eq (fn-bps-field 0 run) :parsed)
        (fn-bps-asb-head-profilep next)
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result next)
                                     (list (cons :head-invariant *fn-bpshi-wire*))) *fn-bpshi-bib*))))
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpshi-start* *fn-bpshi-wire* 592)))
   (and (fn-bps-asb-head-profilep *fn-bpshi-start*)
        (fn-bps-asb-head-profilep (car drive)) (eq (fn-bps-get :status (car drive)) :parsed))))
(assert-event
 (fn-bps-asb-head-profilep (fn-bps-asb-start 99 :head-invariant -1 -1 nil)))

; Hypothesis removal: profile is retained; READY is affirmatively absent,
; and the complete typed-result conclusion fails for feed and drive.
(assert-event
 (let ((one (fn-bps-head-feed *fn-bpshi-head* 24))
       (drive (fn-bps-head-drive *fn-bpshi-head* '(24) 1)))
   (and (fn-bps-head-profilep *fn-bpshi-head*)
        (not (eq (fn-bps-field 0 one) :ready)) (not (fn-bps-ready-headp (fn-bps-field 1 one)))
        (not (eq (fn-bps-field 0 drive) :ready)) (not (fn-bps-ready-headp (fn-bps-field 1 drive))))))
; Corrupted-state omission: shape-only HEADP accepts this unsupported major
; in argument phase. The carried profile rejects it; READY remains true,
; while the typed-ready conclusion fails. This is not a reachable start.
(assert-event
 (let* ((corrupted '(:bps-head :argument 1 24 1 0))
        (one (fn-bps-head-feed corrupted 24)) (drive (fn-bps-head-drive corrupted '(24) 1)))
   (and (fn-bps-headp corrupted) (not (fn-bps-head-profilep corrupted))
        (eq (fn-bps-field 0 one) :ready) (not (fn-bps-ready-headp (fn-bps-field 1 one)))
        (eq (fn-bps-field 0 drive) :ready) (not (fn-bps-ready-headp (fn-bps-field 1 drive))))))
; Sole carried-profile hypothesis omitted, with explicit output failure.
(assert-event
 (let ((one (fn-bps-head-feed nil 24)) (drive (fn-bps-head-drive nil '(24) 1)))
   (and (not (fn-bps-head-profilep nil))
        (not (fn-bps-head-profilep (fn-bps-field 2 one)))
        (not (fn-bps-head-profilep (fn-bps-field 2 drive))))))
; ASB corrupted-state omission mutates only the nested head then preserves it
; via quantum zero or actual wrong-window refusal; no other premise exists.
(assert-event
 (let* ((corrupted (fn-bps-put :head nil *fn-bpshi-start*))
        (drive (fn-bps-asb-drive corrupted *fn-bpshi-wire* 0))
        (step (fn-bps-asb-step corrupted (fn-bps-window-make :foreign 0 *fn-bpshi-wire*) 17)))
   (and (not (fn-bps-asb-head-profilep corrupted))
        (not (fn-bps-asb-head-profilep (car drive)))
        (not (fn-bps-asb-head-profilep (fn-bps-field 2 step))))))
