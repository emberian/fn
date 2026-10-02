; Teeth for books/log-sink (PKT-508, PRF-187): the owner's service-log sink.
(in-package "ACL2")
(include-book "../../books/log-sink")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

(defconst *lst-b* 100)

; fn-log-sink-init-okp.
(assert-event (fn-log-sink-okp (fn-log-sink-init) *lst-b*))

; A reachable run: three lines of 40 octets offered to a sink that never
; drains.  The first two queue (80 <= 100), the third drops (120 > 100).
(defconst *lst-o1* (fn-log-sink-offer (fn-log-sink-init) 40 *lst-b*))
(defconst *lst-o2* (fn-log-sink-offer (cadr *lst-o1*) 40 *lst-b*))
(defconst *lst-o3* (fn-log-sink-offer (cadr *lst-o2*) 40 *lst-b*))
(assert-event (equal (car *lst-o1*) :queue))
(assert-event (equal (car *lst-o2*) :queue))
(assert-event (equal (car *lst-o3*) :drop))
(assert-event (equal (cadr *lst-o3*) '(80 2 1 0 3)))
(assert-event (fn-log-sink-okp (cadr *lst-o3*) *lst-b*))
; The writer drains one line, written, and one whose write failed.
(defconst *lst-t1* (fn-log-sink-take (cadr *lst-o3*) 40 :written))
(defconst *lst-t2* (fn-log-sink-take *lst-t1* 40 :failed))
(assert-event (equal *lst-t1* '(40 1 1 1 3)))
(assert-event (equal *lst-t2* '(0 0 2 1 3)))
(assert-event (fn-log-sink-okp *lst-t2* *lst-b*))
; Taking from an empty queue changes nothing.
(assert-event (equal (fn-log-sink-take *lst-t2* 40 :written) *lst-t2*))

; D27: a line longer than the bound is queued when nothing is pending, and
; the relation still holds (one line pending past the bound).
(defconst *lst-big* (fn-log-sink-offer (fn-log-sink-init) 5000 *lst-b*))
(assert-event (equal (car *lst-big*) :queue))
(assert-event (fn-log-sink-okp (cadr *lst-big*) *lst-b*))
; ... and a second line behind it is dropped.
(assert-event (equal (car (fn-log-sink-offer (cadr *lst-big*) 1 *lst-b*)) :drop))

;; The two preservation keystones with their teeth (books/defkeystone.lisp):
;; the positive witness is the reachable run above; the removal witness of
;; `okp' is a sink whose counts do not add up (offer) or two lines pending
;; past the bound (take), which stays broken, so the weakened theorem is
;; false at it and must fail.
(defconst *lst-bad* '(0 0 0 0 5))
(defconst *lst-over* '(500 3 0 0 3))

(defkeystone lst-offer-preserves
  (implies (fn-log-sink-okp s bound)
           (fn-log-sink-okp (cadr (fn-log-sink-offer s len bound)) bound))
  :subject fn-log-sink-offer
  :mutations (:deferred "no false neighbour named yet")
  :id "PRF-187"
  :restates fn-log-sink-offer-preserves-okp
  :hyps (okp)
  :witness ((s (cadr *lst-o2*)) (len 40) (bound *lst-b*))
  :breaks ((okp ((s *lst-bad*) (len 1))))
  :rule-classes nil)

(defkeystone lst-take-preserves
  (implies (fn-log-sink-okp s bound)
           (fn-log-sink-okp (fn-log-sink-take s len outcome) bound))
  :subject fn-log-sink-take
  :mutations (:deferred "no false neighbour named yet")
  :id "PRF-187"
  :restates fn-log-sink-take-preserves-okp
  :hyps (okp)
  :witness ((s (cadr *lst-o3*)) (len 40) (outcome :written) (bound *lst-b*))
  :breaks ((okp ((s *lst-over*) (len 0))))
  :rule-classes nil)

; fn-log-sink-offer-drops-only-past-the-bound (no hypothesis): both sides.
(assert-event (and (equal (car *lst-o3*) :drop)
                   (posp (fn-log-sink-pending-lines (cadr *lst-o2*)))
                   (< *lst-b* (+ (fn-log-sink-pending-octets (cadr *lst-o2*)) 40))))
(assert-event (and (equal (car *lst-o2*) :queue)
                   (<= (+ (fn-log-sink-pending-octets (cadr *lst-o1*)) 40) *lst-b*)))
; The conclusion fails for a stronger rule that drops any line past the
; bound: the empty-queue line of 5000 is queued.
(must-fail-checked
 (defthm lst-drops-any-line-past-the-bound
   (implies (and (equal s (fn-log-sink-init)) (equal len 5000) (equal bound *lst-b*)
                 (< (nfix bound) (+ (fn-log-sink-pending-octets s) (nfix len))))
            (equal (car (fn-log-sink-offer s len bound)) :drop))
   :rule-classes nil))

;; fn-log-sink-drop-counts: its witness is the third line's drop, and
;; without the :drop hypothesis a queued line (the second) leaves the dropped
;; count alone.
(defkeystone lst-drop-counts
  (implies (equal (car (fn-log-sink-offer s len bound)) :drop)
           (let ((s2 (cadr (fn-log-sink-offer s len bound))))
             (and (equal (fn-log-sink-dropped s2) (+ 1 (fn-log-sink-dropped s)))
                  (equal (fn-log-sink-pending-lines s2) (fn-log-sink-pending-lines s))
                  (equal (fn-log-sink-pending-octets s2) (fn-log-sink-pending-octets s)))))
  :subject fn-log-sink-offer
  :mutations (:deferred "no false neighbour named yet")
  :id "PRF-187"
  :restates fn-log-sink-drop-counts
  :hyps (drop)
  :witness ((s (cadr *lst-o2*)) (len 40) (bound *lst-b*))
  :breaks ((drop ((s (cadr *lst-o1*)))))
  ; the book leaves fn-log-sink-offer disabled; the source keystone is the proof
  :hints (("Goal" :use fn-log-sink-drop-counts))
  :rule-classes nil)
