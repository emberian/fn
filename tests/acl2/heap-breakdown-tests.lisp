; Teeth for books/heap-breakdown (PRF-375, lane f8-reservation): the small
; preset's itemised reservation on the d5ab87aec production image, the
; keystone's reachable witness (hypothesis and conclusion), the witness that
; its hypothesis is needed (an offline list verb: the hypothesis fails and so
; does the conclusion) and the must-fail of the theorem without it, and a
; mutation (a breakdown that drops the collector's room does not add up).
(in-package "ACL2")
(include-book "../../books/heap-breakdown")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

;; hbox, batch AZ's d5ab87aec fn-host.core: the file's octets, and the
;; dynamic space in use at the launcher's probe (the least that reproduces
;; the printed `heap=780 MB' of the empty small store: tools/f8_breakdown.py
;; --solve-figure 780).
(defconst *hbt-core* '(214012928 . 147604131))
(defconst *hbt-nursery* (* 64 1024 1024))
(defconst *hbt-small* *fn-heap-small-profile*)

(defun hbt-conclusion (action profile core nursery observed connections)
  (declare (xargs :mode :program))
  (equal (fn-heap-breakdown-sum
          (fn-heap-breakdown action profile core nursery observed connections))
         (fn-heap-reservation-octets
          (fn-heap-mb-of (fn-heap-operation-figure-octets action profile core nursery observed))
          core (fn-heap-stack-kib profile) (fn-heap-thread-count connections))))

;; The reachable witness: `init''s number for the small preset (the run of
;; the full store, unobserved, at init's connections): the hypothesis holds,
;; the terms add up to it: 1,179 MiB (1,188 MiB before lane f8-reservation,
;; printed 1,187 MB under init's own probe's observation).
(assert! (not (member-equal :run *fn-heap-list-actions*)))
(assert! (hbt-conclusion :run *hbt-small* *hbt-core* *hbt-nursery* nil
                         (fn-heap-reserve-init-connections)))
(assert! (equal (fn-heap-init-reservation-octets *hbt-small* *hbt-core* *hbt-nursery*)
                1236374528))
(assert! (equal (fn-heap-breakdown :run *hbt-small* *hbt-core* *hbt-nursery* nil
                                   (fn-heap-reserve-init-connections))
                '((:image-dynamic . 147604131)
                  (:state-history . 17039424)
                  (:state-handles . 786432)
                  (:state-records . 402653184)
                  (:open-chunk-lists . 79691776)
                  (:open-suffix-vectors . 16777216)
                  (:open-per-record . 33554432)
                  (:inflight-lists . 7864320)
                  (:octet-buffers . 50725002)
                  (:collector-room . 108099417)
                  (:megabyte-rounding . 279866)
                  (:image-outside-heap . 214012928)
                  (:thread-stacks . 31457280)
                  (:thread-runtime . 125829120))))

;; The launcher's figure for the empty store (the :init observation): 780 MB
;; before lane f8-reservation (the observation was solved from it), 770 MB
;; since the payload and the memberships share H.
(assert! (equal (fn-heap-mb-of (fn-heap-operation-figure-octets :init *hbt-small* *hbt-core*
                                                                 *hbt-nursery* nil))
                770))
(assert! (hbt-conclusion :init *hbt-small* *hbt-core* *hbt-nursery* nil 32))

;; The hypothesis is needed: `store compact' reserves the larger of its list
;; copies and the store figure; the breakdown itemises only the latter, so
;; there the hypothesis fails and the terms do not add up to its reservation.
(assert! (member-equal :compact *fn-heap-list-actions*))
(assert! (not (hbt-conclusion :compact *hbt-small* *hbt-core* *hbt-nursery* nil 32)))

(must-fail-checked
 (defthm hbt-breakdown-sums-without-the-hypothesis
   (equal (fn-heap-breakdown-sum
           (fn-heap-breakdown action profile core nursery observed connections))
          (fn-heap-reservation-octets
           (fn-heap-mb-of (fn-heap-operation-figure-octets action profile core nursery observed))
           core (fn-heap-stack-kib profile) (fn-heap-thread-count connections)))
   :hints (("Goal" :in-theory (e/d (fn-heap-operation-figure-octets fn-heap-reservation-octets)
                                   (fn-heap-breakdown-base fn-heap-store-base-octets
                                    fn-heap-store-figure-octets fn-heap-thread-count
                                    fn-heap-stack-kib fn-heap-core-file fn-heap-mb-of
                                    fn-heap-operation-list-figure-octets fn-heap-breakdown-sum
                                    fn-heap-breakdown fn-heap-operation-observation)))))
 :step-limit 20000)

;; Mutation: a breakdown without the collector's room is short of the
;; reservation by exactly that term.
(assert! (let* ((terms (fn-heap-breakdown :run *hbt-small* *hbt-core* *hbt-nursery* nil 32))
                (mutant (remove-equal (assoc-equal :collector-room terms) terms)))
           (and (not (equal (fn-heap-breakdown-sum mutant) (fn-heap-breakdown-sum terms)))
                (equal (- (fn-heap-breakdown-sum terms) (fn-heap-breakdown-sum mutant))
                       (cdr (assoc-equal :collector-room terms))))))
