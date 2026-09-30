(in-package "ACL2")
(include-book "../../books/owner-feed-counts")

(defconst *ofct-peer*
  (fn-cfg-peer-make "p" "p.fn.test" '(:nntp "127.0.0.1" 1120)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.2")))
(defconst *ofct-empty* (fn-own-feed-install-one "p" (fn-cfg-peer-rows *ofct-peer*) nil))
(defconst *ofct-id* '(60 97 62))
(defconst *ofct-counted*
  (fn-own-feed-enqueue-all-counted '("p") *ofct-empty* *ofct-id* 0 0))
(defconst *ofct-one* (car *ofct-counted*))

; Reachable cold install -> exact durable-target enqueue delta.
(assert-event
 (and (fn-own-feed-tablep *ofct-empty*)
      (fn-ofct-table-relationp *ofct-empty*)
      (equal 0 (fn-own-feed-table-pending-model *ofct-empty*))
      (equal (car *ofct-counted*)
             (fn-own-feed-enqueue-all '("p") *ofct-empty* *ofct-id* 0))
      (equal (cdr *ofct-counted*)
             (fn-own-feed-table-pending-model (car *ofct-counted*)))
      (equal (cdr *ofct-counted*) 1)
      (fn-own-feed-tablep *ofct-one*)
      (fn-ofct-table-relationp *ofct-one*)))
(assert-event
 (and (fn-ofct-table-relationp *ofct-one*)
      (equal (fn-own-feed-table-pending-model *ofct-one*)
             (fn-orc-table-pending-model *ofct-one*))
      (fn-feed-count-relationp (fn-own-feed-find "p" *ofct-one*))
      (equal (fn-own-feed-pending-of (fn-own-feed-find "p" *ofct-one*))
             (fn-orc-queue-pending-model
              (fn-feed-queue (fn-own-feed-find "p" *ofct-one*))))))

(defconst *ofct-dropped*
  (fn-feed-give-up (fn-own-feed-find "p" *ofct-one*) *ofct-id* :retry-bound))
(assert-event
 (and (equal (fn-own-feed-table-pending-model
              (fn-own-feed-put "p" *ofct-peer* *ofct-dropped* *ofct-one*))
             (+ (fn-own-feed-table-pending-model *ofct-one*)
                (fn-own-feed-pending-delta
                 (fn-own-feed-find "p" *ofct-one*) *ofct-dropped*)))
      (equal (fn-own-feed-pending-delta
              (fn-own-feed-find "p" *ofct-one*) *ofct-dropped*) -1)))

; Hypothesis-removal: retained table/target fields are valid, but the initial
; carried aggregate is overcounted. A duplicate target does not repair it.
(assert-event
 (and (fn-own-feed-tablep *ofct-one*)
      (fn-ofct-table-relationp *ofct-one*)
      (not (equal 2 (fn-own-feed-table-pending-model *ofct-one*)))
      (not (equal
            (cdr (fn-own-feed-enqueue-all-counted '("p") *ofct-one* *ofct-id* 0 2))
            (fn-own-feed-table-pending-model
             (car (fn-own-feed-enqueue-all-counted '("p") *ofct-one* *ofct-id* 0 2)))))))

(defconst *ofct-port*
  (fn-own-feed-port-peer "p" *ofct-empty* (list :enqueue *ofct-id* 0)))
(assert-event
 (and (fn-own-feed-tablep *ofct-empty*)
      (fn-ofct-table-relationp *ofct-empty*)
      (equal (fn-own-feed-port-status *ofct-port*) :accepted)
      (fn-ofct-table-relationp (fn-own-feed-port-table *ofct-port*))
      (equal (fn-own-feed-table-pending-model (fn-own-feed-port-table *ofct-port*))
             (+ (fn-own-feed-table-pending-model *ofct-empty*)
                (fn-own-feed-port-pending-delta *ofct-port*)))
      (equal (fn-own-feed-port-pending-after 0 *ofct-port*) 1)))

(defconst *ofct-replay*
  (fn-own-feed-port-replay-peer
   "p" *ofct-empty*
   (list (fn-feed-journal-entry :feed-enqueue (list '(112) *ofct-id* 0)))))
(assert-event
 (and (fn-ofct-table-relationp *ofct-empty*)
      (equal (fn-own-feed-port-status *ofct-replay*) :accepted)
      (fn-ofct-table-relationp (fn-own-feed-port-table *ofct-replay*))
      (equal (fn-own-feed-table-pending-model (fn-own-feed-port-table *ofct-replay*))
             (+ (fn-own-feed-table-pending-model *ofct-empty*)
                (fn-own-feed-port-pending-delta *ofct-replay*)))
      (equal (fn-own-feed-port-pending-after 0 *ofct-replay*) 1)))
