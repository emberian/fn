; Layer E: the served consumer's core pieces (fn2/docs/e-surface.md 7;
; lanes/e-continuation E.P1). The subscription-edge table (cns-edges.lisp,
; D8's rows) is a core child here, sized by the ledger's :subscription-edge
; capacity, its link and unlink are declared operations for the request
; kind's arms, and its ready/grant pair is the :wait-row wait kind's source:
; a parked wait is woken by the publish hook's bucket push, through the
; grant service, never by a scan.
(in-package "ACL2")
(include-book "cns-edges")
(include-book "accounts")
(include-book "machines")
(fn2-book-layer :e)

;; The table's rows are the ledger's :subscription-edge capacity (the
;; profile's :esub, else the dimension's default): with rows at least that
;; capacity, every link the ledger's holding admits finds a row, so the
;; ledger stays the one admission authority (cns-edges.lisp, D's review 2).
(defconst *fn2-cns-esub-dimension*
  (position-eq :subscription-edge (strip-cars *fn2-account-holdings*)))
(assert-event (natp *fn2-cns-esub-dimension*))
(defun fn2-cns-edge-rows (profile)
  (declare (xargs :guard t))
  (nfix (fn2-account-profile-capacity *fn2-cns-esub-dimension* profile)))
(defun fn2-cns-edges-profilep (profile)
  ; rows >= the ledger's :subscription-edge capacity, and the table's links
  ; (u32, none = 2^32 - 1) address every row
  (declare (xargs :guard t))
  (let ((cap (fn2-account-profile-capacity *fn2-cns-esub-dimension* profile)))
    (and (natp cap) (<= cap (fn2-cns-edge-rows profile))
         (unsigned-byte-p 31 (fn2-cns-edge-rows profile)))))
(defcorechild fn2-core-cns-edges fn2-cns-edges
 :init (fn2-cns-edges-init (fn2-cns-edge-rows profile) fn2-cns-edges)
 :profilep (fn2-cns-edges-profilep profile)
 :why "A parked consumer wait's subscription edges and the streams' wake buckets (D8's rows, e-surface 7): survive the waiter's park until its wake or cancel.")

;; The operations the request kind's arms call (child form).
(defcost fn2-cns-edge-link-core :child fn2-cns-edge-link :answers (:ok :behind :exhausted)
 :tables (fn2-core-cns-edges)
 :doc "Link a parked wait's edge on its stream from its first unread position: :behind (a publish since its read: read again), :exhausted (every row in use).")
(defcost fn2-cns-edge-unlink-core :child fn2-cns-edge-unlink :tables (fn2-core-cns-edges)
 :doc "Release a wait's edge (its bucket's cursor moved past it).")

;; The :wait-row wait kind (MACHINE-FORM 6.10 F4): a request row parked on
;; its edge; the pair below and the operations' core faces are made in the
;; access section (fn2-cns-wait-events).
(defwait :wait-row :ready fn2-cns-wait-ready-p :grant fn2-cns-wait-grant-one
 :doc "A consumer wait parked on its stream's edge, woken once the publish hook pushed its bucket.")

(defmacro fn2-cns-wait-events ()
 '(progn
   ;; the core faces of the declared operations (one stobj-let each)
   (defun fn2-cns-edge-link-core (stream waiter gen from fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-cns-edges (fn2-core-cns-edges fn2-core)))
       (code e fn2-cns-edges) (fn2-cns-edge-link stream waiter gen from fn2-cns-edges)
       (mv code e fn2-core)))
   (fn2-core-preserves fn2-cns-edge-link-core (stream waiter gen from fn2-core) :position 2 :rows nil)
   (defun fn2-cns-edge-unlink-core (e fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-cns-edges (fn2-core-cns-edges fn2-core)))
       (fn2-cns-edges) (fn2-cns-edge-unlink e fn2-cns-edges)
       fn2-core))
   (fn2-core-preserves fn2-cns-edge-unlink-core (e fn2-core) :rows nil :prefix "")
   ;; the :wait-row source
   (defun fn2-cns-core-ready (fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-cns-edges (fn2-core-cns-edges fn2-core)))
       (r) (fn2-cns-ready-p fn2-cns-edges) r))
   (defun fn2-cns-core-grant (fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-cns-edges (fn2-core-cns-edges fn2-core))
                 (fn2-machines (fn2-core-machines fn2-core))
                 (fn2-control (fn2-core-control fn2-core)))
       (w fn2-cns-edges fn2-machines fn2-control)
       (fn2-cns-grant-one fn2-cns-edges fn2-machines fn2-control)
       (mv w fn2-core)))
   (fn2-core-preserves fn2-cns-core-grant (fn2-core) :position 1 :rows nil)
   (defthm fn2-cns-core-grant-live
     (implies (fn2-cns-core-ready fn2-core)
              (not (equal (mv-nth 0 (fn2-cns-core-grant fn2-core)) *fn2-none*)))
     :hints (("Goal" :in-theory (e/d (fn2-cns-core-ready fn2-cns-core-grant) (fn2-cns-grant-one fn2-cns-ready-p))
                     :use ((:instance fn2-cns-grant-one-live
                                      (fn2-cns-edges (fn2-core-cns-edges fn2-core))
                                      (fn2-machines (fn2-core-machines fn2-core))
                                      (fn2-control (fn2-core-control fn2-core)))))))
   (defattach (fn2-cns-wait-ready-p fn2-cns-core-ready) (fn2-cns-wait-grant-one fn2-cns-core-grant)
     :hints (("Goal" :use ((:instance fn2-cns-core-grant-live)))))
   (in-theory (disable fn2-cns-edge-link-core fn2-cns-edge-unlink-core fn2-cns-core-ready fn2-cns-core-grant))))
