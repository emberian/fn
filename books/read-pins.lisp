; Physical storage pins are owned by operation identity, not machine identity.
; Read and reserved-page write entries share this same reserved edge region.
(in-package "ACL2")
(include-book "commit-alloc")
(include-book "vocab")

(defun fn2-b-read-pin-edge (opslot fn2-extents)
 (declare (xargs :stobjs fn2-extents :guard (fn2-extents-wfp fn2-extents)))
 (+ 6 (* 2 (fn2-extents-rows fn2-extents)) (nfix opslot)))

; Completion can settle an unpinned raw/recovery read. A live pin, however,
; belongs to precisely this operation generation; another completion cannot
; retire it. The concrete identity comes from the held edge, not a caller.
(defun fn2-b-read-pin-drop (opslot opgen fn2-extents fn2-alloc-edges)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges)
                 :guard (and (fn2-extents-wfp fn2-extents)
                             (fn2-alloc-edges-wfp fn2-alloc-edges))))
 (let ((edge (fn2-b-read-pin-edge opslot fn2-extents)))
  (cond ((not (natp opslot)) (mv :bounds fn2-extents fn2-alloc-edges))
        ((not (fn2-alloc-edge-slotp edge fn2-alloc-edges))
         (mv :edge-bounds fn2-extents fn2-alloc-edges))
        ((equal (fn2-alloc-edges-state edge fn2-alloc-edges) *fn2-alloc-edge-state-free*)
         (mv :ok fn2-extents fn2-alloc-edges))
        (t (fn2-alloc-edge-drop edge opgen
             (fn2-alloc-edges-extent edge fn2-alloc-edges)
             (fn2-alloc-edges-epoch edge fn2-alloc-edges)
             (fn2-alloc-edges-counter edge fn2-alloc-edges)
             :outstanding-io fn2-extents fn2-alloc-edges)))))
(fn2-extents-preserves fn2-b-read-pin-drop (opslot opgen fn2-extents fn2-alloc-edges)
 :carriers ((fn2-extents 1 :prefix "-EXTENTS") (fn2-alloc-edges 2 :prefix "-EDGES")))

(defun fn2-b-read-pin-harvest (opslot opgen cell evkind outcome reason count aux0 aux1
                                      fn2-extents fn2-alloc-edges)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges)
                 :guard (and (fn2-extents-wfp fn2-extents)
                             (fn2-alloc-edges-wfp fn2-alloc-edges)))
          (ignore outcome reason count aux0 aux1))
 (if (and (equal cell 0)
          (or (equal evkind *fn2-event-read-result*) (equal evkind *fn2-event-write-result*)))
     (fn2-b-read-pin-drop opslot opgen fn2-extents fn2-alloc-edges)
   (mv :ok fn2-extents fn2-alloc-edges)))
(fn2-extents-preserves fn2-b-read-pin-harvest
 (opslot opgen cell evkind outcome reason count aux0 aux1 fn2-extents fn2-alloc-edges)
 :carriers ((fn2-extents 1 :prefix "-EXTENTS") (fn2-alloc-edges 2 :prefix "-EDGES")))
