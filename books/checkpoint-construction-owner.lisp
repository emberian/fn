; Coordinated C ownership admission over the lower B construction ledger.
(in-package "ACL2")
(include-book "checkpoint-construction")
(include-book "machines-b")
(include-book "c-snapshot")
(fn2-book-layer :c)

; Preflight the allocator's actual next row, then reserve and retain the exact
; returned identity in that row. There is intentionally no register(handle) or
; generic completion operation. Future physical-write harvest owns completion.
; Role0 is the descriptor; roles1..5 are its roots and their descendants;
; role6 is a pre-reserved journal arena ticket, never a caller-selected Free row.
(defun fn2-checkpoint-construction-reserve (token okind oslot ogen role ordinal intended
                                          fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-control)
 (declare (xargs :stobjs (fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-control)
  :guard (and (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)
              (fn2-extents-wfp fn2-extents) (fn2-control-wfp fn2-control))))
 (b* (((unless (and (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot)
                     (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)))
       (mv :snapshot 0 0 0 fn2-checkpoint-construction fn2-extents fn2-control))
      ((unless (and (unsigned-byte-p 60 token) (unsigned-byte-p 8 okind)
                     (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
                     (natp role) (<= role 6) (unsigned-byte-p 60 ordinal)
                     (posp intended) (<= intended *fn2-storage-extent-bytes*)
                     (equal (mod intended *fn2-format-sector-size*) 0)
                     (equal (fn2-checkpoint-construction-rows fn2-checkpoint-construction) (fn2-extents-rows fn2-extents))))
       (mv :bounds 0 0 0 fn2-checkpoint-construction fn2-extents fn2-control))
      (next (fn2-alloc-free-head fn2-extents))
      ((unless (and (fn2-alloc-slotp next fn2-extents)
                     (equal (fn2-extents-state next fn2-extents) *fn2-extent-state-free*)
                     (equal (fn2-checkpoint-construction-live next fn2-checkpoint-construction) 0)))
       (mv :no-space 0 0 0 fn2-checkpoint-construction fn2-extents fn2-control))
      ((mv code extent epoch counter fn2-extents fn2-control) (fn2-storage-reserve-children fn2-extents fn2-control))
      ((unless (eq code :ok)) (mv code extent epoch counter fn2-checkpoint-construction fn2-extents fn2-control))
      ; A mismatch is retained, never cancelled or called ordinary pressure.
      ((unless (equal extent next))
       (mv :uncertain extent epoch counter fn2-checkpoint-construction fn2-extents fn2-control))
      (fn2-checkpoint-construction (fn2-checkpoint-construction-put extent
       (live 1) (token token) (owner-kind okind) (owner-slot oslot) (owner-gen ogen)
       (role role) (ordinal ordinal) (epoch epoch) (counter counter)
       (intended-bytes intended) (completed-bytes 0))))
  (mv :ok extent epoch counter fn2-checkpoint-construction fn2-extents fn2-control)))

(fn2-checkpoint-construction-preserves fn2-checkpoint-construction-reserve
 (token okind oslot ogen role ordinal intended fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-control)
 :carriers ((fn2-checkpoint-construction 4 :prefix "-CONSTRUCTION")
            (fn2-extents 5 :prefix "-EXTENTS") (fn2-control 6 :prefix "-CONTROL")))
