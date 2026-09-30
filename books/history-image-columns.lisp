; Final canonical image domain and one-word scalar-column emission.
(in-package "ACL2")
(include-book "history-image-census")
(include-book "history-page-buffer")

(defun fn-hcl-admit (count pool column-cap pool-cap)
  (declare (xargs :guard t :guard-hints (("Goal" :in-theory (enable fn-hcc-pages)))))
  (if (not (and (unsigned-byte-p 61 count) (unsigned-byte-p 64 pool)
                 (unsigned-byte-p 51 column-cap) (unsigned-byte-p 51 pool-cap)))
      (list :refused :domain)
    (let ((np (fn-hcc-pages column-cap pool-cap)))
      ; Current fn-hp-okp requires canonical IMAGE BYTES below u64, not just
      ; each used region length. Rounded capacities can exceed that bound.
      (if (<= 18446744073709551616 (* 16384 np))
          (list :refused :canonical-extent)
        (list :prepared np)))))

(defthm fn-hcl-admit-keeps-current-image-domain
  (implies (equal (car (fn-hcl-admit count pool column-cap pool-cap)) :prepared)
           (and (unsigned-byte-p 61 count) (unsigned-byte-p 64 pool)
                (posp (nth 1 (fn-hcl-admit count pool column-cap pool-cap)))
                (< (* 16384 (nth 1 (fn-hcl-admit count pool column-cap pool-cap)))
                   18446744073709551616)
                (equal (nth 1 (fn-hcl-admit count pool column-cap pool-cap))
                       (fn-hcc-pages column-cap pool-cap))))
  :hints (("Goal" :in-theory (enable fn-hcc-pages))))

(defun fn-hcl-cell (column key encoded offset)
  (declare (xargs :guard (and (natp column) (< column 4)
                              (unsigned-byte-p 64 key) (unsigned-byte-p 64 encoded)
                              (unsigned-byte-p 64 offset))))
  (let ((padded (+ encoded (fn-hp-pad8-count encoded))))
    (if (<= 18446744073709551616 padded) (mv :refused 0)
      (mv :word (cond ((equal column 0) key) ((equal column 1) encoded)
                      ((equal column 2) offset) (t padded))))))

(defthm fn-hcl-cell-is-u64
  (implies (and (unsigned-byte-p 64 key) (unsigned-byte-p 64 encoded)
                (unsigned-byte-p 64 offset))
           (unsigned-byte-p 64 (mv-nth 1 (fn-hcl-cell column key encoded offset))))
  :hints (("Goal" :in-theory (disable fn-hp-pad8-count))))

(defthm fn-hcl-cell-refines-current-row
  (implies (and (natp column) (< column 4) (natp offset)
                (equal key (fn-hp-mkey ev salt))
                (equal encoded (len (fn-scc-encode ev)))
                (equal (mv-nth 0 (fn-hcl-cell column key encoded offset)) :word))
           (equal (mv-nth 1 (fn-hcl-cell column key encoded offset))
                  (nth column (fn-hp-cells-of ev salt offset))))
  :hints (("Goal" :in-theory (e/d (fn-hp-cells-of nth)
                                    (fn-hp-pad8-count fn-hp-pad8 fn-scc-encode fn-hp-mkey)))))

(defun fn-hcl-put (column key encoded offset fn-hpb)
  (declare (xargs :stobjs fn-hpb
                  :guard (and (natp column) (< column 4)
                              (unsigned-byte-p 64 key) (unsigned-byte-p 64 encoded)
                              (unsigned-byte-p 64 offset))
                  :guard-hints (("Goal" :use fn-hcl-cell-is-u64
                                 :in-theory (disable fn-hcl-cell fn-hcl-cell-refines-current-row)))))
  (mv-let (verdict word) (fn-hcl-cell column key encoded offset)
    (if (eq verdict :word) (fn-hpb-put word fn-hpb)
      (mv :refused fn-hpb))))

(defthm fn-hcl-put-refines-current-row-effect
  (implies (and (natp column) (< column 4) (natp offset)
                (equal key (fn-hp-mkey ev salt))
                (equal encoded (len (fn-scc-encode ev)))
                (natp (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048)
                (equal (mv-nth 0 (fn-hcl-cell column key encoded offset)) :word))
           (and (equal (mv-nth 0 (fn-hcl-put column key encoded offset fn-hpb)) :stored)
                (equal (fn-hpb-prefix (mv-nth 1 (fn-hcl-put column key encoded offset fn-hpb)))
                       (append (fn-hpb-prefix fn-hpb)
                               (list (nth column (fn-hp-cells-of ev salt offset)))))))
  :hints (("Goal" :use (fn-hcl-cell-refines-current-row
                        (:instance fn-hpb-put-refines-prefix
                         (w (mv-nth 1 (fn-hcl-cell column key encoded offset)))))
           :in-theory (disable fn-hcl-cell fn-hp-cells-of fn-hpb-used fn-hpb-prefix
                               fn-scc-encode fn-hp-mkey nth
                               fn-hcl-cell-refines-current-row fn-hpb-put-refines-prefix))))

(in-theory (disable fn-hcl-admit fn-hcl-cell fn-hcl-put))

(defthm fn-hcl-put-keeps-concrete
  (implies (and (fn-hpbp fn-hpb) (unsigned-byte-p 64 key)
                (unsigned-byte-p 64 encoded) (unsigned-byte-p 64 offset))
           (fn-hpbp (mv-nth 1 (fn-hcl-put column key encoded offset fn-hpb))))
  :hints (("Goal" :use fn-hcl-cell-is-u64
           :in-theory (e/d (fn-hcl-put)
                            (fn-hcl-cell fn-hcl-cell-is-u64 fn-hcl-cell-refines-current-row fn-hpbp)))))

(defthm fn-hcl-put-keeps-identities
  (and (equal (fn-hpb-epoch (mv-nth 1 (fn-hcl-put column key encoded offset fn-hpb)))
              (fn-hpb-epoch fn-hpb))
       (equal (fn-hpb-lease (mv-nth 1 (fn-hcl-put column key encoded offset fn-hpb)))
              (fn-hpb-lease fn-hpb)))
  :hints (("Goal" :in-theory (e/d (fn-hcl-put)
                                  (fn-hcl-cell fn-hpb-epoch fn-hpb-lease)))))
