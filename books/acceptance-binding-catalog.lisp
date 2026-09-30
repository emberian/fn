; Proposed component: source admission pending catalog-commit keyring repair.
; Full retained row lookup for immutable acceptance bindings. Unlike the
; acceptance article projection, this preserves metadata, frozen context and
; any separately validated binding column added by the current format.
(in-package "ACL2")
(include-book "catalog-view")

(defun fn-abc-find-row (msgid i v fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (natp i) (natp v) (<= i (fn-cat-count fn-cat)))
                  :guard-hints (("Goal" :in-theory
                   (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)))))
  (if (zp i) nil
    (let ((seq (1- i)))
      (if (and (fn-cat-visible-at seq v fn-cat)
               (equal msgid (fn-record-msgid (fn-cat-at seq fn-cat))))
          (fn-cat-at seq fn-cat)
        (fn-abc-find-row msgid seq v fn-cat)))))

(local (defthm fn-abc-last-visible-in-range
  (implies (fn-cat-view-last-visible seqs v fn-cat)
           (and (natp (fn-cat-view-last-visible seqs v fn-cat))
                (< (fn-cat-view-last-visible seqs v fn-cat)
                   (fn-cat-count fn-cat))))
  :hints (("Goal" :in-theory (enable fn-cat-view-last-visible)))))

(defun fn-abc-row (msgid v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)
                  :guard-hints (("Goal" :in-theory
                   (disable fn-cat-view-last-visible fn-cat-msgid-seqs
                            fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)))))
  (let ((seq (fn-cat-view-last-visible (fn-cat-msgid-seqs msgid fn-cat) v fn-cat)))
    (if seq (fn-cat-at seq fn-cat) nil)))

(local (defthm fn-abc-find-row-is-row-of-find
  (equal (fn-abc-find-row msgid i v fn-cat)
         (let ((seq (fn-cat-view-find msgid i v fn-cat)))
           (if seq (fn-cat-at seq fn-cat) nil)))
  :hints (("Goal" :induct (fn-abc-find-row msgid i v fn-cat)
                  :in-theory (e/d (fn-abc-find-row fn-cat-view-find)
                                   (fn-cat-at fn-cat-visible-at))))))

; Representation boundary: the concrete Message-ID column returns the whole
; original row selected by the logical visible-row query. No whole-history
; validation or walk executes in FN-ABC-ROW.
(defthm fn-abc-row-is-visible-row-query
  (equal (fn-abc-row msgid v fn-cat)
         (fn-abc-find-row msgid (fn-cat-count fn-cat) v fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-abc-row)
                    (fn-abc-find-row fn-cat-view-last-visible fn-cat-msgid-seqs
                     fn-cat-view-find fn-cat-at fn-cat-count))
                  :use ((:instance fn-cat-view-find-is-msgid-column)
                        (:instance fn-abc-find-row-is-row-of-find
                          (i (fn-cat-count fn-cat)))))))

(in-theory (disable fn-abc-find-row fn-abc-row))
