; Canonical HELD records for the paged checkpoint model.  There is one
; interning fold: the shared owner/replay fold, including keyring snapshots.
; Handles count sealed payloads, not records, and continue across a delta.
(in-package "ACL2")
(include-book "store-checkpoint-fold")

(verify-guards fn-scka-fold-at
  :hints (("Goal" :in-theory (e/d (fn-ssr-statep)
                                  (fn-scka-intern-one fn-scka-sealsp fn-ssr-publish
                                   fn-replay-identity-step fn-ssr-at)))))
(verify-guards fn-scka-intern-at)

(defun fn-pck-held (recs)
  (declare (xargs :guard t))
  (fn-scka-intern-at recs (fn-stxk-initial-context 0) 0))

(defthm fn-pck-held-is-the-replay
  (equal (fn-pck-held recs)
         (fn-ssr-rows
          (mv-nth 0 (fn-ssr-intern-step
                     (fn-ssr-seed (fn-stxk-initial-context 0))
                     recs nil nil :resident dicts nil))))
  :hints (("Goal" :in-theory (e/d (fn-pck-held)
                                  (fn-scka-intern-at fn-ssr-intern-step
                                   fn-ssr-rows fn-ssr-seed))
           :use ((:instance fn-ssr-step-rows-are-fn-scka-intern-at
                            (ws recs) (id (fn-stxk-initial-context 0))
                            (fn-arena nil))))))

(defthm fn-pck-held-true-listp
  (implies (not (equal (fn-pck-held recs) :bad))
           (true-listp (fn-pck-held recs)))
  :hints (("Goal" :in-theory (e/d (fn-pck-held) (fn-scka-intern-at)))))

(defthm fn-pck-held-len
  (implies (not (equal (fn-pck-held recs) :bad))
           (equal (len (fn-pck-held recs)) (len recs)))
  :hints (("Goal" :in-theory (e/d (fn-pck-held) (fn-scka-intern-at)))))

(defthm fn-pck-held-store-eventsp
  (implies (not (equal (fn-pck-held recs) :bad))
           (fn-sco-store-eventsp (fn-pck-held recs)))
  :hints (("Goal" :in-theory (e/d (fn-pck-held) (fn-scka-intern-at)))))

(defthm fn-pck-held-of-append
  (implies (and (true-listp prefix)
                (not (equal (fn-pck-held prefix) :bad)))
           (equal (fn-pck-held (append prefix delta))
                  (let ((rows
                         (fn-scka-intern-at
                          delta
                          (fn-replay-identity-loop
                           (fn-pck-held prefix) (fn-stxk-initial-context 0))
                          (len (fn-scka-payloads prefix)))))
                    (if (equal rows :bad) :bad
                      (append (fn-pck-held prefix) rows)))))
  :hints (("Goal" :in-theory (e/d (fn-pck-held)
                                  (fn-scka-intern-at fn-replay-identity-loop
                                   fn-scka-payloads))
           :use ((:instance fn-scka-intern-at-of-append
                            (ws prefix) (vs delta)
                            (id (fn-stxk-initial-context 0)) (h 0))))))
