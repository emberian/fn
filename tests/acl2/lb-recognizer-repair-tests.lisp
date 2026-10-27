; Three coordinator-directed LC counterexamples, restated with LB-owned fixtures.
; Ground lemmas keep the 2^64 compact pool term symbolic: no wide allocation.
(in-package "ACL2")
(include-book "lb-recognizer-repair-aliases")
(include-book "../../books/defkeystone")

(with-prover-time-limit 15 (defthm fn-lbr13-pool-mutation-witness
 (and (let* ((row (fn-lbr13-held)) (rows (list row))
        (log (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil))
        (before (update-nth *fn-lbc-overview-store*
                 (make-list-ac 18446744073709551616 '(0) nil) (create-fn-lbc)))
        (after (fn-lbr13-finish-single-row row (fn-lbc-append-row row log before)))
        (mutant (fn-lbr13-finish-single-row row (fn-lbr13-clamp-append-row row log before))))
  (and (fn-lbc-p before) (fn-cat$ap rows) (fn-lb-log-model-segsp log)
       (fn-lbc-corr before nil log)
       (equal (fn-lbc-render-nov 0 after) (fn-hnov-of *fn-lbr13-payload*))
       (fn-lbc-corr after rows log)
       (not (equal (fn-lbc-render-nov 0 mutant) (fn-hnov-of *fn-lbr13-payload*)))
       (not (fn-lbc-corr mutant rows log)))) (not (fn-lbc-corr (fn-lbr13-clamped-indexed-write) (list (fn-lbr13-held)) (fn-lbr13-single-log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-pool-clamp-repair-control) (:instance fn-lbr13-clamped-indexed-corr-is-false))
 :in-theory (theory 'minimal-theory)))))
(defteeth fn-lbr13-pool-clamp-repair-control
 :claim (() (let* ((row (fn-lbr13-held)) (rows (list row))
        (log (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil))
        (before (update-nth *fn-lbc-overview-store*
                 (make-list-ac 18446744073709551616 '(0) nil) (create-fn-lbc)))
        (after (fn-lbr13-finish-single-row row (fn-lbc-append-row row log before)))
        (mutant (fn-lbr13-finish-single-row row (fn-lbr13-clamp-append-row row log before))))
  (and (fn-lbc-p before) (fn-cat$ap rows) (fn-lb-log-model-segsp log)
       (fn-lbc-corr before nil log)
       (equal (fn-lbc-render-nov 0 after) (fn-hnov-of *fn-lbr13-payload*))
       (fn-lbc-corr after rows log)
       (not (equal (fn-lbc-render-nov 0 mutant) (fn-hnov-of *fn-lbr13-payload*)))
       (not (fn-lbc-corr mutant rows log)))))
 :subject fn-lbc-append-row
 :witness ((r13-control-token 0)) :witness-lemma fn-lbr13-pool-clamp-repair-control
 :breaks nil
 :mutations ((pool-fault (:conclusion (fn-lbc-corr (fn-lbr13-clamped-indexed-write) (list (fn-lbr13-held)) (fn-lbr13-single-log))) ((r13-control-token 0))
 :fault "bedbdeedd clamps a wide pool start to zero and reads a NUL subject" :lemma fn-lbr13-pool-mutation-witness)))

(with-prover-time-limit 15 (defthm fn-lbr13-directory-mutation-witness
 (and (let* ((row (fn-lbr13-held)) (rows (list row))
        (log (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil))
        (before (create-fn-lbc))
        (stray (fn-lbr13-extra-directory before))
        (after (fn-lbr13-finish-single-row row (fn-lbc-append-row row log before)))
        (mutant (fn-lbr13-finish-single-row row (fn-lbc-append-row row log stray))))
  (and (fn-lbc-p before) (fn-lbc-corr before nil log)
       (fn-lbc-p stray) (fn-lbr13-old-corr stray nil log)
       (not (fn-lbc-corr stray nil log))
       (fn-lbc-corr after rows log)
       (not (fn-lbc-corr mutant rows log)))) (not (fn-lbc-corr (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (fn-lbr13-extra-directory (create-fn-lbc)))) (list (fn-lbr13-held)) (fn-lbr13-single-log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-directory-append-repair-control) (:instance fn-lbr13-stray-writer-refused))
 :in-theory (theory 'minimal-theory)))))
(defteeth fn-lbr13-directory-append-repair-control
 :claim (() (let* ((row (fn-lbr13-held)) (rows (list row))
        (log (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil))
        (before (create-fn-lbc))
        (stray (fn-lbr13-extra-directory before))
        (after (fn-lbr13-finish-single-row row (fn-lbc-append-row row log before)))
        (mutant (fn-lbr13-finish-single-row row (fn-lbc-append-row row log stray))))
  (and (fn-lbc-p before) (fn-lbc-corr before nil log)
       (fn-lbc-p stray) (fn-lbr13-old-corr stray nil log)
       (not (fn-lbc-corr stray nil log))
       (fn-lbc-corr after rows log)
       (not (fn-lbc-corr mutant rows log)))))
 :subject fn-lbc-append-row
 :witness ((r13-control-token 0)) :witness-lemma fn-lbr13-directory-append-repair-control
 :breaks nil
 :mutations ((directory-fault (:conclusion (fn-lbc-corr (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (fn-lbr13-extra-directory (create-fn-lbc)))) (list (fn-lbr13-held)) (fn-lbr13-single-log))) ((r13-control-token 0))
 :fault "a stray directory row shifts the resident ordinal after append" :lemma fn-lbr13-directory-mutation-witness)))

(with-prover-time-limit 15 (defthm fn-lbr13-payload-mutation-witness
 (and (let* ((row (fn-lbr13-held)) (rows (list row))
        (fresh (fn-lb-log-model-append row *fn-lbr13-payload* 2 nil))
        (good (append (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil) fresh))
        (bad (fn-lbr13-shadow-log))
        (fn-lbc (fn-lbc-open-rebuild rows fresh (create-fn-lbc)))
        (fn-arena (fn-arena-seal-list *fn-lbr13-payload* (create-fn-arena)))
        (after (fn-lb-log-model-recycle 1 good)))
  (and (fn-lbc-p fn-lbc) (fn-cat$ap rows)
       (fn-lbr13-old-log-model-segsp bad) (fn-lbr13-old-corr fn-lbc rows bad)
       (not (fn-lb-log-model-segsp bad)) (not (fn-lbc-corr fn-lbc rows bad))
       (fn-lb-log-model-segsp good) (fn-lbc-corr fn-lbc rows good)
       (fn-lb-arena-is-log fn-arena rows good)
       (fn-lb-log-model-segsp after) (fn-lbc-corr fn-lbc rows after)
       (fn-lb-arena-is-log fn-arena rows after))) (not (fn-lbc-corr (fn-lbr13-fresh-state) (list (fn-lbr13-held)) (fn-lbr13-shadow-log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-payload-observation-repair-control) (:instance fn-lbr13-shadow-corr-refused (fn-lbc (fn-lbr13-fresh-state)) (rows (list (fn-lbr13-held)))))
 :in-theory (theory 'minimal-theory)))))
(defteeth fn-lbr13-payload-observation-repair-control
 :claim (() (let* ((row (fn-lbr13-held)) (rows (list row))
        (fresh (fn-lb-log-model-append row *fn-lbr13-payload* 2 nil))
        (good (append (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil) fresh))
        (bad (fn-lbr13-shadow-log))
        (fn-lbc (fn-lbc-open-rebuild rows fresh (create-fn-lbc)))
        (fn-arena (fn-arena-seal-list *fn-lbr13-payload* (create-fn-arena)))
        (after (fn-lb-log-model-recycle 1 good)))
  (and (fn-lbc-p fn-lbc) (fn-cat$ap rows)
       (fn-lbr13-old-log-model-segsp bad) (fn-lbr13-old-corr fn-lbc rows bad)
       (not (fn-lb-log-model-segsp bad)) (not (fn-lbc-corr fn-lbc rows bad))
       (fn-lb-log-model-segsp good) (fn-lbc-corr fn-lbc rows good)
       (fn-lb-arena-is-log fn-arena rows good)
       (fn-lb-log-model-segsp after) (fn-lbc-corr fn-lbc rows after)
       (fn-lb-arena-is-log fn-arena rows after))))
 :subject fn-lb-log-model-recycle
 :witness ((r13-control-token 0)) :witness-lemma fn-lbr13-payload-observation-repair-control
 :breaks nil
 :mutations ((payload-fault (:conclusion (fn-lbc-corr (fn-lbr13-fresh-state) (list (fn-lbr13-held)) (fn-lbr13-shadow-log))) ((r13-control-token 0))
 :fault "the current copy semantic PAYLOAD is shadowed while its protected bytes remain intact" :lemma fn-lbr13-payload-mutation-witness)))
