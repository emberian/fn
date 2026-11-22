; Selection from one retained, frame-verified journal member. The public
; view contains identity history and evidence. Storage references, grants,
; recipient indexes, overview lines and other colocated rows remain private.
(in-package "ACL2")
(include-book "journal-members")
(include-book "peer-view-pair")
(include-book "commit-geometry")
(fn2-book-layer :e)

(local (in-theory (disable fn2-fieldsp fn2-fields-wfp fn2-fields-rows
 fn2-fields-value fn2-fields-ref-off fn2-fields-ref-len fn2-pool-wfp
 fn2-journal-record-next fn2-format-record-header-decode)))

; Inspect one record of the current leaf. Return a body span only for
; an actual row of one of the two public identity schemas. Membership comes
; from the article's own overview row; an addressing row grants nothing.
(defun fn2-peer-view-record (stream event off end slot gen base kind owner generation fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :guard
                 (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (mbt (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)))
                    (posp stream) (posp event) (natp base)
                    (<= (+ base *fn2-journal-record-fields*) (fn2-fields-rows fn2-fields))
                    (natp off) (unsigned-byte-p 32 end) (< off end) (<= end *fn2-commit-unit-bytes*)))
       (mv :bounds 0 0 fn2-fields))
      ((mv c next ev rkind fn2-fields)
       (fn2-journal-record-next base slot gen off end kind owner generation fn2-fields fn2-pool))
      ((unless (and (eq c :record) (equal ev event) (natp next) (< off next) (<= next end)))
       (mv :invalid 0 0 fn2-fields))
      ((when (equal rkind *record-kind-overview*))
       (mv (if (and (equal stream (fn2-fields-value (+ base *fn2-overview-entry-field-group*) fn2-fields))
                    (equal event (fn2-fields-value (+ base *fn2-overview-entry-field-article*) fn2-fields))
                    (equal event (fn2-fields-value (+ base *fn2-overview-entry-field-position*) fn2-fields)))
               :membership :private) next 0 fn2-fields))
      (history (equal rkind *record-kind-identity-history*))
      (evidence (equal rkind *record-kind-identity-evidence*))
      ((unless (or history evidence)) (mv :private next 0 fn2-fields))
      ; Local POST binds history, evidence and article in this member to
      ; this one event. Other provenance needs its own import dependency walk.
      (joint (if history
                 (and (equal event (fn2-fields-value (+ base *fn2-identity-history-entry-field-position*) fn2-fields))
                      (equal event (fn2-fields-value (+ base *fn2-identity-history-entry-field-evidence*) fn2-fields))
                      (equal event (fn2-fields-value (+ base *fn2-identity-history-entry-field-article*) fn2-fields)))
               (and (equal event (fn2-fields-value (+ base *fn2-identity-evidence-entry-field-occurrence*) fn2-fields))
                    (equal *fn2-identity-evidence-kind-binding*
                           (fn2-fields-value (+ base *fn2-identity-evidence-entry-field-kind*) fn2-fields)))))
      ((unless joint) (mv :other-identity next 0 fn2-fields))
      ((mv hc body fn2-fields)
       (fn2-format-record-header-decode base slot gen off next kind owner generation fn2-fields fn2-pool)))
  (if (and (eq hc :ok) (natp body) (< off body) (< body next))
      (mv (if history :history :evidence) next body fn2-fields)
    (mv :invalid 0 0 fn2-fields))))
(fn2-fields-preserves fn2-peer-view-record
 (stream event off end slot gen base kind owner generation fn2-fields fn2-pool) :position 3)

(defun fn2-peer-view-pair (event hs he es ee slot gen base kind owner generation fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :guard
                 (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (mbt (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)))
                    (posp event) (natp base)
                    (<= (+ base *fn2-identity-history-entry-num-fields* *fn2-identity-evidence-entry-num-fields*)
                        (fn2-fields-rows fn2-fields))
                    (natp hs) (natp he) (< hs he) (<= he *fn2-commit-unit-bytes*)
                    (natp es) (natp ee) (< es ee) (<= ee *fn2-commit-unit-bytes*)
                    (or (<= he es) (<= ee hs))))
       (mv :bounds fn2-fields))
      (h base) (e (+ h *fn2-identity-history-entry-num-fields*))
      ((mv hc hn fn2-fields)
       (fn2-identity-history-entry-decode h slot gen hs he kind owner generation fn2-fields fn2-pool))
      ((unless (and (eq hc :ok) (equal hn he))) (mv :history-format fn2-fields))
      ((mv ec en fn2-fields)
       (fn2-identity-evidence-entry-decode e slot gen es ee kind owner generation fn2-fields fn2-pool))
      ((unless (and (eq ec :ok) (equal en ee))) (mv :evidence-format fn2-fields))
      (match (and (fn2-peer-view-pair-identity-p h e slot gen kind owner generation fn2-fields fn2-pool)
                  (equal event (fn2-fields-value (+ h *fn2-identity-history-entry-field-position*) fn2-fields))
                  (equal event (fn2-fields-value (+ h *fn2-identity-history-entry-field-evidence*) fn2-fields))
                  (equal event (fn2-fields-value (+ h *fn2-identity-history-entry-field-article*) fn2-fields)))))
  (mv (if match :ok :identity) fn2-fields)))
(fn2-fields-preserves fn2-peer-view-pair
 (event hs he es ee slot gen base kind owner generation fn2-fields fn2-pool) :position 1)
