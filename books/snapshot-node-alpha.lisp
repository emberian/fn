; PRF-1115: node payload abstraction for canonical snapshot recovery.
; Two arenas may name the same retained bytes with different natural handles.
(in-package "ACL2")
(include-book "node-invariants")
(include-book "stx-node-lace")
(local (in-theory (disable (tau-system))))

; The complete node abstraction retains every acceptance/retention field.
; It substitutes referenced payload bytes only at the two handle positions;
; memberships, stamps, archive bindings and pending retention stay literal.
(defun fn-osa-pending-alpha (pending fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp pending)
      (list (fn-pending-txid pending) (fn-pending-generation pending)
            (fn-pending-msgid pending)
            (fn-handle-bytes (fn-pending-payload pending) fn-arena)
            (fn-pending-groups pending) (fn-pending-memberships pending)
            (fn-pending-pin pending) (fn-pending-stamp pending))
    pending))
(defun fn-osa-acceptance-alpha (acceptance fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (list (fn-state-groups acceptance) (fn-state-nexts acceptance)
        (fn-articles-wire-of (fn-state-articles acceptance) fn-arena)
        (fn-state-next-txid acceptance)
        (fn-osa-pending-alpha (fn-state-pending acceptance) fn-arena)
        (fn-state-fenced acceptance)))
(defun fn-osa-node-alpha (node fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (list (fn-osa-acceptance-alpha (fn-node-acceptance node) fn-arena)
        (fn-node-retention node) (fn-node-stage node)
        (fn-node-bindings node)))

(defthm fn-osa-pending-alpha-preserves-presence
  (equal (consp (fn-osa-pending-alpha pending fn-arena)) (consp pending))
  :hints (("Goal" :in-theory (enable fn-osa-pending-alpha))))

(defthm fn-osa-acceptedp-over-article-alpha
  (equal (fn-acceptedp msgid (fn-articles-wire-of articles fn-arena))
         (fn-acceptedp msgid articles))
  :hints (("Goal" :induct (len articles)
           :in-theory (e/d (fn-acceptedp fn-articles-wire-of)
                           (fn-handle-bytes)))))

(defthm fn-osa-prepare-keeps-acceptance-alpha
  (implies (and (fn-statep a) (fn-statep b)
                (equal (fn-osa-acceptance-alpha a source)
                       (fn-osa-acceptance-alpha b target))
                (natp p) (natp q)
                (equal (fn-handle-bytes p source) (fn-handle-bytes q target)))
           (equal (fn-osa-acceptance-alpha
                   (fn-accept-prepare a generation msgid p groups stamp) source)
                  (fn-osa-acceptance-alpha
                   (fn-accept-prepare b generation msgid q groups stamp) target)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-osa-acceptedp-over-article-alpha
                            (articles (fn-state-articles a)) (fn-arena source))
                 (:instance fn-osa-acceptedp-over-article-alpha
                            (articles (fn-state-articles b)) (fn-arena target)))
           :in-theory (e/d (fn-osa-acceptance-alpha fn-osa-pending-alpha
                            fn-accept-prepare)
                           (fn-osa-acceptedp-over-article-alpha
                            fn-statep fn-acceptedp fn-handle-bytes
                            fn-articles-wire-of fn-selection-validp
                            fn-allocate-memberships fn-record-stampp
                            fn-make-state fn-make-pending)))))

(in-theory (disable fn-osa-pending-alpha fn-osa-acceptance-alpha fn-osa-node-alpha))

(defthm fn-osa-complete-keeps-acceptance-alpha
  (implies (and (fn-statep a) (fn-statep b)
                (equal (fn-osa-acceptance-alpha a source)
                       (fn-osa-acceptance-alpha b target)))
           (equal (fn-osa-acceptance-alpha
                   (fn-accept-complete a txid generation status) source)
                  (fn-osa-acceptance-alpha
                   (fn-accept-complete b txid generation status) target)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-osa-acceptance-alpha fn-osa-pending-alpha
                            fn-accept-complete fn-pending-matchesp
                            fn-install-pending fn-clear-pending
                            fn-article-from-pending fn-articles-wire-of)
                           (fn-statep fn-handle-bytes fn-advance-nexts
                            fn-make-state fn-make-pending fn-make-article)))))

(local
 (defthm fn-osa-prepare-noop-is-its-actual-refusal
   (implies (fn-statep s)
            (equal (equal (fn-accept-prepare s generation msgid payload groups stamp) s)
                   (or (equal (fn-state-fenced s) t)
                       (consp (fn-state-pending s))
                       (not (natp generation)) (not (stringp msgid))
                       (not (natp payload)) (not (fn-record-stampp stamp))
                       (not (fn-selection-validp groups (fn-state-groups s)))
                       (fn-acceptedp msgid (fn-state-articles s)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-accept-prepare)
                            (fn-statep fn-acceptedp fn-selection-validp
                             fn-record-stampp fn-make-state fn-make-pending))))))
(local
 (defthm fn-osa-node-valid-implies-acceptance-valid
   (implies (fn-node-statep node) (fn-statep (fn-node-acceptance node)))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

(defthm fn-osa-prepare-keeps-full-node-alpha
  (implies (and (fn-node-statep a) (fn-node-statep b)
                (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
                (natp p) (natp q)
                (equal (fn-handle-bytes p source) (fn-handle-bytes q target)))
           (equal (fn-osa-node-alpha
                   (fn-node-prepare a generation msgid p groups id subject evidence charge stamp)
                   source)
                  (fn-osa-node-alpha
                   (fn-node-prepare b generation msgid q groups id subject evidence charge stamp)
                   target)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-osa-prepare-keeps-acceptance-alpha
                            (a (fn-node-acceptance a)) (b (fn-node-acceptance b)))
                 (:instance fn-osa-acceptedp-over-article-alpha
                            (articles (fn-state-articles (fn-node-acceptance a)))
                            (fn-arena source))
                 (:instance fn-osa-acceptedp-over-article-alpha
                            (articles (fn-state-articles (fn-node-acceptance b)))
                            (fn-arena target)))
           :in-theory (e/d (fn-osa-node-alpha fn-osa-acceptance-alpha
                            fn-osa-pending-alpha fn-node-prepare)
                           (fn-osa-acceptedp-over-article-alpha fn-accept-prepare
                            fn-node-statep fn-statep fn-retain-admissiblep
                            fn-retain-admit fn-node-make-state fn-node-make-stage
                            fn-handle-bytes fn-articles-wire-of fn-acceptedp
                            fn-selection-validp fn-record-stampp)))))

(defthm fn-osa-complete-keeps-full-node-alpha
  (implies (and (fn-node-statep a) (fn-node-statep b)
                (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target)))
           (equal (fn-osa-node-alpha (fn-node-complete a txid generation status) source)
                  (fn-osa-node-alpha (fn-node-complete b txid generation status) target)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-osa-node-valid-implies-acceptance-valid (node a))
                 (:instance fn-osa-node-valid-implies-acceptance-valid (node b))
                 (:instance fn-osa-complete-keeps-acceptance-alpha
                            (a (fn-node-acceptance a)) (b (fn-node-acceptance b)))
                 (:instance fn-osa-complete-keeps-acceptance-alpha
                            (a (fn-node-acceptance a)) (b (fn-node-acceptance b))
                            (status :durable))
                 (:instance fn-osa-complete-keeps-acceptance-alpha
                            (a (fn-node-acceptance a)) (b (fn-node-acceptance b))
                            (status :aborted))
                 (:instance fn-osa-complete-keeps-acceptance-alpha
                            (a (fn-node-acceptance a)) (b (fn-node-acceptance b))
                            (status :indeterminate)))
           :in-theory (e/d (fn-osa-node-alpha fn-osa-acceptance-alpha
                            fn-osa-pending-alpha fn-node-complete
                            fn-node-pending-matchesp fn-pending-matchesp)
                           (fn-node-statep fn-accept-complete fn-statep fn-retain-statep
                            fn-node-binding-listp fn-subsetp fn-article-msgids
                            fn-node-articles-have-archive-bindingsp fn-node-stagep
                            fn-node-make-state fn-handle-bytes fn-articles-wire-of)))))
