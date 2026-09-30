; P2 query's fixed control state. The captured operational source/rows belong
; to its provider ticket; this record never copies backing or retained rows.
(in-package "ACL2")
(include-book "acceptance-alloc")
(include-book "defrecord")

(fn-defrecord fn-miq
  :tag :fn-miq
  :constructor (fn-miq-make ticket generation key count frontier pages msgid tag
                            cursor pending best phase)
  :fields ((fn-miq-ticket t) (fn-miq-generation t) (fn-miq-key t)
           (fn-miq-count t) (fn-miq-frontier t) (fn-miq-pages t)
           (fn-miq-msgid t) (fn-miq-tag t) (fn-miq-cursor t)
           (fn-miq-pending t) (fn-miq-best t) (fn-miq-phase t))
  :recognizer nil)

(defun fn-miq-with-progress (query cursor pending best phase)
  (declare (xargs :guard t))
  (fn-miq-make (fn-miq-ticket query) (fn-miq-generation query)
               (fn-miq-key query) (fn-miq-count query) (fn-miq-frontier query)
               (fn-miq-pages query) (fn-miq-msgid query) (fn-miq-tag query)
               cursor pending best phase))

; No status other than complete may publish the accumulated selection.
(defun fn-miq-answer (query)
  (declare (xargs :guard t))
  (and (equal (fn-miq-phase query) :done) (fn-miq-best query)))

(defthm fn-miq-incomplete-publishes-no-answer
  (implies (not (equal (fn-miq-phase query) :done))
           (equal (fn-miq-answer query) nil)))

(defthm fn-miq-progress-keeps-capture
  (let ((next (fn-miq-with-progress query cursor pending best phase)))
    (and (equal (fn-miq-ticket next) (fn-miq-ticket query))
         (equal (fn-miq-generation next) (fn-miq-generation query))
         (equal (fn-miq-key next) (fn-miq-key query))
         (equal (fn-miq-count next) (fn-miq-count query))
         (equal (fn-miq-frontier next) (fn-miq-frontier query))
         (equal (fn-miq-pages next) (fn-miq-pages query))
         (equal (fn-miq-msgid next) (fn-miq-msgid query))
         (equal (fn-miq-tag next) (fn-miq-tag query))))
  :hints (("Goal" :in-theory (enable fn-miq-with-progress))))

; Both record observations must come from the one held row returned by the
; captured provider. A caller cannot submit a Boolean for exact identity.
(defun fn-miq-confirm (query ordinal record-seq record-msgid)
  (declare (xargs :guard t))
  (if (not (and (equal (fn-miq-phase query) :candidate)
                (equal (fn-miq-pending query) ordinal)
                (natp ordinal) (natp (fn-miq-count query))
                (< ordinal (fn-miq-count query))
                (natp record-seq) (natp (fn-miq-frontier query))
                (< record-seq (fn-miq-frontier query))
                (or (null (fn-miq-best query))
                    (natp (fn-miq-best query)))))
      (mv :recovery-required query)
    (let* ((best (fn-miq-best query))
           (best1 (if (and (equal record-msgid (fn-miq-msgid query))
                           (or (null best) (< ordinal best))) ordinal best)))
      (mv :continue
          (fn-miq-with-progress query (fn-miq-cursor query) nil best1 :probing)))))
