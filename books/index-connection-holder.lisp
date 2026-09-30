; Connection identity is not an allocation address. Native connections retain
; this opaque issued token alongside the logical connection id. The parent
; issuer spends a PRL identity and selects a separately recycled physical slot.
; These INTERNAL segment operations neither admit a grant nor prove that a
; supplied pin came from the owner's selected view: the composed producer does.
(in-package "ACL2")
(include-book "snapshot-source-token")

(defun fn-ich-tokenp (token)
  (declare (xargs :guard t))
  (and (fn-omk-widthp token 4)
       (eq (fn-omk-at 0 token) :connection-holder)
       (posp (fn-omk-at 1 token)) (posp (fn-omk-at 2 token))
       (natp (fn-omk-at 3 token)) (< (fn-omk-at 3 token) 64)))

(defstobj fn-ibp-connection-segment
  (fn-ich-rows :type (array t (64)) :initially nil)
  (fn-ich-segment-id :type (integer 0 *) :initially 0)
  (fn-ich-active :type (integer 0 64) :initially 0)
  :inline t)

; Fixed7: tag, token, actual logical connection id, retained publication pin,
; phase, capacity grant, independent reader aliases. Alias changes are ONLY
; coupled to the once-only request registry transitions, never a host counter.
(defun fn-ich-row (token fn-ibp-connection-segment)
  (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
  (if (and (fn-ich-tokenp token)
           (equal (fn-omk-at 2 token)
                  (fn-ich-segment-id fn-ibp-connection-segment)))
      (let ((row (fn-ich-rowsi (fn-omk-at 3 token)
                              fn-ibp-connection-segment)))
        (if (and (fn-omk-widthp row 7)
                 (eq (fn-omk-at 0 row) :connection-holder)
                 (equal (fn-omk-at 1 row) token)) row nil))
    nil))

(defun fn-ich-reserve (token id grant fn-ibp-connection-segment)
  (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
  (if (not (and (fn-ich-tokenp token) (natp id) grant
                (equal (fn-omk-at 2 token)
                       (fn-ich-segment-id fn-ibp-connection-segment))
                (< (fn-ich-active fn-ibp-connection-segment) 64)))
      (mv :refused fn-ibp-connection-segment)
    (let* ((slot (fn-omk-at 3 token))
           (old (fn-ich-rowsi slot fn-ibp-connection-segment))
           (old-token (fn-omk-at 1 old)))
      (if (or (and old
                   (not (and (fn-omk-widthp old 7)
                             (eq (fn-omk-at 0 old) :connection-holder)
                             (eq (fn-omk-at 4 old) :released)
                             (null (fn-omk-at 3 old))
                             (null (fn-omk-at 5 old))
                             (equal (fn-omk-at 6 old) 0)
                             (fn-ich-tokenp old-token)
                             (equal (fn-omk-at 2 old-token) (fn-omk-at 2 token))
                             (equal (fn-omk-at 3 old-token) slot))))
              (and (fn-ich-tokenp old-token)
                   (<= (fn-omk-at 1 token) (fn-omk-at 1 old-token))))
          (mv :stale fn-ibp-connection-segment)
        (let* ((fn-ibp-connection-segment
                (update-fn-ich-rowsi slot
                  (list :connection-holder token id nil :reserved grant 0)
                  fn-ibp-connection-segment))
               (fn-ibp-connection-segment
                (update-fn-ich-active
                  (+ 1 (fn-ich-active fn-ibp-connection-segment))
                  fn-ibp-connection-segment)))
          (mv :reserved fn-ibp-connection-segment))))))

; PIN is the SAME value returned by successful generation :retain/:pin.
; A reserved row must survive any later failure until that reference and its
; capacity have been settled; a repeated attach cannot acquire another pin.
(defun fn-ich-attach (token pin fn-ibp-connection-segment)
  (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
  (let ((row (fn-ich-row token fn-ibp-connection-segment)))
    (if (not (and (fn-ich-tokenp token) pin
                  (eq (fn-omk-at 4 row) :reserved)))
        (mv :stale fn-ibp-connection-segment)
      (let ((fn-ibp-connection-segment
             (update-fn-ich-rowsi (fn-omk-at 3 token)
               (list :connection-holder token (fn-omk-at 2 row) pin
                     :live (fn-omk-at 5 row) 0)
               fn-ibp-connection-segment)))
        (mv :attached fn-ibp-connection-segment)))))

(defun fn-ich-row-source (id row)
  (declare (xargs :guard t))
  (if (and (natp id) (equal id (fn-omk-at 2 row))
           (eq (fn-omk-at 4 row) :live) (fn-omk-at 3 row))
      (mv :current (fn-omk-at 3 row))
    (mv :stale nil)))
(defun fn-ich-source (id token fn-ibp-connection-segment)
  (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
  (fn-ich-row-source id (fn-ich-row token fn-ibp-connection-segment)))

; Acquiring a borrower is coupled to the request registry's unique transition.
; A return is coupled to its delta1 completion, so duplicate request completion
; cannot decrement a second alias. :closing retains both pin and grant.
(defun fn-ich-alias (token operation fn-ibp-connection-segment)
  (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
  (let* ((row (fn-ich-row token fn-ibp-connection-segment))
         (phase (fn-omk-at 4 row)) (aliases (fn-omk-at 6 row)))
    (if (not (and (fn-ich-tokenp token) (natp aliases)
                  (or (and (eq operation :acquire) (eq phase :live))
                      (and (eq operation :return) (posp aliases)
                           (member-eq phase '(:live :closing))))))
        (mv :stale fn-ibp-connection-segment)
      (let ((fn-ibp-connection-segment
             (update-fn-ich-rowsi (fn-omk-at 3 token)
               (list :connection-holder token (fn-omk-at 2 row)
                     (fn-omk-at 3 row) phase (fn-omk-at 5 row)
                     (if (eq operation :acquire) (+ aliases 1) (- aliases 1)))
               fn-ibp-connection-segment)))
        (mv (if (eq operation :acquire) :acquired :returned)
            fn-ibp-connection-segment)))))

(defun fn-ich-close (id token fn-ibp-connection-segment)
  (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
  (let ((row (fn-ich-row token fn-ibp-connection-segment)))
    (cond
     ((not (and (fn-ich-tokenp token) (natp id)
                (equal id (fn-omk-at 2 row))
                (member-eq (fn-omk-at 4 row) '(:reserved :live :closing))))
      (mv :stale fn-ibp-connection-segment))
     ((eq (fn-omk-at 4 row) :closing)
      (mv :closing fn-ibp-connection-segment))
     (t (let ((fn-ibp-connection-segment
               (update-fn-ich-rowsi (fn-omk-at 3 token)
                 (list :connection-holder token id (fn-omk-at 3 row)
                       :closing (fn-omk-at 5 row) (fn-omk-at 6 row))
                 fn-ibp-connection-segment)))
          (mv :closing fn-ibp-connection-segment))))))

; Readonly retirement preflight. Do NOT drop the generation reference before
; this result: an unjoined alias still needs it even after logical close.
(defun fn-ich-row-release-ready (row)
  (declare (xargs :guard t))
  (cond ((not (eq (fn-omk-at 4 row) :closing)) (mv :stale nil nil))
        ((not (equal (fn-omk-at 6 row) 0)) (mv :held nil nil))
        (t (mv :ready (fn-omk-at 3 row) (fn-omk-at 5 row)))))
(defun fn-ich-release-ready (token fn-ibp-connection-segment)
  (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
  (fn-ich-row-release-ready (fn-ich-row token fn-ibp-connection-segment)))

; INTERNAL final substep only after the actual generation reference was dropped
; (or no pin was attached) in the SAME serialized transition. No host :joined
; assertion is accepted. The parent refunds the returned grant exactly once.
(defun fn-ich-release-finish (token fn-ibp-connection-segment)
  (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
  (mv-let (status pin grant)
    (fn-ich-release-ready token fn-ibp-connection-segment)
    (declare (ignore pin))
    (if (not (and (eq status :ready) (fn-ich-tokenp token)
                  (< 0 (fn-ich-active fn-ibp-connection-segment))))
        (mv :stale nil fn-ibp-connection-segment)
      (let* ((fn-ibp-connection-segment
              (update-fn-ich-rowsi (fn-omk-at 3 token)
                (list :connection-holder token nil nil :released nil 0)
                fn-ibp-connection-segment))
             (fn-ibp-connection-segment
              (update-fn-ich-active
                (- (fn-ich-active fn-ibp-connection-segment) 1)
                fn-ibp-connection-segment)))
        (mv :released grant fn-ibp-connection-segment)))))

(defthm fn-ich-unregistered-token-cannot-change-segment
  (implies (not (fn-ich-row token fn-ibp-connection-segment))
    (and
     (equal (fn-ich-attach token pin fn-ibp-connection-segment)
            (mv :stale fn-ibp-connection-segment))
     (equal (fn-ich-alias token op fn-ibp-connection-segment)
            (mv :stale fn-ibp-connection-segment))
     (equal (fn-ich-close id token fn-ibp-connection-segment)
            (mv :stale fn-ibp-connection-segment))
     (equal (fn-ich-release-finish token fn-ibp-connection-segment)
            (mv :stale nil fn-ibp-connection-segment))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-ich-attach fn-ich-alias fn-ich-close
                 fn-ich-release-finish fn-ich-release-ready
                 fn-ich-row-release-ready fn-omk-at)
                (fn-ich-row fn-ich-tokenp)))))
