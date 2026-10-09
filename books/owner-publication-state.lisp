; Ten fields, one publication/reclaim authority, independent of ACL2 state.
; Props: all observations and writes of a publication decision use this same
; record. The slot setter frames every unrelated global. Its default is the
; ten absent old globals, all nil. Recovery preserves serial (see transitions).
(in-package "ACL2")
(include-book "state-globals")

(defun fn-opub-initial ()
  (declare (xargs :guard t))
  (list nil nil nil nil nil nil nil nil nil nil))

(defun fn-opub-recordp (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 10)))

(defun fn-opub-index (field)
  (declare (xargs :guard t))
  (case field
    (:attempted 0) (:base 1) (:base-payloads 2) (:deferred 3) (:durable 4)
    (:inflight 5) (:pending 6) (:requested 7) (:serial 8) (:pass 9)
    (otherwise nil)))

(defun fn-opub-get (field r)
  (declare (xargs :guard t))
  (let ((i (fn-opub-index field)))
    (and i (nth i (if (true-listp r) r nil)))))

(defun fn-opub-put (field v r)
  (declare (xargs :guard t))
  (let ((i (fn-opub-index field)))
    (if i (update-nth i v (if (true-listp r) r nil)) r)))

(defthm fn-opub-get-of-put
  (equal (fn-opub-get field (fn-opub-put key v r))
         (if (and (fn-opub-index field) (equal field key)) v (fn-opub-get field r)))
  :hints (("Goal" :in-theory (e/d (nth-update-nth) (nth update-nth)))))

(defthm fn-opub-put-preserves-record
  (implies (fn-opub-recordp r) (fn-opub-recordp (fn-opub-put key v r))))

(defun fn-ost-publication (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-publication state)
      (f-get-global 'fn-owner-publication state)
    (fn-opub-initial)))

(defun fn-ost-install-publication (r state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-publication r state))

(defthm fn-ost-publication-of-install
  (equal (fn-ost-publication (fn-ost-install-publication r state)) r))

(defthm fn-ost-publication-of-other-global-put
  (implies (not (equal key 'fn-owner-publication))
           (equal (fn-ost-publication (f-put-global key v state))
                  (fn-ost-publication state))))

(defthm fn-ost-install-publication-frames-global-association
  (implies (not (equal key 'fn-owner-publication))
           (equal (assoc-equal key (nth 2 (fn-ost-install-publication r state)))
                  (assoc-equal key (nth 2 state)))))

; Export at the global-reader boundary: downstream minimal theories keep
; GET-GLOBAL opaque, so the association rule alone cannot frame their reads.
(defthm fn-ost-install-publication-frames-get-global
  (implies (not (equal key 'fn-owner-publication))
           (equal (get-global key (fn-ost-install-publication r state))
                  (get-global key state))))

(defthm fn-ost-install-publication-frames-boundp-global
  (implies (not (equal key 'fn-owner-publication))
           (equal (boundp-global key (fn-ost-install-publication r state))
                  (boundp-global key state))))

(defthm fn-ost-install-publication-preserves-state-p1
  (implies (state-p1 state)
           (state-p1 (fn-ost-install-publication r state)))
  :hints (("Goal" :in-theory (disable state-p1))))

(in-theory (disable fn-ost-publication fn-ost-install-publication))
