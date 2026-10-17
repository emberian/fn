; Props: views and access cache move together; field writes frame siblings.
; The physical reader-views key now carries the whole pair (D68, no old layout).
(in-package "ACL2")
(include-book "state-globals")
(include-book "acceptance-alloc")
(include-book "defrecord")
(fn-defrecord fn-ordr
  :constructor (fn-ordr-make views cache)
  :fields ((fn-ordr-views t) (fn-ordr-cache t)))
(defun fn-ordr-initial ()
  (declare (xargs :guard t))
  (fn-ordr-make nil nil))
(defun fn-ordr-get (field r)
  (declare (xargs :guard t))
  (case field (:views (fn-ordr-views r)) (:cache (fn-ordr-cache r)) (otherwise nil)))
(defun fn-ordr-put (field value r)
  (declare (xargs :guard t))
  (case field
    (:views (fn-ordr-make value (fn-ordr-cache r)))
    (:cache (fn-ordr-make (fn-ordr-views r) value))
    (otherwise r)))
(defthm fn-ordr-get-of-put
  (equal (fn-ordr-get field (fn-ordr-put key value r))
         (if (and (member-eq field '(:views :cache)) (equal field key))
             value (fn-ordr-get field r))))
(defthm fn-ordr-put-preserves-shape
  (implies (fn-ordr-shapep r) (fn-ordr-shapep (fn-ordr-put field value r))))

(defun fn-ordr-index-kind (r)
  (declare (xargs :guard t))
  (if (consp (fn-ordr-views r)) :d :current))
(defthm fn-ordr-index-kind-composition-by-definition
  (equal (fn-ordr-index-kind r)
         (if (consp (fn-ordr-views r)) :d :current)))
(defun fn-ost-readers (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-reader-views state)
      (f-get-global 'fn-owner-reader-views state)
    (fn-ordr-initial)))

(defun fn-ost-install-readers (r state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-reader-views r state))

(defthm fn-ost-readers-of-install
  (equal (fn-ost-readers (fn-ost-install-readers r state)) r))

(defthm fn-ost-readers-of-other-global-put
  (implies (not (equal key 'fn-owner-reader-views))
           (equal (fn-ost-readers (f-put-global key value state))
                  (fn-ost-readers state))))

(defthm fn-ost-install-readers-frames-get-global
  (implies (not (equal key 'fn-owner-reader-views))
           (equal (get-global key (fn-ost-install-readers r state))
                  (get-global key state))))

(defthm fn-ost-install-readers-frames-boundp-global
  (implies (not (equal key 'fn-owner-reader-views))
           (equal (boundp-global key (fn-ost-install-readers r state))
                  (boundp-global key state))))

(defthm fn-ost-install-readers-frames-global-association
  (implies (not (equal key 'fn-owner-reader-views))
           (equal (assoc-equal key (nth 2 (fn-ost-install-readers r state)))
                  (assoc-equal key (nth 2 state)))))

(defthm fn-ost-install-readers-preserves-state-p1
  (implies (state-p1 state) (state-p1 (fn-ost-install-readers r state)))
  :hints (("Goal" :in-theory (disable state-p1))))

(in-theory (disable fn-ost-readers fn-ost-install-readers))
