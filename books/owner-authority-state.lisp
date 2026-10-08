; Three authority observations move atomically; readiness is never invented.
; Props: nil initial observations; field updates frame the other two fields;
; slot installation frames every unrelated global and preserves state-p1.
; The former canonical scalar's physical key now holds this whole record.
; No old layout is accepted or migrated (D68); the slot becomes a stobj at S6.
(in-package "ACL2")
(include-book "state-globals")
(include-book "acceptance-alloc")
(include-book "defrecord")

(fn-defrecord fn-oauth
  :constructor (fn-oauth-make carries root canonical)
  :fields ((fn-oauth-carries t) (fn-oauth-root t) (fn-oauth-canonical t)))

(defun fn-oauth-initial ()
  (declare (xargs :guard t))
  (fn-oauth-make nil nil nil))

(defun fn-oauth-get (field r)
  (declare (xargs :guard t))
  (case field
    (:carries (fn-oauth-carries r))
    (:root (fn-oauth-root r))
    (:canonical (fn-oauth-canonical r))
    (otherwise nil)))

(defun fn-oauth-put (field value r)
  (declare (xargs :guard t))
  (case field
    (:carries (fn-oauth-make value (fn-oauth-root r) (fn-oauth-canonical r)))
    (:root (fn-oauth-make (fn-oauth-carries r) value (fn-oauth-canonical r)))
    (:canonical (fn-oauth-make (fn-oauth-carries r) (fn-oauth-root r) value))
    (otherwise r)))

(defthm fn-oauth-get-of-put
  (equal (fn-oauth-get field (fn-oauth-put key value r))
         (if (and (member-eq field '(:carries :root :canonical)) (equal field key))
             value (fn-oauth-get field r))))

(defthm fn-oauth-put-preserves-shape
  (implies (fn-oauth-shapep r) (fn-oauth-shapep (fn-oauth-put field value r))))

(defun fn-ost-authority (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-canonical-state state)
      (f-get-global 'fn-owner-canonical-state state)
    (fn-oauth-initial)))

(defun fn-ost-install-authority (r state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-canonical-state r state))

(defthm fn-ost-authority-of-install
  (equal (fn-ost-authority (fn-ost-install-authority r state)) r))

(defthm fn-ost-authority-of-other-global-put
  (implies (not (equal key 'fn-owner-canonical-state))
           (equal (fn-ost-authority (f-put-global key value state))
                  (fn-ost-authority state))))

(defthm fn-ost-install-authority-frames-get-global
  (implies (not (equal key 'fn-owner-canonical-state))
           (equal (get-global key (fn-ost-install-authority r state))
                  (get-global key state))))

(defthm fn-ost-install-authority-frames-boundp-global
  (implies (not (equal key 'fn-owner-canonical-state))
           (equal (boundp-global key (fn-ost-install-authority r state))
                  (boundp-global key state))))

(defthm fn-ost-install-authority-frames-global-association
  (implies (not (equal key 'fn-owner-canonical-state))
           (equal (assoc-equal key (nth 2 (fn-ost-install-authority r state)))
                  (assoc-equal key (nth 2 state)))))

(defthm fn-ost-install-authority-preserves-state-p1
  (implies (state-p1 state) (state-p1 (fn-ost-install-authority r state)))
  :hints (("Goal" :in-theory (disable state-p1))))

(in-theory (disable fn-ost-authority fn-ost-install-authority))
