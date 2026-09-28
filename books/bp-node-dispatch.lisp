; Exact durable received-carrier dispatch update.  The one held list is
; shared by live publication and ordered FNBS replay.
(in-package "ACL2")
(include-book "bp-node-fragment-replacement")
(include-book "bp-fnbs-dispatch-codec")
(set-verify-guards-eagerness 0)

(defun fn-bpnp-dispatched-held (h peer)
  (declare (xargs :guard t))
  (if (true-listp h)
      (update-nth 12 '(:forward-pending)
                  (update-nth 11 peer
                              (update-nth 10 '(:dispatched :forward) h)))
    h))

(defun fn-bpnp-dispatch-matches-heldp (record h)
  (declare (xargs :guard t))
  (and (fn-bpnp-dispatch-recordp record)
       (equal (fn-bpn-nth 0 h) :bpnf-held)
       (equal (fn-bpn-nth 3 record) (fn-bpn-nth 3 h))
       (equal (fn-bpn-nth 4 record)
              (fn-bpah-held-primary-identity h))
       (null (fn-bpn-nth 10 h))
       (equal (fn-bpn-nth 12 h) '(:dispatch-pending))
       (null (fn-bpn-nth 13 h))
       (null (fn-bpn-nth 14 h))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-bpnp-replace-dispatched-loop (arrival peer held acc)
  (declare (xargs :measure (acl2-count held) :guard (true-listp acc) :verify-guards nil))
  (if (atom held)
      (revappend acc nil)
    (if (equal arrival (fn-bpn-nth 3 (car held)))
        (revappend acc (cons (fn-bpnp-dispatched-held (car held) peer) (cdr held)))
      (fn-bpnp-replace-dispatched-loop arrival peer (cdr held) (cons (car held) acc)))))

(defun fn-bpnp-replace-dispatched (arrival peer held)
  (declare (xargs :verify-guards nil :guard t :measure (acl2-count held)))
  (mbe :logic
       (if (atom held) nil
         (if (equal arrival (fn-bpn-nth 3 (car held)))
             (cons (fn-bpnp-dispatched-held (car held) peer) (cdr held))
           (cons (car held)
                 (fn-bpnp-replace-dispatched arrival peer (cdr held)))))
       :exec (fn-bpnp-replace-dispatched-loop arrival peer held nil)))

(local
 (defthm fn-bpnp-replace-dispatched-loop-is-revappend
   (equal (fn-bpnp-replace-dispatched-loop arrival peer held acc)
          (revappend acc (fn-bpnp-replace-dispatched arrival peer held)))
   :hints (("Goal" :induct (fn-bpnp-replace-dispatched-loop arrival peer held acc)
                   :in-theory (union-theories '(fn-bpnp-replace-dispatched-loop fn-bpnp-replace-dispatched revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-bpnp-replace-dispatched-loop)

(verify-guards fn-bpnp-replace-dispatched
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-bpnp-replace-dispatched)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-bpnp-replace-dispatched-loop-is-revappend (acc nil))))))


(defun fn-bpnp-dispatch-apply (record held)
  (declare (xargs :guard t))
  (let* ((arrival (fn-bpn-nth 3 record))
         (h (fn-bpnf-find-arrival arrival held)))
    (if (and (equal (fn-bpnf-arrival-count arrival held) 1)
             (fn-bpnp-dispatch-matches-heldp record h))
        (list :ready
              (fn-bpnp-replace-dispatched
               arrival (fn-bpn-nth 5 record) held)
              (fn-bpnp-dispatched-held h (fn-bpn-nth 5 record)))
      (list :fault :dispatch-row))))
