; S9 scalar delta carried by the existing retire/install/scope reconstruction.
(in-package "ACL2")
(include-book "owner-feed-counts")

(defun fn-ofrc-retire-one (key peers tbl pending)
  (declare (xargs :guard (acl2-numberp pending)))
  (let ((entry (fn-own-feed-entry-of key tbl)))
    (if (and entry
             (fn-own-feed-idlep (fn-own-feed-entry-feed entry))
             (not (fn-own-feed-outboundp (fn-cfg-peer-find key peers))))
        (cons (fn-own-feed-forget key tbl)
              (- pending (fn-own-feed-pending-of (fn-own-feed-entry-feed entry))))
      (cons tbl pending))))

(defun fn-ofrc-retire (keys peers tbl pending)
  (declare (xargs :guard (acl2-numberp pending)))
  (if (consp keys)
      (let ((one (fn-ofrc-retire-one (car keys) peers tbl pending)))
        (fn-ofrc-retire (cdr keys) peers (car one) (cdr one)))
    (cons tbl pending)))

(defun fn-own-feed-reconfigure-counted (tbl peers pending)
  (declare (xargs :guard (acl2-numberp pending)))
  (let ((retired (fn-ofrc-retire (fn-own-feed-names tbl) peers tbl pending)))
    (cons (fn-own-feed-scope-all
           (fn-own-feed-install (fn-cfg-peer-names peers) peers (car retired)) peers)
          (cdr retired))))

(defthm fn-ofrc-retire-one-has-original-table
  (equal (car (fn-ofrc-retire-one key peers tbl pending))
         (fn-own-feed-retire-one key peers tbl))
  :hints (("Goal" :in-theory (e/d (fn-ofrc-retire-one fn-own-feed-retire-one fn-own-feed-find)
                                  (fn-own-feed-entry-of fn-own-feed-forget
                                   fn-own-feed-idlep fn-own-feed-outboundp fn-cfg-peer-find)))))

(defthm fn-ofrc-retire-has-original-table
  (equal (car (fn-ofrc-retire keys peers tbl pending))
         (fn-own-feed-retire keys peers tbl))
  :hints (("Goal" :induct (fn-ofrc-retire keys peers tbl pending)
           :in-theory (e/d (fn-ofrc-retire fn-own-feed-retire)
                           (fn-ofrc-retire-one fn-own-feed-retire-one)))))

(defthm fn-own-feed-reconfigure-counted-has-original-table
  (equal (car (fn-own-feed-reconfigure-counted tbl peers pending))
         (fn-own-feed-reconfigure tbl peers))
  :hints (("Goal" :in-theory (enable fn-own-feed-reconfigure-counted fn-own-feed-reconfigure))))

(defthm fn-ofrc-forget-has-exact-pending-delta
  (equal (fn-own-feed-table-pending-model (fn-own-feed-forget peer tbl))
         (- (fn-own-feed-table-pending-model tbl)
            (fn-own-feed-pending-of (fn-own-feed-find peer tbl))))
  :hints (("Goal" :induct (fn-own-feed-forget peer tbl)
           :in-theory (enable fn-own-feed-forget fn-own-feed-table-pending-model
                               fn-own-feed-find fn-own-feed-entry-of
                               fn-own-feed-pending-of fn-own-feed-entry-feed))))

(defthm fn-ofrc-retire-one-preserves-aggregate
  (implies (equal pending (fn-own-feed-table-pending-model tbl))
           (equal (cdr (fn-ofrc-retire-one key peers tbl pending))
                  (fn-own-feed-table-pending-model (car (fn-ofrc-retire-one key peers tbl pending)))))
  :hints (("Goal" :in-theory (e/d (fn-ofrc-retire-one fn-own-feed-find)
                                  (fn-own-feed-forget fn-own-feed-entry-of fn-ofrc-retire-one-has-original-table
                                   fn-own-feed-table-pending-model fn-own-feed-pending-of)))))

(defthm fn-ofrc-retire-preserves-aggregate
  (implies (equal pending (fn-own-feed-table-pending-model tbl))
           (equal (cdr (fn-ofrc-retire keys peers tbl pending))
                  (fn-own-feed-table-pending-model (car (fn-ofrc-retire keys peers tbl pending)))))
  :hints (("Goal" :induct (fn-ofrc-retire keys peers tbl pending)
           :in-theory (e/d (fn-ofrc-retire) (fn-ofrc-retire-one fn-own-feed-retire
                                           fn-ofrc-retire-has-original-table fn-ofrc-retire-one-has-original-table)))))

(defthm fn-ofrc-open-one-pending-zero
  (equal (fn-own-feed-pending-of (fn-own-feed-open-one record)) 0)
  :hints (("Goal" :in-theory (enable fn-own-feed-open-one fn-feed-open
                                     fn-own-feed-pending-of fn-feed-make-counted
                                     fn-feed-undelivered fn-feed-retry-dropped))))

(defthm fn-ofrc-install-one-preserves-pending
  (equal (fn-own-feed-table-pending-model (fn-own-feed-install-one name peers tbl))
         (fn-own-feed-table-pending-model tbl))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-install-one fn-own-feed-find fn-own-feed-pending-delta)
                                  (fn-own-feed-open-one fn-own-feed-table-pending-model
                                   fn-own-feed-put fn-own-feed-entry-of fn-own-feed-pending-of)))))

(defthm fn-ofrc-install-preserves-pending
  (equal (fn-own-feed-table-pending-model (fn-own-feed-install names peers tbl))
         (fn-own-feed-table-pending-model tbl))
  :hints (("Goal" :induct (fn-own-feed-install names peers tbl)
           :in-theory (enable fn-own-feed-install))))

(defthm fn-ofrc-scope-preserves-pending
  (equal (fn-own-feed-table-pending-model (fn-own-feed-scope-all tbl peers))
         (fn-own-feed-table-pending-model tbl))
  :hints (("Goal" :induct (len tbl)
           :in-theory (enable fn-own-feed-scope-all fn-own-feed-table-pending-model
                               fn-own-feed-entry-scoped fn-own-feed-entry fn-own-feed-entry-feed))))

(defthm fn-own-feed-reconfigure-counted-preserves-aggregate
  (implies (equal pending (fn-own-feed-table-pending-model tbl))
           (equal (cdr (fn-own-feed-reconfigure-counted tbl peers pending))
                  (fn-own-feed-table-pending-model
                   (car (fn-own-feed-reconfigure-counted tbl peers pending)))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-reconfigure-counted)
                                  (fn-ofrc-retire fn-ofrc-retire-has-original-table fn-ofrc-retire-one-has-original-table
                                   fn-own-feed-reconfigure-counted-has-original-table)))))

(defthm fn-ofrc-forget-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp (fn-own-feed-forget key tbl)))
  :hints (("Goal" :induct (fn-own-feed-forget key tbl)
           :in-theory (enable fn-own-feed-forget fn-ofct-table-relationp))))

(defthm fn-ofrc-retire-one-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp (car (fn-ofrc-retire-one key peers tbl pending))))
  :hints (("Goal" :in-theory (e/d (fn-ofrc-retire-one)
                                  (fn-ofrc-retire-one-has-original-table fn-own-feed-forget
                                   fn-ofct-table-relationp)))))

(defthm fn-ofrc-retire-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp (car (fn-ofrc-retire keys peers tbl pending))))
  :hints (("Goal" :induct (fn-ofrc-retire keys peers tbl pending)
           :in-theory (e/d (fn-ofrc-retire)
                            (fn-ofrc-retire-one fn-ofrc-retire-has-original-table
                             fn-ofrc-retire-one-has-original-table fn-ofct-table-relationp
                                   fn-own-feed-reconfigure-counted-has-original-table)))))

(defthm fn-ofrc-open-one-has-count-relation
  (implies (fn-own-feed-open-one record)
           (fn-feed-count-relationp (fn-own-feed-open-one record)))
  :hints (("Goal" :in-theory (enable fn-own-feed-open-one fn-feed-open
                                     fn-feed-count-relationp fn-feed-make-counted
                                     fn-feed-undelivered fn-feed-retry-dropped fn-feed-queue))))

(defthm fn-ofrc-install-one-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp (fn-own-feed-install-one name peers tbl)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-install-one fn-own-feed-find)
                                  (fn-own-feed-open-one fn-own-feed-put fn-own-feed-entry-of
                                   fn-ofct-table-relationp fn-feed-count-relationp)))))

(defthm fn-ofrc-install-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp (fn-own-feed-install names peers tbl)))
  :hints (("Goal" :induct (fn-own-feed-install names peers tbl)
           :in-theory (e/d (fn-own-feed-install)
                            (fn-own-feed-install-one fn-ofct-table-relationp)))))

(defthm fn-ofrc-scope-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp (fn-own-feed-scope-all tbl peers)))
  :hints (("Goal" :induct (len tbl)
           :in-theory (e/d (fn-own-feed-scope-all fn-ofct-table-relationp)
                            (fn-own-feed-entry-scoped fn-own-feed-entry-feed fn-feed-count-relationp)))))

(defthm fn-own-feed-reconfigure-counted-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp (car (fn-own-feed-reconfigure-counted tbl peers pending))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-reconfigure-counted)
                                  (fn-ofrc-retire fn-ofrc-retire-has-original-table
                                   fn-ofrc-retire-one-has-original-table fn-ofct-table-relationp
                                   fn-own-feed-reconfigure-counted-has-original-table)))))

(in-theory (disable fn-ofrc-retire-one fn-ofrc-retire fn-own-feed-reconfigure-counted))
