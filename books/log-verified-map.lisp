; LB4: verification belongs to a segment incarnation and served byte offset,
; never to an article handle or a payload-window cache.  LC does not reuse
; segment identifiers.  Recycle removes every bit of the victim identifier.
(in-package "ACL2")
(include-book "lb-log-model")
(include-book "log-locator")

(defstobj fn-lb-vmap
  (fn-lb-vmap-bits :type (hash-table equal))
  (fn-lb-vmap-index :type t :initially nil)
  :renaming ((fn-lb-vmapp fn-lb-vmap-p)))

; Logical field positions of the declared two-field stobj.  These are
; representation addresses, not limits on stored segment identifiers.
(defconst *fn-lb-vmap-bits* 0)
(defconst *fn-lb-vmap-index* 1)

(defun fn-lb-verified-bit (seg entry fn-lb-vmap)
  (declare (xargs :stobjs fn-lb-vmap :guard t))
  (equal (fn-lb-vmap-bits-get (cons seg entry) fn-lb-vmap) t))

(defun fn-lb-verified-entries-invp (bits log)
  (declare (xargs :guard (and (fn-lb-log-read-guardp log) (loop$ for p in (true-list-fix bits) always (and (or (consp p) (null p)) (or (consp (car p)) (null (car p)))))) :verify-guards nil))
  (if (consp bits)
      (and (implies (equal (cdar bits) t)
                    (fn-arx-entry-ok
                      (fn-lb-entry-octets (caaar bits) (cdaar bits) log)
                      (fn-lb-entry-protected-len (caaar bits) (cdaar bits) log)))
           (fn-lb-verified-entries-invp (cdr bits) log))
    t))

(defun fn-lb-vmap-index-covers (bits keys)
  (declare (xargs :guard (and (alistp (remove-equal nil (true-list-fix bits))) (true-listp keys)) :verify-guards nil))
  (if (consp bits)
      (and (implies (equal (cdar bits) t) (member-equal (caar bits) keys))
           (fn-lb-vmap-index-covers (cdr bits) keys))
    t))

; The predicate is evaluated only at establishment and in proofs.  Reads
; ask one bit; they do not walk this relation or recheck a set bit's digest.
(defun-nx fn-lb-verified-invp (log fn-lb-vmap)
  (and (fn-lb-vmap-index-covers (nth *fn-lb-vmap-bits* fn-lb-vmap)
                                (nth *fn-lb-vmap-index* fn-lb-vmap))
       (fn-lb-verified-entries-invp (nth *fn-lb-vmap-bits* fn-lb-vmap) log)))

(defun fn-lb-vmap-mark (seg entry log fn-lb-vmap)
  (declare (xargs :stobjs fn-lb-vmap :guard (fn-lb-log-read-guardp log) :verify-guards nil))
  (if (fn-arx-entry-ok (fn-lb-entry-octets seg entry log)
                       (fn-lb-entry-protected-len seg entry log))
      (let ((fn-lb-vmap
              (if (fn-lb-verified-bit seg entry fn-lb-vmap) fn-lb-vmap
                (update-fn-lb-vmap-index
                  (cons (cons seg entry) (fn-lb-vmap-index fn-lb-vmap)) fn-lb-vmap))))
        (fn-lb-vmap-bits-put (cons seg entry) t fn-lb-vmap))
    fn-lb-vmap))

(defun fn-lb-vmap-recycle-keys (keys seg fn-lb-vmap)
  (declare (xargs :stobjs fn-lb-vmap :guard (alistp (remove-equal nil (true-list-fix keys))) :verify-guards nil))
  (if (consp keys)
      (let ((fn-lb-vmap
              (if (equal (caar keys) seg)
                  (fn-lb-vmap-bits-rem (car keys) fn-lb-vmap)
                fn-lb-vmap)))
        (fn-lb-vmap-recycle-keys (cdr keys) seg fn-lb-vmap))
    fn-lb-vmap))

(defun fn-lb-vmap-retain-keys (keys seg)
  (declare (xargs :guard (alistp (remove-equal nil (true-list-fix keys))) :verify-guards nil))
  (if (consp keys)
      (if (equal (caar keys) seg)
          (fn-lb-vmap-retain-keys (cdr keys) seg)
        (cons (car keys) (fn-lb-vmap-retain-keys (cdr keys) seg)))
    nil))

(defun fn-lb-vmap-recycle (seg fn-lb-vmap)
  (declare (xargs :stobjs fn-lb-vmap :guard (alistp (remove-equal nil (true-list-fix (fn-lb-vmap-index fn-lb-vmap)))) :verify-guards nil))
  (let* ((keys (fn-lb-vmap-index fn-lb-vmap))
         (fn-lb-vmap (fn-lb-vmap-recycle-keys keys seg fn-lb-vmap)))
    (update-fn-lb-vmap-index (fn-lb-vmap-retain-keys keys seg) fn-lb-vmap)))
