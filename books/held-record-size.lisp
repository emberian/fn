; PRF-1113: fixed-spine assembly at the actual held-record constructor.
(in-package "ACL2")
(include-book "store-tree-size")
(include-book "held-record")

; Each carry corresponds to its field. Field values, including immutable
; facts/context, are referenced by fn-held-make; sizing reads only 15 carries.
(defun fn-hsz-make (sequence txid generation msgid payload groups obligation-id
                   content-subject release-evidence charge stamp facts context
                   numbers withdrawn carries)
  (declare (xargs :guard (fn-scs-fixed-carriesp 15 carries)))
  (mv (fn-held-make sequence txid generation msgid payload groups obligation-id
                    content-subject release-evidence charge stamp facts context
                    numbers withdrawn)
      (fn-scs-spine carries)))

(defthm fn-hsz-make-preserves-canonical-size
  (implies
   (fn-scs-correspondsp carries
                       (list sequence txid generation msgid payload groups
                             obligation-id content-subject release-evidence
                             charge stamp facts context numbers withdrawn))
   (equal (mv-nth 1 (fn-hsz-make sequence txid generation msgid payload groups
                               obligation-id content-subject release-evidence
                               charge stamp facts context numbers withdrawn carries))
          (fn-scs-summary
           (mv-nth 0 (fn-hsz-make sequence txid generation msgid payload groups
                                 obligation-id content-subject release-evidence
                                 charge stamp facts context numbers withdrawn carries)))))
  :hints (("Goal" :in-theory (enable fn-hsz-make fn-held-make))))

; A new payload handle can cross a codec width boundary. Rebuild the fixed
; field spine with the replacement's carry; all other child carries are reused.
(defun fn-hsz-remap (h carries handle)
  (declare (xargs :guard (and (true-listp h) (equal (len h) 15) (fn-scs-fixed-carriesp 15 carries) (natp handle))
                  :verify-guards nil))
  (let ((next-carries (update-nth 4 (fn-scs-atom handle) carries)))
    (mv (update-nth 4 handle h)
        next-carries
        (fn-scs-spine next-carries))))

(local
 (defthm fn-hsz-carries-of-update
   (implies (and (fn-scs-carry-listp cs) (fn-scs-carryp c)
                 (natp n) (< n (len cs)))
            (fn-scs-carry-listp (update-nth n c cs)))
   :hints (("Goal" :in-theory (enable fn-scs-carry-listp)))))
(verify-guards fn-hsz-remap)

(local
 (defun fn-hsz-update-induct (n cs xs)
   (if (zp n) (list cs xs)
     (fn-hsz-update-induct (1- n) (cdr cs) (cdr xs)))))

(local
 (defthm fn-hsz-corresponds-of-update
   (implies (and (fn-scs-correspondsp cs xs) (natp n) (< n (len xs)))
            (fn-scs-correspondsp (update-nth n (fn-scs-summary x) cs)
                                 (update-nth n x xs)))
   :hints (("Goal" :induct (fn-hsz-update-induct n cs xs)
            :in-theory (enable fn-scs-correspondsp)))))

(defthm fn-hsz-remap-preserves-canonical-size
  (implies (and (< 4 (len h)) (fn-scs-correspondsp carries h) (atom handle))
           (equal (mv-nth 2 (fn-hsz-remap h carries handle))
                  (fn-scs-summary (mv-nth 0 (fn-hsz-remap h carries handle)))))
  :hints (("Goal"
           :use ((:instance fn-hsz-corresponds-of-update
                            (cs carries) (xs h) (n 4) (x handle))
                 (:instance fn-scs-spine-preserves-canonical-size
                            (cs (update-nth 4 (fn-scs-summary handle) carries))
                            (xs (update-nth 4 handle h))))
           :in-theory (enable fn-hsz-remap fn-held-shapep fn-held-make
                              fn-record-internals fn-held-internals))))

(in-theory (disable fn-hsz-make fn-hsz-remap))
