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

; Root-only payload remapping for the checkpoint pool. A non-octet suffix
; after the payload ensures none of the five reconstructed cons cells can
; collapse to the octet-list opcode. The mandatory binding tail is preserved.
(defun fn-hsz-remap-root (h encoded handle)
  (declare (xargs :guard (and (true-listp h) (< 4 (len h))
                              (natp (nth 4 h)) (natp encoded) (natp handle))))
  (mv (update-nth 4 handle h)
      (+ encoded (- (fn-scs-atom-size (nth 4 h)))
         (fn-scs-atom-size handle))))

(local
 (defthm fn-hsz-non-octet-cons-size
   (implies (not (fn-scc-octet-listp d))
            (and (not (fn-scc-octet-listp (cons a d)))
                 (equal (car (fn-scs-summary (cons a d)))
                        (+ 1 (car (fn-scs-summary a))
                           (car (fn-scs-summary d))))))
   :hints (("Goal"
            :use ((:instance fn-scs-cons-preserves-canonical-size
                              (x a) (y d) (a (fn-scs-summary a))
                              (d (fn-scs-summary d))))
            :in-theory (e/d (fn-scs-cons fn-scs-summary fn-scc-octet-listp)
                             (fn-scs-cons-preserves-canonical-size
                              fn-scc-program fn-scc-atom-octets
                              fn-scc-encode-is-program))))))

(local
 (defthm fn-hsz-octet-list-of-nthcdr
   (implies (fn-scc-octet-listp h)
            (fn-scc-octet-listp (nthcdr n h)))
   :hints (("Goal" :in-theory (enable nthcdr fn-scc-octet-listp)))))

(local
 (defthm fn-hsz-non-octet-spine-size
   (implies (and (consp h) (not (fn-scc-octet-listp (cdr h))))
            (equal (car (fn-scs-summary h))
                   (+ 1 (car (fn-scs-summary (car h)))
                      (car (fn-scs-summary (cdr h))))))
   :hints (("Goal" :use ((:instance fn-hsz-non-octet-cons-size
                                     (a (car h)) (d (cdr h))))))))

(local
 (defthm fn-hsz-root-update-size
   (implies (and (natp n) (< n (len h))
                 (not (fn-scc-octet-listp (nthcdr (+ 1 n) h))))
            (and (not (fn-scc-octet-listp (update-nth n x h)))
                 (equal (car (fn-scs-summary (update-nth n x h)))
                        (+ (car (fn-scs-summary h))
                           (- (car (fn-scs-summary (nth n h))))
                           (car (fn-scs-summary x))))))
   :hints (("Goal" :induct (nth n h)
            :in-theory (enable nthcdr update-nth))
           ("Subgoal *1/3"
            :use ((:instance fn-hsz-octet-list-of-nthcdr (h (cdr h))))))))

(local
 (defthm fn-hsz-nthcdr-past-length
   (implies (and (natp n) (< (len h) n))
            (equal (nthcdr n h) nil))
   :hints (("Goal" :induct (nthcdr n h) :in-theory (enable nthcdr)))))

(local
 (defthm fn-hsz-atom-size-of-summary
   (implies (atom x)
            (equal (fn-scs-atom-size x) (car (fn-scs-summary x))))
   :hints (("Goal" :use fn-scs-atom-establishes-summary
            :in-theory (e/d (fn-scs-atom)
                             (fn-scs-atom-size fn-scs-atom-establishes-summary))))))

(defthm fn-hsz-remap-root-preserves-canonical-size
  (implies (and (not (fn-scc-octet-listp (nthcdr 5 h)))
                (atom (nth 4 h)) (atom handle)
                (equal encoded (car (fn-scs-summary h))))
           (equal (mv-nth 1 (fn-hsz-remap-root h encoded handle))
                  (car (fn-scs-summary
                        (mv-nth 0 (fn-hsz-remap-root h encoded handle))))))
  :hints (("Goal"
           :use ((:instance fn-hsz-root-update-size (n 4) (x handle))
                 (:instance fn-hsz-nthcdr-past-length (n 5)))
           :in-theory (e/d (fn-hsz-remap-root)
                            (fn-hsz-root-update-size fn-scs-atom-size)))))
(in-theory (disable fn-hsz-remap-root))
