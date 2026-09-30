; PRF-1137 source boundary over the actual native writer's producer.
; EMITTED is ghost effect history, never a resident served byte list.
(in-package "ACL2")
(include-book "bp-node-checkpoint-job")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-bpcke-prefix (job)
 (declare (xargs :guard t :verify-guards nil))
 (append (fn-bpck-prefix (fn-bpn-nth 8 job))
         (fn-bpnr-enc (fn-bpn-nth 5 job) (fn-bpn-nth 4 job))))

(defun fn-bpcke-invariantp (job emitted)
 (declare (xargs :guard t :verify-guards nil))
 (and (member-equal (fn-bpn-nth 6 job) '(:emit :digest-finish))
      (natp (fn-bpn-nth 8 job))
      (natp (fn-bpn-nth 10 job))
      (true-listp emitted)
      (equal (len emitted) (fn-bpn-nth 10 job))
      (equal (fn-bpn-nth 8 job)
             (len (fn-bpnr-enc (fn-bpn-nth 5 job) (fn-bpn-nth 4 job))))
      (fn-bpnrc-tasks-validp (fn-bpn-nth 7 job))
      (equal (append emitted (fn-bpnrc-residual (fn-bpn-nth 7 job)))
             (fn-bpcke-prefix job))))

(local (defthm fn-bpcke-append-associative
 (equal (append (append a b) c) (append a b c))
 :hints (("Goal" :induct (len a)))))

(local (defthm fn-bpcke-done-is-empty-unfolds
 (implies (equal (fn-bpn-nth 0 (fn-bpnrc-step tasks)) :done)
          (and (equal (fn-bpn-nth 1 (fn-bpnrc-step tasks)) nil)
               (equal (fn-bpn-nth 2 (fn-bpnrc-step tasks)) nil)
               (equal (fn-bpnrc-residual tasks) nil)))
 :hints (("Goal" :in-theory (enable fn-bpnrc-step fn-bpnrc-answer
                                   fn-bpnrc-residual fn-bpn-nth)))))

(local (defthm fn-bpcke-counted-is-proper
 (true-listp (fn-bpnr-counted tag codes))
 :hints (("Goal" :in-theory (enable fn-bpnr-counted
                                   fn-cbor-octet-listp-implies-true-listp)))))
(local (defthm fn-bpcke-leaf-is-proper
 (true-listp (fn-bpnr-enc-leaf x d))
 :hints (("Goal" :in-theory (enable fn-bpnr-enc-leaf)))))
(local (defthm fn-bpcke-step-emits-proper
 (true-listp (fn-bpn-nth 1 (fn-bpnrc-step tasks)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpnrc-step fn-bpnrc-answer fn-bpnrc-counted-start
                               fn-bpn-nth)
                  (fn-bpc-u64-bytes fn-bpnr-enc-leaf fn-bpnr-counted))))))

(local (defthm fn-bpcke-append-is-proper
 (implies (true-listp b) (true-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append true-listp)))))

(local (defthm fn-bpcke-proper-append-nil
 (implies (true-listp a) (equal (append a nil) a))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append true-listp)))))
(local (defthm fn-bpcke-prefix-length
 (equal (len (fn-bpck-prefix count)) 14)
 :hints (("Goal" :use ((:instance fn-bpc-u64-bytes-have-eight-octets (n (nfix count))))
                  :in-theory (enable fn-bpck-prefix)))))

(defthm fn-bpck-emit-step-preserves-exact-write-history
 (implies (fn-bpcke-invariantp job emitted)
          (let ((answer (fn-bpck-emit-step job)))
           (and (fn-bpcke-invariantp (fn-bpn-nth 0 answer)
                                    (append emitted (fn-bpn-nth 1 answer)))
                (equal (fn-bpn-nth 5 (fn-bpn-nth 0 answer))
                       (fn-bpn-nth 5 job))
                (<= (len (fn-bpn-nth 1 answer)) 9))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpnrc-step-preserves-exact-residual
                   (tasks (fn-bpn-nth 7 job)))
        (:instance fn-bpck-emit-step-is-bounded)
        (:instance fn-bpcke-step-emits-proper (tasks (fn-bpn-nth 7 job))))
  :in-theory (e/d (fn-bpcke-invariantp fn-bpcke-prefix fn-bpck-emit-step
                                    fn-bpck-make fn-bpn-nth)
                  (fn-bpnrc-step fn-bpnrc-residual fn-bpnrc-tasks-validp
                   fn-bpnr-enc fn-bpck-prefix)))))

(defthm fn-bpck-emit-step-terminal-is-exact-frame-prefix
 (implies
  (and (equal (fn-bpn-nth 6 job) :emit)
       (fn-bpcke-invariantp job emitted)
       (equal (fn-bpn-nth 6 (fn-bpn-nth 0 (fn-bpck-emit-step job))) :digest-finish))
  (equal (append emitted (fn-bpn-nth 1 (fn-bpck-emit-step job)))
         (fn-bpnr-checkpoint-prefix
          (fn-bpnr-enc (fn-bpn-nth 5 job) (fn-bpn-nth 4 job)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpck-emit-step-preserves-exact-write-history))
  :in-theory (e/d (fn-bpcke-invariantp fn-bpcke-prefix fn-bpck-emit-step
                                    fn-bpck-make fn-bpn-nth fn-bpnr-checkpoint-prefix
                                    fn-bpck-prefix)
                  (fn-bpnrc-step fn-bpnrc-residual fn-bpnrc-tasks-validp
                   fn-bpnr-enc fn-bpc-u64-bytes)))))
