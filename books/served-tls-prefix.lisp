; fn: the physical receive prefix at a served STARTTLS transition.
;
; A socket read may observe the STARTTLS command line and later transport
; bytes together.  fn-served-step deliberately stops interpreting octets as
; soon as the session enters :handshaking, but its result did not expose the
; position where that happened.  A host that had already consumed the whole
; recv buffer therefore had no way to give the suffix to TLS.
;
; This book derives the prefix length by executing the same fn-served-step,
; one octet at a time.  It is not a second NNTP parser.  The equality theorem
; below is the correspondence needed by the host: applying the actual served
; transition to exactly the reported prefix produces the same state and
; effects as applying it to the complete observed buffer.  The suffix is
; consequently transport input and never plaintext NNTP input.

(in-package "ACL2")
(include-book "served")

(defun fn-served-tls-terminalp (conn)
  (declare (xargs :guard t))
  (fn-served-tls-handshakingp conn))

(defun fn-served-tls-consumed (conn octets)
  (declare (xargs :guard t :measure (len octets)))
  (if (or (not (consp octets))
          (fn-served-tls-terminalp conn))
      0
    (+ 1
       (fn-served-tls-consumed
        (fn-served-result-conn
         (fn-served-step conn (list (car octets))))
        (cdr octets)))))

(defthm fn-served-tls-consumed-is-bounded
  (<= (fn-served-tls-consumed conn octets) (len octets))
  :rule-classes :linear)

(defthm fn-served-tls-consumed-is-natural
  (natp (fn-served-tls-consumed conn octets))
  :rule-classes :type-prescription)

(local
 (defthm fn-served-tls-take-nthcdr-reconstructs
   (implies (and (natp n) (<= n (len xs)))
            (equal (append (take n xs) (nthcdr n xs)) xs))
   :hints (("Goal" :induct (take n xs)
            :in-theory (enable take nthcdr)))))

; The count partitions the exact observed object: no byte is dropped or
; duplicated between the plaintext prefix and the TLS suffix.
(defthm fn-served-tls-prefix-suffix-accounting
  (equal (append (take (fn-served-tls-consumed conn octets) octets)
                 (nthcdr (fn-served-tls-consumed conn octets) octets))
         octets)
  :hints (("Goal"
           :use ((:instance fn-served-tls-take-nthcdr-reconstructs
                            (n (fn-served-tls-consumed conn octets))
                            (xs octets)))
           :in-theory (disable fn-served-tls-take-nthcdr-reconstructs))))

(local
 (defthm fn-served-step-reconstructs
   (equal (fn-served-make-result
           (fn-served-result-conn (fn-served-step conn octets))
           (fn-served-result-effects (fn-served-step conn octets)))
          (fn-served-step conn octets))
   :hints (("Goal" :expand ((fn-served-step conn octets))))))

(local
 (defthm fn-served-step-of-handshaking-connection-full
   (implies (fn-served-tls-handshakingp conn)
            (equal (fn-served-step conn octets)
                   (fn-served-step conn nil)))
   :hints (("Goal"
            :use ((:instance fn-served-step-reconstructs)
                  (:instance fn-served-step-reconstructs (octets nil))
                  (:instance fn-served-step-of-handshaking-connection-is-a-no-op)
                  (:instance fn-served-step-of-handshaking-connection-is-a-no-op
                             (octets nil)))
            :in-theory (disable fn-served-step
                                fn-served-tls-handshakingp
                                fn-served-step-reconstructs
                                fn-served-step-of-handshaking-connection-is-a-no-op)))))

(local
 (defthm fn-served-step-of-invalid-wire
   (implies (not (fn-wire-statep (fn-served-conn-wire conn)))
            (equal (fn-served-step conn octets)
                   (fn-served-make-result conn nil)))
   :hints (("Goal" :expand ((fn-served-step conn octets))))))

(local
 (defthm fn-served-tls-append-is-associative
   (equal (append (append a b) c)
          (append a (append b c)))))

(local
 (defthm fn-served-tls-feed-of-closed-wire
   (implies (fn-served-closed-wirep (fn-served-conn-wire conn))
            (equal (fn-served-feed conn octets)
                   (fn-served-make-result conn nil)))
   :hints (("Goal" :expand ((fn-served-feed conn octets))))))

(local
 (defthm fn-served-step-of-atom
   (implies (not (consp octets))
            (equal (fn-served-step conn octets)
                   (fn-served-step conn nil)))
   :hints (("Goal" :expand ((fn-served-step conn octets)
                             (fn-served-step conn nil)
                             (fn-served-feed conn octets)
                             (fn-served-feed conn nil))))))

; fn-served-step's invalid-wire branch is itself a no-op.  On a valid wire,
; fn-served-feed-preserves-wire-statep supplies the only invariant the
; append proof needs.  The stronger exported partition theorem asks for a
; whole fn-served-connp; the physical prefix correspondence deliberately
; needs only well-formed input bytes.
(local
 (defthm fn-served-step-partition-independence-for-octets
   (equal (fn-served-step conn (append left right))
          (fn-served-make-result
           (fn-served-result-conn
            (fn-served-step
             (fn-served-result-conn (fn-served-step conn left)) right))
           (append
            (fn-served-result-effects (fn-served-step conn left))
            (fn-served-result-effects
             (fn-served-step
              (fn-served-result-conn (fn-served-step conn left))
              right)))))
   :hints (("Goal"
            :do-not-induct t
            :cases ((fn-wire-statep (fn-served-conn-wire conn))
                    (fn-served-closed-wirep
                     (fn-served-conn-wire
                      (fn-served-result-conn
                       (fn-served-feed conn left)))))
            :in-theory (e/d (fn-served-step)
                            (fn-served-feed fn-wire-statep
                             fn-served-step-of-invalid-wire
                             fn-served-feed-preserves-wire-statep))
            :use ((:instance fn-served-feed-preserves-wire-statep
                             (octets left))
                  (:instance fn-served-step-of-invalid-wire
                             (octets (append left right)))
                  (:instance fn-served-step-of-invalid-wire
                             (octets left))
                  (:instance fn-served-step-of-invalid-wire
                             (conn (fn-served-result-conn
                                    (fn-served-step conn left)))
                             (octets right)))))))

(local
 (defthm fn-served-step-of-cons
   (equal (fn-served-step conn (cons byte rest))
          (fn-served-make-result
           (fn-served-result-conn
            (fn-served-step
             (fn-served-result-conn
              (fn-served-step conn (list byte)))
             rest))
           (append
            (fn-served-result-effects
             (fn-served-step conn (list byte)))
            (fn-served-result-effects
             (fn-served-step
              (fn-served-result-conn
               (fn-served-step conn (list byte)))
              rest)))))
   :hints (("Goal"
            :use ((:instance fn-served-step-partition-independence-for-octets
                             (left (list byte)) (right rest)))
            :in-theory (disable fn-served-step
                                fn-served-step-partition-independence-for-octets)))))

; The theorem subject is the function the owner host already calls.  The
; physical adapter may consume exactly this many octets after MSG_PEEK and
; then call fn-served-step on them without changing either its connection
; result or its effects relative to the complete observed buffer.
(defthm fn-served-step-of-tls-consumed-prefix
  (equal (fn-served-step
          conn (take (fn-served-tls-consumed conn octets) octets))
         (fn-served-step conn octets))
  :hints (("Goal"
           :induct (fn-served-tls-consumed conn octets)
           :in-theory (e/d (fn-served-tls-consumed
                            fn-served-tls-terminalp
                            take)
                           (fn-served-step
                            fn-served-step-of-cons
                            fn-served-step-of-handshaking-connection-full
                            fn-served-step-partition-independence)))
          ("Subgoal *1/2"
           :use ((:instance fn-served-step-of-cons
                            (byte (car octets))
                            (rest (cdr octets)))
                 (:instance fn-served-step-of-cons
                            (byte (car octets))
                            (rest (take
                                   (fn-served-tls-consumed
                                    (fn-served-result-conn
                                     (fn-served-step conn
                                                     (list (car octets))))
                                    (cdr octets))
                                   (cdr octets))))
                 )
           :in-theory (disable fn-served-step
                               fn-served-step-of-cons
                               fn-served-step-preserves-connp))
          ("Subgoal *1/1"
           :use ((:instance fn-served-step-of-handshaking-connection-full)
                 (:instance fn-served-step-of-atom))
           :in-theory (disable fn-served-step
                               fn-served-step-of-atom
                               fn-served-step-of-handshaking-connection-full))))
