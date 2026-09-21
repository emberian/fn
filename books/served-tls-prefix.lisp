; fn: one-pass served receive result plus physical prefix ownership.
;
; A socket observation may contain a STARTTLS command line and early TLS
; bytes.  This fold uses fn-served-feed-byte, the same framing/dispatch byte
; transition as fn-served-feed, and returns both the ordinary served result
; and how many observed octets that result consumed before the connection
; became handshaking or closed.  No parser or served transition runs twice.

(in-package "ACL2")
(include-book "served")

; (:fn-served-counted consumed served-result).
(defun fn-served-counted-make (consumed result)
  (declare (xargs :guard t))
  (list :fn-served-counted consumed result))

(defun fn-served-counted-consumed (counted)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr counted)))

(defun fn-served-counted-result (counted)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr counted))))

(defun fn-served-feed-counted (conn octets)
  (declare (xargs :guard (fn-wire-fast-statep (fn-served-conn-wire conn))
                  :verify-guards nil
                  :measure (len octets)))
  (if (or (not (consp octets))
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-tls-handshakingp conn))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (let* ((here (fn-served-feed-byte conn (car octets)))
           (tail (fn-served-feed-counted
                  (fn-served-result-conn here) (cdr octets)))
           (tail-result (fn-served-counted-result tail)))
      (fn-served-counted-make
       (+ 1 (fn-served-counted-consumed tail))
      (fn-served-make-result
        (fn-served-result-conn tail-result)
        (mbe :logic (append (fn-served-result-effects here)
                            (fn-served-result-effects tail-result))
             :exec (fn-ag-append (fn-served-result-effects here)
                                 (fn-served-result-effects tail-result))))))))

(defthm fn-served-feed-counted-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-served-feed-counted conn octets)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-served-feed-counted conn octets)
           :in-theory (enable fn-served-feed-counted
                              fn-served-counted-make
                              fn-served-counted-consumed))))

(verify-guards fn-served-feed-counted
  :hints (("Goal"
           :in-theory (disable fn-served-feed-byte fn-wire-statep
                               fn-served-counted-consumed
                               fn-served-feed-byte-preserves-wire-statep)
           :use ((:instance fn-served-feed-byte-preserves-wire-statep
                            (byte (car octets)))))))

(defthm fn-served-feed-counted-result-is-feed
  (equal (fn-served-counted-result
          (fn-served-feed-counted conn octets))
         (fn-served-feed conn octets))
  :hints (("Goal"
           :induct (fn-served-feed-counted conn octets)
           :in-theory (enable fn-served-feed-counted
                              fn-served-counted-make
                              fn-served-counted-result
                              fn-served-counted-consumed
                              fn-served-feed))))

(defthm fn-served-feed-counted-consumed-is-bounded
  (<= (fn-served-counted-consumed
       (fn-served-feed-counted conn octets))
      (len octets))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-served-feed-counted conn octets)
           :in-theory (enable fn-served-feed-counted
                              fn-served-counted-make
                              fn-served-counted-consumed))))

; Apply fn-served-step's entry guard and close-effect edge once around the
; counted fold.  This is the native owner's actual logical subject.
(defun fn-served-step-counted (conn octets)
  (declare (xargs :guard t))
  (let ((wire (fn-served-conn-wire conn)))
    (if (not (fn-wire-statep wire))
        (fn-served-counted-make 0 (fn-served-make-result conn nil))
      (let* ((fed (fn-served-feed-counted conn octets))
             (result (fn-served-counted-result fed))
             (wire2 (fn-served-conn-wire (fn-served-result-conn result))))
        (fn-served-counted-make
         (fn-served-counted-consumed fed)
         (fn-served-make-result
          (fn-served-result-conn result)
          (mbe :logic
               (append (fn-served-result-effects result)
                       (if (and (not (fn-served-closed-wirep wire))
                                (fn-served-closed-wirep wire2))
                           (list (fn-nntp-close-effect))
                         nil))
               :exec
               (fn-ag-append
                (fn-served-result-effects result)
                (if (and (not (fn-served-closed-wirep wire))
                         (fn-served-closed-wirep wire2))
                    (list (fn-nntp-close-effect))
                  nil)))))))))

; The called counted transition returns the exact ordinary served result.
(defthm fn-served-step-counted-result-is-step
  (equal (fn-served-counted-result
          (fn-served-step-counted conn octets))
         (fn-served-step conn octets))
  :hints (("Goal"
           :in-theory (enable fn-served-step-counted
                              fn-served-counted-make
                              fn-served-counted-result
                              fn-served-counted-consumed
                              fn-served-step)
           :use ((:instance fn-served-feed-counted-result-is-feed)))))

(defthm fn-served-step-counted-consumed-is-bounded
  (<= (fn-served-counted-consumed
       (fn-served-step-counted conn octets))
      (len octets))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable fn-served-step-counted
                              fn-served-counted-make
                              fn-served-counted-consumed)
           :use ((:instance fn-served-feed-counted-consumed-is-bounded)))))

(defthm fn-served-step-counted-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-served-step-counted conn octets)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (enable fn-served-step-counted
                              fn-served-counted-make
                              fn-served-counted-consumed)
           :use ((:instance fn-served-feed-counted-consumed-is-natural)))))

(local
 (defthm fn-served-tls-take-nthcdr-reconstructs
   (implies (and (natp n) (<= n (len xs)))
            (equal (append (take n xs) (nthcdr n xs)) xs))
   :hints (("Goal" :induct (take n xs)
            :in-theory (enable take nthcdr)))))

; The returned count partitions the physical observation without loss or
; duplication.  The suffix is transport input, never another NNTP parse.
(defthm fn-served-tls-prefix-suffix-accounting
  (let ((count (fn-served-counted-consumed
                (fn-served-step-counted conn octets))))
    (equal (append (take count octets) (nthcdr count octets)) octets))
  :hints (("Goal"
           :use ((:instance fn-served-tls-take-nthcdr-reconstructs
                            (n (fn-served-counted-consumed
                                (fn-served-step-counted conn octets)))
                            (xs octets))
                 (:instance fn-served-step-counted-consumed-is-bounded)
                 (:instance fn-served-step-counted-consumed-is-natural))
           :in-theory (disable fn-served-tls-take-nthcdr-reconstructs
                               fn-served-step-counted-consumed-is-bounded
                               fn-served-step-counted-consumed-is-natural
                               fn-served-step-counted
                               fn-served-counted-consumed))))

(in-theory (disable fn-served-counted-make
                    fn-served-counted-consumed
                    fn-served-counted-result
                    fn-served-feed-counted
                    fn-served-step-counted))
