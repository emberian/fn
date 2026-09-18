; General properties of fn-wire-next, the event-yield framing API.
;
; These results describe one call made with a valid wire state and a proper
; octet chunk.  They do not refine an NNTP session mode change: the caller is
; still responsible for dispatching the yielded command before calling
; fn-wire-begin-article and resuming the returned socket suffix.
(in-package "ACL2")
(include-book "wire")

(defun fn-wire-suffixp (suffix octets)
  (if (equal suffix octets)
      t
    (if (consp octets)
        (fn-wire-suffixp suffix (cdr octets))
      nil)))

(defthm fn-wire-suffixp-refl
  (fn-wire-suffixp octets octets))

(defthm fn-wire-suffixp-cdr
  (implies (fn-wire-suffixp suffix octets)
           (fn-wire-suffixp suffix (cons byte octets))))

(defthm fn-wire-suffixp-implies-length-bound
  (implies (and (true-listp octets)
                (fn-wire-suffixp suffix octets))
           (<= (len suffix) (len octets)))
  :hints (("Goal" :induct (fn-wire-suffixp suffix octets))))

(defthm fn-wire-suffixp-reconstruct
  (implies (and (true-listp octets)
                (fn-wire-suffixp suffix octets))
           (equal (append (take (- (len octets) (len suffix)) octets)
                          suffix)
                  octets))
  :hints (("Goal" :induct (fn-wire-suffixp suffix octets))))

; A call either stops at its first framing/rejection event or consumes the
; complete supplied chunk.  In both cases it leaves an actual suffix, so the
; implicit consumed prefix plus the returned bytes reconstruct the chunk.
(defthm fn-wire-next-preserves-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-next-state (fn-wire-next wire-state octets))))
  :hints (("Goal"
           :induct (fn-wire-next wire-state octets)
           :in-theory (enable fn-wire-next
                              fn-wire-next-state
                              fn-wire-make-next))))

(defthm fn-wire-next-unconsumed-is-suffix
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (fn-wire-suffixp
            (fn-wire-next-unconsumed (fn-wire-next wire-state octets))
            octets))
  :hints (("Goal"
           :induct (fn-wire-next wire-state octets)
           :in-theory (enable fn-wire-next
                              fn-wire-next-unconsumed
                              fn-wire-make-next))))

(defthm fn-wire-next-consumed-prefix-reconstructs-input
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (equal
            (append
             (take (- (len octets)
                      (len (fn-wire-next-unconsumed
                            (fn-wire-next wire-state octets))))
                   octets)
             (fn-wire-next-unconsumed (fn-wire-next wire-state octets)))
            octets))
  :hints (("Goal"
           :use ((:instance fn-wire-suffixp-reconstruct
                  (suffix (fn-wire-next-unconsumed
                           (fn-wire-next wire-state octets))))))))

(defthm fn-wire-next-unconsumed-is-bounded
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (<= (len (fn-wire-next-unconsumed
                     (fn-wire-next wire-state octets)))
               (len octets)))
  :hints (("Goal"
           :use ((:instance fn-wire-suffixp-implies-length-bound
                  (suffix (fn-wire-next-unconsumed
                           (fn-wire-next wire-state octets))))))))

; An open valid-state call reports an event only after consuming input.  Thus a
; yielded boundary cannot be manufactured from an empty socket chunk; when no
; event is found, every supplied proper octet has been consumed into the
; returned framing state.
(defthm fn-wire-next-event-needs-input
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (fn-wire-octet-listp octets)
                (fn-wire-next-event (fn-wire-next wire-state octets)))
           (consp octets))
  :hints (("Goal"
           :induct (fn-wire-next wire-state octets)
           :in-theory (enable fn-wire-next
                              fn-wire-next-event
                              fn-wire-make-next))))

(defthm fn-wire-next-no-event-consumes-proper-chunk
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (fn-wire-octet-listp octets)
                (not (fn-wire-next-event (fn-wire-next wire-state octets))))
           (equal (fn-wire-next-unconsumed (fn-wire-next wire-state octets))
                  nil))
  :hints (("Goal"
           :induct (fn-wire-next wire-state octets)
           :in-theory (enable fn-wire-next
                              fn-wire-next-event
                              fn-wire-next-unconsumed
                              fn-wire-make-next))))
