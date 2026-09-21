; fn: carried validity of the outbound connection-phase table.
;
; fn-fc-tablep is a logical invariant over every retained peer framer.  The
; host establishes it once with fn-fc-table-initial-state and preserves it
; only through fn-fc-table-put/remove.  Served input checks the selected state;
; it does not rescan this table or every peer's retained input.
(in-package "ACL2")
(include-book "feed-connection")
(include-book "wire-invariants")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-fc-table-initial-state ()
  (declare (xargs :guard t))
  nil)

(defthm fn-fc-table-initial-state-is-table
  (fn-fc-tablep (fn-fc-table-initial-state)))

(local
 (defthm fn-fwi-input-is-chunk
   (implies (and (fn-fwi-statep st) (fn-fwi-chunkp octets))
            (fn-fwi-chunkp (fn-fwi-input st octets)))
   :hints (("Goal" :in-theory (enable fn-fwi-statep fn-fwi-chunkp
                                      fn-fwi-input)))))

(local
 (defthm fn-fc-wire-next-unconsumed-is-bounded-linear
   (implies (and (fn-wire-statep wire) (fn-wire-octet-listp octets))
            (<= (len (fn-wire-next-unconsumed (fn-wire-next wire octets)))
                (len octets)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-wire-next-unconsumed-is-bounded
                                    (wire-state wire)))))))

(local
 (defthm fn-fwi-wire-next-unconsumed-is-chunk
   (implies (and (fn-wire-statep wire) (fn-fwi-chunkp octets))
            (fn-fwi-chunkp
             (fn-wire-next-unconsumed (fn-wire-next wire octets))))
   :hints (("Goal"
            :use ((:instance fn-wire-next-unconsumed-is-bounded
                             (wire-state wire))
                  (:instance fn-wire-next-unconsumed-octet-listp
                             (wire-state wire)))
            :in-theory (enable fn-fwi-chunkp)))))

(local
 (defthm fn-fwi-from-wire-next-preserves-state
   (implies (and (fn-wire-statep wire) (fn-fwi-chunkp octets))
            (fn-fwi-statep
             (fn-fwi-next-state
              (fn-fwi-from-wire-next (fn-wire-next wire octets)))))
   :hints (("Goal"
            :use ((:instance fn-wire-next-preserves-statep
                             (wire-state wire))
                  (:instance fn-fwi-wire-next-unconsumed-is-chunk))
            :in-theory (enable fn-fwi-from-wire-next fn-fwi-next-state
                               fn-fwi-make-state fn-fwi-statep
                               fn-fwi-chunkp)))))

(local
 (defthm fn-fwi-step-preserves-state
   (implies (and (fn-fwi-statep st) (fn-fwi-chunkp octets))
            (fn-fwi-statep (fn-fwi-next-state (fn-fwi-step st octets))))
   :hints (("Goal" :cases ((fn-fwi-callp st octets))
                   :in-theory (enable fn-fwi-step fn-fwi-next-state
                                      fn-fwi-result fn-fwi-callp
                                      fn-fwi-statep)))))

(local
 (defthm fn-fc-with-input-phase-is-state
   (implies (and (fn-fc-statep st)
                 (fn-fwi-statep input)
                 (fn-fc-phasep phase))
            (fn-fc-statep (fn-fc-with-input-phase st input phase)))
   :hints (("Goal" :in-theory (enable fn-fc-statep
                                      fn-fc-with-input-phase
                                      fn-fc-make-state)))))

(local
 (defthm fn-fc-from-line-preserves-state
   (implies (and (fn-fc-statep st) (fn-fwi-statep input))
            (fn-fc-statep
             (fn-fc-next-state (fn-fc-from-line st input line))))
   :hints (("Goal" :in-theory (enable fn-fc-from-line fn-fc-next-state
                                      fn-fc-result fn-fc-phasep)))))

(defthm fn-fc-step-preserves-state
  (implies (fn-fc-statep st)
           (fn-fc-statep (fn-fc-next-state (fn-fc-step st octets))))
  :hints (("Goal" :cases ((fn-fwi-chunkp octets))
                  :in-theory (enable fn-fc-step fn-fc-next-state
                                     fn-fc-result))))

(defthm fn-fc-table-lookup-after-remove
  (equal (fn-fc-table-lookup peer (fn-fc-table-remove peer table)) nil)
  :hints (("Goal" :induct (fn-fc-table-remove peer table)
                  :in-theory (enable fn-fc-table-remove fn-fc-table-lookup))))

(defthm fn-fc-table-lookup-after-put
  (equal (fn-fc-table-lookup peer (fn-fc-table-put peer st table)) st)
  :hints (("Goal" :in-theory (enable fn-fc-table-put fn-fc-table-lookup))))

(defthm fn-fc-table-lookup-is-state
  (implies (and (fn-fc-tablep table)
                (fn-fc-table-lookup peer table))
           (fn-fc-statep (fn-fc-table-lookup peer table)))
  :hints (("Goal" :induct (fn-fc-table-lookup peer table)
                  :in-theory (enable fn-fc-tablep fn-fc-table-entryp
                                     fn-fc-table-lookup))))

(local
 (defthm fn-fc-table-name-member-of-remove
   (implies (fn-fc-table-memberp name
                                 (fn-fc-table-names
                                  (fn-fc-table-remove peer table)))
            (fn-fc-table-memberp name (fn-fc-table-names table)))
   :hints (("Goal" :induct (fn-fc-table-remove peer table)
                   :in-theory (enable fn-fc-table-remove fn-fc-table-names
                                      fn-fc-table-memberp)))))

(local
 (defthm fn-fc-table-unique-namesp-of-remove
   (implies (fn-fc-table-unique-namesp (fn-fc-table-names table))
            (fn-fc-table-unique-namesp
             (fn-fc-table-names (fn-fc-table-remove peer table))))
   :hints (("Goal" :induct (fn-fc-table-remove peer table)
                   :in-theory (enable fn-fc-table-remove fn-fc-table-names
                                      fn-fc-table-memberp
                                      fn-fc-table-unique-namesp)))))

(defthm fn-fc-table-remove-preserves-table
  (implies (fn-fc-tablep table)
           (fn-fc-tablep (fn-fc-table-remove peer table)))
  :hints (("Goal" :induct (fn-fc-table-remove peer table)
                  :in-theory (enable fn-fc-tablep fn-fc-table-remove
                                     fn-fc-table-names))))

(local
 (defthm fn-fc-table-removed-name-absent
   (implies (fn-fc-tablep table)
            (not (fn-fc-table-memberp
                  peer (fn-fc-table-names
                        (fn-fc-table-remove peer table)))))
   :hints (("Goal" :induct (fn-fc-table-remove peer table)
                   :in-theory (enable fn-fc-table-remove fn-fc-table-names
                                      fn-fc-table-memberp fn-fc-tablep
                                      fn-fc-table-entryp)))))

(defthm fn-fc-table-put-preserves-table
  (implies (and (stringp peer)
                (fn-fc-statep st)
                (fn-fc-tablep table))
           (fn-fc-tablep (fn-fc-table-put peer st table)))
  :hints (("Goal" :in-theory (enable fn-fc-table-put fn-fc-tablep
                                     fn-fc-table-entryp fn-fc-table-names
                                     fn-fc-table-unique-namesp))))
