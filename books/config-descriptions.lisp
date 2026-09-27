;; fn: group descriptions and the node's message in the configuration
;; (PRF-195, NNT-039; specs/nntp.md "Group descriptions and the message of
;; the day").
;;
;; The eleventh configuration slot holds rows (NAME PIECE "" 0) written only
;; by :set-group-description (code 20, books/config.lisp).  The theorems here
;; are over the functions the host path reaches:
;;
;;   `fn-cfg-apply-delta' -- replay and the live owner's staging apply every
;;     published record through it (books/config.lisp `fn-cfg-apply');
;;   `fn-cfg-delta-reason' -- the admission `fn-cfg-admissiblep' asks of
;;     every delta before a record is written;
;;   `fn-cfg-description-octets' and `fn-cfg-motd-lines' -- what
;;     books/owner-agent.lisp `fn-oag-listing' projects into the connection's
;;     reader listing.
;;
;; Keystones: a published description is exactly its pieces concatenated
;; (fn-cfg-description-after-set-is-its-pieces), it leaves every other name's
;; text alone (fn-cfg-description-after-set-of-another-name), the node's
;; message is exactly its lines (fn-cfg-motd-after-set-is-its-lines), and no
;; other delta kind touches the slot (fn-cfg-descriptions-of-other-kinds).
;; Admission refuses a name that is neither "" nor a live group, a row that is
;; not the delta's own printable (NAME PIECE "" 0), and a group text of
;; spaces only.

(in-package "ACL2")
(include-book "config")

(local (in-theory (enable fn-cfg-rows-with-key fn-cfg-rows-without-key
                          fn-cfg-description-rows fn-cfg-row-pieces
                          fn-cfg-pieces-octets fn-cfg-pieces-lines)))

(local
 (defthm fn-cdesc-rows-with-key-of-append
   (equal (fn-cfg-rows-with-key (append x y) a)
          (append (fn-cfg-rows-with-key x a) (fn-cfg-rows-with-key y a)))))

(local
 (defthm fn-cdesc-rows-with-key-of-without-key
   (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows a) a) nil)))

(local
 (defthm fn-cdesc-rows-with-key-of-without-other-key
   (implies (not (equal a b))
            (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows b) a)
                   (fn-cfg-rows-with-key rows a)))))

(local
 (defthm fn-cdesc-rows-with-key-of-description-rows
   (equal (fn-cfg-rows-with-key (fn-cfg-description-rows name pieces) a)
          (if (equal a name) (fn-cfg-description-rows name pieces) nil))))

(local
 (defthm fn-cdesc-row-pieces-of-description-rows
   (equal (fn-cfg-row-pieces (fn-cfg-description-rows name pieces))
          (true-list-fix pieces))))

(local
 (defthm fn-cdesc-pieces-octets-of-true-list-fix
   (equal (fn-cfg-pieces-octets (true-list-fix pieces))
          (fn-cfg-pieces-octets pieces))))

(local
 (defthm fn-cdesc-pieces-lines-of-true-list-fix
   (equal (fn-cfg-pieces-lines (true-list-fix pieces))
          (fn-cfg-pieces-lines pieces))))

(local
 (defthm fn-cdesc-set-delta-fields
   (and (equal (fn-cfg-delta-kind (fn-cfg-set-group-description name pieces))
               :set-group-description)
        (equal (fn-cfg-delta-a (fn-cfg-set-group-description name pieces)) name)
        (equal (fn-cfg-delta-rows (fn-cfg-set-group-description name pieces))
               (fn-cfg-description-rows name pieces)))))

; KEYSTONE.  After the delta for NAME, NAME's description is its pieces.
(defthm fn-cfg-description-after-set-is-its-pieces
  (equal (fn-cfg-description-octets
          (fn-cfg-apply-delta v gen stamp
                              (fn-cfg-set-group-description name pieces))
          name)
         (fn-cfg-pieces-octets pieces))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cfg-description-octets fn-cfg-apply-delta)
                           (fn-cfg-set-group-description fn-cfg-pieces-octets
                            fn-cfg-description-rows fn-cfg-row-pieces
                            fn-cfg-rows-with-key fn-cfg-rows-without-key)))))

; KEYSTONE.  Every other name keeps its text.
(defthm fn-cfg-description-after-set-of-another-name
  (implies (not (equal other name))
           (equal (fn-cfg-description-octets
                   (fn-cfg-apply-delta v gen stamp
                                       (fn-cfg-set-group-description name pieces))
                   other)
                  (fn-cfg-description-octets v other)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cfg-description-octets fn-cfg-apply-delta)
                           (fn-cfg-set-group-description fn-cfg-pieces-octets
                            fn-cfg-description-rows fn-cfg-row-pieces
                            fn-cfg-rows-with-key fn-cfg-rows-without-key)))))

; KEYSTONE.  The node's message ("" names the node) is its lines.
(defthm fn-cfg-motd-after-set-is-its-lines
  (equal (fn-cfg-motd-lines
          (fn-cfg-apply-delta v gen stamp
                              (fn-cfg-set-group-description "" pieces)))
         (fn-cfg-pieces-lines pieces))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cfg-motd-lines fn-cfg-apply-delta)
                           (fn-cfg-set-group-description fn-cfg-pieces-lines
                            fn-cfg-description-rows fn-cfg-row-pieces
                            fn-cfg-rows-with-key fn-cfg-rows-without-key)))))

; KEYSTONE.  No other kind of delta changes the slot.
(defthm fn-cfg-descriptions-of-other-kinds
  (implies (not (equal (fn-cfg-delta-kind d) :set-group-description))
           (equal (fn-cfg-descriptions (fn-cfg-apply-delta v gen stamp d))
                  (fn-cfg-descriptions v)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-set-groups fn-cfg-apply-delta)
                                  (fn-cfg-groups-create fn-cfg-groups-retire
                                   fn-cfg-row-upsert fn-cfg-row-replace-key
                                   fn-cfg-rows-without-key fn-cfg-rows-with-key
                                   fn-cfg-rows-without-members
                                   fn-cfg-rows-without-pair
                                   fn-cfg-rows-without-binding)))))

; Admission, by definition: a delta for a name that is neither the node's "" nor
; a live group is refused :no-such-group, whatever its rows.
(defthm fn-cfg-set-group-description-refuses-an-unknown-group-by-definition
  (implies (and (fn-cfg-deltap d)
                (equal (fn-cfg-delta-kind d) :set-group-description)
                (not (equal (fn-cfg-delta-a d) ""))
                (not (fn-cfg-group-livep v gen (fn-cfg-delta-a d))))
           (equal (fn-cfg-delta-reason v gen stamp reserved ceiling d)
                  :no-such-group))
  :hints (("Goal" :in-theory (e/d (fn-cfg-delta-reason
                                   fn-cfg-set-group-description-reason)
                                  (fn-cfg-deltap fn-cfg-group-livep)))))

; KEYSTONE (admission).  An admitted description delta carries only its own
; printable rows, so every piece the slot shows is printable ASCII.
(defthm fn-cfg-admitted-description-rows-are-printable
  (implies (and (fn-cfg-deltap d)
                (equal (fn-cfg-delta-kind d) :set-group-description)
                (null (fn-cfg-delta-reason v gen stamp reserved ceiling d)))
           (fn-cfg-description-rowsp (fn-cfg-delta-rows d) (fn-cfg-delta-a d)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-delta-reason
                                   fn-cfg-set-group-description-reason)
                                  (fn-cfg-deltap fn-cfg-group-livep
                                   fn-cfg-description-rowsp)))))
