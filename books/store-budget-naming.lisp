; fn: the transaction file name of the staged record, and the POST payload
; bound, both from the state and profile ACL2 already carries (M5).
;
; What the host used to compute.  The owner named each transaction file from a
; count of its own (host/native/owner.lisp, a service-struct slot set to the
; recovered record count at open and incremented after every finish), and the
; developer `store post' named it from the length of the record list it
; recovered.  Both are the committed count the Store state carries
; (`fn-sbud-used'), so they were a second count: checked by ACL2's
; admissibility question, never derived by it.  Now the host asks for the
; staged candidate's own sequence (`fn-sbud-pending-sequence', called by
; host/owner-host.lisp `fn-owner-pending-sequence' and
; host/store-node-host.lisp `fn-store-sn-pending-sequence') and names the file
; with `fn-sbud-txn-name' (host/store-host.lisp `fn-store-txn-name'), which is
; the scan's own `fn-bs-txn-name' (books/byte-store-scan.lisp
; `fn-bs-txn-observation-pairs').
;
; The payload bound.  `fn-sbud-post-boundary' is the POST admission boundary
; host/native/io.lisp `fnn-validate-post-boundary' asks, over the persisted
; profile the host was handed at open: its max_article_octets field A and
; max_groups_per_article field G, never a host constant.  A payload past it is `:payload-bound'; the served
; owner relays that refusal as the Store word `:refused', whose 441 line is
; distinct from every other Store refusal line
; (books/nntp-post.lisp `fn-post-outcome-store-refusal-kinds-are-distinct', W3).
(in-package "ACL2")
(include-book "store-budget")
(include-book "byte-store-scan")
(include-book "byte-store-txn-name")
(include-book "article-fields")

; -----------------------------------------------------------------------------
; The staged record's transaction name

(defun fn-sbud-pending-sequence (s)
  "The sequence of the Store S's staged record candidate, or NIL when none."
  (declare (xargs :guard t :verify-guards nil))
  (let ((record (fn-sf-record-candidate (fn-sn-files s))))
    (if (and record (natp (fn-store-event-sequence record)))
        (fn-store-event-sequence record)
      nil)))

(defun fn-sbud-txn-name (sequence)
  "The final transaction file name of SEQUENCE: the scan's `fn-bs-txn-name'."
  (declare (xargs :guard t))
  (if (natp sequence) (fn-bs-txn-name sequence) ""))

; The names a scan expects for sequences START .. START+N-1, in order, and the
; pairs `fn-bs-txn-observation-pairs' binds them to.
(defun fn-sbud-names (start n)
  (declare (xargs :guard (and (natp start) (natp n))))
  (if (zp n) nil
    (cons (fn-bs-txn-name start) (fn-sbud-names (1+ start) (1- n)))))

(defun fn-sbud-name-pairs (start n)
  (declare (xargs :guard (and (natp start) (natp n))))
  (if (zp n) nil
    (cons (list start (fn-bs-txn-name start))
          (fn-sbud-name-pairs (1+ start) (1- n)))))

; In a record phase the kernel's candidate is the next record
; (`fn-sf-phase-shapep'), so its sequence is the committed count.
(defthm fn-sbud-pending-sequence-is-used
  (implies (and (fn-sf-statep (fn-sn-files s))
                (fn-sf-record-phasep (fn-sf-phase (fn-sn-files s))))
           (equal (fn-sbud-pending-sequence s) (fn-sbud-used s)))
  :hints (("Goal"
           :use ((:instance fn-sbud-candidate-takes-sequence-used
                            (record (fn-sf-record-candidate (fn-sn-files s)))
                            (frontier (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (e/d (fn-sf-statep fn-sf-phase-shapep fn-sbud-used)
                           (fn-sf-record-listp fn-sf-candidatep)))))

(local
 (defthm fn-sbud-names-append-next
   (implies (and (natp start) (natp n))
            (equal (append (fn-sbud-names start n)
                           (list (fn-bs-txn-name (+ start n))))
                   (fn-sbud-names start (1+ n))))))

(local
 (defthm fn-sbud-observation-pairs-of-names
   (implies (natp start)
            (equal (fn-bs-txn-observation-pairs (fn-sbud-names start n) start)
                   (fn-sbud-name-pairs start n)))))

(local
 (defthm fn-sbud-observation-pairs-of-names-and-next
   (implies (natp n)
            (equal (fn-bs-txn-observation-pairs
                    (append (fn-sbud-names 0 n) (list (fn-bs-txn-name n)))
                    0)
                   (fn-sbud-name-pairs 0 (1+ n))))
   :hints (("Goal" :use (:instance fn-sbud-names-append-next (start 0))
            :in-theory (disable fn-sbud-names-append-next)))))

; The keystone.  The name the host writes for the staged record -- the
; called `fn-sbud-txn-name' of the called `fn-sbud-pending-sequence' -- is
; the one name that extends the committed namespace 0 .. used-1 to a
; namespace the scan accepts, bound to sequence `used'.
(defthm fn-sbud-pending-name-is-the-scans-next-name
  (implies (and (fn-sf-statep (fn-sn-files s))
                (fn-sf-record-phasep (fn-sf-phase (fn-sn-files s))))
           (equal (fn-bs-txn-observation-pairs
                   (append (fn-sbud-names 0 (fn-sbud-used s))
                           (list (fn-sbud-txn-name
                                  (fn-sbud-pending-sequence s))))
                   0)
                  (fn-sbud-name-pairs 0 (1+ (fn-sbud-used s)))))
  :hints (("Goal"
           :use (fn-sbud-pending-sequence-is-used
                 (:instance fn-sbud-observation-pairs-of-names-and-next
                            (n (fn-sbud-used s))))
           :in-theory (e/d (fn-sbud-txn-name)
                           (fn-sbud-used fn-sbud-names fn-sbud-name-pairs
                            fn-sbud-pending-sequence fn-sf-statep
                            fn-sf-record-phasep
                            fn-bs-txn-observation-pairs
                            fn-sbud-observation-pairs-of-names-and-next
                            fn-sbud-observation-pairs-of-names
                            fn-sbud-names-append-next)))))

; -----------------------------------------------------------------------------
; The POST payload bound

(defun fn-sbud-payload-bound (profile)
  "The payload octets one article may carry under the persisted PROFILE: its
max_article_octets field A, or 0 when PROFILE is not admitted."
  (declare (xargs :guard t))
  (fn-bs-profile-max-article-octets profile))

(defun fn-sbud-group-bound (profile)
  "The newsgroups one article may name under PROFILE: its
max_groups_per_article field G, or 0 when PROFILE is not admitted."
  (declare (xargs :guard t))
  (fn-bs-profile-max-groups-per-article profile))

(defun fn-sbud-post-boundary (profile msgid payload-length group-count charge)
  "The whole POST admission boundary under the persisted PROFILE."
  (declare (xargs :guard t))
  (cond ((not (fn-af-message-idp msgid)) :bad-message-id)
        ((or (not (natp payload-length))
             (< (fn-sbud-payload-bound profile) payload-length))
         :payload-bound)
        ((or (not (posp group-count))
             (< (fn-sbud-group-bound profile) group-count))
         :group-bound)
        ((or (not (posp charge)) (< *fn-cbor-max-uint* charge))
         :charge-bound)
        (t :ok)))

; Every profile's bounds fit the record codec's payload and group fields
; (`fn-bs-profile-validp-codecs-accept'), so a payload and group list the
; boundary admits are ones `fn-record-make' can carry.
(defthm fn-sbud-payload-bound-within-record-codec
  (and (<= (fn-sbud-payload-bound profile) *fn-record-max-payload*)
       (<= (fn-sbud-group-bound profile) *fn-record-max-groups*))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bs-profile-validp-codecs-accept
                                   (values profile)))
           :in-theory (disable fn-bs-profile-max-article-octets
                               fn-bs-profile-max-groups-per-article))))

; The named presets: A is the format-7 payload, and G is the record codec's
; group ceiling, which the format-7 translation carries by name
; (`fn-bs-profile-from-format-7'), so it moves with the codec (65,535 since
; bounds-p2).
(defthm fn-sbud-named-profile-payload-bounds
  (and (equal (fn-sbud-payload-bound (fn-bs-config-for-profile :development))
              32768)
       (equal (fn-sbud-payload-bound (fn-bs-config-for-profile :scale))
              32768)
       (equal (fn-sbud-group-bound (fn-bs-config-for-profile :scale))
              *fn-bs-profile-groups-ceiling-codec*)))

; The keystone of the bound: with a well-formed Message-ID, a group count
; within the profile's G and a charge in range, the boundary admits exactly
; the payloads at or under the profile's A, and refuses every longer one
; with `:payload-bound'.
(defthm fn-sbud-post-boundary-refuses-exactly-past-the-profile-bound
  (implies (and (fn-af-message-idp msgid)
                (natp payload-length)
                (posp group-count) (<= group-count (fn-sbud-group-bound profile))
                (posp charge) (<= charge *fn-cbor-max-uint*))
           (equal (fn-sbud-post-boundary profile msgid payload-length
                                         group-count charge)
                  (if (<= payload-length (fn-sbud-payload-bound profile))
                      :ok
                    :payload-bound)))
  :hints (("Goal" :in-theory (disable fn-sbud-payload-bound fn-sbud-group-bound
                                      fn-af-message-idp))))

; -----------------------------------------------------------------------------
; The signed article's record bound (D27)
;
; A signed POST is stored as one kind-4 composite: its article record, its
; exact authored source and their verdict (books/stx-accept-records).  The
; article is held to the profile's A at `fn-sbud-post-boundary' like any
; other; the composite, which carries the article and its source, is held to
; the profile's record field R here, over the octets the Store frames
; (`fn-store-event-encode').  host/native/owner.lisp
; `fnn-owner-attempt-transit' asks this (through host/owner-host.lisp
; `fn-owner-signed-event-boundary') for every event `fn-pa-authorized-event'
; or `fn-pa-carried-event' builds, before `fnn-owner-identity-commit', and
; sends the refusal word to the poster: `:event' when no composite was
; formed, `:signed-record' past R (books/nntp-post.lisp names both).
(defun fn-sbud-signed-event-boundary (profile event)
  (declare (xargs :guard t))
  (cond ((not (fn-stxa-p event)) :event)
        ((< (fn-bs-profile-max-record-octets profile)
            (len (fn-stxa-encode event)))
         :signed-record)
        (t :ok)))

; The octets it measures are the ones the Store frames: a composite is no
; other event kind, so `fn-store-event-encode' is its own encoding.
(defthm fn-sbud-store-event-encode-of-composite
  (implies (fn-stxa-p event)
           (equal (fn-store-event-encode event) (fn-stxa-encode event)))
  :hints (("Goal" :in-theory (enable fn-store-event-encode
                                     fn-store-retention-event-p
                                     fn-store-event-nth
                                     fn-stxa-p fn-stxa-shapep
                                     fn-record-p fn-record-shapep
                                     fn-stxe-p fn-stxe-shapep
                                     fn-stxk-p fn-stxk-shapep
                                     fn-stxa-sequence fn-record-uint32p))))

; KEYSTONE (the signed composite the boundary admits is one the publish gate
; admits).  An :ok composite, under an admitted profile with a transaction
; left, satisfies `fn-bs-publication-admissiblep' at its own framed length:
; the count and single-record gate the Store publication checks.
(defthm fn-sbud-signed-event-boundary-ok-is-publishable
  (implies (and (equal (fn-sbud-signed-event-boundary profile event) :ok)
                (fn-bs-profile-admittedp profile)
                (natp count)
                (< count (fn-bs-profile-max-transactions profile)))
           (fn-bs-publication-admissiblep
            profile count (len (fn-store-event-encode event))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-publication-admissiblep
                                   fn-bs-profile-record-ceiling
                                   fn-sbud-store-event-encode-of-composite)
                                  (fn-store-event-encode fn-stxa-encode
                                   fn-bs-profile-max-record-octets
                                   fn-bs-profile-max-transactions
                                   fn-bs-profile-admittedp fn-stxa-p)))))

; KEYSTONE (the record bound is the profile's, and exactly it).  For every
; composite, the boundary refuses exactly the ones whose framed octets exceed
; the profile's R, with `:signed-record'; no constant of the codec enters.
(defthm fn-sbud-signed-event-boundary-refuses-exactly-past-the-record-field
  (implies (fn-stxa-p event)
           (equal (fn-sbud-signed-event-boundary profile event)
                  (if (<= (len (fn-store-event-encode event))
                          (fn-bs-profile-max-record-octets profile))
                      :ok
                    :signed-record)))
  :hints (("Goal" :in-theory (e/d (fn-sbud-store-event-encode-of-composite)
                                  (fn-store-event-encode fn-stxa-encode
                                   fn-bs-profile-max-record-octets
                                   fn-stxa-p)))))

(in-theory (disable fn-sbud-pending-sequence fn-sbud-txn-name
                    fn-sbud-payload-bound fn-sbud-group-bound
                    fn-sbud-post-boundary fn-sbud-signed-event-boundary))
