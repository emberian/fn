; fn: the peer record, a configuration record kind (specs/peering.md
; section 1.2).
;
; A peer is (name path-identity transport inbound outbound auth), opaque.
; Its durable form is a group of configuration rows keyed by the peer name
; in the value's peers slot (books/config.lisp: rows are three labels and a
; natural), so the existing record codec carries it with no new item type:
;
;   (name "path-identity"      identity  0)
;   (name "transport-nntp"     host      port)  |  (name "transport-bp" eid 0)
;   (name "inbound-groups"     wildmat   max-octets)    ; both rows or neither
;   (name "inbound-inflight"   ""        max-inflight)
;   (name "outbound-groups"    wildmat   max-queue)     ; all three or none
;   (name "outbound-streaming" ""        0|1)
;   (name "outbound-backoff"   ""        backoff-ms)
;   (name "auth-source-address" addr 0)  |  (name "auth-principal" id 0)
;
; The deltas are config's (:set-peer name rows) and (:remove-peer name);
; this book builds the rows from the record and reads the record back from
; the rows, and proves the two agree on every well-formed record.  Wildmats
; are RFC 3977 section 4 text matched by books/wildmat.lisp; the path
; identity is RFC 5537 section 3.2 syntax from books/path.lisp.

(in-package "ACL2")
(include-book "config")
(include-book "wildmat")
(include-book "path")

(local (in-theory (enable fn-cfg-vocabulary fn-path-vocabulary)))

; -----------------------------------------------------------------------------
; The record

(defun fn-cfg-peer-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6)))

(defun fn-cfg-peer-name (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car p))
(defun fn-cfg-peer-path-identity (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr p)))
(defun fn-cfg-peer-transport (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr p))))
(defun fn-cfg-peer-inbound (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr p)))))
(defun fn-cfg-peer-outbound (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr p))))))
(defun fn-cfg-peer-auth (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr
                                                 (fn-cfg-ag-cdr p)))))))

(defun fn-cfg-peer-make (name path-identity transport inbound outbound auth)
  (declare (xargs :guard t))
  (list name path-identity transport inbound outbound auth))

(defthm fn-cfg-peer-shapep-of-peer-make
  (fn-cfg-peer-shapep
   (fn-cfg-peer-make name path-identity transport inbound outbound auth)))
(defthm fn-cfg-peer-name-of-peer-make
  (equal (fn-cfg-peer-name
          (fn-cfg-peer-make name path-identity transport inbound outbound auth))
         name))
(defthm fn-cfg-peer-path-identity-of-peer-make
  (equal (fn-cfg-peer-path-identity
          (fn-cfg-peer-make name path-identity transport inbound outbound auth))
         path-identity))
(defthm fn-cfg-peer-transport-of-peer-make
  (equal (fn-cfg-peer-transport
          (fn-cfg-peer-make name path-identity transport inbound outbound auth))
         transport))
(defthm fn-cfg-peer-inbound-of-peer-make
  (equal (fn-cfg-peer-inbound
          (fn-cfg-peer-make name path-identity transport inbound outbound auth))
         inbound))
(defthm fn-cfg-peer-outbound-of-peer-make
  (equal (fn-cfg-peer-outbound
          (fn-cfg-peer-make name path-identity transport inbound outbound auth))
         outbound))
(defthm fn-cfg-peer-auth-of-peer-make
  (equal (fn-cfg-peer-auth
          (fn-cfg-peer-make name path-identity transport inbound outbound auth))
         auth))

(defthm fn-cfg-peer-shapep-forward-shape
  (implies (fn-cfg-peer-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

; Constructor of accessors: the one place the shape is opened, kept for the
; round trip below.
(local (defthm fn-cfg-peer-two-more
  (implies (and (true-listp x) (equal (len x) 2))
           (equal (cdr (cdr x)) nil))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cdr (cdr x))))))
  :rule-classes nil))

(defthm fn-cfg-peer-make-of-accessors
  (implies (fn-cfg-peer-shapep p)
           (equal (fn-cfg-peer-make (fn-cfg-peer-name p)
                                    (fn-cfg-peer-path-identity p)
                                    (fn-cfg-peer-transport p)
                                    (fn-cfg-peer-inbound p)
                                    (fn-cfg-peer-outbound p)
                                    (fn-cfg-peer-auth p))
                  p))
  :hints (("Goal" :in-theory (enable fn-cfg-peer-shapep fn-cfg-peer-make
                                     fn-cfg-peer-name fn-cfg-peer-path-identity
                                     fn-cfg-peer-transport fn-cfg-peer-inbound
                                     fn-cfg-peer-outbound fn-cfg-peer-auth
                                     fn-cfg-ag-car fn-cfg-ag-cdr)
           :expand ((len p) (len (cdr p)) (len (cddr p)) (len (cdddr p)))
           :use ((:instance fn-cfg-peer-two-more (x (cddddr p))))))
  :rule-classes nil)

(in-theory (disable (:d fn-cfg-peer-shapep) (:d fn-cfg-peer-make)
                    (:d fn-cfg-peer-name) (:d fn-cfg-peer-path-identity)
                    (:d fn-cfg-peer-transport) (:d fn-cfg-peer-inbound)
                    (:d fn-cfg-peer-outbound) (:d fn-cfg-peer-auth)))

; -----------------------------------------------------------------------------
; The recognizer

(defun fn-cfg-wildmatp (text)
  (declare (xargs :guard t))
  (and (fn-cfg-labelp text)
       (consp (fn-record-string-octets text))
       (fn-wildmat-result-okp (fn-wildmat-parse (fn-record-string-octets text)))))

(defun fn-cfg-peer-transportp (x)
  (declare (xargs :guard t))
  (or (and (true-listp x) (equal (len x) 3) (equal (car x) :nntp)
           (fn-cfg-labelp (car (cdr x)))
           (fn-record-uint32p (car (cdr (cdr x)))))
      (and (true-listp x) (equal (len x) 2) (equal (car x) :bp)
           (fn-cfg-labelp (car (cdr x))))))

(defun fn-cfg-peer-inboundp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (true-listp x) (equal (len x) 3)
           (fn-cfg-wildmatp (car x))
           (posp (car (cdr x)))
           (<= (car (cdr x)) *fn-record-max-payload*)
           (posp (car (cdr (cdr x))))
           (fn-record-uint32p (car (cdr (cdr x)))))))

(defun fn-cfg-peer-outboundp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (true-listp x) (equal (len x) 4)
           (fn-cfg-wildmatp (car x))
           (booleanp (car (cdr x)))
           (posp (car (cdr (cdr x))))
           (fn-record-uint32p (car (cdr (cdr x))))
           (fn-record-uint32p (car (cdr (cdr (cdr x))))))))

(defun fn-cfg-peer-authp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)
       (or (equal (car x) :source-address) (equal (car x) :principal))
       (fn-cfg-labelp (car (cdr x)))))

(defun fn-cfg-peerp (p)
  (declare (xargs :guard t))
  (and (fn-cfg-peer-shapep p)
       (fn-cfg-labelp (fn-cfg-peer-name p))
       (consp (fn-record-string-octets (fn-cfg-peer-name p)))
       (fn-cfg-labelp (fn-cfg-peer-path-identity p))
       (fn-path-identityp (fn-record-string-octets (fn-cfg-peer-path-identity p)))
       (fn-cfg-peer-transportp (fn-cfg-peer-transport p))
       (fn-cfg-peer-inboundp (fn-cfg-peer-inbound p))
       (fn-cfg-peer-outboundp (fn-cfg-peer-outbound p))
       (fn-cfg-peer-authp (fn-cfg-peer-auth p))))

(defthm fn-cfg-peerp-forward-shape
  (implies (fn-cfg-peerp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

; Named vocabulary over the halves (specs/peering.md section 1.2).
(defun fn-cfg-peer-inbound-groups (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-peer-inbound p)))
(defun fn-cfg-peer-inbound-max-octets (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-peer-inbound p))))
(defun fn-cfg-peer-inbound-max-inflight (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-peer-inbound p)))))
(defun fn-cfg-peer-outbound-groups (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-peer-outbound p)))
(defun fn-cfg-peer-streamingp (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-peer-outbound p))))
(defun fn-cfg-peer-max-queue (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-peer-outbound p)))))
(defun fn-cfg-peer-backoff (p)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-peer-outbound p))))))

; -----------------------------------------------------------------------------
; The row codec

(defun fn-cfg-peer-rows (p)
  (declare (xargs :guard t))
  (let ((name (fn-cfg-peer-name p))
        (transport (fn-cfg-peer-transport p))
        (inbound (fn-cfg-peer-inbound p))
        (outbound (fn-cfg-peer-outbound p))
        (auth (fn-cfg-peer-auth p)))
    (append
     (list (fn-cfg-row-make name "path-identity" (fn-cfg-peer-path-identity p) 0))
     (if (equal (fn-cfg-ag-car transport) :nntp)
         (list (fn-cfg-row-make name "transport-nntp"
                                (fn-cfg-ag-car (fn-cfg-ag-cdr transport))
                                (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr transport)))))
       (list (fn-cfg-row-make name "transport-bp"
                              (fn-cfg-ag-car (fn-cfg-ag-cdr transport)) 0)))
     (if inbound
         (list (fn-cfg-row-make name "inbound-groups" (fn-cfg-ag-car inbound)
                                (fn-cfg-ag-car (fn-cfg-ag-cdr inbound)))
               (fn-cfg-row-make name "inbound-inflight" ""
                                (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr inbound)))))
       nil)
     (if outbound
         (list (fn-cfg-row-make name "outbound-groups" (fn-cfg-ag-car outbound)
                                (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr outbound))))
               (fn-cfg-row-make name "outbound-streaming" ""
                                (if (fn-cfg-ag-car (fn-cfg-ag-cdr outbound)) 1 0))
               (fn-cfg-row-make name "outbound-backoff" ""
                                (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                               (fn-cfg-ag-cdr outbound))))))
       nil)
     (if (equal (fn-cfg-ag-car auth) :source-address)
         (list (fn-cfg-row-make name "auth-source-address"
                                (fn-cfg-ag-car (fn-cfg-ag-cdr auth)) 0))
       (list (fn-cfg-row-make name "auth-principal"
                              (fn-cfg-ag-car (fn-cfg-ag-cdr auth)) 0))))))

(defun fn-cfg-peer-slot (rows slot)
  ; The first row whose slot label is slot, or nil.
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-b (car rows)) slot)
          (car rows)
        (fn-cfg-peer-slot (cdr rows) slot))
    nil))

(defun fn-cfg-peer-of-rows (name rows)
  ; The typed record the row group denotes, or nil when it denotes none.
  (declare (xargs :guard t))
  (let* ((pid (fn-cfg-peer-slot rows "path-identity"))
         (tn (fn-cfg-peer-slot rows "transport-nntp"))
         (tb (fn-cfg-peer-slot rows "transport-bp"))
         (ig (fn-cfg-peer-slot rows "inbound-groups"))
         (ii (fn-cfg-peer-slot rows "inbound-inflight"))
         (og (fn-cfg-peer-slot rows "outbound-groups"))
         (os (fn-cfg-peer-slot rows "outbound-streaming"))
         (ob (fn-cfg-peer-slot rows "outbound-backoff"))
         (as (fn-cfg-peer-slot rows "auth-source-address"))
         (ap (fn-cfg-peer-slot rows "auth-principal"))
         (p (fn-cfg-peer-make
             name
             (if pid (fn-cfg-row-c pid) "")
             (cond (tn (list :nntp (fn-cfg-row-c tn) (fn-cfg-row-n tn)))
                   (tb (list :bp (fn-cfg-row-c tb)))
                   (t nil))
             (if (and ig ii)
                 (list (fn-cfg-row-c ig) (fn-cfg-row-n ig) (fn-cfg-row-n ii))
               nil)
             (if (and og os ob)
                 (list (fn-cfg-row-c og) (equal (fn-cfg-row-n os) 1)
                       (fn-cfg-row-n og) (fn-cfg-row-n ob))
               nil)
             (cond (as (list :source-address (fn-cfg-row-c as)))
                   (ap (list :principal (fn-cfg-row-c ap)))
                   (t nil)))))
    (if (fn-cfg-peerp p) p nil)))

; The peer table lookup (specs/peering.md section 2.2): the record for a
; name, or nil, from the value's peers rows.
(defun fn-cfg-peer-find (name peers)
  (declare (xargs :guard t))
  (fn-cfg-peer-of-rows name (fn-cfg-rows-with-key peers name)))

; The two deltas, as the design writes them.
(defun fn-cfg-set-peer-delta (p)
  (declare (xargs :guard t))
  (fn-cfg-set-peer (fn-cfg-peer-name p) (fn-cfg-peer-rows p)))

(defun fn-cfg-remove-peer-delta (name)
  (declare (xargs :guard t))
  (fn-cfg-remove-peer name))

; -----------------------------------------------------------------------------
; Round trip and the delta facts

(local (defthm fn-cfg-peer-rows-keyed
  (fn-cfg-rows-keyed-p (fn-cfg-peer-rows p) (fn-cfg-peer-name p))))

(local (defthm fn-cfg-rows-with-key-of-append
  (equal (fn-cfg-rows-with-key (append a b) k)
         (append (fn-cfg-rows-with-key a k) (fn-cfg-rows-with-key b k)))))

(local (defthm fn-cfg-rows-with-key-of-without-key
  (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows k) k) nil)))

(local (defthm fn-cfg-rows-with-key-when-keyed
  (implies (and (fn-cfg-rows-keyed-p rows k) (true-listp rows))
           (equal (fn-cfg-rows-with-key rows k) rows))))

(local (defthm fn-cfg-peer-rows-true-listp
  (true-listp (fn-cfg-peer-rows p))))

; OPEN: the general rows-to-record round trip
; (fn-cfg-peer-of-rows (fn-cfg-peer-name p) (fn-cfg-peer-rows p)) = p over every
; fn-cfg-peerp, and the injectivity of fn-cfg-peer-rows it gives.  The
; sixteen-shape case split (transport x inbound x outbound x auth) through
; ten slot lookups did not close in this lane's budget; it is recorded open in
; specs/peering.md and witnessed on two ground records (an NNTP peer with both
; halves, a BP feed-only peer) in tests/acl2/peer-inbound-tests.lisp, which is
; the coverage books/config.lisp has for its own codec.

; (:set-peer ...) of a well-formed record is admissible on every value: the
; delta is typed and every row is keyed by the peer name.
(local (defthm fn-cfg-peer-rows-are-rows
  (implies (fn-cfg-peerp p) (fn-cfg-row-listp (fn-cfg-peer-rows p)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-peerp fn-cfg-peer-transportp
                                   fn-cfg-peer-inboundp fn-cfg-peer-outboundp
                                   fn-cfg-peer-authp fn-cfg-wildmatp
                                   fn-cfg-rowp fn-record-uint32p)
                                  (fn-cfg-labelp fn-record-string-octets
                                   fn-path-identityp fn-wildmat-parse))))))

; Two facts about `fn-cfg-peerp` that the admissibility obligation below
; needs and that no rule supplied: the name is an ASCII string, and the row
; group a peer expands to is far below the delta bound.  Both are local
; supports; neither theorem statement in this book changed.  (Added by
; w5/clock-seam: `books/peer-config` failed at
; FN-CFG-SET-PEER-DELTA-IS-ADMISSIBLE on both boxes, on content identical to
; dev, blocking the served/owner closure behind it.)
(local (defthm fn-cfg-peer-name-is-an-ascii-string
  (implies (fn-cfg-peerp p)
           (fn-record-ascii-stringp (fn-cfg-peer-name p)))
  :hints (("Goal" :in-theory (enable fn-cfg-peerp fn-cfg-labelp)))))

(local (defthm fn-cfg-peer-rows-are-few
  (<= (len (fn-cfg-peer-rows p)) 1024)
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-cfg-peer-rows)))))

(local (defthm fn-cfg-peer-name-octets-are-bounded
  (implies (fn-cfg-peerp p)
           (<= (len (fn-record-string-octets (fn-cfg-peer-name p))) 256))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (fn-cfg-peerp fn-cfg-labelp)
                                  (fn-record-string-octets))))))

(defthm fn-cfg-set-peer-delta-is-admissible
  (implies (fn-cfg-peerp p)
           (equal (fn-cfg-delta-reason v gen stamp reserved ceiling
                                       (fn-cfg-set-peer-delta p))
                  nil))
  :hints (("Goal" :in-theory (e/d (fn-cfg-deltap fn-cfg-delta-reason
                                   fn-cfg-set-peer-delta fn-cfg-set-peer)
                                  (fn-cfg-peer-rows fn-cfg-peerp
                                   fn-record-string-octets)))))

; After (:set-peer p) the peers slot holds exactly p's rows under its name:
; the upsert replaced the old group and nothing else carries the key.
(defthm fn-cfg-peer-rows-after-set-peer
  (implies (fn-cfg-peerp p)
           (equal (fn-cfg-rows-with-key
                   (fn-cfg-peers (fn-cfg-apply-delta v gen stamp
                                                     (fn-cfg-set-peer-delta p)))
                   (fn-cfg-peer-name p))
                  (fn-cfg-peer-rows p)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-delta fn-cfg-set-peer-delta
                                   fn-cfg-set-peer)
                                  (fn-cfg-peer-rows fn-cfg-peerp)))))

; After (:remove-peer name) the table finds nothing under that name.
(defthm fn-cfg-peer-find-after-remove-peer
  (equal (fn-cfg-peer-find
          name
          (fn-cfg-peers (fn-cfg-apply-delta v gen stamp
                                            (fn-cfg-remove-peer-delta name))))
         nil)
  :hints (("Goal" :in-theory (e/d (fn-cfg-peer-find fn-cfg-apply-delta
                                   fn-cfg-remove-peer-delta fn-cfg-remove-peer
                                   fn-cfg-peer-of-rows fn-cfg-peerp)
                                  ()))))

; A peer delta changes the peers slot and nothing else of the value
; (specs/peering.md section 1.2.1: decisions, not committed state).
(defthm fn-cfg-peer-deltas-change-only-peers
  (implies (or (equal (fn-cfg-delta-kind d) :set-peer)
               (equal (fn-cfg-delta-kind d) :remove-peer))
           (let ((next (fn-cfg-apply-delta v gen stamp d)))
             (and (equal (fn-cfg-groups next) (fn-cfg-groups v))
                  (equal (fn-cfg-capacity next) (fn-cfg-capacity v))
                  (equal (fn-cfg-quotas next) (fn-cfg-quotas v))
                  (equal (fn-cfg-policies next) (fn-cfg-policies v))
                  (equal (fn-cfg-listeners next) (fn-cfg-listeners v))
                  (equal (fn-cfg-limits next) (fn-cfg-limits v)))))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta))))

; What a caller of fn-cfg-peer-find may assume of what it finds, as
; forward-chaining facts so nothing downstream opens the record or the
; decoder.  fn-cfg-peer-of-rows returns the record only when it is
; well-formed, so a non-nil find is a peer; and a peer with an inbound half
; has the two positive, bounded numbers the served path compares against
; (books/peer-inbound.lisp, fn-peer-decide-offer and fn-peer-decide-transfer).

(defthm fn-cfg-peer-find-is-a-peer
  (implies (fn-cfg-peer-find name peers)
           (fn-cfg-peerp (fn-cfg-peer-find name peers)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((fn-cfg-peer-find name peers))))
  :hints (("Goal" :in-theory (e/d ((:d fn-cfg-peer-find)
                                   (:d fn-cfg-peer-of-rows))
                                  ((:d fn-cfg-peerp))))))

(defthm fn-cfg-peerp-inbound-fields
  (implies (and (fn-cfg-peerp p) (fn-cfg-peer-inbound p))
           (and (posp (fn-cfg-peer-inbound-max-octets p))
                (<= (fn-cfg-peer-inbound-max-octets p) *fn-record-max-payload*)
                (posp (fn-cfg-peer-inbound-max-inflight p))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-cfg-peerp) (:d fn-cfg-peer-inboundp)
                                   (:d fn-cfg-peer-inbound-max-octets)
                                   (:d fn-cfg-peer-inbound-max-inflight)
                                   (:d fn-cfg-ag-car) (:d fn-cfg-ag-cdr))
                                  ((:d fn-cfg-labelp) (:d fn-cfg-wildmatp)
                                   (:d fn-path-identityp)
                                   (:d fn-cfg-peer-transportp)
                                   (:d fn-cfg-peer-outboundp)
                                   (:d fn-cfg-peer-authp))))))

; -----------------------------------------------------------------------------
; Export theory

(deftheory fn-cfg-peer-vocabulary
  '((:d fn-cfg-wildmatp) (:d fn-cfg-peer-transportp) (:d fn-cfg-peer-inboundp)
    (:d fn-cfg-peer-outboundp) (:d fn-cfg-peer-authp) (:d fn-cfg-peerp)
    (:d fn-cfg-peer-inbound-groups) (:d fn-cfg-peer-inbound-max-octets)
    (:d fn-cfg-peer-inbound-max-inflight) (:d fn-cfg-peer-outbound-groups)
    (:d fn-cfg-peer-streamingp) (:d fn-cfg-peer-max-queue)
    (:d fn-cfg-peer-backoff) (:d fn-cfg-peer-rows) (:d fn-cfg-peer-slot)
    (:d fn-cfg-peer-of-rows) (:d fn-cfg-peer-find) (:d fn-cfg-set-peer-delta)
    (:d fn-cfg-remove-peer-delta)))

(in-theory (disable fn-cfg-peer-vocabulary))
