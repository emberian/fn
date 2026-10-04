; Namespace and accounting for native FNWF/FNRJ/carry journals.
;
; Recovery feeds each observed record to this machine once.  Thereafter the
; carried frontier owns the next name, count, aggregate size, initialization
; state, and resolution headroom.  The host only observes names and byte
; lengths and executes an authorized immutable publication operation.
;
; How many records a journal admits over its life, and how many octets they
; total, are the operator's (D27; lane caps, B003): the journal's profile, a
; file `app-journal-profile' in the journal root, written by `app-journal
; profile' and read by every open (host/native/workflow.lisp fnn-app-open).
; Its absence is the default profile (2^20 records, 2^40 octets: the Store
; profile's namespace-count and history defaults), which every journal
; written before this file existed fits, since they ran under 4,096 records
; and at most 64 MiB.  The frontier carries the profile it was opened under.
;
; What ACL2 fixes is the relation, not the values (fn-aj-profile-validp):
; each field is a frame natural, so the profile file carries every value the
; relation admits (fn-ajpf-read-of-octets); at least three records and three
; widest records' octets, so a fresh journal admits its configuration and one
; intent with its reserved resolution (fn-aj-valid-profile-admits-first-work);
; and every sequence below a frame natural names a record of exactly
; twenty digits (fn-aj-record-name-fixed-width), the width at which the
; host's name sort is sequence order.  The profile of a journal that holds
; a record is only raised (fn-ajpf-write-keeps-the-journal): an outcome
; reserved under the profile in force stays admissible under every later
; one; an empty journal may take any valid profile.  A journal holding more
; than the profile it is opened under (the file was removed or replaced) is
; refused at recovery by name, :beyond-profile, never truncated.
(in-package "ACL2")
(include-book "journal-publish")
(include-book "byte-store-txn-name")
(include-book "frame")
(include-book "frame-invariants")
(include-book "consumer-position")
; PKT-869: the carry control journal's frame (domain :carry).
(include-book "bp-carry-frame")

(defun fn-aj-domainp (domain)
  (member-equal domain '(:workflow :receipt :carry)))

(defun fn-aj-max-record-length (domain)
  (+ *fn-frame-overhead-octets*
     (cond ((equal domain :workflow) *fn-frame-max-workflow-payload*)
           ((equal domain :carry) *fn-bpcc-frame-max-payload*)
           (t *fn-frame-max-receipt-payload*))))

(defun fn-aj-suffix (domain)
  (cond ((equal domain :workflow) '(#\. #\w #\f))
        ((equal domain :carry) '(#\. #\c #\c))
        (t '(#\. #\r #\j))))

(defun fn-aj-record-name-chars (domain sequence)
  (append (fn-bs-txn-digits sequence) (fn-aj-suffix domain)))

(defun fn-aj-record-name (domain sequence)
  (declare (xargs :guard t :verify-guards nil))
  (coerce (fn-aj-record-name-chars domain sequence) 'string))

; -----------------------------------------------------------------------------
; The journal's profile (D27): (RECORDS OCTETS), the records the journal
; admits over its life and the octets they total.

(defconst *fn-ajpf-format*
  '(102 110 45 97 106 45 112 114 111 102 105 108 101 45 49)) ; fn-aj-profile-1
(defconst *fn-ajpf-spec* '(:text :nat :nat))
; A configuration record, one intent and the resolution it reserves.
(defconst *fn-aj-profile-min-records* 3)
(defconst *fn-ajpf-default-records* 1048576)        ; 2^20
(defconst *fn-ajpf-default-octets* 1099511627776)   ; 2^40

(defun fn-ajpf-file-name ()
  (declare (xargs :guard t))
  "app-journal-profile")

; The profile file is one frame of a 15-octet text and two frame naturals;
; the read bound is a work bound on reading it, not a data cap.
(defun fn-ajpf-read-bound ()
  (declare (xargs :guard t))
  256)

(defun fn-aj-profile-validp (domain records octets)
  (and (fn-aj-domainp domain)
       (fn-frame-natp records)
       (fn-frame-natp octets)
       (<= *fn-aj-profile-min-records* records)
       (<= (* 3 (fn-aj-max-record-length domain)) octets)))

(defun fn-ajpf-default ()
  (declare (xargs :guard t))
  (list *fn-ajpf-default-records* *fn-ajpf-default-octets*))

(defun fn-ajpf-records (p) (if (consp p) (car p) 0))
(defun fn-ajpf-octets-limit (p)
  (if (and (consp p) (consp (cdr p))) (car (cdr p)) 0))

(defun fn-ajpf-profilep (domain p)
  (and (true-listp p) (equal (len p) 2)
       (fn-aj-profile-validp domain (fn-ajpf-records p) (fn-ajpf-octets-limit p))))

; The file's octets for a valid profile; NIL otherwise.
(defun fn-ajpf-octets (domain records octets)
  (if (fn-aj-profile-validp domain records octets)
      (fn-frame-fields-octets *fn-ajpf-spec*
                              (list *fn-ajpf-format* records octets))
    nil))

; The profile a DOMAIN journal opens under.  PRESENT is whether the file
; exists; BYTES its octets.  Absent: the default.  Present: (RECORDS OCTETS)
; when the octets are exactly one profile frame of a profile valid for
; DOMAIN, else NIL (the host refuses to open).
(defun fn-ajpf-read (domain present bytes)
  (if (not present)
      (if (fn-aj-domainp domain) (fn-ajpf-default) nil)
    (if (not (fn-cbor-octet-listp bytes))
        nil
      (let ((parsed (fn-frame-fields-parse *fn-ajpf-spec* bytes)))
        (if (not (fn-frame-parse-okp parsed))
            nil
          (let ((v (fn-frame-parse-value parsed)))
            (if (and (true-listp v) (equal (len v) 3)
                     (equal (car v) *fn-ajpf-format*)
                     (fn-aj-profile-validp domain (cadr v) (caddr v)))
                (list (cadr v) (caddr v))
              nil)))))))

; -----------------------------------------------------------------------------
; The frontier: (DOMAIN NEXT AGGREGATE INITIALIZEDP RECORDS OCTETS), the last
; two the profile it was opened under.

(defun fn-aj-state (domain next aggregate initializedp records octets)
  (list domain (nfix next) (nfix aggregate) (if initializedp t nil)
        (nfix records) (nfix octets)))

(defun fn-aj-domain (s) (if (consp s) (car s) nil))
(defun fn-aj-next (s) (if (consp (cdr s)) (car (cdr s)) 0))
(defun fn-aj-aggregate (s)
  (if (consp (cdr (cdr s))) (car (cdr (cdr s))) 0))
(defun fn-aj-initializedp (s)
  (if (consp (cdr (cdr (cdr s))))
      (car (cdr (cdr (cdr s)))) nil))
(defun fn-aj-max-records (s) (nfix (nth 4 s)))
(defun fn-aj-max-octets (s) (nfix (nth 5 s)))

(defun fn-aj-statep (s)
  (and (true-listp s)
       (equal (len s) 6)
       (fn-aj-profile-validp (fn-aj-domain s)
                             (nth 4 s) (nth 5 s))
       (natp (fn-aj-next s))
       (<= (fn-aj-next s) (fn-aj-max-records s))
       (natp (fn-aj-aggregate s))
       (<= (fn-aj-aggregate s) (fn-aj-max-octets s))
       (if (zp (fn-aj-next s)) (equal (fn-aj-aggregate s) 0) t)
       (booleanp (fn-aj-initializedp s))
       (equal (fn-aj-initializedp s)
              (if (zp (fn-aj-next s)) nil t))))

; The empty frontier of a DOMAIN journal opened under PROFILE (what
; fn-ajpf-read answered).
(defun fn-aj-initial (domain profile)
  (if (fn-ajpf-profilep domain profile)
      (fn-aj-state domain 0 0 nil
                   (fn-ajpf-records profile) (fn-ajpf-octets-limit profile))
    :fault))

(defun fn-aj-kind-allowedp (s kind)
  (if (fn-aj-initializedp s)
      (not (equal kind :config))
    (equal kind :config)))

(defun fn-aj-advance (s frame-length)
  (fn-aj-state (fn-aj-domain s)
               (+ 1 (fn-aj-next s))
               (+ (fn-aj-aggregate s) (nfix frame-length))
               t
               (fn-aj-max-records s)
               (fn-aj-max-octets s)))

(defun fn-aj-fits-p (s frame-length reserve-resolutionp)
  (let* ((domain (fn-aj-domain s))
         (reserve-slots (if reserve-resolutionp 2 1))
         (reserve-bytes (if reserve-resolutionp
                            (fn-aj-max-record-length domain) 0)))
    (and (natp frame-length)
         (<= frame-length (fn-aj-max-record-length domain))
         (<= (+ (fn-aj-next s) reserve-slots) (fn-aj-max-records s))
         (<= (+ (fn-aj-aggregate s) frame-length reserve-bytes)
             (fn-aj-max-octets s)))))

(defun fn-aj-recover-record (s observed-name frame-length kind)
  ; OBSERVED-NAME and FRAME-LENGTH are filesystem observations.  ACL2 owns
  ; their interpretation and advances the frontier only on an exact
  ; next-name/configuration match.  A well-formed next record the profile
  ; in force does not admit is :beyond-profile (the journal was written
  ; under a larger profile), never skipped.
  (if (and (fn-aj-statep s)
           (stringp observed-name)
           (equal observed-name
                  (fn-aj-record-name (fn-aj-domain s)
                                     (fn-aj-next s)))
           (fn-aj-kind-allowedp s kind)
           (natp frame-length)
           (<= frame-length (fn-aj-max-record-length (fn-aj-domain s))))
      (if (fn-aj-fits-p s frame-length nil)
          (fn-aj-advance s frame-length)
        :beyond-profile)
    :fault))

; The octets `app-journal profile' publishes for a journal whose frontier is
; S: NIL (refused) unless the profile is valid for S's domain and either the
; journal holds no record yet (nothing to strand: any valid profile) or the
; write raises or keeps both fields in force.
(defun fn-ajpf-write-octets (s records octets)
  (if (and (fn-aj-statep s)
           (fn-aj-profile-validp (fn-aj-domain s) records octets)
           (or (zp (fn-aj-next s))
               (and (<= (fn-aj-max-records s) records)
                    (<= (fn-aj-max-octets s) octets))))
      (fn-ajpf-octets (fn-aj-domain s) records octets)
    nil))

; (:ok final-name kind publication successor) is an authorized operation issued
; after the caller reports ownership of the journal lock and absence of ACL2's
; exact next name.  These are trusted host observations, not an unforgeable
; capability against hostile raw Lisp.  The executor receives the embedded
; publication state and does not independently assert the premise.
(defun fn-aj-authorize (s kind frame-length reserve-resolutionp
                              lock-ownedp next-absentp)
  (if (and (fn-aj-statep s)
           (keywordp kind)
           (fn-aj-kind-allowedp s kind)
           (fn-aj-fits-p s frame-length reserve-resolutionp)
           (equal lock-ownedp t)
           (equal next-absentp t))
      (list :ok
            (fn-aj-record-name (fn-aj-domain s) (fn-aj-next s))
            kind
            (fn-jpub-initial t)
            (fn-aj-advance s frame-length))
    (list :refused :journal-admission)))

(defun fn-aj-operationp (operation)
  (and (true-listp operation)
       (equal (len operation) 5)
       (equal (car operation) :ok)
       (stringp (car (cdr operation)))
       (keywordp (car (cdr (cdr operation))))
       (fn-jpub-statep (car (cdr (cdr (cdr operation)))))
       (equal (fn-jpub-next-action (car (cdr (cdr (cdr operation))))) :stage)
       (fn-aj-statep (car (cdr (cdr (cdr (cdr operation))))))))

(defun fn-aj-operation-name (operation) (car (cdr operation)))
(defun fn-aj-operation-label (operation) (car (cdr (cdr operation))))
(defun fn-aj-operation-publication (operation)
  (car (cdr (cdr (cdr operation)))))
(defun fn-aj-operation-successor (operation)
  (car (cdr (cdr (cdr (cdr operation))))))


(defthm fn-aj-authorize-produces-operation
  (implies (equal (car (fn-aj-authorize s kind frame-length reserve
                                        lock-ownedp next-absentp))
                  :ok)
           (fn-aj-operationp
            (fn-aj-authorize s kind frame-length reserve
                             lock-ownedp next-absentp))))

(defthm fn-aj-authorized-successor-advances-once
  (implies (equal (car (fn-aj-authorize s kind frame-length reserve
                                        lock-ownedp next-absentp))
                  :ok)
           (equal (fn-aj-next
                   (fn-aj-operation-successor
                    (fn-aj-authorize s kind frame-length reserve
                                     lock-ownedp next-absentp)))
                  (+ 1 (fn-aj-next s)))))

; The default profile is a profile of every domain.
(defthm fn-ajpf-default-is-a-profile
  (implies (fn-aj-domainp domain)
           (fn-ajpf-profilep domain (fn-ajpf-default))))

(local
 (defthm fn-ajpf-values-ok
   (implies (fn-aj-profile-validp domain records octets)
            (fn-frame-values-okp *fn-ajpf-spec*
                                 (list *fn-ajpf-format* records octets)))
   :hints (("Goal" :in-theory (enable fn-frame-values-okp fn-frame-field-okp)))))

; Keystone: a saved profile opens.  The octets written for every profile the
; relation admits read back as exactly that profile, so validation and
; representation agree: no valid profile is one the file cannot carry.
(defthm fn-ajpf-read-of-octets
  (implies (fn-aj-profile-validp domain records octets)
           (equal (fn-ajpf-read domain t (fn-ajpf-octets domain records octets))
                  (list records octets)))
  :hints (("Goal" :in-theory (e/d (fn-ajpf-octets)
                                  (fn-frame-fields-octets fn-frame-fields-parse
                                   fn-aj-profile-validp))
           :use ((:instance fn-frame-fields-parse-of-octets
                  (specs *fn-ajpf-spec*)
                  (values (list *fn-ajpf-format* records octets)))
                 (:instance fn-frame-fields-octets-are-octets
                  (specs *fn-ajpf-spec*)
                  (values (list *fn-ajpf-format* records octets)))))))

; What an open reads is always a valid profile or a refusal.
(defthm fn-ajpf-read-is-a-profile
  (let ((p (fn-ajpf-read domain present bytes)))
    (implies p (fn-ajpf-profilep domain p)))
  :hints (("Goal" :in-theory (disable fn-frame-fields-parse))))

; Every profile an open reads opens a frontier carrying exactly it.
(defthm fn-aj-statep-of-initial
  (implies (fn-ajpf-profilep domain profile)
           (let ((s (fn-aj-initial domain profile)))
             (and (fn-aj-statep s)
                  (equal (fn-aj-domain s) domain)
                  (equal (fn-aj-next s) 0)
                  (equal (fn-aj-max-records s) (fn-ajpf-records profile))
                  (equal (fn-aj-max-octets s) (fn-ajpf-octets-limit profile))))))

; Keystone (the reservation): an intent admitted with its resolution
; reserved leaves room for one resolution of the widest frame, so an outcome
; owed to a durable intent is never refused for capacity.
(defthm fn-aj-reserved-resolution-fits
  (implies (and (equal (car (fn-aj-authorize s kind frame-length t
                                             lock-ownedp next-absentp))
                       :ok)
                (keywordp outcome-kind)
                (not (equal outcome-kind :config))
                (natp outcome-length)
                (<= outcome-length
                    (fn-aj-max-record-length (fn-aj-domain s))))
           (equal (car (fn-aj-authorize
                        (fn-aj-operation-successor
                         (fn-aj-authorize s kind frame-length t
                                          lock-ownedp next-absentp))
                        outcome-kind outcome-length nil t t))
                  :ok)))

; Satisfiable: every profile the relation admits opens a journal that takes
; its configuration and one intent of the widest frame with its resolution
; reserved, and then that resolution.
(defthm fn-aj-valid-profile-admits-first-work
  (implies (and (fn-ajpf-profilep domain profile)
                (keywordp kind) (not (equal kind :config)))
           (let* ((l (fn-aj-max-record-length domain))
                  (op1 (fn-aj-authorize (fn-aj-initial domain profile)
                                        :config l nil t t))
                  (op2 (fn-aj-authorize (fn-aj-operation-successor op1)
                                        kind l t t t))
                  (op3 (fn-aj-authorize (fn-aj-operation-successor op2)
                                        kind l nil t t)))
             (and (equal (car op1) :ok)
                  (equal (car op2) :ok)
                  (equal (car op3) :ok)))))

; Keystone: an admitted write reads back as written, and the journal it was
; written for reopens under it: its frontier, carrying the new profile, is a
; frontier that admits whatever the old one admitted.  A journal that holds
; a record is only ever raised.
(defthm fn-ajpf-write-keeps-the-journal
  (let ((w (fn-ajpf-write-octets s records octets))
        (r (fn-aj-state (fn-aj-domain s) (fn-aj-next s)
                        (fn-aj-aggregate s) (fn-aj-initializedp s)
                        records octets)))
    (implies w
             (and (equal (fn-ajpf-read (fn-aj-domain s) t w)
                         (list records octets))
                  (fn-aj-statep r)
                  (implies (not (zp (fn-aj-next s)))
                           (and (<= (fn-aj-max-records s) records)
                                (<= (fn-aj-max-octets s) octets)))
                  (implies (and (not (zp (fn-aj-next s)))
                                (fn-aj-fits-p s frame-length reserve))
                           (fn-aj-fits-p r frame-length reserve)))))
  :hints (("Goal" :in-theory (disable fn-ajpf-read fn-ajpf-octets))))

; Teeth: a well-formed next record past the profile in force is refused by
; name at recovery, never admitted or skipped.
(defthm fn-aj-recover-past-profile-is-named
  (implies (and (fn-aj-statep s)
                (equal (fn-aj-next s) (fn-aj-max-records s))
                (fn-aj-kind-allowedp s kind)
                (natp frame-length)
                (<= frame-length (fn-aj-max-record-length (fn-aj-domain s))))
           (equal (fn-aj-recover-record
                   s (fn-aj-record-name (fn-aj-domain s) (fn-aj-next s))
                   frame-length kind)
                  :beyond-profile)))

; The record name codec (books/byte-store-txn-name) at the profile's width.
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defun fn-aj-digits-induct (n k)
   (declare (xargs :measure (nfix k)))
   (if (or (zp k) (< (nfix n) 10)) (list n k)
     (fn-aj-digits-induct (floor (nfix n) 10) (1- k)))))

(local
 (defthm fn-aj-floor-10-bound
   (implies (and (natp n) (natp m) (< n (* 10 m)))
            (< (floor n 10) m))))

(local
 (defthm fn-aj-expt-10-step
   (implies (posp k)
            (equal (expt 10 k) (* 10 (expt 10 (1- k)))))
   :rule-classes nil))

(local
 (defthm fn-aj-len-of-natural-digits-rev-bound
   (implies (and (natp n) (posp k) (< n (expt 10 k)))
            (<= (len (fn-bs-txn-natural-digits-rev n)) k))
   :hints (("Goal" :in-theory (enable fn-bs-txn-natural-digits-rev)
            :induct (fn-aj-digits-induct n k))
           ("Subgoal *1/2" :use ((:instance fn-aj-expt-10-step)
                                 (:instance fn-aj-floor-10-bound
                                            (m (expt 10 (1- k)))))))
   :rule-classes :linear))

(local
 (defthm fn-aj-len-of-txn-reverse
   (equal (len (fn-bs-txn-reverse xs)) (len xs))
   :hints (("Goal" :in-theory (enable fn-bs-txn-reverse)))))

(local
 (defthm fn-aj-frame-nat-below-twenty-digits
   (implies (fn-frame-natp n)
            (< n (expt 10 20)))
   :hints (("Goal" :in-theory (enable fn-frame-natp)))
   :rule-classes nil))

; Representation: every sequence a profile admits (a frame natural) names a
; record of exactly twenty digits and its domain's three-character suffix,
; so the names are one width, where lexical order is sequence order.  (The
; host's sort is an observation only: recovery admits nothing but the exact
; next name.)
(defthm fn-aj-record-name-fixed-width
  (implies (and (fn-aj-statep s)
                (natp n)
                (<= n (fn-aj-max-records s)))
           (equal (len (fn-aj-record-name-chars (fn-aj-domain s) n)) 23))
  :hints (("Goal" :in-theory (e/d (fn-aj-record-name-chars fn-bs-txn-digits
                                   fn-bs-txn-natural-digits fn-aj-suffix)
                                  (fn-bs-txn-natural-digits-rev))
           :use ((:instance fn-aj-frame-nat-below-twenty-digits
                  (n (fn-aj-max-records s)))
                 (:instance fn-aj-len-of-natural-digits-rev-bound
                  (n n) (k 20))))))

(deftheory fn-app-journal-vocabulary
  '(fn-aj-domainp fn-aj-max-record-length fn-aj-suffix
    fn-aj-record-name-chars fn-aj-record-name fn-aj-state fn-aj-domain
    fn-aj-next fn-aj-aggregate fn-aj-initializedp fn-aj-statep fn-aj-initial
    fn-aj-kind-allowedp fn-aj-advance fn-aj-fits-p fn-aj-recover-record
    fn-aj-authorize fn-aj-operationp fn-aj-operation-name
    fn-aj-operation-label fn-aj-operation-publication
    fn-aj-operation-successor fn-aj-max-records fn-aj-max-octets
    fn-aj-profile-validp fn-ajpf-default fn-ajpf-records fn-ajpf-octets-limit
    fn-ajpf-profilep fn-ajpf-octets fn-ajpf-read fn-ajpf-write-octets))
