; LB: the resident catalog columns.  The sixteen u64 positions follow
; D-LB-1 exactly.  The house representation generator owns their column
; pages and the byte pools; no catalog-row tree codec is instantiated.
;
; The concrete API takes FN-LBC.  The generic FN-CAT attachment uses the
; unchanged abstract exports through a separate correspondence square.
; Full-row reads take LOG explicitly; resident reads do not take LOG.
(in-package "ACL2")
(include-book "def-representation-pages")
(include-book "def-representation-pageread")
(include-book "def-representation")
(include-book "catalog-dense-map")
(include-book "lb-log-model")
(include-book "log-locator")

; The row generator reasons about typed columns, not the unrelated dense
; map's page predicates.  Use the same isolation as catalog-paged's schema.
(local (in-theory (disable (tau-system) floor mod nth update-nth
                          fn-dm-zerosp fn-dmap$c-pgp fn-dpgp)))

(def-representation fn-lbc-rowwords
  (handle :u64)
  (loc0 :u64)
  (loc1 :u64)
  (head-length :u64)
  (stamp :u64)
  (prefix-max :u64)
  (txid :u64)
  (generation :u64)
  (charge :u64)
  (msgid-hash :u64)
  (msgid-offset :u64)
  (msgid-length :u64)
  (withdrawal-at :u64)
  (withdrawal-by :u64)
  (overview-offset :u64)
  (flags :u64)
  :pages t)

(def-representation fn-lbc-msgid-octets
  (octet :u8) :pages t)

(def-representation fn-lbc-overview-octets
  (octet :u8) :pages t)

(def-representation fn-lbc-msgid-slots
  (word :u64) :pages t)

; The overview directory and membership runs are resident, page-addressed
; columns.  They carry no obligation, subject, release, or context fields.
; A directory position is also the sequence key of the sparse escape map.
(def-representation fn-lbc-directory
  (sequence :u64) (facts-octets :u64) (body-start :u64)
  (body-start-present :bool) (body-lines :u64)
  (nov-start :u64) (nov-length :u64)
  (render-nov-start :u64) (render-nov-length :u64)
  (groups-start :u64) (groups-count :u64)
  (numbers-start :u64) (numbers-count :u64)
  (article-ok :bool) (head-ok :bool)
  (body-ok :bool) (raw-head-length :u64) (framed :bool)
  :pages t)

(def-representation fn-lbc-memberships
  (group-start :u64) (group-length :u64) (number :u64)
  :pages t)

(def-representation fn-lbc-nov
  (tomb :bool) (ok :bool)
  (subject-start :u64) (subject-length :u64)
  (from-start :u64) (from-length :u64)
  (date-start :u64) (date-length :u64)
  (msgid-start :u64) (msgid-length :u64)
  (references-start :u64) (references-length :u64)
  :pages t)

(defstobj fn-lbc
  (fn-lbc-row-store :type fn-lbc-rowwords)
  (fn-lbc-msgid-store :type fn-lbc-msgid-octets)
  (fn-lbc-overview-store :type fn-lbc-overview-octets)
  (fn-lbc-number-store :type fn-dmap)
  (fn-lbc-slot-store :type fn-lbc-msgid-slots)
  (fn-lbc-directory-store :type fn-lbc-directory)
  (fn-lbc-membership-store :type fn-lbc-memberships)
  (fn-lbc-nov-store :type fn-lbc-nov)
  (fn-lbc-summary-groups :type t :initially nil)
  (fn-lbc-escape-store :type (hash-table eql))
  (fn-lbc-slot-escape-keys :type t :initially nil)
  :renaming ((fn-lbcp fn-lbc-p)))

; Bit positions are shared by writers and readers.  RECLAIMED is checked
; before section cuts; NOV-TOMB describes the persisted NOV fact, whereas
; RECLAIMED describes the payload bound by LOG, including undecided rows.
(defconst *fn-lbc-nov-ok-bit* 0)
(defconst *fn-lbc-nov-tomb-bit* 1)
(defconst *fn-lbc-withdrawn-bit* 2)
(defconst *fn-lbc-escaped-bit* 3)
(defconst *fn-lbc-ingest-verified-bit* 4)
(defconst *fn-lbc-reclaimed-bit* 5)

(defun fn-lbc-count (fn-lbc)
  (declare (xargs :stobjs fn-lbc))
  (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
             (count) (fn-lbc-rowwords-count fn-lbc-rowwords) count))

; Stobj-aware guard recognizers: no loop closure captures FN-LBC.
(defun fn-lbc-escape-cellsp (i fn-lbc)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp i) (<= i (fn-lbc-count fn-lbc)))
                  :measure (nfix (- (fn-lbc-count fn-lbc) (nfix i)))
                  :verify-guards nil))
  (if (and (natp i) (< i (fn-lbc-count fn-lbc)))
      (and (alistp (fn-lbc-escape-store-get i fn-lbc))
           (fn-lbc-escape-cellsp (+ i 1) fn-lbc))
    t))

(defun fn-lbc-number-escape-cellsp (i fn-lbc)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp i) (<= i (fn-lbc-count fn-lbc))
                              (fn-lbc-escape-cellsp i fn-lbc))
                  :measure (nfix (- (fn-lbc-count fn-lbc) (nfix i)))
                  :verify-guards nil))
  (if (and (natp i) (< i (fn-lbc-count fn-lbc)))
      (and (alistp (cdr (assoc-eq :numbers
                          (fn-lbc-escape-store-get i fn-lbc))))
           (fn-lbc-number-escape-cellsp (+ i 1) fn-lbc))
    t))

(defun fn-lbc-stamp-escape-cellsp (i fn-lbc)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp i) (<= i (fn-lbc-count fn-lbc))
                              (fn-lbc-escape-cellsp i fn-lbc))
                  :measure (nfix (- (fn-lbc-count fn-lbc) (nfix i)))
                  :verify-guards nil))
  (if (and (natp i) (< i (fn-lbc-count fn-lbc)))
      (let ((escape (assoc-eq :stamp (fn-lbc-escape-store-get i fn-lbc))))
        (and (or (not escape) (acl2-numberp (cdr escape)))
             (fn-lbc-stamp-escape-cellsp (+ i 1) fn-lbc)))
    t))

(defun fn-lbc-loc0 (i fn-lbc)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp i) (< i (fn-lbc-count fn-lbc)))
                  :verify-guards nil))
  (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
             (word) (fn-lbc-rowwords-get-loc0 i fn-lbc-rowwords) word))

(defun fn-lbc-loc1 (i fn-lbc)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp i) (< i (fn-lbc-count fn-lbc)))
                  :verify-guards nil))
  (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
             (word) (fn-lbc-rowwords-get-loc1 i fn-lbc-rowwords) word))

(defun update-fn-lbc-loc0 (i word fn-lbc)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp i) (< i (fn-lbc-count fn-lbc))
                              (unsigned-byte-p 64 word))
                  :verify-guards nil))
  (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
             (fn-lbc-rowwords)
             (fn-lbc-rowwords-set-loc0 i word fn-lbc-rowwords)
             fn-lbc))

(defun update-fn-lbc-loc1 (i word fn-lbc)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp i) (< i (fn-lbc-count fn-lbc))
                              (unsigned-byte-p 64 word))
                  :verify-guards nil))
  (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
             (fn-lbc-rowwords)
             (fn-lbc-rowwords-set-loc1 i word fn-lbc-rowwords)
             fn-lbc))
; BEGIN LB SCHEMA ACCESSOR DISPATCHES

(defun fn-lbc-word (field i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
    (value)
    (if (and (natp i) (< i (fn-lbc-rowwords-count fn-lbc-rowwords)))
        (case field
          (:handle (fn-lbc-rowwords-get-handle i fn-lbc-rowwords))
          (:loc0 (fn-lbc-rowwords-get-loc0 i fn-lbc-rowwords))
          (:loc1 (fn-lbc-rowwords-get-loc1 i fn-lbc-rowwords))
          (:head-length (fn-lbc-rowwords-get-head-length i fn-lbc-rowwords))
          (:stamp (fn-lbc-rowwords-get-stamp i fn-lbc-rowwords))
          (:prefix-max (fn-lbc-rowwords-get-prefix-max i fn-lbc-rowwords))
          (:txid (fn-lbc-rowwords-get-txid i fn-lbc-rowwords))
          (:generation (fn-lbc-rowwords-get-generation i fn-lbc-rowwords))
          (:charge (fn-lbc-rowwords-get-charge i fn-lbc-rowwords))
          (:msgid-hash (fn-lbc-rowwords-get-msgid-hash i fn-lbc-rowwords))
          (:msgid-offset (fn-lbc-rowwords-get-msgid-offset i fn-lbc-rowwords))
          (:msgid-length (fn-lbc-rowwords-get-msgid-length i fn-lbc-rowwords))
          (:withdrawal-at (fn-lbc-rowwords-get-withdrawal-at i fn-lbc-rowwords))
          (:withdrawal-by (fn-lbc-rowwords-get-withdrawal-by i fn-lbc-rowwords))
          (:overview-offset (fn-lbc-rowwords-get-overview-offset i fn-lbc-rowwords))
          (:flags (fn-lbc-rowwords-get-flags i fn-lbc-rowwords))
          (otherwise nil))
      nil)
    value))

(defun fn-lbc-directory-field (field i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (stobj-let ((fn-lbc-directory (fn-lbc-directory-store fn-lbc)))
    (value)
    (if (and (natp i) (< i (fn-lbc-directory-count fn-lbc-directory)))
        (case field
          (:sequence (fn-lbc-directory-get-sequence i fn-lbc-directory))
          (:facts-octets (fn-lbc-directory-get-facts-octets i fn-lbc-directory))
          (:body-start (fn-lbc-directory-get-body-start i fn-lbc-directory))
          (:body-start-present (fn-lbc-directory-get-body-start-present i fn-lbc-directory))
          (:body-lines (fn-lbc-directory-get-body-lines i fn-lbc-directory))
          (:nov-start (fn-lbc-directory-get-nov-start i fn-lbc-directory))
          (:nov-length (fn-lbc-directory-get-nov-length i fn-lbc-directory))
          (:render-nov-start (fn-lbc-directory-get-render-nov-start i fn-lbc-directory))
          (:render-nov-length (fn-lbc-directory-get-render-nov-length i fn-lbc-directory))
          (:groups-start (fn-lbc-directory-get-groups-start i fn-lbc-directory))
          (:groups-count (fn-lbc-directory-get-groups-count i fn-lbc-directory))
          (:numbers-start (fn-lbc-directory-get-numbers-start i fn-lbc-directory))
          (:numbers-count (fn-lbc-directory-get-numbers-count i fn-lbc-directory))
          (:article-ok (fn-lbc-directory-get-article-ok i fn-lbc-directory))
          (:head-ok (fn-lbc-directory-get-head-ok i fn-lbc-directory))
          (:body-ok (fn-lbc-directory-get-body-ok i fn-lbc-directory))
          (:raw-head-length (fn-lbc-directory-get-raw-head-length i fn-lbc-directory))
          (:framed (fn-lbc-directory-get-framed i fn-lbc-directory))
          (otherwise nil))
      nil)
    value))

(defun fn-lbc-membership-field (field i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (stobj-let ((fn-lbc-memberships (fn-lbc-membership-store fn-lbc)))
    (value)
    (if (and (natp i) (< i (fn-lbc-memberships-count fn-lbc-memberships)))
        (case field
          (:group-start (fn-lbc-memberships-get-group-start i fn-lbc-memberships))
          (:group-length (fn-lbc-memberships-get-group-length i fn-lbc-memberships))
          (:number (fn-lbc-memberships-get-number i fn-lbc-memberships))
          (otherwise nil))
      nil)
    value))

(defun fn-lbc-nov-field (field i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (stobj-let ((fn-lbc-nov (fn-lbc-nov-store fn-lbc)))
    (value)
    (if (and (natp i) (< i (fn-lbc-nov-count fn-lbc-nov)))
        (case field
          (:tomb (fn-lbc-nov-get-tomb i fn-lbc-nov))
          (:ok (fn-lbc-nov-get-ok i fn-lbc-nov))
          (:subject-start (fn-lbc-nov-get-subject-start i fn-lbc-nov))
          (:subject-length (fn-lbc-nov-get-subject-length i fn-lbc-nov))
          (:from-start (fn-lbc-nov-get-from-start i fn-lbc-nov))
          (:from-length (fn-lbc-nov-get-from-length i fn-lbc-nov))
          (:date-start (fn-lbc-nov-get-date-start i fn-lbc-nov))
          (:date-length (fn-lbc-nov-get-date-length i fn-lbc-nov))
          (:msgid-start (fn-lbc-nov-get-msgid-start i fn-lbc-nov))
          (:msgid-length (fn-lbc-nov-get-msgid-length i fn-lbc-nov))
          (:references-start (fn-lbc-nov-get-references-start i fn-lbc-nov))
          (:references-length (fn-lbc-nov-get-references-length i fn-lbc-nov))
          (otherwise nil))
      nil)
    value))

(defun fn-lbc-msgid-pool-count (fn-lbc)
  (declare (xargs :stobjs fn-lbc))
  (stobj-let ((fn-lbc-msgid-octets (fn-lbc-msgid-store fn-lbc)))
    (n) (fn-lbc-msgid-octets-count fn-lbc-msgid-octets) n))

(defun fn-lbc-msgid-pool-octet (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (stobj-let ((fn-lbc-msgid-octets (fn-lbc-msgid-store fn-lbc)))
    (byte)
    (if (and (natp i) (< i (fn-lbc-msgid-octets-count fn-lbc-msgid-octets)))
        (fn-lbc-msgid-octets-get-octet i fn-lbc-msgid-octets)
      nil)
    byte))

(defun fn-lbc-msgid-pool-range (off n fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (natp off) (natp n))
                  :measure (nfix n) :verify-guards nil))
  (if (or (zp n) (> (+ off n) (fn-lbc-msgid-pool-count fn-lbc))) nil
    (cons (fn-lbc-msgid-pool-octet off fn-lbc)
          (fn-lbc-msgid-pool-range (+ 1 off) (- n 1) fn-lbc))))

(defun fn-lbc-msgid-pool-append (bytes fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-cbor-octet-listp bytes)
                  :verify-guards nil))
  (if (consp bytes)
      (let ((fn-lbc
             (stobj-let ((fn-lbc-msgid-octets (fn-lbc-msgid-store fn-lbc)))
               (fn-lbc-msgid-octets)
               (fn-lbc-msgid-octets-append (list (car bytes)) fn-lbc-msgid-octets)
               fn-lbc)))
        (fn-lbc-msgid-pool-append (cdr bytes) fn-lbc))
    fn-lbc))

(defun fn-lbc-overview-pool-count (fn-lbc)
  (declare (xargs :stobjs fn-lbc))
  (stobj-let ((fn-lbc-overview-octets (fn-lbc-overview-store fn-lbc)))
    (n) (fn-lbc-overview-octets-count fn-lbc-overview-octets) n))

(defun fn-lbc-overview-pool-octet (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (stobj-let ((fn-lbc-overview-octets (fn-lbc-overview-store fn-lbc)))
    (byte)
    (if (and (natp i) (< i (fn-lbc-overview-octets-count fn-lbc-overview-octets)))
        (fn-lbc-overview-octets-get-octet i fn-lbc-overview-octets)
      nil)
    byte))

(defun fn-lbc-overview-pool-range (off n fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (natp off) (natp n))
                  :measure (nfix n) :verify-guards nil))
  (if (or (zp n) (> (+ off n) (fn-lbc-overview-pool-count fn-lbc))) nil
    (cons (fn-lbc-overview-pool-octet off fn-lbc)
          (fn-lbc-overview-pool-range (+ 1 off) (- n 1) fn-lbc))))

(defun fn-lbc-overview-pool-append (bytes fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-cbor-octet-listp bytes)
                  :verify-guards nil))
  (if (consp bytes)
      (let ((fn-lbc
             (stobj-let ((fn-lbc-overview-octets (fn-lbc-overview-store fn-lbc)))
               (fn-lbc-overview-octets)
               (fn-lbc-overview-octets-append (list (car bytes)) fn-lbc-overview-octets)
               fn-lbc)))
        (fn-lbc-overview-pool-append (cdr bytes) fn-lbc))
    fn-lbc))

(defun fn-lbc-clear-columns (fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (let* (

    (fn-lbc (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
                (fn-lbc-rowwords) (fn-lbc-rowwords-clear fn-lbc-rowwords) fn-lbc))

    (fn-lbc (stobj-let ((fn-lbc-msgid-octets (fn-lbc-msgid-store fn-lbc)))
                (fn-lbc-msgid-octets) (fn-lbc-msgid-octets-clear fn-lbc-msgid-octets) fn-lbc))

    (fn-lbc (stobj-let ((fn-lbc-overview-octets (fn-lbc-overview-store fn-lbc)))
                (fn-lbc-overview-octets) (fn-lbc-overview-octets-clear fn-lbc-overview-octets) fn-lbc))

    (fn-lbc (stobj-let ((fn-lbc-msgid-slots (fn-lbc-slot-store fn-lbc)))
                (fn-lbc-msgid-slots) (fn-lbc-msgid-slots-clear fn-lbc-msgid-slots) fn-lbc))

    (fn-lbc (stobj-let ((fn-lbc-directory (fn-lbc-directory-store fn-lbc)))
                (fn-lbc-directory) (fn-lbc-directory-clear fn-lbc-directory) fn-lbc))

    (fn-lbc (stobj-let ((fn-lbc-memberships (fn-lbc-membership-store fn-lbc)))
                (fn-lbc-memberships) (fn-lbc-memberships-clear fn-lbc-memberships) fn-lbc))

    (fn-lbc (stobj-let ((fn-lbc-nov (fn-lbc-nov-store fn-lbc)))
                (fn-lbc-nov) (fn-lbc-nov-clear fn-lbc-nov) fn-lbc))

    (fn-lbc (stobj-let ((fn-dmap (fn-lbc-number-store fn-lbc)))
                (fn-dmap) (fn-dmap-clear fn-dmap) fn-lbc))

    (fn-lbc (fn-lbc-escape-store-clear fn-lbc))
    (fn-lbc (update-fn-lbc-slot-escape-keys nil fn-lbc)))
    (update-fn-lbc-summary-groups nil fn-lbc)))
; END LB SCHEMA ACCESSOR DISPATCHES

; Escapes carry individual values, keyed by catalog sequence.  Presence
; is distinguished from NIL, so an escaped NIL does not become a word 0.
(defun fn-lbc-escape (i field fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (if (symbolp field) (alistp (fn-lbc-escape-store-get i fn-lbc)) (symbol-alistp (fn-lbc-escape-store-get i fn-lbc)))) :verify-guards nil))
  (assoc-eq field (fn-lbc-escape-store-get i fn-lbc)))

(defun fn-lbc-value (i field fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (if (symbolp field) (alistp (fn-lbc-escape-store-get i fn-lbc)) (symbol-alistp (fn-lbc-escape-store-get i fn-lbc)))) :verify-guards nil))
  (let ((escape (fn-lbc-escape i field fn-lbc)))
    (if escape (cdr escape) (fn-lbc-word field i fn-lbc))))

(defun fn-lbc-directory-value (i field fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (if (symbolp field) (alistp (fn-lbc-escape-store-get i fn-lbc)) (symbol-alistp (fn-lbc-escape-store-get i fn-lbc)))) :verify-guards nil))
  (let ((escape (fn-lbc-escape i field fn-lbc)))
    (if escape (cdr escape) (fn-lbc-directory-field field i fn-lbc))))

(defun fn-lbc-msgid (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (let ((length (nfix (fn-lbc-value i :msgid-length fn-lbc))))
    (if (> length *fn-record-max-msgid*) ""
      (fn-record-octets-string
        (fn-lbc-msgid-pool-range
          (nfix (fn-lbc-value i :msgid-offset fn-lbc)) length fn-lbc)))))

(defun fn-lbc-flag (i bit fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (natp bit) :verify-guards nil))
  (logbitp bit (nfix (fn-lbc-word :flags i fn-lbc))))

(defun fn-lbc-withdrawn (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (if (fn-lbc-flag i *fn-lbc-withdrawn-bit* fn-lbc)
      (cons (fn-lbc-value i :withdrawal-at fn-lbc)
            (fn-lbc-value i :withdrawal-by fn-lbc))
    nil))

(defun fn-lbc-membership-group (j fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (fn-record-octets-string
    (fn-lbc-overview-pool-range
      (nfix (fn-lbc-membership-field :group-start j fn-lbc))
      (nfix (fn-lbc-membership-field :group-length j fn-lbc)) fn-lbc)))

(defun fn-lbc-membership-run (start count numbersp fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (natp start) (natp count))
                  :measure (nfix count) :verify-guards nil))
  (if (zp count) nil
    (cons (if numbersp
              (cons (fn-lbc-membership-group start fn-lbc)
                    (fn-lbc-membership-field :number start fn-lbc))
            (fn-lbc-membership-group start fn-lbc))
          (fn-lbc-membership-run (+ 1 start) (- count 1) numbersp fn-lbc))))

(defun fn-lbc-groups (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (fn-lbc-membership-run
    (nfix (fn-lbc-directory-value i :groups-start fn-lbc))
    (nfix (fn-lbc-directory-value i :groups-count fn-lbc)) nil fn-lbc))

(defun fn-lbc-numbers (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (let ((escape (fn-lbc-escape i :numbers fn-lbc)))
    (if escape (cdr escape)
      (fn-lbc-membership-run
        (nfix (fn-lbc-directory-value i :numbers-start fn-lbc))
        (nfix (fn-lbc-directory-value i :numbers-count fn-lbc)) t fn-lbc))))

(defun fn-lbc-nov-text (start length fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (fn-record-octets-string
    (fn-lbc-overview-pool-range (nfix start) (nfix length) fn-lbc)))

(defun fn-lbc-nov-at (j fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (fn-hnov-make
    (fn-lbc-nov-field :tomb j fn-lbc) (fn-lbc-nov-field :ok j fn-lbc)
    (fn-lbc-nov-text (fn-lbc-nov-field :subject-start j fn-lbc)
                     (fn-lbc-nov-field :subject-length j fn-lbc) fn-lbc)
    (fn-lbc-nov-text (fn-lbc-nov-field :from-start j fn-lbc)
                     (fn-lbc-nov-field :from-length j fn-lbc) fn-lbc)
    (fn-lbc-nov-text (fn-lbc-nov-field :date-start j fn-lbc)
                     (fn-lbc-nov-field :date-length j fn-lbc) fn-lbc)
    (fn-lbc-nov-text (fn-lbc-nov-field :msgid-start j fn-lbc)
                     (fn-lbc-nov-field :msgid-length j fn-lbc) fn-lbc)
    (fn-lbc-nov-text (fn-lbc-nov-field :references-start j fn-lbc)
                     (fn-lbc-nov-field :references-length j fn-lbc) fn-lbc)))

(defun fn-lbc-original-nov (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (let ((escape (fn-lbc-escape i :nov fn-lbc)))
    (if escape (cdr escape)
      (if (equal (fn-lbc-directory-value i :nov-length fn-lbc) 0) nil
        (fn-lbc-nov-at (fn-lbc-directory-value i :nov-start fn-lbc) fn-lbc)))))

(defun fn-lbc-render-nov (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (fn-lbc-nov-at (fn-lbc-directory-value i :render-nov-start fn-lbc) fn-lbc))

(defun fn-cat-served-projection (row)
  (declare (xargs :guard t))
  (let ((facts (fn-held-facts row)))
    (list (fn-record-msgid row) (fn-record-payload row)
          (fn-record-groups row) (fn-held-numbers row) (fn-record-stamp row)
          (fn-held-withdrawn row)
          (list (fn-hf-octets facts) (fn-hf-body-start facts)
                (fn-hf-body-lines facts) (fn-hf-nov facts))
          (list (fn-record-txid row) (fn-record-generation row)
                (fn-record-charge row))
          (fn-record-sequence row))))

(defun fn-lbc-served-row (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (eqlablep i) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (list (fn-lbc-msgid i fn-lbc) (fn-lbc-value i :handle fn-lbc)
        (fn-lbc-groups i fn-lbc) (fn-lbc-numbers i fn-lbc)
        (fn-lbc-value i :stamp fn-lbc) (fn-lbc-withdrawn i fn-lbc)
        (list (fn-lbc-directory-value i :facts-octets fn-lbc)
              (if (fn-lbc-directory-value i :body-start-present fn-lbc)
                  (fn-lbc-directory-value i :body-start fn-lbc) nil)
              (fn-lbc-directory-value i :body-lines fn-lbc)
              (fn-lbc-original-nov i fn-lbc))
        (list (fn-lbc-value i :txid fn-lbc)
              (fn-lbc-value i :generation fn-lbc)
              (fn-lbc-value i :charge fn-lbc))
        (fn-lbc-directory-value i :sequence fn-lbc)))

; The parser adapter supplies the full log-home fields.  They are not
; recovered from a resident copy of the held record.
(defun fn-lbc-home-entry (i fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lb-log-entries-guardp log)) :verify-guards nil))
  (let* ((loc0 (fn-lbc-loc0 i fn-lbc)) (loc1 (fn-lbc-loc1 i fn-lbc))
         (seg (fn-lb-log-model-segment (fn-loc-segment loc0 loc1) log)))
    (fn-lb-log-model-home-entry
      (+ (fn-loc-offset loc0 loc1) (fn-loc-len loc0 loc1)) (caddr seg))))

(defun fn-lbc-restore-control (home nov)
  (declare (xargs :guard (and (true-listp home) (or (< (nfix (car home)) 4) (true-listp (cadr home)))) :verify-guards nil))
  (if (< (nfix (car home)) 4) (cadr home)
    (append (cadr home) (cons nov (caddr home)))))

(defun fn-lbc-home-guardp (i fn-lbc log)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp i) (< i (fn-lbc-count fn-lbc))
                              (fn-lb-log-entries-guardp log))
                  :verify-guards nil))
  (let ((homes (nth 7 (fn-lbc-home-entry i fn-lbc log))))
    (and (true-listp homes)
         (let ((home (nth 4 homes)))
           (and (true-listp home)
                (or (< (nfix (car home)) 4) (true-listp (cadr home))))))))

; LC's guard invariant is independent of the current locator values.
; This makes arbitrary in-range locator-word updates preserve it.
(defun fn-lbc-lc-guardp (log fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (and (fn-lb-log-homes-guardp log)
       (fn-lbc-escape-cellsp 0 fn-lbc)))

(defun fn-lbc-at (i fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lb-log-entries-guardp log) (alistp (fn-lbc-escape-store-get i fn-lbc)) (fn-lbc-home-guardp i fn-lbc log)) :verify-guards nil))
  (let* ((r (fn-lbc-served-row i fn-lbc))
         (homes (nth 7 (fn-lbc-home-entry i fn-lbc log)))
         (facts (nth 6 r)) (identity (nth 7 r)))
    (fn-held-make (nth 8 r) (car identity) (cadr identity)
      (nth 0 r) (nth 1 r) (nth 2 r)
      (nth 0 homes) (nth 1 homes) (nth 2 homes)
      (caddr identity) (nth 4 r)
      (fn-hf-make (nth 0 facts) (nth 1 facts) (nth 2 facts)
                  (fn-lbc-restore-control (nth 4 homes) (nth 3 facts)))
      (nth 3 homes) (nth 3 r) (nth 5 r))))

(defun fn-lbc-u64 (value)
  (declare (xargs :guard t))
  (if (unsigned-byte-p 64 value) value 0))

(defun fn-lbc-sparse-u64 (fields values)
  (declare (xargs :guard (true-listp values) :verify-guards nil))
  (if (consp fields)
      (if (unsigned-byte-p 64 (car values))
          (fn-lbc-sparse-u64 (cdr fields) (cdr values))
        (cons (cons (car fields) (car values))
              (fn-lbc-sparse-u64 (cdr fields) (cdr values))))
    nil))

(defun fn-lbc-text-smallp (text)
  (declare (xargs :guard t :verify-guards nil))
  (and (stringp text) (fn-cbor-octet-listp (fn-record-string-octets text))))

(defun fn-lbc-nov-smallp (nov)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hnov-p nov)
       (fn-lbc-text-smallp (fn-hnov-subject nov))
       (fn-lbc-text-smallp (fn-hnov-from nov))
       (fn-lbc-text-smallp (fn-hnov-date nov))
       (fn-lbc-text-smallp (fn-hnov-msgid nov))
       (fn-lbc-text-smallp (fn-hnov-references nov))))

(defun fn-lbc-numbers-smallp (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (and (consp (car numbers))
           (fn-lbc-text-smallp (caar numbers))
           (unsigned-byte-p 64 (cdar numbers))
           (fn-lbc-numbers-smallp (cdr numbers)))
    (null numbers)))

(defun fn-lbc-nov-record-count (fn-lbc)
  (declare (xargs :stobjs fn-lbc))
  (stobj-let ((fn-lbc-nov (fn-lbc-nov-store fn-lbc)))
    (n) (fn-lbc-nov-count fn-lbc-nov) n))

(defun fn-lbc-membership-record-count (fn-lbc)
  (declare (xargs :stobjs fn-lbc))
  (stobj-let ((fn-lbc-memberships (fn-lbc-membership-store fn-lbc)))
    (n) (fn-lbc-memberships-count fn-lbc-memberships) n))

(defun fn-lbc-append-nov-texts (texts fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (if (consp texts)
      (let ((fn-lbc (fn-lbc-overview-pool-append
                       (fn-record-string-octets (car texts)) fn-lbc)))
        (fn-lbc-append-nov-texts (cdr texts) fn-lbc))
    fn-lbc))

(defun fn-lbc-nov-spans (texts offset)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp texts)
      (let ((n (len (fn-record-string-octets (car texts)))))
        (cons (fn-lbc-u64 offset)
              (cons (fn-lbc-u64 n)
                    (fn-lbc-nov-spans (cdr texts) (+ (nfix offset) n)))))
    nil))

(defun fn-lbc-append-nov (nov fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-nov-smallp nov)
                  :verify-guards nil))
  (let* ((texts (list (fn-hnov-subject nov) (fn-hnov-from nov)
                     (fn-hnov-date nov) (fn-hnov-msgid nov)
                     (fn-hnov-references nov)))
         (record (cons (fn-hnov-tomb nov)
                       (cons (fn-hnov-ok nov)
                             (fn-lbc-nov-spans texts (fn-lbc-overview-pool-count fn-lbc)))))
         (fn-lbc (fn-lbc-append-nov-texts texts fn-lbc)))
    (stobj-let ((fn-lbc-nov (fn-lbc-nov-store fn-lbc)))
      (fn-lbc-nov) (fn-lbc-nov-append record fn-lbc-nov) fn-lbc)))

(defun fn-lbc-append-memberships (items numbersp fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (or (not numbersp) (alistp (remove-equal nil (true-list-fix items)))) :verify-guards nil))
  (if (consp items)
      (let* ((group (if numbersp (caar items) (car items)))
             (bytes (fn-record-string-octets group))
             (record (list (fn-lbc-u64 (fn-lbc-overview-pool-count fn-lbc))
                           (fn-lbc-u64 (len bytes))
                           (if numbersp (fn-lbc-u64 (cdar items)) 0)))
             (fn-lbc (fn-lbc-overview-pool-append bytes fn-lbc))
             (fn-lbc
              (stobj-let ((fn-lbc-memberships (fn-lbc-membership-store fn-lbc)))
                (fn-lbc-memberships)
                (fn-lbc-memberships-append record fn-lbc-memberships) fn-lbc)))
        (fn-lbc-append-memberships (cdr items) numbersp fn-lbc))
    fn-lbc))

(defun fn-lbc-msgid-hash-octets (bytes hash)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp bytes)
      (fn-lbc-msgid-hash-octets (cdr bytes)
        (mod (+ (* 1099511628211 (nfix hash)) (nfix (car bytes)))
             18446744073709551616))
    (nfix hash)))

(defun fn-lbc-msgid-hash (msgid)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lbc-msgid-hash-octets (fn-record-string-octets msgid) 14695981039346656037))

; Appends the columns of an already committed row.  The log adapter's
; directory supplies its locator and entry ordinal; no locator is invented
; for a row absent from LOG.  The open and commit adapters use this worker.
(defun fn-lbc-row-log-guardp (row log)
  (declare (xargs :guard (fn-lb-log-read-guardp log) :verify-guards nil))
  (let ((entry (fn-lb-log-model-row-entry row log))
        (segment (fn-lb-log-model-row-segment row log)))
    (and (unsigned-byte-p 64 segment)
         (unsigned-byte-p 32 (nth 3 entry))
         (unsigned-byte-p 32 (nth 4 entry)))))

(defun fn-lbc-rows-log-guardp (rows log)
  (declare (xargs :guard (fn-lb-log-read-guardp log) :verify-guards nil))
  (if (consp rows)
      (and (fn-lbc-row-log-guardp (car rows) log)
           (fn-lbc-rows-log-guardp (cdr rows) log))
    t))

(defun fn-lbc-row-homes-guardp (rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (and (fn-lb-value-treep (fn-lb-log-model-homes (car rows)))
           (fn-lbc-row-homes-guardp (cdr rows)))
    t))

(defun fn-lbc-append-row (row log fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (fn-cat-rowp row) (fn-lb-log-read-guardp log) (fn-lbc-row-log-guardp row log) (fn-lbc-escape-cellsp 0 fn-lbc))
                  :verify-guards nil))
  (let* ((i (fn-lbc-count fn-lbc))
         (entry (fn-lb-log-model-row-entry row log))
         (segment (fn-lb-log-model-row-segment row log))
         (payload (nth 6 entry))
         (facts (fn-held-facts row)) (nov (fn-hf-nov facts))
         (nov-small (fn-lbc-nov-smallp nov))
         (render-nov (fn-hnov-of payload))
         (numbers-small (fn-lbc-numbers-smallp (fn-held-numbers row)))
         (nov-start (fn-lbc-nov-record-count fn-lbc))
         (fn-lbc (if nov-small (fn-lbc-append-nov nov fn-lbc) fn-lbc))
         (render-start (fn-lbc-nov-record-count fn-lbc))
         (fn-lbc (fn-lbc-append-nov render-nov fn-lbc))
         (groups-start (fn-lbc-membership-record-count fn-lbc))
         (fn-lbc (fn-lbc-append-memberships (fn-record-groups row) nil fn-lbc))
         (numbers-start (fn-lbc-membership-record-count fn-lbc))
         (fn-lbc (if numbers-small
                     (fn-lbc-append-memberships (fn-held-numbers row) t fn-lbc)
                   fn-lbc))
         (msgid-offset (fn-lbc-msgid-pool-count fn-lbc))
         (msgid-bytes (fn-record-string-octets (fn-record-msgid row)))
         (fn-lbc (fn-lbc-msgid-pool-append msgid-bytes fn-lbc))
         (head-length (len (fn-nntp-stuffed-section :head payload)))
         (raw-head-length
           (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))))
         (previous-max (if (zp i) 0 (fn-lbc-value (- i 1) :prefix-max fn-lbc)))
         (max-stamp (max (nfix previous-max) (nfix (fn-record-stamp row))))
         (w (fn-held-withdrawn row))
         (escape
           (append
             (fn-lbc-sparse-u64
               '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)
               (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp
                     (fn-record-txid row) (fn-record-generation row) (fn-record-charge row)
                     msgid-offset (len msgid-bytes) (nfix (car w)) (nfix (cdr w)) i
                     (fn-record-sequence row) (fn-hf-octets facts)
                     (nfix (fn-hf-body-start facts)) (fn-hf-body-lines facts)
                     nov-start render-start groups-start (len (fn-record-groups row))
                     numbers-start (len (fn-held-numbers row)) raw-head-length))
             (if (and nov (not nov-small)) (list (cons :nov nov)) nil)
             (if numbers-small nil (list (cons :numbers (fn-held-numbers row))))))
         (flags (+ (if (and (fn-hnov-p nov) (fn-hnov-ok nov)) 1 0)
                   (if (and (fn-hnov-p nov) (fn-hnov-tomb nov)) 2 0)
                   (if w 4 0) (if escape 8 0)
                   (if (fn-arx-entry-ok
                         (fn-lb-entry-octets segment (nth 3 entry) log)
                         (fn-lb-entry-protected-len segment (nth 3 entry) log)) 16 0)
                   (if (fn-rcl-tombstonep payload) 32 0))))
    (mv-let (loc0 loc1) (fn-loc-make segment (nth 3 entry) (nth 4 entry))
      (let* ((words
               (list (fn-lbc-u64 (fn-record-payload row)) loc0 loc1
                     (fn-lbc-u64 head-length) (fn-lbc-u64 (fn-record-stamp row))
                     (fn-lbc-u64 max-stamp) (fn-lbc-u64 (fn-record-txid row))
                     (fn-lbc-u64 (fn-record-generation row)) (fn-lbc-u64 (fn-record-charge row))
                     (fn-lbc-msgid-hash (fn-record-msgid row))
                     (fn-lbc-u64 msgid-offset) (fn-lbc-u64 (len msgid-bytes))
                     (fn-lbc-u64 (car w)) (fn-lbc-u64 (cdr w)) (fn-lbc-u64 i) flags))
             (directory
               (list (fn-lbc-u64 (fn-record-sequence row))
                     (fn-lbc-u64 (fn-hf-octets facts))
                     (fn-lbc-u64 (fn-hf-body-start facts))
                     (if (natp (fn-hf-body-start facts)) t nil)
                     (fn-lbc-u64 (fn-hf-body-lines facts))
                     (fn-lbc-u64 nov-start) (if nov-small 1 0)
                     (fn-lbc-u64 render-start) 1
                     (fn-lbc-u64 groups-start) (fn-lbc-u64 (len (fn-record-groups row)))
                     (fn-lbc-u64 numbers-start) (fn-lbc-u64 (len (fn-held-numbers row)))
                     (equal (car (fn-nntp-section-of-bytes payload :article)) :ok)
                     (equal (car (fn-nntp-section-of-bytes payload :head)) :ok)
                     (equal (car (fn-nntp-section-of-bytes payload :body)) :ok)
                     (fn-lbc-u64 raw-head-length) (fn-nntp-framed-of-bytes payload)))
             (fn-lbc
               (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
                 (fn-lbc-rowwords) (fn-lbc-rowwords-append words fn-lbc-rowwords) fn-lbc))
             (fn-lbc
               (stobj-let ((fn-lbc-directory (fn-lbc-directory-store fn-lbc)))
                 (fn-lbc-directory) (fn-lbc-directory-append directory fn-lbc-directory) fn-lbc)))
        (fn-lbc-escape-store-put i escape fn-lbc)))))

(defun fn-lbc-visiblep (i v fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (or (not (and (natp i) (< i (rfix v)) (< i (fn-lbc-count fn-lbc)))) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (and (natp i) (< i (rfix v)) (< i (fn-lbc-count fn-lbc))
       (let ((w (fn-lbc-withdrawn i fn-lbc)))
         (or (null w) (<= (rfix v) (nfix (car w)))))))

(defun lb-prefix-max (stamps m)
  (declare (xargs :guard t))
  (if (atom stamps) nil
    (let ((m2 (max (nfix m) (nfix (car stamps)))))
      (cons m2 (lb-prefix-max (cdr stamps) m2)))))

(defun lb-first-at-least (th pm i)
  (declare (xargs :guard (and (natp th) (natp i))))
  (cond ((atom pm) i)
        ((>= (nfix (car pm)) th) i)
        (t (lb-first-at-least th (cdr pm) (+ 1 i)))))

(defun lb-keep-from (j th stamps i)
  (declare (xargs :guard (and (natp j) (natp th) (natp i))))
  (cond ((atom stamps) nil)
        ((and (>= i j) (>= (nfix (car stamps)) th))
         (cons i (lb-keep-from j th (cdr stamps) (+ 1 i))))
        (t (lb-keep-from j th (cdr stamps) (+ 1 i)))))

; This is the binary search used by the column reader.  The pure
; first-reaching lemma is kept separate so a stepped-back stamp is tested
; against its own value after the search, never against the prefix maximum.
(defun fn-lbc-first-reaching (threshold lo hi fn-lbc)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp threshold) (natp lo) (natp hi) (<= lo hi) (<= hi (fn-lbc-count fn-lbc)) (fn-lbc-escape-cellsp 0 fn-lbc))
                  :measure (nfix (- (nfix hi) (nfix lo)))
                  :verify-guards nil))
  (if (and (natp lo) (natp hi) (< lo hi))
      (let ((mid (+ lo (floor (- hi lo) 2))))
        (if (< (* 1000 (nfix (fn-lbc-value mid :prefix-max fn-lbc))) threshold)
            (fn-lbc-first-reaching threshold (+ 1 mid) hi fn-lbc)
          (fn-lbc-first-reaching threshold lo mid fn-lbc)))
    (nfix lo)))

(defun fn-lbc-newnews-candidatep (groups numbers)
  (declare (xargs :guard (or (atom groups) (alistp numbers)) :verify-guards nil))
  (if (consp groups)
      (or (let ((number (fn-nntp-membership-number (car groups) numbers)))
            (and (posp number) (<= number *fn-nntp-max-article-number*)))
          (fn-lbc-newnews-candidatep (cdr groups) numbers))
    nil))

(defun fn-lbc-newnews-tail (groups threshold v lo hi fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (natp lo) (natp hi) (<= lo hi) (<= hi (fn-lbc-count fn-lbc)) (fn-lbc-escape-cellsp 0 fn-lbc) (or (atom groups) (fn-lbc-number-escape-cellsp 0 fn-lbc)) (fn-lbc-stamp-escape-cellsp 0 fn-lbc))
                  :measure (nfix (- (nfix hi) (nfix lo)))
                  :verify-guards nil))
  (if (and (natp lo) (natp hi) (< lo hi))
      (let* ((i (- hi 1))
             (rest (fn-lbc-newnews-tail groups threshold v lo i fn-lbc)))
        (if (and (fn-lbc-visiblep i v fn-lbc)
                 (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc))
                 (fn-nntp-article-idp
                   (fn-make-article (fn-lbc-msgid i fn-lbc) 0 nil nil t 0))
                 (fn-lbc-newnews-candidatep groups (fn-lbc-numbers i fn-lbc))
                 (fn-ng-less-equal threshold
                   (* 1000 (fn-lbc-value i :stamp fn-lbc))))
            (cons (fn-nntp-string-octets (fn-lbc-msgid i fn-lbc)) rest)
          rest))
    nil))

(defun fn-lbc-newnews-range (groups threshold v horizon fn-lbc)
  (declare (xargs :stobjs fn-lbc
                  :guard (and (natp threshold) (natp v) (<= v (fn-lbc-count fn-lbc)) (fn-lbc-escape-cellsp 0 fn-lbc) (or (atom groups) (fn-lbc-number-escape-cellsp 0 fn-lbc)) (fn-lbc-stamp-escape-cellsp 0 fn-lbc))
                  :verify-guards nil)
           (ignore horizon))
  (let ((start (fn-lbc-first-reaching threshold 0 v fn-lbc)))
    (fn-lbc-newnews-tail groups threshold v start v fn-lbc)))

; Section success is an ingest fact.  A malformed logical payload may have
; a valid HEAD and an invalid BODY or vice versa; retain the raw header
; span separately so the all-row section equation also covers that case.
; The served dispatcher tests RECLAIMED first and never calls this worker
; for a tombstone.  Its all-row logical value is nevertheless specified.
; Raw tombstones use their raw span and the reference section conversion;
; a stuffed header length is not an offset into their unstuffed bytes.
(defun fn-lbc-stored-range (i kind fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lb-log-read-guardp log) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
  (let* ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
         (segment (fn-loc-segment a b)) (offset (fn-loc-offset a b))
         (length (fn-loc-len a b))
         (head (nfix (fn-lbc-value i :head-length fn-lbc)))
         (raw-head (nfix (fn-lbc-directory-value i :raw-head-length fn-lbc))))
    (cond
      ((fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)
       (fn-nntp-stuffed-section
         kind (fn-lb-log-model-read-range segment offset length log)))
      ((equal kind :article)
       (if (fn-lbc-directory-value i :article-ok fn-lbc)
           (fn-lb-log-model-read-range segment offset length log) nil))
      ((equal kind :head)
       (if (fn-lbc-directory-value i :head-ok fn-lbc)
           (fn-lb-log-model-read-range segment offset head log) nil))
      (t
       (if (fn-lbc-directory-value i :body-ok fn-lbc)
           (fn-lb-log-model-read-range segment (+ offset raw-head 2)
                                      (nfix (- (- length raw-head) 2)) log)
         nil)))))

(defun fn-lbc-number-get (group number fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (stobj-let ((fn-dmap (fn-lbc-number-store fn-lbc)))
    (value) (fn-dmap-get 0 (cons group number) fn-dmap) value))

(defun fn-lbc-number-put-first (group number i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (stobj-let ((fn-dmap (fn-lbc-number-store fn-lbc)))
    (fn-dmap)
    (if (natp (fn-dmap-get 0 (cons group number) fn-dmap)) fn-dmap
      (fn-dmap-put 0 (cons group number) i fn-dmap))
    fn-lbc))

(defun fn-lbc-number-put-row-seen (numbers seen i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (alistp (remove-equal nil (true-list-fix numbers))) (true-listp seen)) :verify-guards nil))
  (if (consp numbers)
      (let ((fn-lbc (if (member-equal (caar numbers) seen) fn-lbc
                     (fn-lbc-number-put-first (caar numbers) (cdar numbers) i fn-lbc))))
        (fn-lbc-number-put-row-seen (cdr numbers) (cons (caar numbers) seen) i fn-lbc))
    fn-lbc))

(defun fn-lbc-number-put-row (numbers i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (alistp (remove-equal nil (true-list-fix numbers))) :verify-guards nil))
  (fn-lbc-number-put-row-seen numbers nil i fn-lbc))

(defun fn-lbc-summary-word (group field fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (stobj-let ((fn-dmap (fn-lbc-number-store fn-lbc)))
    (value) (fn-dmap-get 1 (cons (list :summary group) field) fn-dmap)
    (if value value (if (equal field 4) 1 0))))

(defun fn-lbc-live-summary (group fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (list (fn-lbc-summary-word group 1 fn-lbc)
        (fn-lbc-summary-word group 2 fn-lbc)
        (fn-lbc-summary-word group 3 fn-lbc)
        (fn-lbc-summary-word group 4 fn-lbc)))

(defun fn-lbc-summary-put (group values field fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (if (consp values)
      (let ((fn-lbc
             (stobj-let ((fn-dmap (fn-lbc-number-store fn-lbc)))
               (fn-dmap) (fn-dmap-put 1 (cons (list :summary group) field)
                                     (car values) fn-dmap) fn-lbc)))
        (fn-lbc-summary-put group (cdr values) (+ 1 (nfix field)) fn-lbc))
    fn-lbc))

(defun fn-lbc-number-group-keys (numbers)
  (declare (xargs :guard (alistp (remove-equal nil (true-list-fix numbers))) :verify-guards nil))
  (if (consp numbers)
      (cons (caar numbers) (fn-lbc-number-group-keys (cdr numbers))) nil))

(defun fn-lbc-row-group-keys (rows)
  (declare (xargs :guard (fn-cat$ap rows) :verify-guards nil))
  (if (consp rows)
      (union-equal (fn-lbc-number-group-keys (fn-held-numbers (car rows)))
                   (fn-lbc-row-group-keys (cdr rows))) nil))

; Open's rebuild owns this recomputation.  No served summary reader calls
; the recomputation or walks a row.  Commit/withdraw maintain these cells.
(defun fn-lbc-rebuild-summaries (groups rows fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-cat$ap rows) :verify-guards nil))
  (if (consp groups)
      (let* ((g (car groups))
             (fn-lbc (fn-lbc-summary-put g
                         (list (fn-cat$a-group-live-count g rows)
                               (fn-cat$a-group-live-low g rows)
                               (fn-cat$a-group-live-high g rows)
                               (fn-cat$a-group-next g rows)) 1 fn-lbc)))
        (fn-lbc-rebuild-summaries (cdr groups) rows fn-lbc))
    fn-lbc))

(defun fn-lbc-rebuild-rows (rows log fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (fn-cat$ap rows) (fn-lb-log-read-guardp log) (fn-lbc-rows-log-guardp rows log) (fn-lbc-escape-cellsp 0 fn-lbc)) :verify-guards nil))
  (if (consp rows)
      (let* ((i (fn-lbc-count fn-lbc))
             (fn-lbc (fn-lbc-append-row (car rows) log fn-lbc))
             (fn-lbc (fn-lbc-number-put-row (fn-held-numbers (car rows)) i fn-lbc)))
        (fn-lbc-rebuild-rows (cdr rows) log fn-lbc))
    fn-lbc))

(defun fn-lbc-slot-count (fn-lbc)
  (declare (xargs :stobjs fn-lbc))
  (stobj-let ((fn-lbc-msgid-slots (fn-lbc-slot-store fn-lbc)))
    (n) (fn-lbc-msgid-slots-count fn-lbc-msgid-slots) n))

; The largest u64 word marks an escaped slot ordinal.  Escape records
; remain keyed by the row sequence; this small key directory provides the
; inverse lookup needed only on the unsupported-profile escape path.
(defconst *fn-lbc-slot-escape-word* 18446744073709551615)

; Guard-only shape of the inverse slot owners and each row's slot value.
; These predicates supply callee domains, never a logical data ceiling.
(defun fn-lbc-slot-owners-guardp (keys fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil))
  (if (consp keys)
      (and (eqlablep (car keys))
           (let ((cell (fn-lbc-escape-store-get (car keys) fn-lbc)))
             (and (alistp cell)
                  (true-listp (cdr (assoc-eq :msgid-slot cell)))))
           (fn-lbc-slot-owners-guardp (cdr keys) fn-lbc))
    (null keys)))

(defun fn-lbc-slot-values-guardp (i fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard t :verify-guards nil
                  :measure (nfix (- (fn-lbc-count fn-lbc) (nfix i)))))
  (if (and (natp i) (< i (fn-lbc-count fn-lbc)))
      (let ((cell (fn-lbc-escape-store-get i fn-lbc)))
        (and (alistp cell)
             (true-listp (cdr (assoc-eq :msgid-slot cell)))
             (fn-lbc-slot-values-guardp (+ i 1) fn-lbc)))
    t))

(defun fn-lbc-escaped-slot-word (slot keys fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-slot-owners-guardp keys fn-lbc) :verify-guards nil))
  (if (consp keys)
      (let ((position (fn-lbc-escape (car keys) :msgid-slot fn-lbc)))
        (if (and position (member-equal slot (cdr position)))
            (+ 1 (nfix (car keys)))
          (fn-lbc-escaped-slot-word slot (cdr keys) fn-lbc)))
    0))

(defun fn-lbc-slot-word (slot fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc) :verify-guards nil))
  (stobj-let ((fn-lbc-msgid-slots (fn-lbc-slot-store fn-lbc)))
    (word)
    (if (and (natp slot) (< slot (fn-lbc-msgid-slots-count fn-lbc-msgid-slots)))
        (fn-lbc-msgid-slots-get-word slot fn-lbc-msgid-slots) 0)
    (if (equal word *fn-lbc-slot-escape-word*)
        (fn-lbc-escaped-slot-word slot (fn-lbc-slot-escape-keys fn-lbc) fn-lbc)
      word)))

; Remove the current slot's inverse ownership and all stale copies before
; a write.  Other escaped slots retain their sequence-keyed records.
(defun fn-lbc-slot-drop-owner (slot keys fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-slot-owners-guardp keys fn-lbc) :verify-guards nil))
  (if (consp keys)
      (let* ((key (car keys))
             (cell (fn-lbc-escape-store-get key fn-lbc))
             (position (assoc-eq :msgid-slot cell))
             (drop (and position (member-equal slot (cdr position))))
             (remaining (remove-equal slot (cdr position)))
             (fn-lbc (if drop
                         (fn-lbc-escape-store-put key
                           (if remaining (put-assoc-eq :msgid-slot remaining cell)
                             (remove-assoc-eq :msgid-slot cell)) fn-lbc)
                       fn-lbc)))
        (mv-let (rest fn-lbc)
          (fn-lbc-slot-drop-owner slot (cdr keys) fn-lbc)
          (mv (if (and drop (not remaining)) rest (cons key rest)) fn-lbc)))
    (mv nil fn-lbc)))

(defun fn-lbc-slot-put (slot ordinal fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc) (or (not (and (natp slot) (< slot (fn-lbc-slot-count fn-lbc)))) (or (< (nfix ordinal) *fn-lbc-slot-escape-word*) (let* ((seq (- (nfix ordinal) 1)) (cell (fn-lbc-escape-store-get seq fn-lbc))) (and (alistp cell) (true-listp (cdr (assoc-eq :msgid-slot cell)))))))) :verify-guards nil))
  (if (not (and (natp slot) (< slot (fn-lbc-slot-count fn-lbc)))) fn-lbc
    (mv-let (keys fn-lbc)
      (fn-lbc-slot-drop-owner slot (fn-lbc-slot-escape-keys fn-lbc) fn-lbc)
    (let* ((fn-lbc (update-fn-lbc-slot-escape-keys keys fn-lbc))
           (ordinal (nfix ordinal))
           (escaped (<= *fn-lbc-slot-escape-word* ordinal))
           (seq (if (zp ordinal) 0 (- ordinal 1)))
           (fn-lbc
             (if escaped
                 (let* ((old (fn-lbc-escape-store-get seq fn-lbc))
                        (fn-lbc (fn-lbc-escape-store-put seq
                                   (put-assoc-eq :msgid-slot
                                     (cons slot (cdr (assoc-eq :msgid-slot old))) old) fn-lbc)))
                   (update-fn-lbc-slot-escape-keys
                     (if (member-equal seq (fn-lbc-slot-escape-keys fn-lbc))
                         (fn-lbc-slot-escape-keys fn-lbc)
                       (cons seq (fn-lbc-slot-escape-keys fn-lbc))) fn-lbc))
               fn-lbc))
           (fn-lbc
             (if (and escaped (< seq (fn-lbc-count fn-lbc)))
                 (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
                   (fn-lbc-rowwords)
                   (fn-lbc-rowwords-set-flags seq
                     (logior (fn-lbc-rowwords-get-flags seq fn-lbc-rowwords) 8)
                     fn-lbc-rowwords) fn-lbc)
               fn-lbc)))
      (stobj-let ((fn-lbc-msgid-slots (fn-lbc-slot-store fn-lbc)))
        (fn-lbc-msgid-slots)
        (fn-lbc-msgid-slots-set-word slot
          (if escaped *fn-lbc-slot-escape-word* ordinal) fn-lbc-msgid-slots)
        fn-lbc)))))

(defun fn-lbc-reserve-slots (n fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (natp n) :measure (nfix n)
                  :verify-guards nil))
  (if (zp n) fn-lbc
    (let ((fn-lbc
            (stobj-let ((fn-lbc-msgid-slots (fn-lbc-slot-store fn-lbc)))
              (fn-lbc-msgid-slots)
              (fn-lbc-msgid-slots-append '(0) fn-lbc-msgid-slots) fn-lbc)))
      (fn-lbc-reserve-slots (- n 1) fn-lbc))))

(defun fn-lbc-slot-insert (i slot fuel fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (natp fuel) (or (zp fuel) (and (natp slot) (< slot (fn-lbc-slot-count fn-lbc)) (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc) (or (< (nfix (+ 1 (nfix i))) *fn-lbc-slot-escape-word*) (let* ((seq (- (nfix (+ 1 (nfix i))) 1)) (cell (fn-lbc-escape-store-get seq fn-lbc))) (and (alistp cell) (true-listp (cdr (assoc-eq :msgid-slot cell))))))))) :measure (nfix fuel)
                  :verify-guards nil))
  (cond ((zp fuel) fn-lbc)
        ((equal (fn-lbc-slot-word slot fn-lbc) 0)
         (fn-lbc-slot-put slot (+ 1 (nfix i)) fn-lbc))
        (t (fn-lbc-slot-insert i (mod (+ 1 (nfix slot))
                                     (max 1 (fn-lbc-slot-count fn-lbc)))
                               (- fuel 1) fn-lbc))))

(defun fn-lbc-index-slots (i n fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (natp i) (natp n) (<= i n) (<= n (fn-lbc-count fn-lbc)) (fn-lbc-escape-cellsp 0 fn-lbc) (fn-lbc-slot-values-guardp 0 fn-lbc) (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc))
                  :measure (nfix (- (nfix n) (nfix i))) :verify-guards nil))
  (if (and (natp i) (natp n) (< i n))
      (let* ((capacity (fn-lbc-slot-count fn-lbc))
             (slot (mod (nfix (fn-lbc-word :msgid-hash i fn-lbc)) (max 1 capacity)))
             (fn-lbc (fn-lbc-slot-insert i slot capacity fn-lbc)))
        (fn-lbc-index-slots (+ i 1) n fn-lbc))
    fn-lbc))

(defun fn-lbc-msgid-probe (msgid hash slot fuel fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (natp fuel) (fn-lbc-escape-cellsp 0 fn-lbc) (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc)) :measure (nfix fuel)
                  :verify-guards nil))
  (if (zp fuel) nil
    (let ((word (fn-lbc-slot-word slot fn-lbc)))
      (if (zp word) nil
        (let* ((i (- word 1))
               (rest (fn-lbc-msgid-probe msgid hash
                       (mod (+ 1 (nfix slot)) (max 1 (fn-lbc-slot-count fn-lbc)))
                       (- fuel 1) fn-lbc)))
          (if (and (< i (fn-lbc-count fn-lbc))
                   (equal hash (fn-lbc-word :msgid-hash i fn-lbc))
                   (equal msgid (fn-lbc-msgid i fn-lbc)))
              (cons i rest)
            rest))))))

(defun fn-lbc-msgid-seqs (msgid fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (fn-lbc-escape-cellsp 0 fn-lbc) (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc)) :verify-guards nil))
  (let ((hash (fn-lbc-msgid-hash msgid)) (capacity (fn-lbc-slot-count fn-lbc)))
    (fn-lbc-msgid-probe msgid hash (mod hash (max 1 capacity)) capacity fn-lbc)))

; Independent canonical linear-probing table over full logical Message-IDs.
(defun fn-lbc-canonical-slot-insert (ordinal slot fuel table)
  (declare (xargs :guard (and (natp fuel) (true-listp table)) :measure (nfix fuel) :verify-guards nil))
  (cond ((zp fuel) table)
        ((equal (nth (nfix slot) table) 0) (update-nth (nfix slot) ordinal table))
        (t (fn-lbc-canonical-slot-insert ordinal
              (mod (+ 1 (nfix slot)) (max 1 (len table))) (- fuel 1) table))))

(defun fn-lbc-canonical-slots-from (rows i table)
  (declare (xargs :guard (true-listp table) :measure (acl2-count rows) :verify-guards nil))
  (if (consp rows)
      (fn-lbc-canonical-slots-from (cdr rows) (+ 1 (nfix i))
        (fn-lbc-canonical-slot-insert (+ 1 (nfix i))
          (mod (fn-lbc-msgid-hash (fn-record-msgid (car rows))) (max 1 (len table)))
          (len table) table))
    table))

(defun fn-lbc-canonical-slots (rows)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lbc-canonical-slots-from rows 0 (make-list (+ 1 (* 2 (len rows))) :initial-element 0)))

(defun fn-lbc-slot-cells-corr (table slot fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc) :verify-guards nil))
  (if (consp table)
      (and (equal (fn-lbc-slot-word slot fn-lbc) (car table))
           (fn-lbc-slot-cells-corr (cdr table) (+ 1 (nfix slot)) fn-lbc))
    t))

(defun fn-lbc-slots-corr (fn-lbc rows)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc) :verify-guards nil))
  (let* ((capacity (fn-lbc-slot-count fn-lbc))
         (table (fn-lbc-canonical-slots-from rows 0
                   (make-list capacity :initial-element 0))))
    (and (or (and (null rows) (equal capacity 0))
             (< (len rows) capacity))
         (fn-lbc-slot-cells-corr table 0 fn-lbc))))

(defun fn-lbc-number-keys-covered (numbers rows fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (alistp (remove-equal nil (true-list-fix numbers))) :verify-guards nil))
  (if (consp numbers)
      (and (equal (fn-lbc-number-get (caar numbers) (cdar numbers) fn-lbc)
                  (fn-cat-number-seq (caar numbers) (cdar numbers) rows 0))
           (fn-lbc-number-keys-covered (cdr numbers) rows fn-lbc))
    t))

(defun fn-lbc-number-rows-covered (rest rows fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-cat$ap rest) :verify-guards nil))
  (if (consp rest)
      (and (fn-lbc-number-keys-covered (fn-held-numbers (car rest)) rows fn-lbc)
           (fn-lbc-number-rows-covered (cdr rest) rows fn-lbc))
    t))

(defun fn-lbc-open-rebuild (rows log fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (fn-cat$ap rows) (fn-lb-log-read-guardp log) (fn-lbc-rows-log-guardp rows log) (fn-lb-log-homes-guardp log)) :verify-guards nil))
  (let* ((fn-lbc (fn-lbc-clear-columns fn-lbc))
         (fn-lbc (fn-lbc-rebuild-rows rows log fn-lbc))
         (groups (fn-lbc-row-group-keys rows))
         (fn-lbc (fn-lbc-rebuild-summaries groups rows fn-lbc))
         (fn-lbc (update-fn-lbc-summary-groups groups fn-lbc))
         (fn-lbc (fn-lbc-reserve-slots (+ 1 (* 2 (len rows))) fn-lbc)))
    (fn-lbc-index-slots 0 (len rows) fn-lbc)))

; Correspondence checks every log-home field against the original row.
; Comparing a decoded frame only with its own re-encoding would not bind
; the obligation, subject, release evidence, context, or control fields.
(defun fn-lbc-row-corr (i row prefix-max fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (and (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lb-log-read-guardp log) (alistp (fn-lbc-escape-store-get i fn-lbc))) (or (not (fn-cat-rowp row)) (fn-lb-value-treep (fn-lb-log-model-homes row)))) :verify-guards nil))
  (let* ((entry (fn-lbc-home-entry i fn-lbc log))
         (payload (fn-lb-log-payload row log))
         (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
         (segment (fn-loc-segment a b))
         (offset (fn-loc-offset a b)) (length (fn-loc-len a b))
         (reclaimed (fn-rcl-tombstonep payload)))
    (and (fn-lb-log-model-entryp entry)
         ; A catalog row names a committed entry, checked by the replay or
         ; ingest seal.  A corrupt trailer with a clear vmap bit is still a
         ; typed fault input to retrieval, but is not this correspondence.
         (fn-lbc-flag i *fn-lbc-ingest-verified-bit* fn-lbc)
         (fn-arx-entry-ok (fn-lb-entry-octets segment offset log)
                          (fn-lb-entry-protected-len segment offset log))
         (equal (nth 5 entry) (fn-record-payload row))
         (equal (nth 8 entry) (fn-record-sequence row))
         (equal (nth 7 entry) (fn-lb-log-model-homes row))
         (equal offset (nth 3 entry)) (equal length (nth 4 entry))
         (equal (fn-lbc-served-row i fn-lbc) (fn-cat-served-projection row))
         (equal (fn-lbc-value i :prefix-max fn-lbc) prefix-max)
         (equal (fn-lbc-word :msgid-hash i fn-lbc)
                (fn-lbc-msgid-hash (fn-record-msgid row)))
         (equal (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc) reclaimed)
         (equal (fn-lbc-value i :head-length fn-lbc)
                (len (fn-nntp-stuffed-section :head payload)))
         (equal (fn-lbc-directory-value i :raw-head-length fn-lbc)
                (len (fn-la-payload-wire
                       (fn-nntp-split-head (fn-nntp-split-article payload)))))
         (equal (fn-lbc-directory-value i :article-ok fn-lbc)
                (equal (car (fn-nntp-section-of-bytes payload :article)) :ok))
         (equal (fn-lbc-directory-value i :head-ok fn-lbc)
                (equal (car (fn-nntp-section-of-bytes payload :head)) :ok))
         (equal (fn-lbc-directory-value i :body-ok fn-lbc)
                (equal (car (fn-nntp-section-of-bytes payload :body)) :ok))
         (equal (fn-lbc-directory-value i :framed fn-lbc)
                (fn-nntp-framed-of-bytes payload))
         (equal (fn-lbc-render-nov i fn-lbc) (fn-hnov-of payload))
         (equal (fn-lb-log-model-read-range segment offset length log)
                (if reclaimed (fn-la-tombstone-raw payload) (fn-la-payload-wire payload)))
         (equal (fn-lb-log-model-read-home-frame (list segment (+ offset length)) log)
                (fn-lb-log-model-home-frame row)))))

(defun fn-lbc-rows-corr (i rows prefix-max fn-lbc log)
  (declare (xargs :stobjs fn-lbc :guard (and (natp i) (<= (+ i (len rows)) (fn-lbc-count fn-lbc)) (fn-lb-log-read-guardp log) (fn-lbc-escape-cellsp 0 fn-lbc) (fn-lbc-row-homes-guardp rows)) :measure (acl2-count rows)
                  :verify-guards nil))
  (if (consp rows)
      (let ((next-max (max (nfix prefix-max) (nfix (fn-record-stamp (car rows))))))
        (and (fn-lbc-row-corr i (car rows) next-max fn-lbc log)
             (fn-lbc-rows-corr (+ 1 (nfix i)) (cdr rows) next-max fn-lbc log)))
    t))

(defun fn-lbc-summaries-corr (groups rows fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-cat$ap rows) :verify-guards nil))
  (if (consp groups)
      (and (equal (fn-lbc-live-summary (car groups) fn-lbc)
                  (list (fn-cat$a-group-live-count (car groups) rows)
                        (fn-cat$a-group-live-low (car groups) rows)
                        (fn-cat$a-group-live-high (car groups) rows)
                        (fn-cat$a-group-next (car groups) rows)))
           (fn-lbc-summaries-corr (cdr groups) rows fn-lbc))
    t))

(defun fn-lbc-summary-cells-corr (keys table rows)
  (declare (xargs :guard (and (alistp table) (fn-cat$ap rows) (loop$ for p in (true-list-fix keys) always (and (or (consp p) (null p)) (or (consp (car p)) (null (car p))) (true-listp (car (car p)))))) :verify-guards nil))
  (if (consp keys)
      (let* ((key (caar keys)) (tag (car key)) (field (cdr key))
             (group (cadr tag)))
        (and (implies (and (true-listp tag) (equal (len tag) 2)
                           (equal (car tag) :summary)
                           (member-equal field '(1 2 3 4)))
                      (equal (cdr (assoc-equal key table))
                             (case field
                               (1 (fn-cat$a-group-live-count group rows))
                               (2 (fn-cat$a-group-live-low group rows))
                               (3 (fn-cat$a-group-live-high group rows))
                               (4 (fn-cat$a-group-next group rows)))))
             (fn-lbc-summary-cells-corr (cdr keys) table rows)))
    t))

(defun fn-lbc-number-cells-corr (keys table rows)
  (declare (xargs :guard (and (alistp table) (loop$ for p in (true-list-fix keys) always (and (or (consp p) (null p)) (or (consp (car p)) (null (car p)))))) :verify-guards nil))
  (if (consp keys)
      (let ((key (caar keys)))
        (and (equal (cdr (assoc-equal key table))
                    (fn-cat-number-seq (car key) (cdr key) rows 0))
             (fn-lbc-number-cells-corr (cdr keys) table rows)))
    t))

(defun-nx fn-lbc-tables-corr (fn-lbc rows)
  (let* ((dm (nth *fn-lbc-number-store* fn-lbc))
         (numbers (nth 0 dm)) (summaries (nth 1 dm)))
    (and (fn-lbc-number-cells-corr numbers numbers rows)
         (fn-lbc-summary-cells-corr summaries summaries rows))))

(defun-nx fn-lbc-corr (fn-lbc rows log)
  (and (equal (fn-lbc-count fn-lbc) (len rows))
       (equal (fn-lbc-summary-groups fn-lbc) (fn-lbc-row-group-keys rows))
       (fn-lbc-rows-corr 0 rows 0 fn-lbc log)
       (fn-lbc-tables-corr fn-lbc rows)
       (fn-lbc-number-rows-covered rows rows fn-lbc)
       (fn-lbc-slots-corr fn-lbc rows)
       (fn-lbc-summaries-corr (fn-lbc-row-group-keys rows) rows fn-lbc)))
