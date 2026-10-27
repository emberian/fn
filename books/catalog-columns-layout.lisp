; Unchanged resident page schemas and stobj fields. Isolated so changes to
; constructor/read decisions do not rebuild all page-generator proofs.
(in-package "ACL2")
(include-book "def-representation-pages")
(include-book "def-representation-pageread")
(include-book "def-representation")
(include-book "catalog-dense-map")
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

