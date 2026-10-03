; Existing ordinary RECORD report, never a modified signed statement. The
; internal caller owes genuine retained row/payload/report extent authority.
; Metadata preparation takes one bounded codec-name per tick; concrete output
; takes one octet per tick. Arena attachment/physical reader funding is separate.
(in-package "ACL2")
(include-book "consumer-remote-semantic-scan")
(include-book "consumer-local-control")
(include-book "records")
(include-book "payload-arena")
(include-book "octets-stobj")

; Proof/client observation only; no served payload materialization.
(defun fn-crvp-record (row groups payload)
 (declare (xargs :guard t))
 (fn-record-make (fn-record-sequence row) (fn-record-txid row)
  (fn-record-generation row) (fn-record-msgid row) payload groups
  (fn-record-obligation-id row) (fn-record-content-subject row)
  (fn-record-release-evidence row) (fn-record-charge row) (fn-record-stamp row)))

(defun fn-crvp-prefix (row payload-length)
 (declare (xargs :guard t))
 (append (fn-record-item-encode (cons :bytes *fn-record-magic*))
  (fn-record-uint-encode (fn-record-schema-octet row))
  (fn-record-uint-encode (fn-record-sequence row))
  (fn-record-uint-encode (fn-record-txid row))
  (fn-record-uint-encode (fn-record-generation row))
  (fn-record-item-encode (cons :bytes (fn-record-string-octets (fn-record-msgid row))))
  (fn-cbor-encode-argument 2 (nfix payload-length))))

(defun fn-crvp-suffix (row)
 (declare (xargs :guard t))
 (append
  (fn-record-item-encode (cons :bytes (fn-record-string-octets (fn-record-obligation-id row))))
  (fn-record-item-encode (cons :bytes (fn-record-string-octets (fn-record-content-subject row))))
  (fn-record-item-encode (cons :bytes (fn-record-string-octets (fn-record-release-evidence row))))
  (fn-record-uint-encode (fn-record-charge row)) (fn-record-uint-encode (fn-record-stamp row))))

(defun fn-crvp-textp (text maximum nonempty)
 (declare (xargs :guard t))
 (and (stringp text) (<= (length text) (nfix maximum))
      (or (not nonempty) (< 0 (length text)))))

; Fixed16: key,phase,row,whole authorized groups,group suffix,count,group width,
; payload length,report ceiling,initial offset,next offset,payload index,bytes,
; exact end,next phase. A current-row/payload alias is data, never a grant.
(defun fn-crvp-state (key phase row groups suffix count width plen ceiling base pos i bytes end next)
 (declare (xargs :guard t))
 (list :remote-visible-write key phase row groups suffix count width plen ceiling base pos i bytes end next))

(defun fn-crvp-begin (key kind projection event ceiling used fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (let* ((row (fn-crps-row-article event)) (tagged (fn-cp-nth 1 projection))
        (article (fn-cp-nth 1 tagged)) (groups (fn-cp-nth 2 projection))
        (h (fn-record-payload row)))
  (cond
   ((not (eq kind :visible)) '(:refused :remote-visible-kind))
   ((not (and row (eq (fn-cp-nth 0 projection) :report-input)
               (eq (fn-cp-nth 0 tagged) :current-article) (consp groups)
               (equal (fn-record-msgid row) (fn-article-msgid article))
               (equal h (fn-article-payload article))
               (equal (fn-record-stamp row) (fn-article-stamp article))))
    '(:refused :remote-visible-source-binding))
   ((not (and (natp used) (posp ceiling) (fn-cp-uintp ceiling)))
    '(:refused :remote-report-profile))
   ((not (and (natp h) (< h (fn-arena-count fn-arena))))
    '(:unavailable :remote-payload-source))
   ((or (< *fn-record-max-payload* (fn-arena-payload-len h fn-arena))
        (not (and (fn-record-uint64p (fn-record-sequence row))
                   (fn-record-uint64p (fn-record-txid row))
                   (fn-record-uint64p (fn-record-generation row))
                   (fn-record-uint64p (fn-record-charge row))
                   (fn-record-stampp (fn-record-stamp row))
                   (fn-crvp-textp (fn-record-msgid row) *fn-record-max-msgid* t)
                   (fn-crvp-textp (fn-record-obligation-id row) *fn-record-max-metadata* t)
                   (fn-crvp-textp (fn-record-content-subject row) *fn-record-max-metadata* t)
                   (fn-crvp-textp (fn-record-release-evidence row) *fn-record-max-metadata* t))))
    '(:refused :remote-visible-codec))
   (t (list :yield (fn-crvp-state key :prepare row groups groups 0 0
        (fn-arena-payload-len h fn-arena) ceiling used used 0 nil nil nil))))))
(fn-payload-kind fn-crvp-begin :handle "compares the row's handle with the article's; reads no octets")

; PREPARE walks one projected name, whose maximum is the existing codec's.
; Later phases queue only one name or the fixed bounded record metadata.
(defun fn-crvp-plan (s key used extent fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (let* ((phase (fn-cp-nth 2 s)) (row (fn-cp-nth 3 s))
        (groups (fn-cp-nth 4 s)) (suffix (fn-cp-nth 5 s))
        (count (fn-cp-nth 6 s)) (width (fn-cp-nth 7 s)) (plen (fn-cp-nth 8 s))
        (ceiling (fn-cp-nth 9 s)) (base (fn-cp-nth 10 s))
        (pos (fn-cp-nth 11 s)) (i (fn-cp-nth 12 s))
        (bytes (fn-cp-nth 13 s)) (end (fn-cp-nth 14 s)) (next (fn-cp-nth 15 s))
        (h (fn-record-payload row)))
  (cond
   ((not (equal key (fn-cp-nth 1 s))) '(:refused :consumer-source-changed))
   ((not (and (eq (fn-cp-nth 0 s) :remote-visible-write) (natp used) (equal used pos)
               (natp pos) (natp base) (natp count) (natp width) (natp plen)
               (posp ceiling) (fn-cp-uintp ceiling) (natp extent) (natp i)))
    '(:refused :remote-visible-coordinate))
   ((not (and (natp h) (< h (fn-arena-count fn-arena))
               (equal plen (fn-arena-payload-len h fn-arena))))
    '(:unavailable :remote-payload-source))
   ((eq phase :prepare)
    (cond
     ((consp suffix)
      (if (and (< count *fn-record-max-groups*)
                (fn-crvp-textp (car suffix) *fn-record-max-group-name* t)
                (fn-record-group-namep (car suffix)))
       (list :yield (fn-crvp-state key phase row groups (cdr suffix) (1+ count)
         (+ width (len (fn-record-item-encode (cons :bytes (fn-record-string-octets (car suffix))))))
         plen ceiling base pos i nil nil nil))
       '(:refused :remote-visible-group-codec)))
     ((not (null suffix)) '(:refused :remote-visible-groups))
     ((zp count) '(:refused :remote-visible-read-scope))
     (t
      (let* ((prefix (fn-crvp-prefix row plen)) (tail (fn-crvp-suffix row))
             (size (+ (len prefix) plen (len (fn-record-uint-encode count)) width (len tail)))
             (finish (+ base size)))
       (if (or (< ceiling size) (< *fn-stxa-max-octets* size) (< extent finish))
           '(:refused :oversize)
        (list :yield (fn-crvp-state key :bytes row groups groups count width plen ceiling
                               base pos i prefix finish :payload)))))))
   ((not (and (natp end) (<= base pos) (<= pos end) (<= end extent)))
    '(:refused :remote-report-extent))
   ((eq phase :bytes)
    (cond ((consp bytes)
           (if (and (< pos end) (fn-cbor-octetp (car bytes)))
            (list :append (car bytes) (fn-crvp-state key phase row groups suffix count width plen
              ceiling base (1+ pos) i (cdr bytes) end next))
            '(:refused :remote-visible-octet)))
          ((not (null bytes)) '(:refused :remote-visible-tail))
          (t (list :yield (fn-crvp-state key next row groups suffix count width plen
                                        ceiling base pos i nil end nil)))))
   ((eq phase :payload)
    (cond ((and (< i plen) (< pos end))
           (let ((octet (fn-arena-get h i fn-arena)))
            (if (fn-cbor-octetp octet)
             (list :append octet (fn-crvp-state key phase row groups suffix count width plen ceiling
                                   base (1+ pos) (1+ i) nil end nil))
             '(:refused :remote-payload-octet))))
          ((equal i plen)
           (list :yield (fn-crvp-state key :bytes row groups groups count width plen ceiling base pos i
                                     (fn-record-uint-encode count) end :groups)))
          (t '(:refused :remote-payload-coordinate))))
   ((eq phase :groups)
    (cond ((consp suffix)
           (if (fn-crvp-textp (car suffix) *fn-record-max-group-name* t)
            (list :yield (fn-crvp-state key :bytes row groups (cdr suffix) count width plen ceiling base pos i
               (fn-record-item-encode (cons :bytes (fn-record-string-octets (car suffix)))) end :groups))
            '(:refused :remote-visible-group-codec)))
          ((not (null suffix)) '(:refused :remote-visible-groups))
          (t (list :yield (fn-crvp-state key :bytes row groups nil count width plen ceiling base pos i
                                        (fn-crvp-suffix row) end :finished)))))
   ((eq phase :finished) (if (equal pos end) '(:encoded) '(:refused :remote-visible-end)))
   (t '(:refused :remote-visible-phase)))))

(defun fn-crvp-step (s key extent fn-arena fn-octets)
 (declare (xargs :stobjs (fn-arena fn-octets) :guard t
   :guard-hints (("Goal" :in-theory (enable fn-crvp-plan fn-cp-nth)))))
 (let ((plan (fn-crvp-plan s key (fn-octets-len fn-octets) extent fn-arena)))
  (if (eq (fn-cp-nth 0 plan) :append)
      (let ((fn-octets (fn-octets-append-list (list (fn-cp-nth 1 plan)) fn-octets)))
       (mv (list :yield (fn-cp-nth 2 plan)) fn-octets))
   (mv plan fn-octets))))

(defun fn-crvp-reference (s key extent fn-arena bytes)
 (declare (xargs :stobjs fn-arena :guard t))
 (let ((plan (fn-crvp-plan s key (len bytes) extent fn-arena)))
  (if (eq (fn-cp-nth 0 plan) :append)
      (mv (list :yield (fn-cp-nth 2 plan)) (ec-call (binary-append bytes (list (fn-cp-nth 1 plan)))))
    (mv plan bytes))))

(defthm fn-crvp-step-is-reference-result-and-buffer-effect
 (equal (fn-crvp-step s key extent fn-arena fn-octets)
        (fn-crvp-reference s key extent fn-arena fn-octets))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-crvp-step fn-crvp-reference fn-oct-len-is-len fn-oct-append-list-is-append)
       (fn-crvp-plan fn-cp-nth len)))))

(in-theory (disable fn-crvp-record fn-crvp-prefix fn-crvp-suffix fn-crvp-textp
 fn-crvp-state fn-crvp-begin fn-crvp-plan fn-crvp-step fn-crvp-reference))
