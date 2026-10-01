; Version-aware remote client support; the outer FNCT/reason contract is
; unchanged. Located framing reads fixed9/fixed4 bytes before any item read.
; Logical semantic reference decoding is not a funded served parser claim.
(in-package "ACL2")
(include-book "consumer-remote-collection")

(defun fn-crcol-client-item (bytes)
 (declare (xargs :guard t))
 (let ((withdrawal (fn-ncr-withdrawal-decode bytes)))
  (if (eq (fn-cp-nth 0 withdrawal) :withdrawn) withdrawal
   (let* ((decoded (fn-record-decode-exact bytes)) (row (fn-record-result-record decoded)))
    (if (eq (fn-cp-nth 0 decoded) :ok)
        (list :article (fn-record-msgid row) (fn-record-payload row) (fn-record-groups row))
     '(:refused :remote-report-variant))))))

(defun fn-crcol-client-parts (bytes count)
 (declare (xargs :guard t :measure (nfix count)))
 (if (zp (nfix count)) (if (null bytes) '(:reports) '(:refused :remote-report-tail))
  (if (not (and (true-listp bytes) (<= 4 (len bytes)) (fn-cbor-octet-listp (take 4 bytes))))
      '(:refused :remote-report-length)
   (let* ((width (nfix (ec-call (fn-cbor-u32-from bytes)))) (rest (nthcdr 4 bytes)))
    (if (not (and (posp width) (<= width (len rest)))) '(:refused :remote-report-length)
     (let* ((item (fn-crcol-client-item (take width rest)))
            (next (if (eq (fn-cp-nth 0 item) :refused) item
                    (fn-crcol-client-parts (nthcdr width rest) (1- (nfix count))))))
      (if (eq (fn-cp-nth 0 next) :reports)
          (cons :reports (cons item (cdr next))) next)))))))

; SUPPORTED-VERSION is an explicit client capability; absence/unknown refuses
; collection magic before treating it as an article or producing an ACK.
; Existing singleton wire remains unchanged and needs no collection capability.
(defun fn-crcol-client-report (bytes supported-version items ceiling)
 (declare (xargs :guard t :guard-hints (("Goal" :in-theory (enable fn-crcol-profilep)))))
 (cond ((not (and (fn-crcol-profilep items ceiling) (true-listp bytes)
                  (<= (len bytes) ceiling) (fn-cbor-octet-listp bytes)))
        '(:refused :remote-report-profile))
       ((equal (take 4 bytes) *fn-crcol-magic*)
        (cond ((not (equal supported-version *fn-crcol-version*))
               '(:refused :remote-report-version))
              ((not (and (<= 9 (len bytes)) (equal (nth 4 bytes) *fn-crcol-version*)))
               '(:refused :remote-report-version))
              (t
               (let ((count (nfix (ec-call (fn-cbor-u32-from (nthcdr 5 bytes))))))
                (if (and (< 1 count) (<= count items))
                    (fn-crcol-client-parts (nthcdr 9 bytes) count)
                 '(:refused :remote-report-count))))))
       ((null bytes) '(:reports))
       (t (let ((item (fn-crcol-client-item bytes)))
            (if (eq (fn-cp-nth 0 item) :refused) item (list :reports item))))))

; Actual existing FNCT poll parser first, then versioned report validation.
; Cursor bytes are returned only with the complete validated report list.
(defun fn-crcol-client-poll (operation bytes version items ceiling)
 (declare (xargs :guard t))
 (let ((reply (fn-ncr-consumer-reply-decode operation bytes)))
  (if (not (and (member-eq operation '(:poll :wait))
                (eq (fn-cp-nth 0 reply) :consumer-poll-reply)
                (eq (fn-cp-nth 1 reply) :accepted))) reply
   (let ((reports (fn-crcol-client-report (fn-cp-nth 3 reply) version items ceiling)))
    (if (eq (fn-cp-nth 0 reports) :reports)
        (list :consumer-poll-reports (fn-cp-nth 2 reply) (cdr reports)) reports)))))

(defun fn-crcol-buffer-u32 (position fn-octets)
 (declare (xargs :stobjs fn-octets :guard (and (natp position) (<= (+ 4 position) (fn-octets-len fn-octets)))))
 (+ (* 16777216 (nfix (fn-octets-get (nfix position) fn-octets)))
    (* 65536 (nfix (fn-octets-get (+ 1 (nfix position)) fn-octets)))
    (* 256 (nfix (fn-octets-get (+ 2 (nfix position)) fn-octets)))
    (nfix (fn-octets-get (+ 3 (nfix position)) fn-octets))))

; Fixed5 key,next length offset,end,remaining. The caller retains immutable
; input buffer custody; a key by itself is not that physical grant.
(defun fn-crcol-client-locate-begin (key version items ceiling fn-octets)
 (declare (xargs :stobjs fn-octets :guard t
   :guard-hints (("Goal" :in-theory (enable fn-crcol-profilep)))))
 (let ((end (fn-octets-len fn-octets)))
  (cond ((not (and (fn-crcol-profilep items ceiling) (<= end ceiling) (<= 9 end)))
         '(:refused :remote-report-profile))
        ((not (and (equal version 1) (equal (fn-octets-get 0 fn-octets) 70)
                    (equal (fn-octets-get 1 fn-octets) 78) (equal (fn-octets-get 2 fn-octets) 82)
                    (equal (fn-octets-get 3 fn-octets) 66) (equal (fn-octets-get 4 fn-octets) 1)))
         '(:refused :remote-report-version))
        (t (let ((count (fn-crcol-buffer-u32 5 fn-octets)))
             (if (and (< 1 count) (<= count items))
              (list :yield (list :remote-collection-locate key 9 end count))
              '(:refused :remote-report-count)))))))

(defun fn-crcol-client-locate-step (s key fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (let ((position (fn-cp-nth 2 s)) (end (fn-cp-nth 3 s)) (remaining (fn-cp-nth 4 s)))
  (cond ((not (equal key (fn-cp-nth 1 s))) '(:refused :consumer-source-changed))
        ((not (and (eq (fn-cp-nth 0 s) :remote-collection-locate) (natp position)
                    (natp end) (equal end (fn-octets-len fn-octets)) (<= position end)
                    (natp remaining))) '(:refused :remote-report-coordinate))
        ((zp remaining) (if (equal position end) '(:complete) '(:refused :remote-report-tail)))
        ((< end (+ 4 position)) '(:refused :remote-report-length))
        (t (let* ((width (fn-crcol-buffer-u32 position fn-octets)) (start (+ 4 position))
                  (finish (+ start width)))
             (if (and (posp width) (<= finish end))
              (list :part start finish (list :remote-collection-locate key finish end (1- remaining)))
              '(:refused :remote-report-length)))))))

; Complete logical observations of the two concrete located reader results.
(defun fn-crcol-nth-reference (i bytes)
 (declare (xargs :guard (natp i)))
 (ec-call (nth i bytes)))
(defun fn-crcol-buffer-u32-reference (position bytes)
 (declare (xargs :guard t))
 (+ (* 16777216 (nfix (fn-crcol-nth-reference (nfix position) bytes)))
    (* 65536 (nfix (fn-crcol-nth-reference (+ 1 (nfix position)) bytes)))
    (* 256 (nfix (fn-crcol-nth-reference (+ 2 (nfix position)) bytes)))
    (nfix (fn-crcol-nth-reference (+ 3 (nfix position)) bytes))))

(defun fn-crcol-client-locate-begin-reference (key version items ceiling bytes)
 (declare (xargs :guard t
   :guard-hints (("Goal" :in-theory (enable fn-crcol-profilep)))))
 (let ((end (len bytes)))
  (cond ((not (and (fn-crcol-profilep items ceiling) (<= end ceiling) (<= 9 end)))
         '(:refused :remote-report-profile))
        ((not (and (equal version 1) (equal (fn-crcol-nth-reference 0 bytes) 70)
                    (equal (fn-crcol-nth-reference 1 bytes) 78) (equal (fn-crcol-nth-reference 2 bytes) 82)
                    (equal (fn-crcol-nth-reference 3 bytes) 66) (equal (fn-crcol-nth-reference 4 bytes) 1)))
         '(:refused :remote-report-version))
        (t (let ((count (fn-crcol-buffer-u32-reference 5 bytes)))
             (if (and (< 1 count) (<= count items))
              (list :yield (list :remote-collection-locate key 9 end count))
              '(:refused :remote-report-count)))))))

(defun fn-crcol-client-locate-step-reference (s key bytes)
 (declare (xargs :guard t))
 (let ((position (fn-cp-nth 2 s)) (end (fn-cp-nth 3 s)) (remaining (fn-cp-nth 4 s)))
  (cond ((not (equal key (fn-cp-nth 1 s))) '(:refused :consumer-source-changed))
        ((not (and (eq (fn-cp-nth 0 s) :remote-collection-locate) (natp position)
                    (natp end) (equal end (len bytes)) (<= position end)
                    (natp remaining))) '(:refused :remote-report-coordinate))
        ((zp remaining) (if (equal position end) '(:complete) '(:refused :remote-report-tail)))
        ((< end (+ 4 position)) '(:refused :remote-report-length))
        (t (let* ((width (fn-crcol-buffer-u32-reference position bytes)) (start (+ 4 position))
                  (finish (+ start width)))
             (if (and (posp width) (<= finish end))
              (list :part start finish (list :remote-collection-locate key finish end (1- remaining)))
              '(:refused :remote-report-length)))))))

(defthm fn-crcol-client-locate-begin-is-reference
 (equal (fn-crcol-client-locate-begin key version items ceiling fn-octets)
        (fn-crcol-client-locate-begin-reference key version items ceiling fn-octets))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d
   (fn-crcol-client-locate-begin fn-crcol-client-locate-begin-reference
    fn-crcol-buffer-u32 fn-crcol-buffer-u32-reference fn-oct-get-is-nth fn-oct-len-is-len fn-crcol-nth-reference)
   (fn-crcol-profilep fn-cp-nth nth nfix len)))))
(defthm fn-crcol-client-locate-step-is-reference
 (equal (fn-crcol-client-locate-step s key fn-octets)
        (fn-crcol-client-locate-step-reference s key fn-octets))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d
   (fn-crcol-client-locate-step fn-crcol-client-locate-step-reference
    fn-crcol-buffer-u32 fn-crcol-buffer-u32-reference fn-oct-get-is-nth fn-oct-len-is-len fn-crcol-nth-reference)
   (fn-cp-nth nth nfix len)))))

(in-theory (disable fn-crcol-client-item fn-crcol-client-parts fn-crcol-client-report
 fn-crcol-client-poll fn-crcol-buffer-u32 fn-crcol-client-locate-begin fn-crcol-client-locate-step fn-crcol-buffer-u32-reference
 fn-crcol-client-locate-begin-reference fn-crcol-client-locate-step-reference fn-crcol-nth-reference))
