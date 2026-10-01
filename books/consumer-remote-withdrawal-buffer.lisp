; Concrete target-only writer for the EXISTING FNWD1 report. No authority or
; funding is issued here. The installed caller must reserve this exact report
; extent and retain source/buffer custody before entering the bounded writer.
(in-package "ACL2")
(include-book "consumer-reason")
(include-book "consumer-remote-semantic-scan")
(include-book "octets-stobj")

; Fixed5: key, remaining bounded report bytes, exact next offset, exact end.
(defun fn-crwd-state (key remaining position end)
 (declare (xargs :guard t))
 (list :remote-withdrawal-write key remaining position end))

; The semantic producer supplied a current ARTICLE and readable projection.
; Only that TARGET Message-ID is encoded: no cause, content, group or number.
; Conversion/validation is bounded by the existing Message-ID codec width.
(defun fn-crwd-begin (key kind projection report-ceiling used)
 (declare (xargs :guard t))
 (let* ((tagged (fn-cp-nth 1 projection)) (article (fn-cp-nth 1 tagged))
        (msgid (fn-article-msgid article)))
  (cond ((not (member-eq kind '(:withdrawn :withdrawal-target)))
         '(:unavailable :remote-visible-report-producer))
        ((not (and (eq (fn-cp-nth 0 projection) :report-input)
                    (eq (fn-cp-nth 0 tagged) :current-article)
                    (consp (fn-cp-nth 2 projection))))
         '(:refused :remote-withdrawal-projection))
        ((not (and (stringp msgid) (< 0 (length msgid))
                    (<= (length msgid) *fn-cp-max-token*)))
         '(:refused :remote-withdrawal-message-id))
        ((not (and (natp used) (posp report-ceiling) (fn-cp-uintp report-ceiling)))
         '(:refused :remote-report-profile))
        (t
         (let ((bytes (fn-ncr-withdrawal-report (fn-record-string-octets msgid))))
          (cond ((not bytes) '(:refused :remote-withdrawal-message-id))
                ((< report-ceiling (+ used (len bytes))) '(:refused :oversize))
                (t (list :yield (fn-crwd-state key bytes used (+ used (len bytes)))
                         (+ used (len bytes))))))))))

; No whole byte-list validation on a writer step. A maintained constructor
; supplies it; malformed current octets/coordinates refuse before any write.
(defun fn-crwd-plan (s key used extent)
 (declare (xargs :guard t))
 (let ((remaining (fn-cp-nth 2 s)) (position (fn-cp-nth 3 s)) (end (fn-cp-nth 4 s)))
  (cond ((not (equal key (fn-cp-nth 1 s))) '(:refused :consumer-source-changed))
        ((not (and (eq (fn-cp-nth 0 s) :remote-withdrawal-write)
                    (natp position) (equal position used) (natp end)
                    (natp extent) (<= position end) (<= end extent)))
         '(:refused :remote-report-extent))
        ((consp remaining)
         (if (and (< position end) (fn-cbor-octetp (car remaining)))
             (list :append (car remaining)
                (fn-crwd-state key (cdr remaining) (1+ position) end))
           '(:refused :remote-withdrawal-octet)))
        ((and (null remaining) (equal position end)) '(:encoded))
        (t '(:refused :remote-withdrawal-tail)))))

; The concrete caller writes exactly ONE octet per scheduling step.
(defun fn-crwd-step (s key extent fn-octets)
 (declare (xargs :stobjs fn-octets :guard t
   :guard-hints (("Goal" :in-theory (enable fn-crwd-plan fn-cp-nth)))))
 (let ((plan (fn-crwd-plan s key (fn-octets-len fn-octets) extent)))
  (if (eq (fn-cp-nth 0 plan) :append)
      (let ((fn-octets (fn-octets-append-list (list (fn-cp-nth 1 plan)) fn-octets)))
       (mv (list :yield (fn-cp-nth 2 plan)) fn-octets))
    (mv plan fn-octets))))

; Proof-only observation of complete result and complete concrete effect.
(defun fn-crwd-reference (s key extent bytes)
 (declare (xargs :guard t))
 (let ((plan (fn-crwd-plan s key (len bytes) extent)))
  (if (eq (fn-cp-nth 0 plan) :append)
      (mv (list :yield (fn-cp-nth 2 plan))
          (ec-call (binary-append bytes (list (fn-cp-nth 1 plan)))))
    (mv plan bytes))))

(defthm fn-crwd-step-is-reference-result-and-buffer-effect
 (equal (fn-crwd-step s key extent fn-octets)
        (fn-crwd-reference s key extent fn-octets))
 :rule-classes nil
 :hints (("Goal" :in-theory
   (e/d (fn-crwd-step fn-crwd-reference fn-oct-len-is-len fn-oct-append-list-is-append)
        (fn-crwd-plan fn-cp-nth len)))))

(in-theory (disable fn-crwd-state fn-crwd-begin fn-crwd-plan fn-crwd-step fn-crwd-reference))
