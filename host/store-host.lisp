; Trusted experimental POSIX store bridge.  The record codec and replay engine
; remain ACL2 definitions; this file only converts bounded numeric octets at the
; process boundary and keeps an interpreted ACL2 node in globals.
(in-package "ACL2")

(defconst *fn-store-groups* '("fn.letters" "fn.test"))
(defconst *fn-store-capacity* 1048576)
(defconst *fn-store-max-text* 512)
(defconst *fn-store-max-payload* 32768)

(defun fn-store-text-octetsp-tail (xs)
  (if (consp xs)
      (and (fn-octetp (car xs)) (<= 33 (car xs)) (<= (car xs) 126)
           (fn-store-text-octetsp-tail (cdr xs)))
    (null xs)))

(defun fn-store-text-octetsp (xs)
  (and (consp xs)
       (<= (len xs) *fn-store-max-text*)
       (fn-octet-listp xs)
       (<= 33 (car xs)) (<= (car xs) 126)
       (fn-store-text-octetsp-tail (cdr xs))))

(defun fn-store-msgid-octetsp (xs)
  (and (fn-store-text-octetsp xs)
       (<= 3 (len xs))
       (equal (car xs) 60)
       (equal (car (last xs)) 62)))

; Inputs reached this point as decimal octet literals, after length and
; character checks.  The records codec's ACL2 conversion is used directly;
; no incoming bytes are passed to the Lisp reader or evaluator.
(defun fn-store-octets->string (xs)
  (fn-record-octets-string xs))

(defun fn-store-group-code (code)
  (if (equal code 0) "fn.letters"
    (if (equal code 1) "fn.test" nil)))

(defun fn-store-groups-from-codes (codes)
  (if (consp codes)
      (let ((group (fn-store-group-code (car codes))))
        (if group
            (let ((rest (fn-store-groups-from-codes (cdr codes))))
              (if (or (equal rest :bad) (member-equal group rest))
                  :bad
                (cons group rest)))
          :bad))
    (if (null codes) nil :bad)))

(defun fn-store-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-store-node
                               (fn-node-initial-state *fn-store-groups*
                                                      *fn-store-capacity*) state))
         (state (f-put-global 'fn-store-records nil state))
         (state (f-put-global 'fn-store-next-sequence 0 state))
         (state (f-put-global 'fn-store-action :ready state))
         (state (f-put-global 'fn-store-pending-record nil state))
         (state (f-put-global 'fn-store-pending-txid nil state))
         (state (f-put-global 'fn-store-pending-generation nil state)))
    (value :ready)))

(defun fn-store-decode-records (octet-records)
  (declare (xargs :mode :program))
  (if (consp octet-records)
      (let ((decoded (fn-record-decode-exact (car octet-records))))
        (if (and (consp decoded) (equal (car decoded) :ok)
                 (consp (cdr decoded)) (fn-record-p (car (cdr decoded))))
            (let ((rest (fn-store-decode-records (cdr octet-records))))
              (if (equal rest :bad) :bad (cons (car (cdr decoded)) rest)))
          :bad))
    (if (null octet-records) nil :bad)))

(defun fn-store-recover (octet-records allocation-frontier state)
  (declare (xargs :stobjs state :mode :program))
  (let ((records (fn-store-decode-records octet-records)))
    (if (equal records :bad)
        (let ((state (f-put-global 'fn-store-action :fault state)))
          (value :fault))
      (let ((result (fn-replay *fn-store-groups* *fn-store-capacity* records)))
        (if (and (consp result) (equal (car result) :ok))
            (let* ((replayed-node (car (cdr result)))
                   (next (car (cdr (cdr result))))
                   ; The durable allocator frontier records IDs consumed by
                   ; known aborts which have no commit record.  Replay owns
                   ; the only state reconstruction; this call only advances
                   ; an idle, unfenced replay result through its ACL2 helper.
                   (node (if (fn-replay-advance-okp replayed-node allocation-frontier)
                             (fn-replay-advance-txid replayed-node allocation-frontier)
                           nil)))
              (if (and node
                       (equal (fn-state-next-txid (fn-node-acceptance node))
                              allocation-frontier))
                  (let* ((state (f-put-global 'fn-store-node node state))
                         (state (f-put-global 'fn-store-records records state))
                         (state (f-put-global 'fn-store-next-sequence next state))
                         (state (f-put-global 'fn-store-action :ready state))
                         (state (f-put-global 'fn-store-pending-record nil state))
                         (state (f-put-global 'fn-store-pending-txid nil state))
                         (state (f-put-global 'fn-store-pending-generation nil state)))
                    (value :ready))
                (let ((state (f-put-global 'fn-store-action :fault state)))
                  (value :fault))))
          (let ((state (f-put-global 'fn-store-action :fault state)))
            (value :fault)))))))

(defun fn-store-record-sequence (octets)
  (declare (xargs :mode :program))
  (let ((decoded (fn-record-decode-exact octets)))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (consp (cdr decoded)) (fn-record-p (car (cdr decoded))))
        (fn-record-sequence (car (cdr decoded)))
      -1)))

(defun fn-store-record-txid (octets)
  (declare (xargs :mode :program))
  (let ((decoded (fn-record-decode-exact octets)))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (consp (cdr decoded)) (fn-record-p (car (cdr decoded))))
        (fn-record-txid (car (cdr decoded)))
      -1)))

(defun fn-store-advance-frontier (frontier state)
  (declare (xargs :stobjs state :mode :program))
  (let ((node (fn-replay-advance-txid
               (f-get-global 'fn-store-node state) frontier)))
    (if (and (fn-node-statep node)
             (equal (fn-state-next-txid (fn-node-acceptance node)) frontier))
        (let* ((state (f-put-global 'fn-store-node node state))
               (state (f-put-global 'fn-store-action :ready state)))
          (value :ready))
      (let ((state (f-put-global 'fn-store-action :fault state)))
        (value :fault)))))

(defun fn-store-article-match (msgid payload groups node)
  (let ((article (fn-find-article msgid
                                  (fn-state-articles (fn-node-acceptance node)))))
    (if article
        (if (and (equal payload (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

(defun fn-store-existing-action (msgid-octets payload group-codes state)
  (declare (xargs :stobjs state :mode :program))
  (let ((groups (fn-store-groups-from-codes group-codes)))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload))
            (equal groups :bad) (null groups))
        (value :absent)
      (let ((action (fn-store-article-match
                     (fn-store-octets->string msgid-octets) payload groups
                     (f-get-global 'fn-store-node state))))
        (value (if action action :absent))))))

(defun fn-store-prepare (msgid-octets payload group-codes id-octets
                          subject-octets evidence-octets charge state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((node (f-get-global 'fn-store-node state))
         (groups (fn-store-groups-from-codes group-codes)))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (> (len payload) *fn-store-max-payload*)
            (equal groups :bad) (null groups)
            (not (fn-store-text-octetsp id-octets))
            (not (fn-store-text-octetsp subject-octets))
            (not (fn-store-text-octetsp evidence-octets))
            (not (posp charge)))
        (let ((state (f-put-global 'fn-store-action :invalid state)))
          (value :invalid))
      (let* ((msgid (fn-store-octets->string msgid-octets))
             (existing (fn-store-article-match msgid payload groups node)))
        (if existing
            (let ((state (f-put-global 'fn-store-action existing state)))
              (value existing))
          (let* ((sequence (f-get-global 'fn-store-next-sequence state))
                 (txid (fn-state-next-txid (fn-node-acceptance node)))
                 ; Generation follows the durable allocator identity, not the
                 ; contiguous journal sequence (which excludes known aborts).
                 (generation txid)
                 (id (fn-store-octets->string id-octets))
                 (subject (fn-store-octets->string subject-octets))
                 (evidence (fn-store-octets->string evidence-octets))
                 (next (fn-node-prepare node generation msgid payload groups id subject
                                        evidence charge)))
            (if (equal next node)
                (let ((state (f-put-global 'fn-store-action :refused state)))
                  (value :refused))
              (let* ((record (fn-record-make sequence txid generation msgid payload groups
                                              id subject evidence charge))
                     (encoded (fn-record-encode record)))
                (if (or (null encoded) (not (fn-record-p record)))
                    (let ((state (f-put-global 'fn-store-action :fault state)))
                      (value :fault))
                  (let* ((state (f-put-global 'fn-store-node next state))
                         (state (f-put-global 'fn-store-pending-record record state))
                         (state (f-put-global 'fn-store-pending-txid txid state))
                         (state (f-put-global 'fn-store-pending-generation generation state))
                         (state (f-put-global 'fn-store-action :prepared state)))
                    (value :prepared)))))))))))

(defun fn-store-complete (status state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((record (f-get-global 'fn-store-pending-record state))
         (before (f-get-global 'fn-store-node state)))
    (if (or (null record)
            (not (or (equal status :durable) (equal status :aborted)
                     (equal status :indeterminate))))
        (let ((state (f-put-global 'fn-store-action :fault state))) (value :fault))
      (let* ((txid (f-get-global 'fn-store-pending-txid state))
             (generation (f-get-global 'fn-store-pending-generation state))
             (node (fn-node-complete before txid generation status)))
        ; Completion is an observation about this exact staged transition, not
        ; an instruction to echo.  A stale/fenced/core-refused event leaves the
        ; pending metadata intact for recovery diagnostics.
        (if (or (not (fn-node-pending-matchesp before txid generation))
                (not (fn-node-statep node))
                (equal node before))
            (let ((state (f-put-global 'fn-store-action :fault state)))
              (value :fault))
          (let* ((state (f-put-global 'fn-store-node node state))
                 (state (if (equal status :durable)
                            (f-put-global 'fn-store-records
                                          (append (f-get-global 'fn-store-records state)
                                                  (list record)) state)
                          state))
                 (state (if (equal status :durable)
                            (f-put-global 'fn-store-next-sequence
                                          (1+ (f-get-global 'fn-store-next-sequence state)) state)
                          state))
                 (state (f-put-global 'fn-store-pending-record nil state))
                 (state (f-put-global 'fn-store-pending-txid nil state))
                 (state (f-put-global 'fn-store-pending-generation nil state))
                 (state (f-put-global 'fn-store-action status state)))
            (value status)))))))

(defun fn-store-pending-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((record (f-get-global 'fn-store-pending-record state)))
    (if record (value (fn-record-encode record)) (value nil))))

(defun fn-store-article-count (state)
  (declare (xargs :stobjs state :mode :program))
  (value (len (fn-state-articles
               (fn-node-acceptance (f-get-global 'fn-store-node state))))))

(defun fn-store-next-txid (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-state-next-txid
          (fn-node-acceptance (f-get-global 'fn-store-node state)))))

(defun fn-store-group-next (code state)
  (declare (xargs :stobjs state :mode :program))
  (let ((group (fn-store-group-code code)))
    (value (if group
               (fn-next-number group
                               (fn-state-nexts
                                (fn-node-acceptance
                                 (f-get-global 'fn-store-node state))))
             0))))

(defun fn-store-pin-count (state)
  (declare (xargs :stobjs state :mode :program))
  (value (len (fn-retain-pins
               (fn-node-retention (f-get-global 'fn-store-node state))))))

(defun fn-store-reserved (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-retain-reserved
          (fn-node-retention (f-get-global 'fn-store-node state)))))

(defun fn-store-lookup (msgid-octets state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-store-msgid-octetsp msgid-octets))
      (value nil)
    (let ((article (fn-find-article
                    (fn-store-octets->string msgid-octets)
                    (fn-state-articles
                     (fn-node-acceptance (f-get-global 'fn-store-node state))))))
      (value (if article (fn-article-payload article) nil)))))

(defun fn-store-lookup-foundp (msgid-octets state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-store-msgid-octetsp msgid-octets))
      (value nil)
    (value (if (fn-find-article
                (fn-store-octets->string msgid-octets)
                (fn-state-articles
                 (fn-node-acceptance (f-get-global 'fn-store-node state))))
               t nil))))
