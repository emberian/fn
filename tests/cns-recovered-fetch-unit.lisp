; Served-machine APPEND -> discarded core -> fresh-core recovery -> FETCH.
; Simulator persistence model; native process-death cuts are a separate gate.
; Only the persisted device and the client's acceptance coordinates cross
; the death boundary. No live article/directory/phase state is copied.
; Source-only until the shared application world executes these assertions.
(in-package "ACL2")
(include-book "consumer-session-support")

(defconst *fn2-crf-mid* "<recovered-fetch@example.invalid>")
(defconst *fn2-crf-mid-bytes* (fn2-cw-chars (coerce *fn2-crf-mid* 'list)))
(defconst *fn2-crf-headers*
  (fn2-cw-crlf-octets
    '("From: recovery@example.invalid" "Subject: recovered bytes"
      "Newsgroups: local.test" "Message-ID: <recovered-fetch@example.invalid>" "")))
(defconst *fn2-crf-crosspost-headers*
  (fn2-cw-crlf-octets
    '("From: recovery@example.invalid" "Subject: recovered bytes"
      "Newsgroups: local.test,local.empty,local.third"
      "Message-ID: <recovered-fetch@example.invalid>" "")))
(defconst *fn2-crf-crosspost-profile*
  (put-assoc-equal :groups '(("local.test" . 11) ("local.empty" . 22) ("local.third" . 33))
    *fn2-ccu-profile*))
; Exact requested length with short CRLF body lines, so crossing source/storage
; windows does not accidentally test an overlong article line instead.
(defun fn2-crf-body (n)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (<= (nfix n) 82)
      (append (repeat (nfix (- (nfix n) 2)) 120) '(13 10))
    (let ((line (if (equal n 83) 79 80)))
      (append (repeat line 120) '(13 10)
              (fn2-crf-body (- (nfix n) (+ line 2)))))))
(defun fn2-crf-article (n crosspost)
  (declare (xargs :verify-guards nil))
  (let ((headers (if crosspost *fn2-crf-crosspost-headers* *fn2-crf-headers*)))
    (append headers (fn2-crf-body (- (nfix n) (len headers))))))

(defun fn2-crf-seed-frame (op group mid)
  (declare (xargs :verify-guards nil))
  (fnc-append op (fn2-cw-crlf-octets
                   (list "From: recovery@example.invalid" "Subject: seed"
                         (concatenate 'string "Newsgroups: " group)
                         (concatenate 'string "Message-ID: " mid) "" mid))))

(defun fn2-crf-append-event (wire)
  (declare (xargs :verify-guards nil))
  (b* ((result (fnc-parse (cadr (assoc-eq 'append *fn2-fnct-results*))
                            (fnc-k28-result wire)))
       (receipt (and result (fnc-parse *fn2-fnct-append-receipt* (nth 4 (cadr result))))))
    (and receipt (equal (car (cadr receipt)) 1) (nth 4 (cadr receipt)))))

(defun fn2-crf-drop-frames (n wire)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) wire
    (fn2-crf-drop-frames (- n 1) (nthcdr (len (fnc-frame-extent wire)) wire))))

(defun fn2-crf-produce (profile article crosspost)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
           ((mv epoch fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
              (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           (seeds (and crosspost
                       (list (fn2-crf-seed-frame 6 "local.empty" "<seed-empty@example.invalid>")
                             (fn2-crf-seed-frame 7 "local.third" "<seed-third-a@example.invalid>")
                             (fn2-crf-seed-frame 8 "local.third" "<seed-third-b@example.invalid>"))))
           ((mv status wire store fn2-core)
            (fn2-ccu-session 0 (append seeds (list (fnc-append 9 article) (fnc-control 5))) fn2-core))
           (seed-replies (and crosspost (fnc-replies '(append append append) wire)))
           (target-wire (fn2-crf-drop-frames (len seeds) wire))
           (reply (car (fnc-replies '(append) target-wire))))
        (mv (list epoch status reply store (fn2-core-stop-reason fn2-core)
                  seed-replies (fn2-crf-append-event target-wire))
            fn2-core))
      result)))

(defun fn2-crf-read-values (fields fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (endp fields) nil
    (mv-let (code value) (fn2-read-value 0 (car fields) fn2-core)
      (cons (if (eq code :ok) value code)
            (fn2-crf-read-values (cdr fields) fn2-core)))))

(defun fn2-crf-range-walk (fuel fields rows fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv (list :fuel (reverse rows)) fn2-core)
    (b* (((mv code fn2-core) (fn2-read-next 0 256 fn2-core)))
      (case code
        (:more (fn2-crf-range-walk (- fuel 1) fields rows fn2-core))
        (:entry (fn2-crf-range-walk (- fuel 1) fields
                  (cons (fn2-crf-read-values fields fn2-core) rows) fn2-core))
        (:end (mv (reverse rows) fn2-core))
        (otherwise (mv (list code (reverse rows)) fn2-core))))))

; Every schema probed here starts with two scalar key fields.
(defun fn2-crf-read-range (sid lo hi fields fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv start fn2-core)
        (fn2-cs-chain (fn2-read-key 0 :lo 0 (car lo) fn2-core)
                      (fn2-read-key 0 :lo 1 (cadr lo) fn2-core)
                      (fn2-read-key 0 :hi 0 (car hi) fn2-core)
                      (fn2-read-key 0 :hi 1 (cadr hi) fn2-core)
                      (fn2-read-range 0 sid *fn2-range-no-position* 0 fn2-core)))
       ((mv rows fn2-core)
        (if (eq start :ok) (fn2-crf-range-walk 128 fields nil fn2-core)
          (mv (list :start start) fn2-core)))
       ((mv released fn2-core) (fn2-read-release 0 fn2-core)))
    (mv (if (eq released :ok) rows (list :release released rows)) fn2-core)))

(defun fn2-crf-recovered-memberships (position event fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv occurrence fn2-core)
        (fn2-crf-read-range *fn2-addr-sid*
          (list *fnc-fixture-owner-pid* position) (list *fnc-fixture-owner-pid* (+ 1 position))
          (list *fn2-addr-entry-field-position* *fn2-addr-entry-field-article*
                *fn2-addr-entry-field-stream* *fn2-addr-entry-field-reasons*
                *fn2-addr-entry-field-additional-count*) fn2-core))
       ((mv memberships fn2-core)
        (fn2-crf-read-range *fn2-article-stream-sid*
          (list (- event 1) 0) (list (+ event 1) 3)
          (list *fn2-article-stream-entry-field-article* *fn2-article-stream-entry-field-ordinal*
                *fn2-article-stream-entry-field-stream*) fn2-core))
       ((mv overview fn2-core)
        (fn2-crf-read-range *fn2-overview-sid* '(11 0) '(33 4)
          (list *fn2-overview-entry-field-group* *fn2-overview-entry-field-number*
                *fn2-overview-entry-field-article* *fn2-overview-entry-field-position*) fn2-core)))
    (mv (list occurrence memberships overview) fn2-core)))

(defun fn2-crf-recover-fetch (profile store position event crosspost)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
           (rid (fn2-machine-global-id *fn2-recovery-machine-kind* 0 profile))
           ; Same named persistence-fence assumption as consumer-commit/M2.
           ((mv start fn2-core) (fn2-recovery-start rid 2 0 fn2-core))
           ((mv status & store fn2-core)
            (fn2-cw-loop 400000 0 0 nil store fn2-core))
           (done (equal (fn2-machine-phase rid fn2-core) *fn2-recovery-machine-state-done*))
           (class (nth (fn2-machine-rc-class rid fn2-core) *fn2-rec-classes*))
           ((unless (and (eq start :ok) (eq status :quiet) done
                         (eq class :intact) (equal (fn2-core-stop-reason fn2-core) 0)))
            (mv (list :recovery start status done class
                      (fn2-core-stop-reason fn2-core)) fn2-core))
           ((mv memberships fn2-core)
            (if crosspost (fn2-crf-recovered-memberships position event fn2-core)
              (mv nil fn2-core)))
           ((mv fetched wire & fn2-core)
            (fn2-ccu-session-store 0
              (list (fnc-fetch *fn2-crf-mid-bytes* position) (fnc-control 5))
              store fn2-core)))
        (mv (list :fetched fetched (fnc-replies '(fetch) wire)
                  (fn2-core-stop-reason fn2-core) memberships) fn2-core))
      result)))

(defun fn2-crf-run (n crosspost)
  (declare (xargs :verify-guards nil))
  (let* ((profile (if crosspost *fn2-crf-crosspost-profile* *fn2-ccu-profile*))
         (article (fn2-crf-article n crosspost)) (live (fn2-crf-produce profile article crosspost))
         (reply (nth 2 live)) (position (car (nth 2 reply))) (store (nth 3 live))
         (seeds (nth 5 live)) (event (nth 6 live)))
    (if (and (equal (len article) n) (eq (nth 0 live) :ok) (eq (nth 1 live) :quiet)
             (equal (nth 4 live) 0) (consp store)
             (eq (car reply) :accepted) (equal (cadr reply) "")
             (posp position) (equal (cadr (nth 2 reply)) 1)
             (or (not crosspost)
                 (and (equal seeds '((:accepted "" (1 1)) (:accepted "" (2 1)) (:accepted "" (3 1))))
                      (equal position 4) (equal event 4))))
        (fn2-crf-recover-fetch profile store position event crosspost)
      (list :producer (take 3 live) (nth 4 live) seeds event))))

; Exact octets, not an accepted reply alone or a reconstructed shadow model.
(assert-event
 (equal (fn2-crf-run 1024 nil)
        (list :fetched :quiet (list (list :accepted "" (fn2-crf-article 1024 nil))) 0 nil)))
; The 6 KiB source crosses storage units, input/feed quanta and output loans.
; Its recovered occurrence at position 4 owns article event 4, primary group 11,
; and two more groups at adjacent ordinals. There is no ordinal zero, no
; out-of-range ordinal, and no membership at either neighboring article key.
; The same event has distinct NNTP article numbers 1, 2 and 3 in its groups.
(assert-event
 (equal (fn2-crf-run 6144 t)
        (list :fetched :quiet (list (list :accepted "" (fn2-crf-article 6144 t))) 0
              '(((4 4 11 1 2))
                ((4 1 22) (4 2 33))
                ((11 1 4 4) (22 1 1 1) (22 2 4 4) (33 1 2 2) (33 2 3 3) (33 3 4 4))))))
