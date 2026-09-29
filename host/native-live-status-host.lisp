; ACL2-facing boundary for the operator's status report
; (books/native-live-status.lisp).  Every wrapper here returns one value and
; no `state': the offline report reads the Store the command just replayed,
; the owner's reply reads the Store, configuration and pins the owner
; carries, and neither can update what it reads.  Raw Lisp transports the
; octets and prints them; it renders no field.
(in-package "ACL2")
(include-book "../books/native-health")
; lane scale-reads: the owner's reclaim line reads the catalog's tombstone
; column, one walk (books/native-status-columns.lisp fn-nsc-answer-report).
(include-book "../books/native-status-columns")
; HST-023: the owner's scheduler lines on `health' (books/owner-scheduler.lisp);
; HST-026 (lane time-model): the disk line on `health' and `status'
; (books/owner-time-model.lisp fn-otm-health-lines, fn-otm-disk-lines).
(include-book "../books/owner-time-model")
; PKT-209: `control log' and `control evidence MSGID' (books/control-evidence.lisp).
(include-book "../books/control-evidence")
; lane obligations-paged: `obligations' page by page with a version token
; (books/native-live-pages.lisp).
(include-book "../books/native-live-pages")

(defun fn-native-live-status-host-offline (kind profile obs fn-arena state)
  ; `status', `pins', `obligations' and `peer list' with no owner running:
  ; the Store and configuration this process replayed, no connection.
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (if (fn-cev-report-kindp kind)
      ;; PKT-209: the records decided as recovery decides them.
      (fn-cev-offline-report kind (f-get-global 'fn-store-sn state))
    (fn-nls-offline-report kind profile
                           (f-get-global 'fn-store-sn state)
                           (f-get-global 'fn-store-cfg state)
                           obs fn-arena)))

(defun fn-native-live-status-host-answer (request cached obs min log-sink sched fn-arena fn-cat state)
  ; The running owner's page for one FNLS request, under its mutex
  ; (host/native/control.lisp `fnn-control-live-status-answer'): (REPLY
  ; CACHED').  A request from offset 0 renders the report once into a
  ; buffer (`fn-nls-buffer'); a later page of the same kind is a substring
  ; of the buffer its first page stored (`fn-nls-cached-buffer',
  ; `fn-nls-page-of-buffer-is-reply').  CACHED is carried by the host and
  ; chosen here.  The carried octet sum is read, not extended in place:
  ; `fn-owner-record-octets' stores its extension, this does not.  LOG-SINK is
  ; the owner's service-log sink (books/log-sink.lisp, PKT-508), NIL when no
  ; writer runs; SCHED the owner's scheduler value (books/owner-scheduler.lisp,
  ; HST-023): `health' ends with the sink's line and the scheduler's.
  (declare (xargs :stobjs (fn-arena fn-cat state) :mode :program))
  ;; PKT-209: FNLS frame kind 3 carries a control report kind and its
  ;; argument (fn-cev-any-request-decode reads either frame).
  (let ((decoded (fn-cev-any-request-decode request)))
    (cond
     ((not (equal (car decoded) :live-status))
      (list (fn-nls-reply-encode :refused 0 nil nil) cached))
     ;; lane obligations-paged: a paged kind is never rendered whole; the
     ;; whole-report exchange refuses it by name (fn-nlp-pagedp).
     ((fn-nlp-pagedp (cadr decoded))
      (list (fn-nls-reply-encode :refused 0 nil *fn-nlp-refusal-paged*) cached))
     (t
      (let* ((kind (cadr decoded))
             (offset (caddr decoded))
             (stored (fn-nls-cached-buffer kind offset cached))
             (buffer
              (or stored
                  (fn-nls-buffer
                   ;; :health is books/native-health.lisp's report
                   ;; (fn-nh-live-report), every other kind the status
                   ;; report (fn-nls-live-report).  MIN is the owner's
                   ;; [alerts] headroom_min_percent, ACL2's projection of
                   ;; the run plan the host carried
                   ;; (fn-native-operator-result-health-min-percent).
                   ;; PRF-161: `health' also carries the exposure lines
                   ;; (books/public-exposure.lisp fn-exp-health-lines),
                   ;; after the eight states, so the first line and its exit
                   ;; code are fn-nh-render's unchanged.
                   (if (fn-cev-report-kindp kind)
                       ;; PKT-209 (PRF-185): the records and archive the
                       ;; owner's committed view carries.
                       (fn-cev-live-report kind (fn-owner-ocfg state))
                   (append
                    ;; fn-nsc-answer-report-is-answer-report: under the
                    ;; column relation F this is fn-nh-answer-report.
                    (fn-nsc-answer-report kind
                                         (fn-owner-store-profile state)
                                         ;; PKT-885: at the reader view while
                                         ;; a batch is in flight, so the
                                         ;; counts never include it
                                         ;; (fn-nsc-answer-report-counts-are-
                                         ;; the-reader-view).
                                         (fn-ocfg-at-reader-view
                                          (fn-owner-ocfg state)
                                          (fn-owner-reader-views state))
                                         (if (boundp-global 'fn-owner-record-octets state)
                                             (f-get-global 'fn-owner-record-octets state)
                                           nil)
                                         ;; PKT-492: the owner's deferred
                                         ;; publication is the observation's
                                         ;; sixth element (books/native-live-
                                         ;; status.lisp fn-nls-obs-checkpoint-
                                         ;; deferred); the host's OBS is the
                                         ;; five-element list of
                                         ;; host/native/io.lisp
                                         ;; fnn-store-observation.
                                         (append (take 5 obs)
                                                 (list (fn-owner-sco-deferred state)))
                                         min
                                         ;; PRF-358 (PKT-879): the ninth
                                         ;; state, the disk, from the same
                                         ;; scheduler value the disk lines
                                         ;; below are rendered from.
                                         (fn-otm-health-disk sched)
                                         fn-arena fn-cat)
                    (cond ((equal kind :health)
                           ;; PKT-508 (PRF-187): the log sink's line last;
                           ;; fn-nh-report-exit-of-render-and-more: the exit is
                           ;; the verdict's whatever follows the eight states.
                           (append (fn-owner-exposure-health state)
                                   (if log-sink (fn-nh-log-sink-line log-sink) nil)
                                   ;; HST-026: SCHED is the snapshot
                                   ;; (S NOW) of books/owner-time-model.lisp:
                                   ;; the scheduler's lines, then the disk's.
                                   (fn-otm-health-lines sched)
                                   ;; THE SWITCH (PRF-1037): the keyed
                                   ;; Message-ID index's line, from
                                   ;; fn-cat-index-health under the ring's
                                   ;; key (books/post-admission-keyed.lisp
                                   ;; fn-pak-index-health-line).
                                   (fn-pak-index-health-line
                                    (fn-cat-index-health (fn-owner-mpx-key state)
                                                         fn-cat))))
                          ;; PRF-211: `status' ends with the capacity line
                          ;; (books/public-exposure.lisp fn-exp-capacity-line);
                          ;; HST-026: then the disk line.
                          ((equal kind :status)
                           (append (fn-owner-exposure-capacity state)
                                   (fn-otm-disk-lines sched)))
                          (t nil))))))))
        (list (fn-nls-page buffer offset)
              (if stored cached (fn-nls-cache-put kind buffer cached))))))))

; lane obligations-paged (books/native-live-pages.lisp).  The running owner's
; page of a paged report, under its mutex (host/native/control.lisp
; `fnn-control-live-pages-answer'): (REPLY CACHE').  CACHE is the owner's
; report cursors, carried by the host and chosen here; the retention is read
; only by a request that starts a report (fn-nlp-answer).  Answering changes
; no state: the wrapper returns no `state'.
(defun fn-native-live-pages-host-answer (request cache state)
  (declare (xargs :stobjs state :mode :program))
  (fn-nlp-answer request cache (fn-nlp-live-retention (fn-owner-ocfg state))
                 *fn-nls-chunk-octets*))

(defun fn-native-live-pages-host-requestp (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (equal (car (fn-nlp-request-decode octets)) :page))

(defun fn-native-live-pages-host-pagedp (kind)
  (declare (xargs :mode :program))
  (fn-nlp-pagedp kind))

(defun fn-native-live-pages-host-request-encode (kind version page)
  (declare (xargs :mode :program))
  (fn-nlp-request-encode kind version page))

(defun fn-native-live-pages-host-client-step (version page reply)
  ; (:done CHUNK) (:next CHUNK VERSION' PAGE') (:restart) (:refused)
  ; (:transport): KEYSTONE fn-nlp-pages-join-to-the-report.
  (declare (xargs :mode :program))
  (fn-nlp-client-step version page reply))

(defun fn-native-live-pages-host-offline-start (state)
  ; The replayed Store's report cursor (fn-nlp-offline-start).
  (declare (xargs :stobjs state :mode :program))
  (fn-nlp-offline-start (fn-nls-retention (f-get-global 'fn-store-sn state))))

(defun fn-native-live-pages-host-offline-step (cursor)
  ; (CHUNK CURSOR' DONEP): KEYSTONE fn-nlp-offline-pages-join-to-the-report.
  (declare (xargs :mode :program))
  (fn-nlp-offline-step cursor *fn-nls-chunk-octets*))

(defun fn-native-live-status-host-requestp (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (equal (car (fn-cev-any-request-decode octets)) :live-status))

(defun fn-native-live-status-host-request-encode (kind offset)
  (declare (xargs :mode :program))
  (fn-cev-any-request-encode kind offset))

(defun fn-native-live-status-host-client-step-chunks (chunks n total digest reply)
  ; lane scale-reads: the client's step over the pages so far, newest first,
  ; and their joined length N (books/native-status-columns.lisp
  ; fn-nsc-client-step, KEYSTONE fn-nsc-client-step-is-client-step): the join
  ; is linear in the report, not quadratic.
  (declare (xargs :mode :program))
  (fn-nsc-client-step chunks n total digest reply))

(defun fn-native-live-status-host-route (socket-present outcome)
  (declare (xargs :mode :program))
  (fn-nls-route socket-present outcome))

; Row S3d: the exit the client reads back from the `store inspect --group'
; report it printed (books/owner-inspect-group.lisp fn-oig-report-exit): 0 for
; the members and their lines, 1 for the refusal by name.
(defun fn-native-live-status-host-inspect-group-exit (octets)
  (declare (xargs :mode :program))
  (fn-oig-report-exit octets))

(defun fn-native-live-status-host-max-frame ()
  (declare (xargs :mode :program))
  *fn-nls-max-frame*)

(defun fn-native-live-status-host-max-restarts ()
  (declare (xargs :mode :program))
  *fn-nls-max-restarts*)

;; PRF-112: the health verdict (books/native-health.lisp).
(defun fn-native-health-host-offline (profile min state)
  ; `health' with no owner running: the Store this process replayed; the
  ; feed table lives only in a running owner and is reported unobserved.
  (declare (xargs :stobjs state :mode :program))
  (fn-nh-offline-report profile (f-get-global 'fn-store-sn state)
                        (f-get-global 'fn-store-cfg state) min))

(defun fn-native-health-host-step (socket-present outcome lock clone-fence-present
                                                  listener-expected)
  ; One `health' invocation's decision over the host's observations
  ; (fn-nh-health-step, PKT-454): (:answered OCTETS) the owner's report,
  ; (:refused), (:fenced OCTETS) the fenced report, or (:offline) and the
  ; host opens the Store.
  (declare (xargs :mode :program))
  (let ((step (fn-nh-health-step socket-present outcome lock clone-fence-present
                                 listener-expected)))
    (if (equal (car step) :fenced)
        (list :fenced (fn-nh-fenced-report (cadr step)))
      step)))

;; friend-path-2: the node that is not running (books/native-health.lisp).
;; (:not-running) from the step above: the host opens the Store read-only and
;; prints this report, with the last run line of the service log.
(defun fn-native-health-host-not-running (profile min last state)
  (declare (xargs :stobjs state :mode :program))
  (fn-nh-not-running-report profile (f-get-global 'fn-store-sn state)
                            (f-get-global 'fn-store-cfg state) min last))

(defun fn-native-health-host-not-running-lines (last)
  (declare (xargs :mode :program))
  (fn-nh-not-running-lines last))

(defun fn-native-health-host-log-tail-octets ()
  (declare (xargs :mode :program))
  (fn-nh-log-tail-octets))

(defun fn-native-health-host-last-run (tail)
  (declare (xargs :mode :program))
  (fn-nh-last-run tail))

(defun fn-native-health-host-run-started-line ()
  (declare (xargs :mode :program))
  (fn-nh-run-started-line))

(defun fn-native-health-host-run-opened-line (ms)
  (declare (xargs :mode :program))
  (fn-nh-run-opened-line ms))

(defun fn-native-health-host-run-stopped-line (code reason)
  (declare (xargs :mode :program))
  (fn-nh-run-stopped-line code reason))

(defun fn-native-health-host-exit (octets)
  (declare (xargs :mode :program))
  (fn-nh-report-exit octets))
