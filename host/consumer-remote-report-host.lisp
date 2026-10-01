; Actual serialized high caller: current view/account/config inputs are read
; again before each policy/report tick. No native installer/BODY is minted.
(in-package "ACL2")
(include-book "consumer-remote-reader-host")
(include-book "../books/consumer-remote-report-profile")
(include-book "../books/consumer-remote-collection-state")
(include-book "../books/runtime-operation-source")
(include-book "../books/consumer-remote-response")
(include-book "../books/consumer-remote-collection-client")

(defun fn-owner-remote-reader-report-step-internal
 (request protectedp g token fn-arena fn-history-backing fn-page-read-pool fn-octets state)
 (declare (xargs :stobjs (fn-arena fn-history-backing fn-page-read-pool fn-octets state) :mode :program))
 (mv-let (word inputs state)
  (fn-owner-remote-reader-inputs request protectedp g token fn-history-backing state)
  (let* ((held (fn-owner-remote-scan-read state)) (pending (fn-cp-nth 5 held))
         (tag (fn-cp-nth 0 pending)) (key (fn-cp-nth 1 inputs))
         (generation (fn-cp-nth 4 inputs)))
   (cond
    ((not (eq (fn-cp-nth 0 word) :inputs)) (mv word fn-octets state))
    ((not (and (equal token (fn-cp-nth 1 held)) (eq (fn-cp-nth 2 held) :active)
                (equal key (fn-cp-nth 7 held))))
     (mv '(:refused :consumer-source-changed) fn-octets state))
    ((member-eq tag '(:event-before-query :semantic))
     (let ((start (fn-crcol-policy-begin key generation
                   (fn-cfg-limits (fn-cfg-value (fn-cp-nth 11 inputs))))))
      (mv-let (answer state)
        (fn-owner-remote-collection-keep token
         (list :remote-report-policy (fn-cp-nth 1 start) pending) :report-policy state)
       (mv answer fn-octets state))))
    ((eq tag :remote-report-policy)
     (let ((answer (fn-crcol-policy-tick (fn-cp-nth 1 pending) key generation)))
      (if (not (member-eq (fn-cp-nth 0 answer) '(:yield :ready))) (mv answer fn-octets state)
       (mv-let (status state)
         (fn-owner-remote-collection-keep token
          (if (eq (fn-cp-nth 0 answer) :yield)
              (list tag (fn-cp-nth 1 answer) (fn-cp-nth 2 pending))
            (list :remote-report-policy-ready
              (fn-crcol-policy-finish (fn-cp-nth 1 answer) key generation)
              (fn-cp-nth 2 pending))) :report-policy state)
        (mv status fn-octets state)))))
    (t
     ; Immutable operation-derived representation/extent publication is still
     ; unavailable. Actual getter, not supplied family shape/profile budget.
     (mv-let (status family)
       (fn-owner-runtime-operation-source :remote-frame fn-page-read-pool state)
      (declare (ignore family))
      (if (not (eq status :runtime-operation-available))
          (mv (list :unavailable status) fn-octets state)
       (mv-let (roles-status roles)
         (fn-owner-runtime-operation-role-table :remote-frame fn-page-read-pool state)
        (declare (ignore roles))
        (if (not (eq roles-status :runtime-operation-available))
            (mv (list :unavailable roles-status) fn-octets state)
         (mv '(:unavailable :remote-report-runtime-representation) fn-octets state))))))))))

 ; INTERNAL body after the real native operation/role/extent producer has
; admitted and retained its buffer/source. No public export or issuer exists.
; Limits are taken from the maintained same-generation saved policy, never
; independent caller values. Every tick rereads actual current owner inputs.
(defun fn-owner-remote-reader-report-advance-borrowed
 (request protectedp g token extent fn-arena fn-history-backing fn-octets state)
 (declare (xargs :stobjs (fn-arena fn-history-backing fn-octets state) :mode :program))
 (mv-let (word inputs state)
  (fn-owner-remote-reader-inputs request protectedp g token fn-history-backing state)
  (let* ((held (fn-owner-remote-scan-read state)) (pending (fn-cp-nth 5 held))
         (tag (fn-cp-nth 0 pending)) (key (fn-cp-nth 1 inputs))
         (policy (fn-cp-nth 1 pending))
         (items (case tag
           (:remote-report-policy-ready (fn-cp-nth 1 policy))
           (:collection-preparing (fn-cp-nth 10 policy))
           ((:collection-ready :collection-encoded) (fn-cp-nth 4 pending))
           (:collection-writing (fn-cp-nth 2 pending))))
         (ceiling (case tag
           (:remote-report-policy-ready (fn-cp-nth 2 policy))
           (:collection-preparing (fn-cp-nth 11 policy))
           ((:collection-ready :collection-encoded) (fn-cp-nth 5 pending))
           (:collection-writing (fn-cp-nth 3 pending)))))
   (cond ((not (eq (fn-cp-nth 0 word) :inputs)) (mv word fn-octets state))
         ((not (and (equal key (fn-cp-nth 7 held)) (fn-crcol-profilep items ceiling)))
          (mv '(:refused :remote-report-policy-source-changed) fn-octets state))
         (t
          (mv-let (status state)
           (if (eq tag :remote-report-policy-ready)
               (fn-owner-remote-collection-keep token (fn-cp-nth 2 pending) :preparing state)
             (mv '(:held) state))
           (if (not (eq (fn-cp-nth 0 status) :held)) (mv status fn-octets state)
            (fn-owner-remote-collection-step-internal token key (fn-cp-nth 2 inputs)
             (fn-cp-nth 4 inputs) (fn-cp-nth 6 inputs) (fn-cp-nth 5 inputs)
             g items ceiling extent fn-arena fn-history-backing fn-octets state))))))))

; Supported remote client entry keeps all old singleton/reason/uncertain paths.
; Collection capability is checked before returning any next-cursor proposal.
; Caller must consume every returned report before sending ACK.
(defun fn-remote-consumer-client-read-version (operation bytes version items ceiling state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((shared (fn-cr-response-client-read operation bytes))
        (reply (fn-cp-nth 1 shared)))
  (value (if (and (eq (fn-cp-nth 0 shared) :reply)
                   (member-eq operation '(:poll :wait))
                   (eq (fn-cp-nth 0 reply) :consumer-poll-reply)
                   (eq (fn-cp-nth 1 reply) :accepted)
                   (equal (take 4 (fn-cp-nth 3 reply)) *fn-crcol-magic*))
             (fn-crcol-client-poll operation bytes version items ceiling) shared))))
