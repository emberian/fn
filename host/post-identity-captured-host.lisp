; Actual retained captured-controller caller. PROGRAM assembly only; source,
; cost, inverse, producer and native qualification obligations remain open.
(in-package "ACL2")
(include-book "../books/post-identity-captured-holder")
(include-book "../books/runtime-operation-source")
(include-book "index-incoming-request-host")
(include-book "query-payload-scalar-host")

; Read actual SAME installed source/table. No shaped family or parser state
; can produce an allowance. The genuine captured allowance lowering is absent.
(defun fn-owner-pic-demand (fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
 (mv-let (word family)
  (fn-owner-runtime-operation-source :captured-confirmation fn-page-read-pool state)
  (declare (ignore family))
  (if (not (eq word :ready)) (mv word nil)
   (mv-let (table-word table)
    (fn-owner-runtime-operation-role-table :captured-confirmation fn-page-read-pool state)
    (declare (ignore table))
    (mv (if (eq table-word :ready) :captured-allowance-unavailable table-word) nil)))))

; Startup issuer subject is closed until SAME-pool allowance lowering and
; constructor issuance exist. This readout never reserves or manufactures a token.
(defun fn-owner-pic-runtime-issue (fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
 (fn-owner-pic-demand fn-page-read-pool state))

(defun fn-owner-pic-state (state)
 (declare (xargs :stobjs state :mode :program))
 (if (boundp-global 'fn-owner-pic-continuation state)
     (f-get-global 'fn-owner-pic-continuation state) nil))
(defun fn-owner-pic-keep (token context controller terminal state)
 (declare (xargs :stobjs state :mode :program))
 (f-put-global 'fn-owner-pic-continuation
               (list :pic-retained token context controller terminal) state))

; One scalar/feedback action. Reserve the feedback quantum BEFORE the actual
; selected read. A partial reader never spends an independent fuel allowance.
(defun fn-owner-pic-effect (c fuel fn-mio$c fn-arena fn-octets
                              fn-page-read-pool pgs-digest-state state)
 (declare (xargs :stobjs (fn-mio$c fn-arena fn-octets fn-page-read-pool
                         pgs-digest-state state) :mode :program))
 (mv-let (word next left) (fn-pic-held-next c fuel fn-octets fn-page-read-pool)
  (if (not (eq word :demand)) (mv word next left pgs-digest-state)
   (let ((d (fn-pic-demand c)))
    (cond
     ((< fuel 2) (mv :yield c fuel pgs-digest-state))
     ((eq d :held-length)
      (mv-let (read observation remaining)
       (fn-miq-selected-payload-length (fn-pic-get selected c) (- fuel 1)
                                       fn-mio$c fn-arena state)
       (if (not (eq read :ready)) (mv read c remaining pgs-digest-state)
        (mv-let (word next left)
         (fn-pic-feed-funded c observation (+ 1 remaining))
         (mv word next left pgs-digest-state)))))
     ((eq (fn-pic-at 0 d) :held)
      (mv-let (read observation remaining)
       (fn-miq-selected-payload-byte (fn-pic-get selected c) (fn-pic-at 1 d)
         (- fuel 1) fn-mio$c fn-arena state)
       (if (not (eq read :ready)) (mv read c remaining pgs-digest-state)
        (mv-let (word next left)
         (fn-pic-feed-funded c observation (+ 1 remaining))
         (mv word next left pgs-digest-state)))))
     ((or (eq d :digest-next) (member-eq (fn-pic-at 0 d) '(:digest-begin :digest-step)))
      (fn-pic-digest-next c fuel pgs-digest-state))
     (t (mv :unavailable c fuel pgs-digest-state)))))))

; Public caller derives the actual completed original input and registered
; query internally. No native row/controller/token/source/demand arguments.
; Seven outputs: ERP, word, fuel-left, MIO, pool, digest, STATE.
(defun fn-owner-pic-next (fuel fn-input-copy fn-mio$c fn-arena fn-octets
                             fn-page-read-pool pgs-digest-state state)
 (declare (xargs :stobjs (fn-input-copy fn-mio$c fn-arena fn-octets
                         fn-page-read-pool pgs-digest-state state) :mode :program))
 (mv-let (allowance ignored) (fn-owner-pic-demand fn-page-read-pool state)
  (declare (ignore ignored))
  (cond
   ((not (eq allowance :ready))
    (mv nil allowance fuel fn-mio$c fn-page-read-pool pgs-digest-state state))
   ((zp fuel) (mv nil :yield fuel fn-mio$c fn-page-read-pool pgs-digest-state state))
   ((not (boundp-global 'fn-owner state))
    (mv nil :authority-unavailable fuel fn-mio$c fn-page-read-pool pgs-digest-state state))
   (t
    (mv-let (authority fn-page-read-pool state)
     (fn-owner-incoming-authority-recheck fn-page-read-pool state)
     (if (not (eq authority :authority-current))
         (mv nil authority fuel fn-mio$c fn-page-read-pool pgs-digest-state state)
      (let ((context (fn-owner-incoming-context-read fn-page-read-pool state))
            (job (fn-owner-pic-state state)))
       (mv-let (source-word source)
        (fn-iiq-completed-input-source context fn-input-copy fn-page-read-pool)
        (if (not (eq source-word :source-current))
            (mv nil source-word fuel fn-mio$c fn-page-read-pool pgs-digest-state state)
         (cond
          ((null job)
           (mv-let (erp word token left fn-mio$c fn-page-read-pool state)
            (fn-owner-index-incoming-begin fuel fn-input-copy fn-mio$c fn-arena fn-page-read-pool state)
            (let ((state (if (eq word :captured)
                             (fn-owner-pic-keep token context nil :pending state) state)))
             (mv erp word left fn-mio$c fn-page-read-pool pgs-digest-state state))))
          ((not (and (eq (fn-cp-nth 0 job) :pic-retained)
                     (fn-iaf-holder= (fn-cp-nth 1 context) (fn-cp-nth 1 (fn-cp-nth 2 job)))
                     (equal (fn-cp-nth 1 job)
                            (fn-cp-nth 11 (fn-owner-incoming-freshness-state state)))))
           (mv nil :recapture-required fuel fn-mio$c fn-page-read-pool pgs-digest-state state))
          ((not (eq (fn-cp-nth 4 job) :pending))
           (mv nil :confirmation-required fuel fn-mio$c fn-page-read-pool pgs-digest-state state))
          ((null (fn-cp-nth 3 job))
           (mv-let (word selected left fn-mio$c)
            (fn-miq-select (fn-cp-nth 1 job) fuel fn-mio$c)
            (cond
             ((eq word :absent)
              (let ((state (fn-owner-pic-keep (fn-cp-nth 1 job) context nil :absent state)))
               (mv nil :confirmation-required left fn-mio$c fn-page-read-pool pgs-digest-state state)))
             ((not (eq word :selected))
              (mv nil word left fn-mio$c fn-page-read-pool pgs-digest-state state))
             ((zp left) (mv nil :yield left fn-mio$c fn-page-read-pool pgs-digest-state state))
             (t
              (mv-let (word held grant left)
               (fn-miq-selected-read selected (- left 1) fn-mio$c)
               (if (not (eq word :selected))
                   (mv nil word left fn-mio$c fn-page-read-pool pgs-digest-state state)
                (let* ((c (fn-pic-begin selected grant held (fn-cp-nth 1 context)
                           (fn-cp-nth 3 source) (fn-record-msgid held)
                           (fn-cp-nth 5 context) (fn-cp-nth 6 context)))
                       (state (fn-owner-pic-keep (fn-cp-nth 1 job) context c :pending state)))
                 (mv nil :continue left fn-mio$c fn-page-read-pool pgs-digest-state state))))))))
          (t
           (mv-let (word c left pgs-digest-state)
            (fn-owner-pic-effect (fn-cp-nth 3 job) fuel fn-mio$c fn-arena fn-octets
                                  fn-page-read-pool pgs-digest-state state)
            (let ((state (fn-owner-pic-keep (fn-cp-nth 1 job) context c
                           (if (eq (fn-pic-get phase c) :done) word :pending) state)))
             (mv nil (if (eq (fn-pic-get phase c) :done) :confirmation-required word)
                 left fn-mio$c fn-page-read-pool pgs-digest-state state))))))))))))))

(defun fn-owner-pic-begin (fuel fn-input-copy fn-mio$c fn-arena fn-octets
                              fn-page-read-pool pgs-digest-state state)
 (declare (xargs :stobjs (fn-input-copy fn-mio$c fn-arena fn-octets
                         fn-page-read-pool pgs-digest-state state) :mode :program))
 (fn-owner-pic-next fuel fn-input-copy fn-mio$c fn-arena fn-octets
                     fn-page-read-pool pgs-digest-state state))

; Confirmation replays a readonly actual registered selector/held call, never
; grants authority by inspecting a native parser/controller phase Boolean.
(defun fn-owner-pic-confirm (fuel fn-input-copy fn-mio$c fn-arena fn-octets
                                fn-page-read-pool pgs-digest-state state)
 (declare (xargs :stobjs (fn-input-copy fn-mio$c fn-arena fn-octets
                         fn-page-read-pool pgs-digest-state state) :mode :program))
 (mv-let (allowance ignored) (fn-owner-pic-demand fn-page-read-pool state)
  (declare (ignore ignored))
  (if (not (eq allowance :ready))
      (mv nil allowance fuel fn-mio$c fn-page-read-pool pgs-digest-state state)
   (let* ((job (fn-owner-pic-state state)) (c (fn-cp-nth 3 job))
          (context (fn-owner-incoming-context-read fn-page-read-pool state)))
    (mv-let (authority fn-page-read-pool state)
     (fn-owner-incoming-authority-recheck fn-page-read-pool state)
     (mv-let (source-word source)
      (fn-iiq-completed-input-source context fn-input-copy fn-page-read-pool)
      (declare (ignore source))
      (if (not (and (eq authority :authority-current) (eq source-word :source-current)
                    (eq (fn-cp-nth 0 job) :pic-retained)
                    (fn-iaf-holder= (fn-cp-nth 1 context)
                                    (fn-cp-nth 1 (fn-cp-nth 2 job)))
                    (equal (fn-cp-nth 1 job)
                           (fn-cp-nth 11 (fn-owner-incoming-freshness-state state)))))
          (mv nil :recapture-required fuel fn-mio$c fn-page-read-pool pgs-digest-state state)
       (if (eq (fn-cp-nth 4 job) :absent)
           (mv-let (word selected left fn-mio$c)
            (fn-miq-select (fn-cp-nth 1 job) fuel fn-mio$c)
            (declare (ignore selected))
            (mv nil (if (eq word :absent) :confirmed word) left fn-mio$c
                fn-page-read-pool pgs-digest-state state))
         (mv-let (word held grant left)
          (fn-miq-selected-read (fn-pic-get selected c) fuel fn-mio$c)
          (declare (ignore held grant))
          (if (not (eq word :selected))
              (mv nil word left fn-mio$c fn-page-read-pool pgs-digest-state state)
           (mv-let (word unchanged left)
            (fn-pic-held-next c left fn-octets fn-page-read-pool)
            (declare (ignore unchanged))
            (mv nil (if (equal word (fn-cp-nth 4 job)) :confirmed :confirmation-required)
                left fn-mio$c fn-page-read-pool pgs-digest-state state)))))))))))

)

; Genuine all-alias retirement source/receipt is missing. Query, original
; input, controller, charge and intent remain retained. No fabricated JOINED
; argument, generic FnMIQRelease call or success-by-lexical-return exists.
(defun fn-owner-pic-retire (fuel fn-input-copy fn-mio$c fn-arena fn-octets
                               fn-page-read-pool pgs-digest-state state)
 (declare (xargs :stobjs (fn-input-copy fn-mio$c fn-arena fn-octets
                         fn-page-read-pool pgs-digest-state state) :mode :program))
 (declare (ignore fn-input-copy fn-arena fn-octets))
 (mv nil :retire-unavailable fuel fn-mio$c fn-page-read-pool pgs-digest-state state))
