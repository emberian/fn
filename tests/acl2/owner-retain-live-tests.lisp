; Whole live invariant and each independent conjunct removal.
(in-package "ACL2")
(include-book "../../books/owner-retain-carried")
(include-book "../../books/owner-retain-livep")
(include-book "reclaim-fold-contexts-live-tests")

(defun fn-owner-retain-teeth-triple (state fn-arena)
  (declare (xargs :stobjs (state fn-arena) :guard t :verify-guards nil))
  (list (fn-owner-retain-statep state)
        (fn-osr-retainedp (fn-owner-store state))
        (fn-rfcl-okp (fn-owner-store state) fn-arena)))

(defun fn-owner-retain-teeth-evaluate (fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state)
                  :guard t :verify-guards nil))
  (let ((before (fn-arena-count fn-arena)))
    ; books/owner-retain-carried.lisp:201-203 witness arguments, substituting
    ; actual state and fresh executable local stobjs for logical constructors.
    (mv-let (erp word fn-arena fn-cat fn-hist state)
      (fn-owner-install-extended
       (fn-owner-retain-witness-oc) nil (make-list 32 :initial-element 0)
       fn-arena fn-cat fn-hist state)
      (declare (ignore erp))
      (let* ((positive (list :w+ word (fn-owner-retain-teeth-triple state fn-arena)
                             :arena-count before (fn-arena-count fn-arena)
                             :livep (fn-owner-retain-livep state fn-arena)))
             ; CANDIDATES-2.lisp:65-66 R-old, using the actual state.
             (state (fn-owner-install-ocfg nil state))
             (state (fn-owner-retain-carry-put nil state))
             (old (list :r-old (fn-owner-retain-teeth-triple state fn-arena)))
             (old-trace (list :nil-owner-config-history
                              (fn-sn-config-history (fn-owner-store state))
                              :nil-owner-osr-livep
                              (fn-osr-livep (fn-owner-store state))))
             (oc (rfcllive-ready-owner fn-arena))
             (state (fn-owner-install-ocfg oc state))
             (state (fn-owner-retain-carry-put nil state))
             (control (list :ready (fn-owner-retain-teeth-triple state fn-arena)))
             ; CANDIDATES-2.lisp:28-33 alternative old-only removal.
             (state (fn-owner-install-ocfg
                     (fn-ocfg-make (fn-ocfg-owner oc) (fn-ocfg-config oc)
                                   '(:bad) (fn-ocfg-staged oc)) state))
             (pins (list :r-old-pins (fn-owner-retain-teeth-triple state fn-arena)))
             ; R-retain: real Store field constructor, owner refresh/install.
             (s (fn-sn-with-event-index (fn-sbud-oc-store oc) '(:a21-private)))
             (state (fn-owner-install-ocfg
                     (fn-ocfg-with-owner oc
                       (fn-ocl-owner-with-store (fn-ocfg-owner oc) s)) state))
             (retained (list :r-retain (fn-owner-retain-teeth-triple state fn-arena)))
             (retain-trace (list :osr-livep (fn-osr-livep s)
                                 :resolvedp (fn-skp-resolvedp s)
                                 :verdict-prefixp (fn-osr-verdict-prefixp s)
                                 :frozen-index-prefixp (fn-osr-frozen-index-prefixp s)
                                 :event-index (fn-sn-event-index s)))
             (state (fn-owner-install-ocfg oc state)))
        ; CANDIDATES-2.lisp:68-69: actual identity prepare, no seal.
        (mv-let (erp word state)
          (fn-owner-prepare-identity *sit-composite-wire* fn-arena state)
          (declare (ignore erp))
          (mv (list positive old old-trace control pins retained retain-trace
                    (list :r-rfcl (fn-owner-retain-teeth-triple state fn-arena)
                          :word-head (if (consp word) (car word) word)
                          :phase (fn-sf-phase (fn-sn-files (fn-owner-store state)))
                          :arena-count (fn-arena-count fn-arena)
                          :handles-inp (fn-rows-handles-inp
                                         (fn-rfcl-rows (fn-owner-store state)) fn-arena)))
              fn-arena fn-cat fn-hist state))))))

(defun fn-owner-retain-teeth-run (state)
  (declare (xargs :stobjs state :guard t :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena state)
      (with-local-stobj fn-cat
        (mv-let (answer fn-arena fn-cat state)
          (with-local-stobj fn-hist
            (mv-let (answer fn-arena fn-cat fn-hist state)
              (fn-owner-retain-teeth-evaluate fn-arena fn-cat fn-hist state)
              (mv answer fn-arena fn-cat state)))
          (mv answer fn-arena state)))
      (mv answer state))))

; Evaluate with real local stobjs and actual ACL2 state. Each observed tooth
; is asserted separately; malformed countermodels require guards off here.
(with-guard-checking-event
 :none
 (make-event
  (mv-let (answer state) (fn-owner-retain-teeth-run state)
    (value
     (list 'progn
           (list 'assert-event
                 (list 'equal (list 'quote (nth 0 answer))
                       (list 'quote '(:w+ :recovering (t t t)
                                          :arena-count 0 0 :livep t))))
           (list 'assert-event
                 (list 'equal (list 'quote (nth 4 answer))
                       (list 'quote '(:r-old-pins (nil t t)))))
           (list 'assert-event
                 (list 'equal (list 'quote (nth 5 answer))
                       (list 'quote '(:r-retain (t nil t)))))
           (list 'assert-event
                 (list 'equal (list 'quote (nth 7 answer))
                       (list 'quote '(:r-rfcl (t t nil) :word-head :seal
                                            :phase :record-staged :arena-count 0
                                            :handles-inp nil)))))))))
