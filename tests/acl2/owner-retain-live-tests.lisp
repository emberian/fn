; Whole live invariant and each independent conjunct removal.
(in-package "ACL2")
(include-book "../../books/owner-retain-live")
(include-book "../../host/owner-served-carried")
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

; V1e: the writer list is read from the generated row, never duplicated here.
; Identity's keeper is at the host seal cut; the unsealed preparation tooth
; above deliberately has RFCL NIL. The other preparations leave the arena.
(defconst *fn-owner-retain-live-keepers*
  '((fn-owner-prepare-identity . fn-owner-retain-identity-prepare-keeps-live-after-seal)
    (fn-owner-prepare-consumer . fn-owner-retain-consumer-prepare-keeps-live)
    (fn-owner-prepare-topic . fn-owner-retain-topic-prepare-keeps-live)
    (fn-owner-install-extended . fn-owner-retain-live-established-at-recovery)
    (fn-owner-retain-post-quantum . fn-owner-post-quantum-keeps-retain-live)
    (fn-owner-retain-identity-quantum . fn-owner-identity-quantum-keeps-retain-live)
    (fn-owner-cfg-capture . fn-owner-retain-cfg-capture-keeps-live)
    (fn-owner-refuse-reservation . fn-owner-retain-refuse-reservation-keeps-live)
    (fn-owner-known-abort . fn-owner-retain-known-abort-keeps-live)
    (fn-owner-io . fn-owner-retain-io-keeps-live)
    (fn-owner-take . fn-owner-retain-take-keeps-live)
    (fn-owner-control-submit . fn-owner-retain-control-submit-keeps-live)
    (fn-owner-prepare-retention . fn-owner-retain-prepare-retention-keeps-live)
    (fn-owner-install-effects . fn-owner-retain-install-effects-keeps-live)
    (fn-owner-close . fn-owner-retain-close-keeps-live)
    (fn-owner-fault . fn-owner-retain-fault-keeps-live)
    (fn-owner-open-peer . fn-owner-retain-open-peer-keeps-live)
    (fn-owner-install-node-secret . fn-owner-retain-install-node-secret-keeps-live)
    (fn-owner-apply-limit-profile . fn-owner-retain-apply-limit-profile-keeps-live)
    ;; lane memory-run-launch (A28 grant): this lane's five carried writers.
    (fn-owner-memory-physical-return . fn-owner-memory-physical-return-keeps-live)
    (fn-owner-memory-lease-install . fn-owner-memory-lease-install-keeps-live)
    (fn-owner-memory-reclaim-complete . fn-owner-memory-reclaim-complete-keeps-live)
    (fn-owner-peer-rearm . fn-owner-peer-rearm-keeps-live)
    (fn-owner-exposure-rearm . fn-owner-exposure-rearm-keeps-live)))

(defun fn-owner-retain-tree-mentionsp (symbol tree)
  (declare (xargs :guard t))
  (if (consp tree)
      (or (fn-owner-retain-tree-mentionsp symbol (car tree))
          (fn-owner-retain-tree-mentionsp symbol (cdr tree)))
    (equal symbol tree)))

(defun fn-owner-retain-coverage-listp (writers mapping world)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom writers) t
    (let* ((entry (assoc-eq (car writers) mapping))
           (formula (and entry (getpropc (cdr entry) 'theorem nil world))))
      (and entry formula
           (fn-owner-retain-tree-mentionsp (car writers) formula)
           (fn-owner-retain-tree-mentionsp 'fn-owner-retain-livep formula)
           (fn-owner-retain-coverage-listp (cdr writers) mapping world)))))

(defun fn-owner-retain-coveragep (writers mapping world)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((quanta '(fn-owner-retain-post-quantum fn-owner-retain-identity-quantum))
         (keepers (set-difference-eq (strip-cars mapping) quanta)))
   (and (consp writers)
        (no-duplicatesp-eq writers)
        (no-duplicatesp-eq keepers)
        (equal (len writers) (len keepers))
        (subsetp-eq writers keepers)
        (subsetp-eq keepers writers)
        (fn-owner-retain-coverage-listp
         (append writers quanta) mapping world))))

(assert-event
 (let* ((world (w state))
        (row (cdr (assoc-eq 'fn-owner-served-carried
                            (table-alist 'fn-carried world))))
        (writers (append (strip-cars (fn-cd-get :established row))
                         (strip-cars (fn-cd-get :transitions row)))))
   (and row (fn-owner-retain-coveragep writers *fn-owner-retain-live-keepers* world))))


; New ground witnesses use the included RFCL fixture, not fixture twins.
; Memory limits are computed at the gate's exact edge and one octet below it.
(defun fn-owner-retain-new-keystone-evaluate (fn-arena fn-cat state)
  (declare (xargs :stobjs (fn-arena fn-cat state) :guard t :verify-guards nil))
  (let* ((oc (rfcllive-ready-owner fn-arena))
         (s (fn-sbud-oc-store oc))
         (sub (fn-own-sub-make 1 0 0
                (fn-inj-make-decision :injected nil
                  (fn-record-string-octets (fn-record-msgid *rfcllive-wire*))
                  *sit-groups* (fn-record-payload *rfcllive-wire*)) nil))
         (payload (fn-own-sub-stored-octets nil sub nil))
         (record (fn-record-make 1 1 1 (fn-record-msgid *rfcllive-wire*) payload
                   *sit-groups* "retain-finish-obligation" "retain-finish-subject"
                   "retain-finish-release" 2 841000000))
         (row (fn-intern-row-at record (fn-sn-keyring s)
                                (fn-sn-keyring-generation s) (fn-arena-count fn-arena)))
         (profile *fn-heap-small-profile*)
         (img '(0 0 0)) (cfg nil)
         (tot (fn-mm-make-tot 0 0 0 0 0 0 0 0 :resident))
         (after (fn-adm-after tot row))
         (edge (max (fn-mm-sum profile img cfg after)
                    (fn-mm-reopen-need profile img cfg after)))
         (budget (fn-adm-article-budget profile img cfg edge 0 0 record 0 tot row))
         (low-budget (fn-adm-article-budget profile img cfg (1- edge) 0 0 record 0 tot row))
         (carry (fn-prc-refresh nil (fn-node-retention (fn-sn-node s))))
         (out (mv-list 2 (fn-pout-prepare-article oc row budget carry)))
         (low-out (mv-list 2 (fn-pout-prepare-article oc row low-budget carry)))
         (word (mv-nth 0 out)) (low-word (mv-nth 0 low-out))
         (admitted (fn-adm-article-word word profile img cfg edge 0 0 record 0 tot row))
         (refused (fn-adm-article-word low-word profile img cfg (1- edge) 0 0 record 0 tot row))
         (state (fn-owner-install-ocfg oc state))
         (state (fn-owner-retain-carry-put nil state))
         (identity-out (mv-list 2 (fn-pout-prepare-identity oc *sit-composite-wire* (fn-arena-count fn-arena)))))
    (mv-let (erp identity-word state)
      (fn-owner-prepare-identity *sit-composite-wire* fn-arena state)
      (declare (ignore erp))
      (let* ((identity (and (fn-prc-carryp nil)
                            (equal identity-word (list :seal (fn-oii-identity-payload *sit-composite-wire*)))
                            (equal (mv-nth 0 identity-out) :prepared)
                            (equal (fn-owner-ocfg state) (mv-nth 1 identity-out))))
             (fn-arena (fn-arena-seal-list payload fn-arena))
             (completed (fn-sit-publish (fn-sbud-oc-store (mv-nth 1 out))))
             (owner (update-nth 11 sub (fn-ocl-owner-with-store (fn-ocfg-owner oc) completed)))
             (fault-owner (update-nth 11 nil owner))
             (finished (fn-own-finish owner nil fn-arena))
             (fault (fn-own-finish fault-owner nil fn-arena)))
        (mv (list
             (list :r-identity :antecedent-and-conclusion identity)
             (list :admitted word admitted
                   :iff (iff (equal admitted :prepared) (equal word :prepared)))
             (list :memory-refused low-word refused :budget low-budget
                   :iff (iff (equal refused :prepared) (equal low-word :prepared)))
             (list :finish :durable :input-retained (fn-osr-retainedp (fn-own-store owner))
                   :word (car finished) :output-retained (fn-osr-retainedp (fn-own-store (cdr finished))))
             (list :finish :fault :input-retained (fn-osr-retainedp (fn-own-store fault-owner))
                   :word (car fault) :output-retained (fn-osr-retainedp (fn-own-store (cdr fault)))))
            fn-arena fn-cat state)))))

(defun fn-owner-retain-new-keystone-run (state)
  (declare (xargs :stobjs state :guard t :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena state)
      (with-local-stobj fn-cat
        (mv-let (answer fn-arena fn-cat state)
          (fn-owner-retain-new-keystone-evaluate fn-arena fn-cat state)
          (mv answer fn-arena state)))
      (mv answer state))))

(with-guard-checking-event :none
 (make-event
  (mv-let (answer state) (fn-owner-retain-new-keystone-run state)
    (value
     (list 'progn
       (list 'assert-event (list 'equal (list 'quote (nth 0 answer)) ''(:r-identity :antecedent-and-conclusion t)))
       (list 'assert-event (list 'equal (list 'quote (nth 1 answer)) ''(:admitted :prepared :prepared :iff t)))
       (list 'assert-event (list 'equal (list 'quote (nth 2 answer)) ''(:memory-refused :unaffordable :memory :budget 0 :iff t)))
       (list 'assert-event (list 'equal (list 'quote (nth 3 answer)) ''(:finish :durable :input-retained t :word :durable :output-retained t)))
       (list 'assert-event (list 'equal (list 'quote (nth 4 answer)) ''(:finish :fault :input-retained t :word :fault :output-retained t))))))))


; R-POST-1: the existing RFCL fixture with fresh local arena/catalog.
; FN-SCJ-INVP is DEFUN-NX: prove its ground value in ACL2 rather than
; creating an executable twin. The other antecedents and both equalities
; are evaluated on exactly the captured owner and fresh stobjs.
(defun fn-owner-retain-rpost1-witness-in (fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (let* ((oc (rfcllive-ready-owner fn-arena))
         (s (fn-sbud-oc-store oc))
         (row (fn-apc-intern-row-at *rfcllive-wire* (fn-sn-keyring s)
                 (fn-sn-keyring-generation s) (fn-arena-count fn-arena) nil))
         (carry (fn-prc-refresh nil (fn-node-retention (fn-sn-node s)))))
    (mv-let (host-word host-oc)
      (fn-ppc-pout-prepare-article-cat oc row 100 carry fn-arena fn-cat)
      (mv-let (word next)
        (fn-pout-prepare-article oc
          (fn-intern-row-at *rfcllive-wire* (fn-sn-keyring s)
            (fn-sn-keyring-generation s) (fn-arena-count fn-arena)) 100 carry)
        (mv (list oc (fn-ocl-relation oc) (fn-apc-p nil)
                  (equal host-word word) (equal host-oc next)
                  host-word (fn-arena-count fn-arena) (fn-cat-count fn-cat))
            fn-arena fn-cat)))))

(defun fn-owner-retain-rpost1-witness ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (with-local-stobj fn-cat
        (mv-let (answer fn-arena fn-cat)
          (fn-owner-retain-rpost1-witness-in fn-arena fn-cat)
          (mv answer fn-arena)))
      answer)))

(with-guard-checking-event :none
 (make-event
  (let* ((answer (fn-owner-retain-rpost1-witness))
         (claim (list 'fn-scj-invp (list 'fn-ocfg-owner (list 'quote (car answer)))
                      '(create-fn-arena$a) '(create-fn-cat$a))))
    (value
     (list 'progn
       (list 'defthm 'fn-owner-retain-rpost1-fixture-scj claim
         :hints '(("Goal" :in-theory (enable fn-scj-invp fn-scj-joinp
                   fn-scj-rows-invp fn-scj-vvp fn-scj-live-okp fn-scj-conns-pinp
                   fn-scj-marks-below fn-scj-seqs-below fn-scj-arts-map
                   fn-scr-live-catalogp fn-scr-fields-catalogp fn-scr-catalogp))))
       (list 'assert-event
         (list 'and
           (list 'equal (list 'quote (cdr answer)) '(quote (t t t t :prepared 0 0)))
           (list 'equal (list 'getpropc '(quote fn-owner-retain-rpost1-fixture-scj)
                             '(quote theorem) nil '(w state)) (list 'quote claim)))))))))
