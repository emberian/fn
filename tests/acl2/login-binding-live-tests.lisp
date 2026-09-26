; Witnesses and teeth for books/login-binding-live.lisp (PKT-221, PRF-166).
;
; The binding table is rows of the configuration.  A positive witness per
; keystone asserts every antecedent literal and the conclusion; a must-fail
; per hypothesis shows the conclusion fails without it.  The gate witness
; uses books/login-binding's constructed owner (*lbt-o*: a submission in
; flight from connection 5, authenticated as `ember') and the signed article
; *pat-relayed* (carrier by *tha-principal*, accepted under *pat-snapshots*);
; the publication witness is config-owner-live-tests' replayed ground owner
; driven through the host's live path (reconfigure, then fn-ocl-publish).
(in-package "ACL2")
(include-book "../../books/login-binding-live")
(include-book "login-binding-tests")
(include-book "config-owner-live-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *lblt-p* *tha-principal*)
(defconst *lblt-q* (make-list 32 :initial-element 9))
(defconst *lblt-name* *lbt-login*)
(defconst *lblt-guest* *lbt-other-login*)

; A value with the posting policy on, `ember' bound to P and `guest' to Q.
(defconst *lblt-v-p*
  (fn-cfg-apply (fn-cfg-empty-value) 1 0
                (list (fn-cfg-set-policy "posting-policy" "bound-logins")
                      (fn-lb-binding-delta *lblt-name* *lblt-p*)
                      (fn-lb-binding-delta *lblt-guest* *lblt-q*))))
(assert-event (equal (fn-lb-value-bindings *lblt-v-p*)
                     (list (cons *lblt-name* *lblt-p*)
                           (cons *lblt-guest* *lblt-q*))))

; --- fn-lb-binding-delta-binds-the-login -------------------------------------
; Witness: re-binding ember to Q over a table that binds it to P.
(assert-event (fn-cbor-octet-listp *lblt-name*))
(assert-event (consp *lblt-name*))
(assert-event (fn-lb-principalp *lblt-q*))
(assert-event (equal (fn-lb-binding *lblt-name*
                                    (fn-lb-value-bindings
                                     (fn-cfg-apply-delta
                                      *lblt-v-p* 2 0
                                      (fn-lb-binding-delta *lblt-name* *lblt-q*))))
                     *lblt-q*))
; ... and the unbind (principal nil).
(assert-event (null (fn-lb-binding *lblt-name*
                                   (fn-lb-value-bindings
                                    (fn-cfg-apply-delta
                                     *lblt-v-p* 2 0
                                     (fn-lb-binding-delta *lblt-name* nil))))))
; Without (consp name): the empty login is never bound.
(must-fail
 (defthm lblt-binds-without-consp
   (implies (and (fn-cbor-octet-listp name) (fn-lb-principalp principal))
            (equal (fn-lb-binding
                    name (fn-lb-value-bindings
                          (fn-cfg-apply-delta v gen stamp
                                              (fn-lb-binding-delta name principal))))
                   principal))
   :hints (("Goal" :in-theory (disable fn-lb-binding-delta fn-lb-value-bindings)))))
(assert-event (null (fn-lb-binding nil (fn-lb-value-bindings
                                        (fn-cfg-apply-delta
                                         *lblt-v-p* 2 0
                                         (fn-lb-binding-delta nil *lblt-q*))))))
; Without octets: a login that is not octets is spelled "" and never found.
(must-fail
 (defthm lblt-binds-without-octets
   (implies (and (consp name) (fn-lb-principalp principal))
            (equal (fn-lb-binding
                    name (fn-lb-value-bindings
                          (fn-cfg-apply-delta v gen stamp
                                              (fn-lb-binding-delta name principal))))
                   principal))
   :hints (("Goal" :in-theory (disable fn-lb-binding-delta fn-lb-value-bindings)))))
(assert-event (null (fn-lb-binding '(300) (fn-lb-value-bindings
                                           (fn-cfg-apply-delta
                                            *lblt-v-p* 2 0
                                            (fn-lb-binding-delta '(300) *lblt-q*))))))
; Without a principal the row can spell: (300) is written as the unbind.
(must-fail
 (defthm lblt-binds-without-principalp
   (implies (and (fn-cbor-octet-listp name) (consp name))
            (equal (fn-lb-binding
                    name (fn-lb-value-bindings
                          (fn-cfg-apply-delta v gen stamp
                                              (fn-lb-binding-delta name principal))))
                   principal))
   :hints (("Goal" :in-theory (disable fn-lb-binding-delta fn-lb-value-bindings)))))
(assert-event (null (fn-lb-binding *lblt-name*
                                   (fn-lb-value-bindings
                                    (fn-cfg-apply-delta
                                     *lblt-v-p* 2 0
                                     (fn-lb-binding-delta *lblt-name* '(300)))))))

; --- fn-lb-binding-delta-keeps-other-logins ----------------------------------
; Witness: re-binding ember leaves guest bound to Q.
(assert-event (not (equal *lblt-guest* *lblt-name*)))
(assert-event (equal (fn-lb-binding *lblt-guest*
                                    (fn-lb-value-bindings
                                     (fn-cfg-apply-delta
                                      *lblt-v-p* 2 0
                                      (fn-lb-binding-delta *lblt-name* nil))))
                     (fn-lb-binding *lblt-guest* (fn-lb-value-bindings *lblt-v-p*))))
(assert-event (equal (fn-lb-binding *lblt-guest* (fn-lb-value-bindings *lblt-v-p*))
                     *lblt-q*))
; Without (not (equal other name)): the login itself moves.
(must-fail
 (defthm lblt-keeps-without-other
   (equal (fn-lb-binding
           other (fn-lb-value-bindings
                  (fn-cfg-apply-delta v gen stamp
                                      (fn-lb-binding-delta name principal))))
          (fn-lb-binding other (fn-lb-value-bindings v)))
   :hints (("Goal" :in-theory (disable fn-lb-binding-delta fn-lb-value-bindings)))))

; --- fn-lb-binding-delta-is-admitted -----------------------------------------
(assert-event (fn-lb-bindable-namep *lblt-name*))
(assert-event (null (fn-cfg-delta-reason *lblt-v-p* 2 nil 0 512
                                         (fn-lb-binding-delta *lblt-name* *lblt-q*))))
; Without a bindable name: a login with a space is not one the slot spells.
(defconst *lblt-spaced* (fn-record-string-octets "two words"))
(assert-event (fn-lb-principalp *lblt-q*))
(assert-event (not (fn-lb-bindable-namep *lblt-spaced*)))
(assert-event (equal (fn-cfg-delta-reason *lblt-v-p* 2 nil 0 512
                                          (fn-lb-binding-delta *lblt-spaced* *lblt-q*))
                     :binding-login))
(must-fail
 (defthm lblt-admitted-without-bindable
   (implies (fn-lb-principalp principal)
            (not (fn-cfg-delta-reason v gen stamp reserved ceiling
                                      (fn-lb-binding-delta name principal))))
   :hints (("Goal" :in-theory (disable fn-lb-binding-delta)))))
; Without a principal of 32 octets: two octets are not a principal's text.
(assert-event (not (fn-lb-principalp '(1 2))))
(assert-event (equal (fn-cfg-delta-reason *lblt-v-p* 2 nil 0 512
                                          (fn-lb-binding-delta *lblt-name* '(1 2)))
                     :binding-principal))
(must-fail
 (defthm lblt-admitted-without-principalp
   (implies (fn-lb-bindable-namep name)
            (not (fn-cfg-delta-reason v gen stamp reserved ceiling
                                      (fn-lb-binding-delta name principal))))
   :hints (("Goal" :in-theory (disable fn-lb-binding-delta)))))

; --- fn-lb-sync-binds-every-login-as-the-file-does ---------------------------
; Witness: the file binds ember to Q and says nothing of guest; the
; configuration binds ember to P and guest to Q.  The plan re-binds ember and
; unbinds guest, and after it the configuration agrees with the file.
(defconst *lblt-file* (list (cons *lblt-name* *lblt-q*)))
(defconst *lblt-pairs* (fn-lb-sync-pairs *lblt-file* (fn-lb-value-bindings *lblt-v-p*)))
(assert-event (equal *lblt-pairs* (list (cons *lblt-name* *lblt-q*)
                                        (cons *lblt-guest* nil))))
(assert-event (fn-lb-pairs-okp *lblt-pairs*))
(defconst *lblt-synced*
  (fn-cfg-apply *lblt-v-p* 2 nil (fn-lb-pairs-deltas *lblt-pairs*)))
(assert-event (equal (fn-lb-binding *lblt-name* (fn-lb-value-bindings *lblt-synced*))
                     (fn-lb-binding *lblt-name* *lblt-file*)))
(assert-event (equal (fn-lb-binding *lblt-guest* (fn-lb-value-bindings *lblt-synced*))
                     (fn-lb-binding *lblt-guest* *lblt-file*)))
(assert-event (null (fn-lb-binding *lblt-guest* (fn-lb-value-bindings *lblt-synced*))))
(assert-event (equal (fn-lb-sync-plan *lblt-file* *lblt-v-p*)
                     (list :ok (list (fn-lb-pairs-deltas *lblt-pairs*)))))
; A configuration that already agrees plans nothing.
(assert-event (equal (fn-lb-sync-plan *lblt-file* *lblt-synced*) (list :ok nil)))
; Without the plan's check: a file principal that is not octets is written as
; the unbind, so the configuration does not bind the login as the file does.
(defconst *lblt-bad-file* (list (cons *lblt-name* '(300))))
(assert-event (not (fn-lb-pairs-okp
                    (fn-lb-sync-pairs *lblt-bad-file* (fn-lb-value-bindings *lblt-v-p*)))))
(assert-event (equal (fn-lb-sync-plan *lblt-bad-file* *lblt-v-p*)
                     (list :refused :binding-login)))
(assert-event (not (equal (fn-lb-binding
                           *lblt-name*
                           (fn-lb-value-bindings
                            (fn-cfg-apply *lblt-v-p* 2 nil
                                          (fn-lb-pairs-deltas
                                           (fn-lb-sync-pairs
                                            *lblt-bad-file*
                                            (fn-lb-value-bindings *lblt-v-p*))))))
                          (fn-lb-binding *lblt-name* *lblt-bad-file*))))
(must-fail
 (defthm lblt-sync-without-okp
   (equal (fn-lb-binding
           name (fn-lb-value-bindings
                 (fn-cfg-apply v gen stamp
                               (fn-lb-pairs-deltas
                                (fn-lb-sync-pairs file (fn-lb-value-bindings v))))))
          (fn-lb-binding name file))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (disable fn-lb-value-bindings fn-lb-sync-pairs
                                fn-lb-pairs-deltas)))))

; --- the pinned view ----------------------------------------------------------
; fn-lb-an-open-session-is-decided-under-its-pinned-table.  Witness (the
; constructed owner of login-binding-tests): connection 5 pinned the table
; binding ember to the carrier's principal P; the live configuration has
; since re-bound ember to Q.  Over a trace that does not re-pin 5 (a
; reconfiguration by connection 6), the gate the host calls passes the
; P-signed article; the gate over the LIVE table would refuse it.
(defconst *lblt-cfg-p* (fn-cfg-make 2 *lblt-v-p*))
(defconst *lblt-cfg-q*
  (fn-cfg-make 3 (fn-cfg-apply-delta *lblt-v-p* 3 0
                                     (fn-lb-binding-delta *lblt-name* *lblt-q*))))
(defconst *lblt-oc* (fn-ocfg-make *lbt-o* *lblt-cfg-q* (list (cons 5 *lblt-cfg-p*)) nil))
(defconst *lblt-events*
  (list (list :reconfigure 6 (list (fn-lb-binding-delta *lblt-guest* nil)))))
(assert-event (fn-ocfg-pin-find 5 (fn-ocfg-pins *lblt-oc*)))
(assert-event (not (fn-ocfg-repins-forp 5 *lblt-events*)))
(defmacro lblt-run () '(fn-ocfg-run *lblt-oc* *lblt-events*))
(assert-event
 (with-guard-checking :none
  (equal (fn-lb-inflight-id (fn-ocfg-owner (lblt-run))) 5)))
(assert-event
 (with-guard-checking :none
  (equal (fn-lb-ocfg-gate (lblt-run) *pat-relayed*)
                     (fn-lb-owner-gate (fn-ocfg-owner (lblt-run))
                                       (fn-ocfg-config (lblt-run))
                                       (fn-lb-conn-bindings *lblt-oc* 5)
                                       *pat-relayed*))))
(assert-event
 (with-guard-checking :none
  (equal (fn-lb-ocfg-gate (lblt-run) *pat-relayed*)
                     (list :pass *lblt-name* *lblt-p*))))
(assert-event
 (with-guard-checking :none
  (equal (fn-lb-owner-gate (fn-ocfg-owner (lblt-run))
                                       (fn-ocfg-config (lblt-run))
                                       (fn-lb-value-bindings *lblt-v-p*)
                                       *pat-relayed*)
                     (list :pass *lblt-name* *lblt-p*))))
(assert-event
 (with-guard-checking :none
  (equal (car (fn-lb-owner-gate (fn-ocfg-owner (lblt-run))
                                            (fn-ocfg-config (lblt-run))
                                            (fn-lb-value-bindings
                                             (fn-cfg-value (fn-ocfg-config (lblt-run))))
                                            *pat-relayed*))
                     :refused)))
; Without the stable pin: an :advance of 5 re-pins it to the live table.
(defconst *lblt-advance* (list (list :advance 5)))
(assert-event (fn-ocfg-repins-forp 5 *lblt-advance*))
(must-fail
 (defthm lblt-pinned-without-no-repin
   (implies (and (fn-ocfg-pin-find id (fn-ocfg-pins oc))
                 (equal (fn-lb-inflight-id (fn-ocfg-owner (fn-ocfg-run oc events))) id))
            (equal (fn-lb-ocfg-gate (fn-ocfg-run oc events) received)
                   (fn-lb-owner-gate (fn-ocfg-owner (fn-ocfg-run oc events))
                                     (fn-ocfg-config (fn-ocfg-run oc events))
                                     (fn-lb-conn-bindings oc id)
                                     received)))
   :hints (("Goal" :in-theory (disable fn-ocfg-run fn-lb-owner-gate)))))
; Without the in-flight connection being ID: the table of another pin.
(must-fail
 (defthm lblt-pinned-without-inflight
   (implies (and (fn-ocfg-pin-find id (fn-ocfg-pins oc))
                 (not (fn-ocfg-repins-forp id events)))
            (equal (fn-lb-ocfg-gate (fn-ocfg-run oc events) received)
                   (fn-lb-owner-gate (fn-ocfg-owner (fn-ocfg-run oc events))
                                     (fn-ocfg-config (fn-ocfg-run oc events))
                                     (fn-lb-conn-bindings oc id)
                                     received)))
   :hints (("Goal" :in-theory (disable fn-ocfg-run fn-lb-owner-gate)))))
; Without a pin for ID before the trace: none to keep.
(must-fail
 (defthm lblt-pinned-without-pin
   (implies (and (not (fn-ocfg-repins-forp id events))
                 (equal (fn-lb-inflight-id (fn-ocfg-owner (fn-ocfg-run oc events))) id))
            (equal (fn-lb-ocfg-gate (fn-ocfg-run oc events) received)
                   (fn-lb-owner-gate (fn-ocfg-owner (fn-ocfg-run oc events))
                                     (fn-ocfg-config (fn-ocfg-run oc events))
                                     (fn-lb-conn-bindings oc id)
                                     received)))
   :hints (("Goal" :in-theory (disable fn-ocfg-run fn-lb-owner-gate)))))

; --- the host's live path: publication, then a new connection -----------------
; The replayed ground owner (config-owner-live-tests), a clock observed;
; connection 0 opens (session A), connection 1 stages the re-binding of ember
; to Q and closes, the record is published durably, connection 2 opens
; (session B).
(defconst *lblt-max* 32768)
(defconst *lblt-0* (fn-ocfg-make (fn-own-start *cpo-t-ready* 4) *ocl-t-cfg* nil nil))
(defconst *lblt-clocked*
  (fn-ocfg-step *lblt-0*
                (list :observe (fn-clock-observation 5000000 1790000000000 0 t))))
(defconst *lblt-a* (cdr (fn-ocfg-open *lblt-clocked* nil)))
(defconst *lblt-admin* (cdr (fn-ocfg-open *lblt-a* nil)))
(defconst *lblt-pairs-q* (list (cons *lblt-name* *lblt-q*)))
(defconst *lblt-file-q* (list (cons *lblt-name* *lblt-q*)))
(defconst *lblt-staged*
  (fn-ocfg-step *lblt-admin*
                (list :reconfigure 1 (fn-lb-pairs-deltas *lblt-pairs-q*))))
(assert-event (fn-ocfg-staged *lblt-staged*))
(defconst *lblt-pub*
  (mv-list 2 (fn-ocl-publish *lblt-staged*
                             (fn-cfg-record-generation (fn-ocfg-staged *lblt-staged*))
                             *lblt-max*)))
(defconst *lblt-published* (cadr *lblt-pub*))
(defconst *lblt-b* (cdr (fn-ocfg-open *lblt-published* nil)))
(defconst *lblt-new* (fn-own-next-id (fn-ocfg-owner *lblt-published*)))
; fn-lb-a-publication-keeps-every-open-connections-table: A's table is the
; one it opened with (no binding), across the publication.
(assert-event (equal (fn-lb-conn-bindings *lblt-published* 0)
                     (fn-lb-conn-bindings *lblt-admin* 0)))
(assert-event (null (fn-lb-binding *lblt-name* (fn-lb-conn-bindings *lblt-published* 0))))
; fn-lb-a-connection-opened-after-a-publication-is-bound-anew: every
; antecedent, then B's table binds ember to Q.
(assert-event (not (fn-ocfg-staged *lblt-admin*)))
(assert-event (equal (car *lblt-pub*) :durable))
(assert-event (fn-ocl-config-historyp *lblt-staged*))
(assert-event (not (fn-ocfg-pin-find *lblt-new* (fn-ocfg-pins *lblt-published*))))
(assert-event (fn-own-find-conn *lblt-new* (fn-own-conns (fn-ocfg-owner *lblt-b*))))
(assert-event (fn-lb-pairs-okp *lblt-pairs-q*))
(assert-event (fn-lb-pairs-targetp *lblt-pairs-q* *lblt-file-q*))
(assert-event (equal (fn-lb-binding *lblt-name* (fn-lb-conn-bindings *lblt-b* *lblt-new*))
                     (fn-lb-binding *lblt-name* *lblt-file-q*)))
(assert-event (equal (fn-lb-binding *lblt-name* (fn-lb-conn-bindings *lblt-b* *lblt-new*))
                     *lblt-q*))
; Without a durable verdict: a write of another generation publishes
; nothing, and the next connection pins the old table.
(defconst *lblt-wrong* (mv-list 2 (fn-ocl-publish *lblt-staged* 99 *lblt-max*)))
(assert-event (equal (car *lblt-wrong*) :refused))
(assert-event (not (fn-ocfg-pin-find (fn-own-next-id (fn-ocfg-owner (cadr *lblt-wrong*)))
                                       (fn-ocfg-pins (cadr *lblt-wrong*)))))
(assert-event (fn-own-find-conn
               (fn-own-next-id (fn-ocfg-owner (cadr *lblt-wrong*)))
               (fn-own-conns (fn-ocfg-owner (cdr (fn-ocfg-open (cadr *lblt-wrong*) nil))))))
(assert-event (null (fn-lb-binding *lblt-name*
                                   (fn-lb-conn-bindings
                                    (cdr (fn-ocfg-open (cadr *lblt-wrong*) nil))
                                    (fn-own-next-id (fn-ocfg-owner (cadr *lblt-wrong*)))))))
(must-fail
 (defthm lblt-anew-without-durable
   (let* ((staged (fn-ocfg-step oc (list :reconfigure other
                                         (fn-lb-pairs-deltas pairs))))
          (result (fn-ocl-publish staged generation max-octets))
          (published (mv-nth 1 result))
          (opened (cdr (fn-ocfg-open published acfg)))
          (new (fn-own-next-id (fn-ocfg-owner published))))
     (implies (and (not (fn-ocfg-staged oc))
                   (fn-ocl-config-historyp staged)
                   (not (fn-ocfg-pin-find new (fn-ocfg-pins published)))
                   (fn-own-find-conn new (fn-own-conns (fn-ocfg-owner opened)))
                   (fn-lb-pairs-okp pairs)
                   (fn-lb-pairs-targetp pairs file))
              (equal (fn-lb-binding name (fn-lb-conn-bindings opened new))
                     (if (and name (fn-lb-has name pairs))
                         (fn-lb-binding name file)
                       (fn-lb-binding name (fn-lb-value-bindings
                                            (fn-cfg-value (fn-ocfg-config oc))))))))
   ; The counter-witness is *lblt-wrong* above (every other antecedent
   ; asserted, the conclusion false); the search is bounded so the book
   ; stays inside D26 (the open theory spent 8.8 s refusing it).
   :hints (("Goal" :do-not-induct t :do-not '(preprocess)
            :in-theory (theory 'minimal-theory)))))
; Without the targets naming the file's bindings: pairs that bind ember to Q
; do not bind it as a file binding ember to P does.
(assert-event (not (fn-lb-pairs-targetp *lblt-pairs-q* (list (cons *lblt-name* *lblt-p*)))))
(assert-event (not (equal (fn-lb-binding *lblt-name* (fn-lb-conn-bindings *lblt-b* *lblt-new*))
                          (fn-lb-binding *lblt-name* (list (cons *lblt-name* *lblt-p*))))))
