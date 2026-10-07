; fn: teeth for books/article-kind.lisp and books/article-kind-acceptance.lisp.
;
; fn-ak-layout-is-injected and fn-ak-layout-is-a-hybrid-injection: a ground positive witness on which every
; hypothesis and the conclusion hold, and for each hypothesis a witness on
; which every other hypothesis holds, that one fails, and the conclusion
; fails (the decision is not the injection).  fn-ak-layout-parses gets the
; same.  The kind's refinements (the From mailbox-list, the newsgroup-list,
; the msg-id) are shown to be needed: the same octets spelled out without
; the refinement are refused by fn-inj-decide by name.

(in-package "ACL2")
(include-book "../../books/article-kind-acceptance")
(include-book "../../books/article-kind-hybrid")
(include-book "../../books/codec-attach")
(include-book "../../books/defkeystone")

(defconst *akt-from* (fn-ak-text "Mini <mini@example.invalid>"))
(defconst *akt-date* (fn-ak-text "Sun, 04 Oct 2026 12:00:00 +0000"))
(defconst *akt-groups* (fn-ak-text "mini.blocks"))
(defconst *akt-subject* (fn-ak-text "block 1"))
(defconst *akt-msgid* (fn-ak-text "<b1.mini@example.invalid>"))
(defconst *akt-media* (fn-ak-text "application/vnd.dregg.fn-native-prefix; version=1"))
(defconst *akt-payload* (fn-ak-iota 115))
(defconst *akt-agent* (fn-ak-text "node.example"))

(defun akt-config (allow agent groups octets limits)
  (declare (xargs :guard t))
  (fn-inj-make-config-full allow agent groups
                           (fn-inj-post-bound octets limits) nil nil))

(defconst *akt-limits* '(64 256 16384))
(defconst *akt-config*
  (akt-config t *akt-agent* (list *akt-groups*) 100000 *akt-limits*))
(defconst *akt-observation* (fn-clock-observation 1 1790000000000 0 t))

; The hypotheses of fn-ak-layout-is-injected, in its order, and its
; conclusion, at one point.
(defun akt-hyps (from date groups subject msgid media payload config obs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((vals (fn-ak-values from date groups subject msgid media))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config)
                                               nil nil)
                                source)))
    (list (fn-ak-valuesp from date groups subject msgid media)
          (fn-cbor-octet-listp payload)
          (fn-inj-configp config)
          (fn-inj-config-allow config)
          (fn-clock-observationp obs)
          (fn-clock-has-wall obs)
          (and (fn-clock-wall obs) (acl2-numberp (fn-clock-wall obs))
               (< (floor (fn-clock-wall obs) *fn-inj-ms-per-day*) *fn-inj-cycle-days*))
          (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config)))
          (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config)))
          (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
              (fn-article-limit-octets (fn-inj-config-header-limits config)))
          (fn-inj-groups-admissiblep names (fn-inj-config-groups config))
          (<= (len octets) (fn-inj-config-max-octets config)))))

(defun akt-conclusion (from date groups subject msgid media payload config obs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((vals (fn-ak-values from date groups subject msgid media))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config)
                                               nil nil)
                                source)))
    (equal (fn-inj-decide source config obs)
           (fn-inj-make-decision :injected nil msgid names octets))))

; All true but hypothesis K (0-based), and that one false.
(defun akt-all-but (k hyps)
  (declare (xargs :guard t :measure (len hyps)))
  (if (consp hyps)
      (and (if (equal k 0) (not (car hyps)) (car hyps))
           (akt-all-but (if (and (natp k) (< 0 k)) (1- k) nil) (cdr hyps)))
    t))

(defun akt-all (hyps)
  (declare (xargs :guard t))
  (if (consp hyps) (and (car hyps) (akt-all (cdr hyps))) t))

(defmacro akt-tooth (k &key (from '*akt-from*) (date '*akt-date*) (groups '*akt-groups*)
                        (subject '*akt-subject*) (msgid '*akt-msgid*) (media '*akt-media*)
                        (payload '*akt-payload*) (config '*akt-config*)
                        (obs '*akt-observation*))
  `(assert-event
    (and (akt-all-but ,k (akt-hyps ,from ,date ,groups ,subject ,msgid ,media
                                   ,payload ,config ,obs))
         (not (akt-conclusion ,from ,date ,groups ,subject ,msgid ,media
                              ,payload ,config ,obs)))))

; POSITIVE: every hypothesis and the conclusion, ground.
(assert-event
 (and (akt-all (akt-hyps *akt-from* *akt-date* *akt-groups* *akt-subject* *akt-msgid*
                         *akt-media* *akt-payload* *akt-config* *akt-observation*))
      (akt-conclusion *akt-from* *akt-date* *akt-groups* *akt-subject* *akt-msgid*
                      *akt-media* *akt-payload* *akt-config* *akt-observation*)))
; ... and the empty payload (no body lines).
(assert-event
 (and (akt-all (akt-hyps *akt-from* *akt-date* *akt-groups* *akt-subject* *akt-msgid*
                         *akt-media* nil *akt-config* *akt-observation*))
      (akt-conclusion *akt-from* *akt-date* *akt-groups* *akt-subject* *akt-msgid*
                      *akt-media* nil *akt-config* *akt-observation*)))

; HYPOTHESIS REMOVAL, one per hypothesis.
(akt-tooth 0 :from (fn-ak-text "yue"))                         ; not a mailbox-list
(akt-tooth 1 :payload '(1 2 256))                              ; not octets
(akt-tooth 2 :config (akt-config t (fn-ak-text "no de") (list *akt-groups*)
                                 100000 *akt-limits*))         ; agent not a dot-atom
(akt-tooth 3 :config (akt-config nil *akt-agent* (list *akt-groups*)
                                 100000 *akt-limits*))         ; posting not allowed
(akt-tooth 4 :obs (list :fn-clock-observation 1 1790000000000 -1 t)) ; negative wall error
(akt-tooth 5 :obs (fn-clock-observation 1 1790000000000 0 nil)); no wall clock
(akt-tooth 6 :obs (fn-clock-observation 1 (* 146097 86400000) 0 t)) ; past the cycle
(akt-tooth 7 :config (akt-config t *akt-agent* (list *akt-groups*) 100000
                                 '(7 256 16384)))              ; 7 fields
(akt-tooth 8 :config (akt-config t *akt-agent* (list *akt-groups*) 100000
                                 '(64 7 16384)))               ; 7 lines
(akt-tooth 9 :config (akt-config t *akt-agent* (list *akt-groups*) 100000
                                 '(64 256 200)))               ; 200 header octets
(akt-tooth 10 :config (akt-config t *akt-agent* (list (fn-ak-text "other.group"))
                                  100000 *akt-limits*))        ; group not served
(akt-tooth 11 :config (akt-config t *akt-agent* (list *akt-groups*)
                                  470 *akt-limits*))           ; article bound: 439-octet source, about 500 injected

; WHY THE KIND REFINES THE GRAMMAR: the same octets spelled out with a value
; the grammar's :header class admits but the kind refuses are refused by the
; injection decision, by name.
(defun akt-raw (from groups msgid)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-ak-render-rows *fn-ak-v1-rows*
                             (fn-ak-values from *akt-date* groups *akt-subject*
                                           msgid *akt-media*))
          '(13 10)
          (fn-ak-frame (fn-ot-b64-encode *akt-payload*))))

(assert-event
 (equal (fn-inj-decision-reason
         (fn-inj-decide (akt-raw (fn-ak-text "yue") *akt-groups* *akt-msgid*)
                        *akt-config* *akt-observation*))
        :from-invalid))
(assert-event
 (equal (fn-inj-decision-reason
         (fn-inj-decide (akt-raw *akt-from* (fn-ak-text "mini..blocks") *akt-msgid*)
                        *akt-config* *akt-observation*))
        :newsgroups-invalid))
(assert-event
 (equal (fn-inj-decision-reason
         (fn-inj-decide (akt-raw *akt-from* *akt-groups* (fn-ak-text "b1.mini"))
                        *akt-config* *akt-observation*))
        :message-id-invalid))
; ... and each is outside the kind.
(assert-event
 (and (not (fn-ak-valuesp (fn-ak-text "yue") *akt-date* *akt-groups* *akt-subject*
                          *akt-msgid* *akt-media*))
      (not (fn-ak-valuesp *akt-from* *akt-date* (fn-ak-text "mini..blocks")
                          *akt-subject* *akt-msgid* *akt-media*))
      (not (fn-ak-valuesp *akt-from* *akt-date* *akt-groups* *akt-subject*
                          (fn-ak-text "b1.mini") *akt-media*))))

; The version word: "opaque 2" is not a value of the kind (its row is exact).
(assert-event
 (not (fn-ak-rows-valuesp *fn-ak-v1-rows*
                          (list *akt-from* *akt-date* *akt-groups* *akt-subject*
                                *akt-msgid* (fn-ak-text "opaque 2") *akt-media*
                                (fn-ak-text "base64")))))

; fn-ak-layout-parses: positive (the eight fields, the body after the blank
; line) and its hypotheses.
(assert-event
 (let* ((vals (fn-ak-example-values))
        (parsed (fn-article-parse (fn-ak-layout vals *akt-payload*))))
   (and (equal (car parsed) :ok)
        (equal (len (fn-article-fields (cadr parsed))) 8)
        (equal (fn-article-body (cadr parsed))
               (fn-ak-frame (fn-ot-b64-encode *akt-payload*))))))
; A header value opening with SP is grammar-legal (the :header class) but
; outside the kind: the kind's values open with a VCHAR.
(assert-event
 (not (fn-ak-valuesp *akt-from* *akt-date* *akt-groups* (fn-ak-text " lead")
                     *akt-msgid* *akt-media*)))

; The exported vectors' values are values of the kind.
(assert-event
 (and (fn-ak-rows-valuesp *fn-ak-v1-rows* (fn-ak-example-values))
      (equal (len (fn-ak-example-payloads)) 4)))

; -----------------------------------------------------------------------------
; fn-ak-layout-is-a-hybrid-injection: the hybrid-author route.

(defconst *akt-keys* (list (cons :ed25519 (make-list 32 :initial-element 17))
                           (cons :ml-dsa-65 (make-list 1952 :initial-element 34))))
(defconst *akt-sigs* (list (cons :ed25519 (make-list 64 :initial-element 51))
                           (cons :ml-dsa-65 (make-list 3309 :initial-element 68))))
(defconst *akt-principal* (make-list 32 :initial-element 85))

(defun akt-hyb-hyps (from payload principal keys sigs config obs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((vals (fn-ak-values from *akt-date* *akt-groups* *akt-subject* *akt-msgid* *akt-media*))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source) principal keys sigs))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse *akt-groups*)))
         (octets (fn-inj-append (fn-inj-prefix nil *akt-msgid* (fn-inj-config-agent config)
                                               nil nil)
                                carrier)))
    (list (fn-ak-valuesp from *akt-date* *akt-groups* *akt-subject* *akt-msgid* *akt-media*)
          (fn-cbor-octet-listp payload)
          (and field t)
          (fn-inj-configp config)
          (fn-inj-config-allow config)
          (fn-clock-observationp obs)
          (fn-clock-has-wall obs)
          (and (fn-clock-wall obs) (acl2-numberp (fn-clock-wall obs))
               (< (floor (fn-clock-wall obs) *fn-inj-ms-per-day*) *fn-inj-cycle-days*))
          (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config)))
          (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
              (fn-article-limit-lines (fn-inj-config-header-limits config)))
          (<= (+ (len (fn-hc-field-lines field))
                 (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
              (fn-article-limit-octets (fn-inj-config-header-limits config)))
          (fn-inj-groups-admissiblep names (fn-inj-config-groups config))
          (<= (len octets) (fn-inj-config-max-octets config)))))

(defun akt-hyb-conclusion (from payload principal keys sigs config obs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((vals (fn-ak-values from *akt-date* *akt-groups* *akt-subject* *akt-msgid* *akt-media*))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source) principal keys sigs))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse *akt-groups*)))
         (octets (fn-inj-append (fn-inj-prefix nil *akt-msgid* (fn-inj-config-agent config)
                                               nil nil)
                                carrier)))
    (equal (fn-hsig-injected-carrier-plan source principal keys sigs config obs)
           (fn-inj-make-decision :injected nil *akt-msgid* names octets))))

(defmacro akt-hyb-tooth (k &key (from '*akt-from*) (payload '*akt-payload*)
                            (principal '*akt-principal*) (keys '*akt-keys*)
                            (sigs '*akt-sigs*) (config '*akt-config*)
                            (obs '*akt-observation*))
  `(assert-event
    (and (akt-all-but ,k (akt-hyb-hyps ,from ,payload ,principal ,keys ,sigs ,config ,obs))
         (not (akt-hyb-conclusion ,from ,payload ,principal ,keys ,sigs ,config ,obs)))))

; POSITIVE, ground: the carrier of 7208 field octets in 101 lines.
(assert-event
 (and (akt-all (akt-hyb-hyps *akt-from* *akt-payload* *akt-principal* *akt-keys*
                             *akt-sigs* *akt-config* *akt-observation*))
      (akt-hyb-conclusion *akt-from* *akt-payload* *akt-principal* *akt-keys*
                          *akt-sigs* *akt-config* *akt-observation*)))

; HYPOTHESIS REMOVAL, one per hypothesis.
(akt-hyb-tooth 0 :from (fn-ak-text "yue"))
(akt-hyb-tooth 1 :payload '(1 2 256))
(akt-hyb-tooth 2 :principal (make-list 31 :initial-element 85))   ; no carrier field
(akt-hyb-tooth 3 :config (akt-config t (fn-ak-text "no de") (list *akt-groups*)
                                     100000 *akt-limits*))
(akt-hyb-tooth 4 :config (akt-config nil *akt-agent* (list *akt-groups*)
                                     100000 *akt-limits*))
(akt-hyb-tooth 5 :obs (list :fn-clock-observation 1 1790000000000 -1 t))
(akt-hyb-tooth 6 :obs (fn-clock-observation 1 1790000000000 0 nil))
(akt-hyb-tooth 7 :obs (fn-clock-observation 1 (* 146097 86400000) 0 t))
(akt-hyb-tooth 8 :config (akt-config t *akt-agent* (list *akt-groups*) 100000
                                     '(8 256 16384)))                ; the carrier is a ninth field
(akt-hyb-tooth 9 :config (akt-config t *akt-agent* (list *akt-groups*) 100000
                                     '(64 100 16384)))               ; 101 carrier lines + 8 rows
(akt-hyb-tooth 10 :config (akt-config t *akt-agent* (list *akt-groups*) 100000
                                      '(64 256 7000)))               ; header octets
(akt-hyb-tooth 11 :config (akt-config t *akt-agent* (list (fn-ak-text "other.group"))
                                      100000 *akt-limits*))
(akt-hyb-tooth 12 :config (akt-config t *akt-agent* (list *akt-groups*)
                                      7000 *akt-limits*))             ; article bound

; -----------------------------------------------------------------------------
; The PRF-1320/1321/1322/1323 keystones with their teeth (TEETH CONTRACT v1),
; over the fixtures above.  fn-ak-layout-is-injected and
; fn-ak-layout-is-a-hybrid-injection state their antecedents inside a `let*',
; so each antecedent's removal is a mutation (the claim drops it; every
; other one holds, it fails, the conclusion fails), and the same removals the
; hand witnesses above make.  The size antecedents of the parse keystones
; (a layout of at most *fn-article-max-octets* = 4261412864 octets) have no
; counterexample a book can build, so each is grouped with the neighbour whose
; removal is shown (payload / field) and the group's witness breaks the
; neighbour.
(defconst *akt-vals* (fn-ak-example-values))
(make-event
 `(defconst *akt-field*
    ',(fn-hc-field-encode-at (fn-hsig-source-version (fn-ak-layout *akt-vals* *akt-payload*))
                             *akt-principal* *akt-keys* *akt-sigs*)))

(defteeth fn-ak-layout-is-injected
  :claim (() (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
  :subject fn-inj-decide
  :witness ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation *akt-observation*))
  :mutations ((without-values
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from (fn-ak-text "yue")) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation *akt-observation*))
               :fault "the antecedent dropped: (fn-ak-valuesp from date groups subject msgid media-type)")
              (without-octets
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload '(1 2 256)) (config *akt-config*) (observation *akt-observation*))
               :fault "the antecedent dropped: (fn-cbor-octet-listp payload)")
              (without-config
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t (fn-ak-text "no de") (list *akt-groups*) 100000 *akt-limits*)) (observation *akt-observation*))
               :fault "the antecedent dropped: (fn-inj-configp config)")
              (without-allow
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config nil *akt-agent* (list *akt-groups*) 100000 *akt-limits*)) (observation *akt-observation*))
               :fault "the antecedent dropped: (fn-inj-config-allow config)")
              (without-obs
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation (list :fn-clock-observation 1 1790000000000 -1 t)))
               :fault "the antecedent dropped: (fn-clock-observationp observation)")
              (without-wall
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation (fn-clock-observation 1 1790000000000 0 nil)))
               :fault "no wall clock: the cycle test reads a nil wall, outside its guard")
              (without-cycle
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation (fn-clock-observation 1 (* 146097 86400000) 0 t)))
               :fault "the antecedent dropped: (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cy")
              (without-fields
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list *akt-groups*) 100000 '(7 256 16384))) (observation *akt-observation*))
               :fault "the antecedent dropped: (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config)))")
              (without-lines
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list *akt-groups*) 100000 '(64 7 16384))) (observation *akt-observation*))
               :fault "the antecedent dropped: (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config)))")
              (without-header-octets
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list *akt-groups*) 100000 '(64 256 200))) (observation *akt-observation*))
               :fault "the antecedent dropped: (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit")
              (without-groups
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list (fn-ak-text "other.group")) 100000 *akt-limits*)) (observation *akt-observation*))
               :fault "the antecedent dropped: (fn-inj-groups-admissiblep names (fn-inj-config-groups config))")
              (without-article-bound
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config))) (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list *akt-groups*) 470 *akt-limits*)) (observation *akt-observation*))
               :fault "the antecedent dropped: (<= (len octets) (fn-inj-config-max-octets config))")))
(defteeth fn-ak-layout-is-a-hybrid-injection
  :claim (() (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
  :subject fn-hsig-injected-carrier-plan
  :witness ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
  :mutations ((without-values
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from (fn-ak-text "yue")) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (fn-ak-valuesp from date groups subject msgid media-type)")
              (without-octets
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload '(1 2 256)) (config *akt-config*) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (fn-cbor-octet-listp payload)")
              (without-field
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation *akt-observation*) (principal (make-list 31 :initial-element 85)) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: field")
              (without-config
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t (fn-ak-text "no de") (list *akt-groups*) 100000 *akt-limits*)) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (fn-inj-configp config)")
              (without-allow
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config nil *akt-agent* (list *akt-groups*) 100000 *akt-limits*)) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (fn-inj-config-allow config)")
              (without-obs
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation (list :fn-clock-observation 1 1790000000000 -1 t)) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (fn-clock-observationp observation)")
              (without-wall
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation (fn-clock-observation 1 1790000000000 0 nil)) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "no wall clock: the cycle test reads a nil wall, outside its guard")
              (without-cycle
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config *akt-config*) (observation (fn-clock-observation 1 (* 146097 86400000) 0 t)) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cy")
              (without-fields
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list *akt-groups*) 100000 '(8 256 16384))) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config)))")
              (without-lines
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list *akt-groups*) 100000 '(64 100 16384))) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limi")
              (without-header-octets
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config)) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list *akt-groups*) 100000 '(64 256 7000))) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *f")
              (without-groups
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (<= (len octets) (fn-inj-config-max-octets config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list (fn-ak-text "other.group")) 100000 *akt-limits*)) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (fn-inj-groups-admissiblep names (fn-inj-config-groups config))")
              (without-article-bound
               (:conclusion (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier))) (implies (and (fn-ak-valuesp from date groups subject msgid media-type) (fn-cbor-octet-listp payload) field (fn-inj-configp config) (fn-inj-config-allow config) (fn-clock-observationp observation) (fn-clock-has-wall observation) (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*) (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config))) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config))) (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config))) (fn-inj-groups-admissiblep names (fn-inj-config-groups config))) (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets)))))
               ((from *akt-from*) (date *akt-date*) (groups *akt-groups*) (subject *akt-subject*) (msgid *akt-msgid*) (media-type *akt-media*) (payload *akt-payload*) (config (akt-config t *akt-agent* (list *akt-groups*) 7000 *akt-limits*)) (observation *akt-observation*) (principal *akt-principal*) (keys *akt-keys*) (signatures *akt-sigs*))
               :fault "the antecedent dropped: (<= (len octets) (fn-inj-config-max-octets config))")))
(defteeth fn-ak-layout-parses
  :claim (((values (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)) (payload-and-size (and (fn-cbor-octet-listp payload) (<= (len (fn-ak-layout vals payload)) *fn-article-max-octets*))))
          (equal (fn-article-parse (fn-ak-layout vals payload))
                  (fn-article-ok
                   (fn-article-make (fn-ak-render-rows *fn-ak-v1-rows* vals)
                                    (fn-ak-frame (fn-ot-b64-encode payload))
                                    (fn-ak-fields *fn-ak-v1-rows* vals)))))
  :subject fn-article-parse
  :witness ((vals *akt-vals*) (payload *akt-payload*))
  :breaks ((values ((vals (fn-ak-values (fn-ak-text "yue") *akt-date* *akt-groups* *akt-subject* *akt-msgid* *akt-media*)) (payload *akt-payload*)))
           (payload-and-size ((vals *akt-vals*) (payload '(1 2 256)))))
  :mutations ())
(defteeth fn-ak-layout-parses-under
  :claim (((values (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)) (octets (fn-cbor-octet-listp payload)) (size-and-limits (and (fn-cbor-at-mostp (fn-ak-layout vals payload) *fn-article-max-octets*) (<= 8 (fn-article-limit-fields limits)) (<= 8 (fn-article-limit-lines limits)) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                    (fn-article-limit-octets limits)))))
          (equal (fn-article-parse-under (fn-ak-layout vals payload) limits)
                  (fn-article-ok
                   (fn-article-make (fn-ak-render-rows *fn-ak-v1-rows* vals)
                                    (fn-ak-frame (fn-ot-b64-encode payload))
                                    (fn-ak-fields *fn-ak-v1-rows* vals)))))
  :subject fn-article-parse-under
  :witness ((vals *akt-vals*) (payload *akt-payload*) (limits *akt-limits*))
  :breaks ((values ((vals (fn-ak-values (fn-ak-text "yue") *akt-date* *akt-groups* *akt-subject* *akt-msgid* *akt-media*)) (payload *akt-payload*) (limits *akt-limits*)))
           (octets ((vals *akt-vals*) (payload '(1 2 256)) (limits *akt-limits*)))
           (size-and-limits ((vals *akt-vals*) (payload *akt-payload*) (limits '(7 256 16384)))))
  :mutations ((no-field-limit
               (:hypothesis size-and-limits (and (fn-cbor-at-mostp (fn-ak-layout vals payload) *fn-article-max-octets*) (<= 8 (fn-article-limit-lines limits)) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                    (fn-article-limit-octets limits))))
               ((vals *akt-vals*) (payload *akt-payload*) (limits '(7 256 16384)))
               :fault "the field-count limit dropped from the antecedent")
              (no-line-limit
               (:hypothesis size-and-limits (and (fn-cbor-at-mostp (fn-ak-layout vals payload) *fn-article-max-octets*) (<= 8 (fn-article-limit-fields limits)) (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                    (fn-article-limit-octets limits))))
               ((vals *akt-vals*) (payload *akt-payload*) (limits '(64 7 16384)))
               :fault "the line-count limit dropped from the antecedent")
              (no-header-octet-limit
               (:hypothesis size-and-limits (and (fn-cbor-at-mostp (fn-ak-layout vals payload) *fn-article-max-octets*) (<= 8 (fn-article-limit-fields limits)) (<= 8 (fn-article-limit-lines limits))))
               ((vals *akt-vals*) (payload *akt-payload*) (limits '(64 256 200)))
               :fault "the header-octet limit dropped from the antecedent")))
(defteeth fn-ak-carrier-parses
  :claim (((values (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)) (payload (fn-cbor-octet-listp payload)) (vchars (fn-akh-vchars-p field)) (field-and-size (and (consp field) (<= (+ (len (fn-hc-field-lines field)) (len (fn-ak-layout vals payload)))
                    *fn-article-max-octets*))))
          (equal (fn-article-parse
                   (append (fn-hc-field-lines field) (fn-ak-layout vals payload)))
                  (fn-article-ok
                   (fn-article-make (append (fn-hc-field-lines field)
                                            (fn-ak-render-rows *fn-ak-v1-rows* vals))
                                    (fn-ak-frame (fn-ot-b64-encode payload))
                                    (cons (fn-akh-auth-field field)
                                          (fn-ak-fields *fn-ak-v1-rows* vals))))))
  :subject fn-article-parse
  :witness ((vals *akt-vals*) (payload *akt-payload*) (field *akt-field*))
  :breaks ((values ((vals (fn-ak-values (fn-ak-text "yue") *akt-date* *akt-groups* *akt-subject* *akt-msgid* *akt-media*)) (payload *akt-payload*) (field *akt-field*)))
           (payload ((vals *akt-vals*) (payload '(1 2 256)) (field *akt-field*)))
           (vchars ((vals *akt-vals*) (payload *akt-payload*) (field '(0 1))))
           (field-and-size ((vals *akt-vals*) (payload *akt-payload*) (field nil))))
  :mutations ())
(defteeth fn-ak-carrier-parses-under
  :claim (((values (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)) (payload (fn-cbor-octet-listp payload)) (vchars (fn-akh-vchars-p field)) (field-size-limits (and (consp field) (<= (+ (len (fn-hc-field-lines field)) (len (fn-ak-layout vals payload)))
                    *fn-article-max-octets*) (<= 9 (fn-article-limit-fields limits)) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                    (fn-article-limit-lines limits)) (<= (+ (len (fn-hc-field-lines field))
                       (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                    (fn-article-limit-octets limits)))))
          (equal (fn-article-parse-under
                   (append (fn-hc-field-lines field) (fn-ak-layout vals payload)) limits)
                  (fn-article-ok
                   (fn-article-make (append (fn-hc-field-lines field)
                                            (fn-ak-render-rows *fn-ak-v1-rows* vals))
                                    (fn-ak-frame (fn-ot-b64-encode payload))
                                    (cons (fn-akh-auth-field field)
                                          (fn-ak-fields *fn-ak-v1-rows* vals))))))
  :subject fn-article-parse-under
  :witness ((vals *akt-vals*) (payload *akt-payload*) (field *akt-field*) (limits *akt-limits*))
  :breaks ((values ((vals (fn-ak-values (fn-ak-text "yue") *akt-date* *akt-groups* *akt-subject* *akt-msgid* *akt-media*)) (payload *akt-payload*) (field *akt-field*) (limits *akt-limits*)))
           (payload ((vals *akt-vals*) (payload '(1 2 256)) (field *akt-field*) (limits *akt-limits*)))
           (vchars ((vals *akt-vals*) (payload *akt-payload*) (field '(0 1)) (limits *akt-limits*)))
           (field-size-limits ((vals *akt-vals*) (payload *akt-payload*) (field nil) (limits *akt-limits*))))
  :mutations ((no-field-limit
               (:hypothesis field-size-limits (and (consp field) (<= (+ (len (fn-hc-field-lines field)) (len (fn-ak-layout vals payload)))
                    *fn-article-max-octets*) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                    (fn-article-limit-lines limits)) (<= (+ (len (fn-hc-field-lines field))
                       (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                    (fn-article-limit-octets limits))))
               ((vals *akt-vals*) (payload *akt-payload*) (field *akt-field*) (limits '(8 256 16384)))
               :fault "the field-count limit dropped from the antecedent")
              (no-line-limit
               (:hypothesis field-size-limits (and (consp field) (<= (+ (len (fn-hc-field-lines field)) (len (fn-ak-layout vals payload)))
                    *fn-article-max-octets*) (<= 9 (fn-article-limit-fields limits)) (<= (+ (len (fn-hc-field-lines field))
                       (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                    (fn-article-limit-octets limits))))
               ((vals *akt-vals*) (payload *akt-payload*) (field *akt-field*) (limits '(64 100 16384)))
               :fault "the line-count limit dropped from the antecedent")
              (no-header-octet-limit
               (:hypothesis field-size-limits (and (consp field) (<= (+ (len (fn-hc-field-lines field)) (len (fn-ak-layout vals payload)))
                    *fn-article-max-octets*) (<= 9 (fn-article-limit-fields limits)) (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                    (fn-article-limit-lines limits))))
               ((vals *akt-vals*) (payload *akt-payload*) (field *akt-field*) (limits '(64 256 7000)))
               :fault "the header-octet limit dropped from the antecedent")))
