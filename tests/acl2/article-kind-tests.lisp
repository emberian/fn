; fn: teeth for books/article-kind.lisp and books/article-kind-acceptance.lisp.
;
; fn-ak-layout-is-injected: a ground positive witness on which every
; hypothesis and the conclusion hold, and for each hypothesis a witness on
; which every other hypothesis holds, that one fails, and the conclusion
; fails (the decision is not the injection).  fn-ak-layout-parses gets the
; same.  The kind's refinements (the From mailbox-list, the newsgroup-list,
; the msg-id) are shown to be needed: the same octets spelled out without
; the refinement are refused by fn-inj-decide by name.

(in-package "ACL2")
(include-book "../../books/article-kind-acceptance")

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
