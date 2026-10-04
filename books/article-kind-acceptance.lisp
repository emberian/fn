; fn: every article of the kind `opaque' v1 is accepted (D50; M6).
;
; The expensive half of M6: the layout of every value of the kind
; (books/article-kind.lisp fn-ak-layout) is accepted by the article parser
; every reader calls and by the injection decision every POST route calls.

(in-package "ACL2")
(include-book "article-kind")
(include-book "injection")
(include-book "article-header-limits")

(defun fn-aka-line-ind (l acc left)
  (if (consp l) (fn-aka-line-ind (cdr l) (cons (car l) acc) (1- left)) (list acc left)))

(defthm fn-aka-next-line-aux-of-a-line
  (implies (and (fn-ak-no-crlfp l) (true-listp l) (<= (len l) (nfix left))
                (true-listp acc))
           (equal (fn-article-next-line-aux (append l (list* 13 10 r)) acc left)
                  (list :ok (append (reverse acc) l) r)))
  :hints (("Goal" :induct (fn-aka-line-ind l acc left)
           :in-theory (enable fn-article-next-line-aux))))

(defun fn-ak-rows-namesp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-article-namep (fn-ak-row-name (car rows)))
           (true-listp (fn-ak-row-name (car rows)))
           (fn-ak-rows-namesp (cdr rows)))
    t))

(defun fn-ak-row-field (row v)
  (declare (xargs :guard t))
  (fn-article-make-field (list (append (fn-ak-row-prefix row) (true-list-fix v)))
                         (fn-article-ascii-downcase (true-list-fix (fn-ak-row-name row)))
                         (cons 32 (true-list-fix v))))

(defun fn-ak-fields (rows vals)
  (declare (xargs :guard t))
  (if (consp rows)
      (cons (fn-ak-row-field (car rows) (if (consp vals) (car vals) nil))
            (fn-ak-fields (cdr rows) (if (consp vals) (cdr vals) nil)))
    nil))

(defthm fn-aka-split-colon-of-a-name
  (implies (and (fn-article-ftext-listp name) (true-listp acc))
           (equal (fn-article-split-colon-aux (append name (cons 58 rest)) acc)
                  (list :ok (append (reverse acc) name) rest)))
  :hints (("Goal" :induct (fn-aka-line-ind name acc 0)
           :in-theory (enable fn-article-split-colon-aux fn-article-ftextp))))

(defthm fn-aka-sp-vchar-is-header-bytes
  (implies (fn-ak-sp-vchar-listp v) (fn-article-header-bytes-p v))
  :hints (("Goal" :in-theory (enable fn-article-header-bytes-p fn-article-header-bytep
                                     fn-article-wspp fn-article-vcharp fn-ak-vcharp))))

(defthm fn-aka-new-field-of-a-row-line
  (implies (and (fn-article-namep name) (true-listp name) (fn-ak-text-valuep v))
           (equal (fn-article-new-field (append name (list* 58 32 v)))
                  (list :ok (fn-article-make-field (list (append name (list* 58 32 v)))
                                                   (fn-article-ascii-downcase name)
                                                   (cons 32 v)))))
  :hints (("Goal" :in-theory (enable fn-article-new-field fn-article-namep
                                     fn-article-header-bytes-p fn-article-header-bytep
                                     fn-article-wspp))))

(defthm fn-aka-sp-vchar-no-crlf
  (implies (fn-ak-sp-vchar-listp v) (fn-ak-no-crlfp v))
  :hints (("Goal" :in-theory (enable fn-ak-vcharp))))

(defthm fn-aka-ftext-no-crlf
  (implies (fn-article-ftext-listp v) (fn-ak-no-crlfp v))
  :hints (("Goal" :in-theory (enable fn-article-ftext-listp fn-article-ftextp))))

(defthm fn-aka-no-crlf-append
  (equal (fn-ak-no-crlfp (append a b))
         (and (fn-ak-no-crlfp a) (fn-ak-no-crlfp b))))

(defthm fn-aka-next-line-of-a-line
  (implies (and (fn-ak-no-crlfp l) (true-listp l) (<= (len l) 998))
           (equal (fn-article-next-line (append l (list* 13 10 r)))
                  (list :ok l r)))
  :hints (("Goal" :in-theory (enable fn-article-next-line)
           :use ((:instance fn-aka-next-line-aux-of-a-line (acc nil) (left 998))))))

(defthm fn-aka-next-line-of-blank
  (equal (fn-article-next-line (list* 13 10 r)) (list :ok nil r))
  :hints (("Goal" :in-theory (enable fn-article-next-line fn-article-next-line-aux))))

(defun fn-aka-parse-ind (rows vals lines-left hb nf frev cur hrev)
  (declare (xargs :measure (len rows)))
  (if (consp rows)
      (let ((line (append (fn-ak-row-prefix (car rows)) (car vals))))
        (fn-aka-parse-ind (cdr rows) (cdr vals) (1- lines-left)
                          (+ hb (len line) 2)
                          (if cur (+ 1 (nfix nf)) nf)
                          (if cur (cons cur frev) frev)
                          (fn-ak-row-field (car rows) (car vals))
                          (fn-article-header-rev-add-line hrev line)))
    (list vals lines-left hb nf frev cur hrev)))

(defthm fn-aka-next-line-of-a-field-line
  (implies (and (fn-article-ftext-listp name) (true-listp name)
                (fn-ak-sp-vchar-listp v)
                (<= (+ (len name) 2 (len v)) 998))
           (equal (fn-article-next-line
                   (append name (cons 58 (cons 32 (append v (cons 13 (cons 10 r)))))))
                  (list :ok (append name (cons 58 (cons 32 v))) r)))
  :hints (("Goal" :in-theory (disable fn-aka-next-line-of-a-line fn-article-next-line)
           :use ((:instance fn-aka-next-line-of-a-line
                            (l (append name (cons 58 (cons 32 v)))))))))

(defthm fn-aka-name-opens-no-wsp
  (implies (fn-article-namep name)
           (and (consp name)
                (not (fn-article-wspp (car name)))))
  :hints (("Goal" :in-theory (enable fn-article-namep fn-article-ftext-listp
                                     fn-article-ftextp fn-article-wspp))))

(defthm fn-aka-text-value-has-vchar
  (implies (fn-ak-text-valuep v)
           (and (fn-article-has-vcharp (cons 32 v))
                (fn-ak-sp-vchar-listp v)
                (true-listp v)))
  :hints (("Goal" :in-theory (enable fn-ak-text-valuep fn-ak-vcharp
                                     fn-article-has-vcharp fn-article-vcharp))))


(defthm fn-aka-car-append-of-consp
  (implies (consp name) (equal (car (append name x)) (car name))))

(defthm fn-aka-parse-lines-of-a-field-line
  (implies (and (fn-article-namep name) (true-listp name)
                (fn-ak-text-valuep v)
                (<= (+ (len name) 2 (len v)) 998)
                (posp lines-left)
                (natp hb) (natp nf)
                (or (null cur)
                    (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (+ hb (len name) 4 (len v))
                    (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append name (cons 58 (cons 32 (append v (cons 13 (cons 10 rest))))))
                   limits lines-left hb nf frev cur hrev)
                  (fn-article-parse-lines
                   rest limits (1- lines-left)
                   (+ hb (len name) 4 (len v))
                   (if cur (+ 1 nf) nf)
                   (if cur (cons cur frev) frev)
                   (fn-article-make-field (list (append name (cons 58 (cons 32 v))))
                                          (fn-article-ascii-downcase name)
                                          (cons 32 v))
                   (fn-article-header-rev-add-line
                    hrev (append name (cons 58 (cons 32 v)))))))
  :hints (("Goal"
           :expand ((:free (cur nf frev hrev)
                     (fn-article-parse-lines
                      (append name (cons 58 (cons 32 (append v (cons 13 (cons 10 rest))))))
                      limits lines-left hb nf frev cur hrev)))
           :in-theory (e/d (fn-article-field-closedp fn-article-namep)
                           (fn-article-parse-lines fn-article-new-field
                            fn-article-next-line fn-ak-sp-vchar-listp fn-ak-text-valuep
                            fn-article-ftext-listp fn-article-has-vcharp
                            fn-article-header-rev-add-line fn-article-wspp binary-append))
           :do-not-induct t)))

(defthm fn-aka-reverse-is-rev
  (implies (true-listp x) (equal (reverse x) (rev x)))
  :hints (("Goal" :in-theory (enable rev))))

(defthm fn-aka-parse-lines-of-the-blank-line
  (implies (and (posp lines-left)
                (fn-article-body-crlfp body)
                (fn-article-field-closedp cur)
                (true-listp hrev))
           (equal (fn-article-parse-lines (cons 13 (cons 10 body))
                                          limits lines-left hb nf frev cur hrev)
                  (fn-article-ok
                   (fn-article-make (rev hrev) body
                                    (fn-article-finish-fields frev cur)))))
  :hints (("Goal" :expand ((fn-article-parse-lines (cons 13 (cons 10 body))
                                                   limits lines-left hb nf frev cur hrev))
           :in-theory (disable fn-article-parse-lines fn-article-field-closedp))))

(defthm fn-aka-row-value-is-text
  (implies (fn-ak-row-valuep row v)
           (fn-ak-text-valuep v))
  :hints (("Goal" :in-theory (e/d (fn-ak-row-valuep)
                                  (fn-ak-text-valuep fn-mbx-mailbox-listp
                                   fn-af-newsgroup-list-parse fn-af-message-idp
                                   fn-af-trim-wsp)))))

(defthm fn-aka-row-value-bound
  (implies (and (fn-ak-row-valuep row v)
                (true-listp (car row)))
           (<= (+ (len (car row)) 2 (len v)) 998))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-ak-row-valuep fn-ak-row-fuel fn-ak-row-prefix
                                   fn-ak-text-valuep)
                                  (fn-ak-sp-vchar-listp fn-ak-vcharp fn-mbx-mailbox-listp
                                   fn-af-newsgroup-list-parse fn-af-message-idp
                                   fn-af-trim-wsp)))))

(defthm fn-aka-parse-lines-of-rows
  (implies (and (fn-ak-rows-namesp rows)
                (fn-ak-rows-valuesp rows vals)
                (natp lines-left) (< (len rows) lines-left)
                (natp hb) (natp nf) (true-listp hrev)
                (fn-article-field-closedp cur)
                (<= (+ hb (len (fn-ak-render-rows rows vals)))
                    (fn-article-limit-octets limits))
                (or (atom rows)
                    (<= (+ nf (if cur 1 0) (len rows))
                        (fn-article-limit-fields limits)))
                (fn-article-body-crlfp body))
           (equal (fn-article-parse-lines
                   (append (fn-ak-render-rows rows vals) (cons 13 (cons 10 body)))
                   limits lines-left hb nf frev cur hrev)
                  (fn-article-ok
                   (fn-article-make
                    (append (rev hrev) (fn-ak-render-rows rows vals))
                    body
                    (if (consp rows)
                        (append (rev frev) (if cur (list cur) nil)
                                (fn-ak-fields rows vals))
                      (fn-article-finish-fields frev cur))))))
  :hints (("Goal" :induct (fn-aka-parse-ind rows vals lines-left hb nf frev cur hrev)
           :in-theory (e/d (fn-ak-row-prefix fn-ak-row-field fn-article-field-closedp
                            fn-article-finish-fields)
                           (fn-article-parse-lines fn-ak-row-valuep fn-ak-text-valuep
                            fn-article-header-rev-add-line fn-article-has-vcharp
                            fn-article-namep)))
          ("Subgoal *1/1" :in-theory (e/d (fn-ak-row-prefix fn-ak-row-field
                                           fn-article-field-closedp fn-article-header-rev-add-line)
                                          (fn-article-parse-lines fn-ak-row-valuep fn-ak-text-valuep
                                           fn-article-has-vcharp fn-article-namep)))))

(defthm fn-aka-octet-listp-of-append
  (equal (fn-cbor-octet-listp (append a b))
         (and (fn-cbor-octet-listp (true-list-fix a)) (fn-cbor-octet-listp b)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))

(defun fn-aka-b64-charsp (xs)
  (if (consp xs)
      (and (or (fn-ot-b64-value (car xs)) (equal (car xs) 61))
           (fn-aka-b64-charsp (cdr xs)))
    (null xs)))

(defthm fn-aka-b64-charsp-of-encode
  (fn-aka-b64-charsp (fn-ot-b64-encode xs))
  :hints (("Goal" :in-theory (enable fn-ot-b64-encode fn-ot-b64-c0 fn-ot-b64-c1
                                     fn-ot-b64-c2 fn-ot-b64-c3 fn-ot-b64-c1-last
                                     fn-ot-b64-c2-last))))

(defthm fn-aka-b64-chars-are-octets-without-crlf
  (implies (fn-aka-b64-charsp xs)
           (and (fn-ak-no-crlfp xs) (fn-cbor-octet-listp xs) (true-listp xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-ot-b64-value))))

(defthm fn-aka-take-of-chars
  (implies (fn-aka-b64-charsp xs) (fn-aka-b64-charsp (fn-ak-take n xs))))

(defthm fn-aka-drop-of-chars
  (implies (fn-aka-b64-charsp xs) (fn-aka-b64-charsp (fn-ak-drop n xs))))

(defthm fn-aka-body-crlfp-of-a-line
  (implies (and (fn-ak-no-crlfp a) (fn-article-body-crlfp b))
           (fn-article-body-crlfp (append a (cons 13 (cons 10 b)))))
  :hints (("Goal" :in-theory (enable fn-article-body-crlfp))))

(defthm fn-aka-frame-of-b64-chars
  (implies (fn-aka-b64-charsp text)
           (and (fn-article-body-crlfp (fn-ak-frame text))
                (fn-cbor-octet-listp (fn-ak-frame text))))
  :hints (("Goal" :induct (fn-ak-frame text)
           :in-theory (e/d (fn-ak-frame) (fn-aka-b64-charsp)))))

(defthm fn-aka-ftext-are-octets
  (implies (fn-article-ftext-listp xs) (fn-cbor-octet-listp xs))
  :hints (("Goal" :in-theory (enable fn-article-ftext-listp fn-article-ftextp
                                     fn-cbor-octet-listp fn-cbor-octetp))))

(defthm fn-aka-render-rows-are-octets
  (implies (and (fn-ak-rows-namesp rows) (fn-ak-rows-valuesp rows vals))
           (fn-cbor-octet-listp (fn-ak-render-rows rows vals)))
  :hints (("Goal" :in-theory (e/d (fn-ak-row-prefix fn-article-namep)
                                  (fn-ak-row-valuep fn-ak-text-valuep)))))

(defthm fn-ak-v1-rows-are-named
  (fn-ak-rows-namesp *fn-ak-v1-rows*))

(defthm fn-ak-layout-parses-under
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-cbor-octet-listp payload)
                (fn-cbor-at-mostp (fn-ak-layout vals payload) *fn-article-max-octets*)
                (<= 8 (fn-article-limit-fields limits))
                (<= 8 (fn-article-limit-lines limits))
                (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                    (fn-article-limit-octets limits)))
           (equal (fn-article-parse-under (fn-ak-layout vals payload) limits)
                  (fn-article-ok
                   (fn-article-make (fn-ak-render-rows *fn-ak-v1-rows* vals)
                                    (fn-ak-frame (fn-ot-b64-encode payload))
                                    (fn-ak-fields *fn-ak-v1-rows* vals)))))
  :hints (("Goal" :in-theory (e/d (fn-article-parse-under fn-ak-layout fn-article-field-closedp)
                                  (fn-ak-rows-valuesp fn-ak-render-rows fn-ak-fields
                                   fn-article-parse-lines fn-ak-frame fn-ot-b64-encode
                                   (:executable-counterpart fn-ak-rows-namesp)
                                   fn-ak-rows-namesp))
           :use ((:instance fn-aka-parse-lines-of-rows
                            (rows *fn-ak-v1-rows*)
                            (body (fn-ak-frame (fn-ot-b64-encode payload)))
                            (lines-left (+ 1 (fn-article-limit-lines limits)))
                            (hb 0) (nf 0) (frev nil) (cur nil) (hrev nil))))))

(defthm fn-aka-at-mostp-is-len
  (implies (natp n)
           (equal (fn-cbor-at-mostp xs n) (<= (len xs) n)))
  :hints (("Goal" :in-theory (enable fn-cbor-at-mostp))))

(defthm fn-ak-layout-parses
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-cbor-octet-listp payload)
                (<= (len (fn-ak-layout vals payload)) *fn-article-max-octets*))
           (equal (fn-article-parse (fn-ak-layout vals payload))
                  (fn-article-ok
                   (fn-article-make (fn-ak-render-rows *fn-ak-v1-rows* vals)
                                    (fn-ak-frame (fn-ot-b64-encode payload))
                                    (fn-ak-fields *fn-ak-v1-rows* vals)))))
  :hints (("Goal" :in-theory (e/d (fn-article-parse)
                                  (fn-ak-rows-valuesp fn-ak-render-rows fn-ak-fields
                                   fn-ak-frame fn-ot-b64-encode fn-article-parse-under
                                   fn-ak-layout-parses-under))
           :use ((:instance fn-ak-layout-parses-under
                            (limits *fn-article-ceiling-limits*))))
          ("Subgoal 1" :in-theory (e/d (fn-article-parse fn-ak-layout)
                                  (fn-ak-rows-valuesp fn-ak-render-rows fn-ak-fields
                                   fn-ak-frame fn-ot-b64-encode fn-article-parse-under
                                   fn-ak-layout-parses-under)))))

(defthm fn-aka-census-passes
  (implies (and (fn-article-result-okp (fn-article-parse source))
                (fn-article-result-okp (fn-article-parse-under source limits)))
           (not (fn-article-census-refusal (fn-article-header-census source) limits)))
  :hints (("Goal" :use ((:instance fn-article-census-refusal-is-the-parse
                                   (octets source))))))


(defthm fn-aka-fields-check
  (implies (fn-ak-valuesp from date groups subject msgid media-type)
           (let ((article (fn-article-make
                           h b (fn-ak-fields *fn-ak-v1-rows*
                                             (fn-ak-values from date groups subject
                                                           msgid media-type)))))
             (and (equal (fn-inj-proto-reason (fn-af-proto-article-check article)) nil)
                  (equal (fn-inj-nth 1 (fn-af-proto-article-check article)) msgid)
                  (equal (fn-inj-nth 2 (fn-af-proto-article-check article))
                         (cadr (fn-af-newsgroup-list-parse groups)))
                  (fn-inj-absentp article *fn-inj-path-name*)
                  (not (fn-inj-absentp article *fn-inj-date-name*))
                  (equal (fn-inj-mandatory-reason article) nil))))
  :hints (("Goal" :in-theory (e/d (fn-inj-proto-reason fn-af-proto-article-check
                                   fn-af-relayed-article-check fn-af-message-id-status
                                   fn-af-newsgroups-status fn-af-message-id-field-value
                                   fn-af-newsgroups-field-value fn-af-status-kind
                                   fn-af-status-value fn-af-status-field
                                   fn-inj-mandatory-reason fn-inj-absentp
                                   fn-inj-single-fieldp fn-inj-from-validp
                                   fn-inj-nth fn-inj-car fn-inj-cdr
                                   fn-ak-valuesp fn-ak-values fn-ak-row-valuep
                                   fn-ak-text-valuep fn-article-header-bytes-p fn-article-header-bytep fn-article-wspp)
                                  (fn-mbx-mailbox-listp fn-af-newsgroup-list-parse
                                   fn-af-message-idp fn-af-trim-wsp
                                   fn-ak-sp-vchar-listp)))))

(defthm fn-aka-fields-are-fields
  (implies (fn-ak-valuesp from date groups subject msgid media-type)
           (fn-article-field-listp
            (fn-ak-fields *fn-ak-v1-rows*
                          (fn-ak-values from date groups subject msgid media-type))))
  :hints (("Goal" :in-theory (e/d (fn-ak-valuesp fn-ak-values fn-ak-row-valuep
                                   fn-ak-text-valuep fn-article-header-bytes-p
                                   fn-article-header-bytep fn-article-wspp
                                   fn-article-field-listp fn-article-fieldp)
                                  (fn-mbx-mailbox-listp fn-af-newsgroup-list-parse
                                   fn-af-message-idp fn-af-trim-wsp
                                   fn-ak-sp-vchar-listp)))))


(defthm fn-aka-layout-article-syntax
  (implies (and (fn-ak-valuesp from date groups subject msgid media-type)
                (fn-cbor-octet-listp payload))
           (fn-article-syntax-p
            (fn-article-make
             (fn-ak-render-rows *fn-ak-v1-rows*
                                (fn-ak-values from date groups subject msgid media-type))
             (fn-ak-frame (fn-ot-b64-encode payload))
             (fn-ak-fields *fn-ak-v1-rows*
                           (fn-ak-values from date groups subject msgid media-type)))))
  :hints (("Goal" :in-theory (e/d (fn-article-syntax-p fn-ak-valuesp)
                                  (fn-ak-values fn-ak-fields fn-ak-render-rows
                                   fn-ak-frame fn-ot-b64-encode fn-ak-rows-valuesp))
           :use ((:instance fn-aka-fields-are-fields)))))


(defthm fn-aka-len-of-inj-append
  (equal (len (fn-inj-append a b)) (+ (len a) (len b)))
  :hints (("Goal" :in-theory (enable fn-inj-append))))

(defthm fn-aka-values-msgid-is-present
  (implies (fn-ak-rows-valuesp *fn-ak-v1-rows*
                               (fn-ak-values from date groups subject msgid media-type))
           (consp msgid))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-ak-values fn-ak-row-valuep fn-ak-text-valuep)
                                  (fn-mbx-mailbox-listp fn-af-newsgroup-list-parse
                                   fn-af-message-idp fn-af-trim-wsp
                                   fn-ak-sp-vchar-listp)))))

(defthm fn-aka-values-groups-are-present
  (implies (fn-ak-rows-valuesp *fn-ak-v1-rows*
                               (fn-ak-values from date groups subject msgid media-type))
           (consp (cadr (fn-af-newsgroup-list-parse groups))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-ak-values fn-ak-row-valuep fn-ak-text-valuep)
                                  (fn-mbx-mailbox-listp fn-af-newsgroup-list-parse
                                   fn-af-message-idp fn-af-trim-wsp
                                   fn-ak-sp-vchar-listp)))))

(defthm fn-ak-layout-is-injected
  (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                         source)))
    (implies (and (fn-ak-valuesp from date groups subject msgid media-type)
                  (fn-cbor-octet-listp payload)
                  (fn-inj-configp config)
                  (fn-inj-config-allow config)
                  (fn-clock-observationp observation)
                  (fn-clock-has-wall observation)
                  (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*)
                  (<= 8 (fn-article-limit-fields (fn-inj-config-header-limits config)))
                  (<= 8 (fn-article-limit-lines (fn-inj-config-header-limits config)))
                  (<= (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
                      (fn-article-limit-octets (fn-inj-config-header-limits config)))
                  (fn-inj-groups-admissiblep names (fn-inj-config-groups config))
                  (<= (len octets) (fn-inj-config-max-octets config)))
             (equal (fn-inj-decide source config observation)
                    (fn-inj-make-decision :injected nil msgid names octets))))
  :hints (("Goal"
           :in-theory (e/d (fn-inj-decide fn-inj-configp fn-inj-prefix fn-inj-append
                            fn-inj-car fn-inj-cdr fn-inj-nth fn-ak-valuesp
                            fn-article-result-okp fn-article-result-article fn-article-ok)
                           (fn-ak-layout fn-ak-rows-valuesp fn-ak-values fn-ak-fields
                            fn-ak-render-rows fn-ak-frame fn-ot-b64-encode
                            fn-article-parse fn-article-parse-under fn-article-make
                            fn-article-syntax-p
                            fn-af-proto-article-check fn-inj-mandatory-reason
                            fn-inj-absentp fn-inj-proto-reason
                            fn-article-header-census fn-article-census-refusal
                            fn-af-newsgroup-list-parse fn-inj-groups-admissiblep)))))
