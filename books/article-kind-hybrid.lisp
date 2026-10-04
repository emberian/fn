; fn: the kind `opaque' v1 through the hybrid-author route (D50; M6).
;
; Mini posts through the owner's control socket with `fn hybrid-author'
; (Mini's root, FN-660-RESPONSE: "every Mini post goes through the control
; socket").  That route does not hand the source to the injecting agent
; directly: it renders the portable carrier (the FN-Authorship field, folded
; base64 of the principal, keys and signatures, books/hybrid-carrier.lisp
; fn-hc-render) IN FRONT of the authored source, and injects that
; (books/hybrid-store-injected.lisp fn-hsig-injected-carrier-plan, which the
; host calls through fn-hsig-injected-carrier-octets,
; host/native/hybrid-control.lisp, and
; fn-hsig-authorized-injected-carried-submission-event,
; host/native/signatures.lisp).
;
; KEYSTONE fn-ak-layout-is-a-hybrid-injection: for every value of the kind,
; octet payload and carrier material whose field encodes (the principal,
; keys and signatures well formed: fn-hc-field-encode-at answers), under a
; valid posting-allowed configuration whose header limits hold the carrier's
; lines, a usable in-cycle clock, the newsgroups admissible and the injected
; octets within the article bound, the plan is :injected with the author's
; Message-ID and the octets Path + Injection-Info + carrier + source: the
; authored source is an unchanged suffix of what the Store keeps.
; fn-ak-carrier-parses[-under]: the carrier parses with its FN-Authorship
; field first and the kind's eight fields after it.

(in-package "ACL2")
(include-book "article-kind-acceptance")
(include-book "hybrid-store-injected")

(defun fn-akh-vchars-p (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-ak-vcharp (car xs)) (fn-akh-vchars-p (cdr xs)))
    (null xs)))

(defthm fn-akh-stx-sextet-is-vchar
  (fn-ak-vcharp (fn-stx-b64-sextet n))
  :hints (("Goal" :in-theory (enable fn-stx-b64-sextet fn-ak-vcharp))))

(defthm fn-akh-vchars-of-stx-b64-encode
  (fn-akh-vchars-p (fn-stx-b64-encode x))
  :hints (("Goal" :in-theory (enable fn-stx-b64-encode fn-ak-vcharp))))

(defthm fn-akh-vchars-of-hc-take
  (implies (fn-akh-vchars-p xs) (fn-akh-vchars-p (fn-hc-take n xs)))
  :hints (("Goal" :in-theory (enable fn-hc-take))))

(defthm fn-akh-vchars-of-hc-drop
  (implies (fn-akh-vchars-p xs) (fn-akh-vchars-p (fn-hc-drop n xs)))
  :hints (("Goal" :in-theory (enable fn-hc-drop))))

(defthm fn-akh-vchars-facts
  (implies (fn-akh-vchars-p xs)
           (and (fn-ak-sp-vchar-listp xs)
                (fn-ak-no-crlfp xs)
                (true-listp xs)
                (fn-article-header-bytes-p xs)
                (fn-cbor-octet-listp xs)))
  :hints (("Goal" :in-theory (enable fn-ak-vcharp fn-article-header-bytes-p
                                     fn-article-header-bytep fn-article-vcharp
                                     fn-article-wspp fn-cbor-octet-listp fn-cbor-octetp))))

(defthm fn-akh-hc-take-len
  (<= (len (fn-hc-take n xs)) (nfix n))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-hc-take))))

(defthm fn-akh-hc-take-consp
  (implies (and (consp xs) (posp n)) (consp (fn-hc-take n xs)))
  :hints (("Goal" :expand ((fn-hc-take n xs)))))

(defun fn-akh-fold (cur r)
  (declare (xargs :measure (len r) :verify-guards nil))
  (if (atom r) cur
    (fn-akh-fold (fn-article-add-fold cur (cons 9 (fn-hc-take 72 r)))
                 (fn-hc-drop 72 r))))

(defun fn-akh-fold-hrev (hrev r)
  (declare (xargs :measure (len r) :verify-guards nil))
  (if (atom r) hrev
    (fn-akh-fold-hrev (fn-article-header-rev-add-line hrev (cons 9 (fn-hc-take 72 r)))
                      (fn-hc-drop 72 r))))

(defun fn-akh-fold-count (r)
  (declare (xargs :measure (len r) :verify-guards nil))
  (if (atom r) 0 (+ 1 (fn-akh-fold-count (fn-hc-drop 72 r)))))

(defun fn-akh-fold-ind (r lines-left hb cur hrev)
  (declare (xargs :measure (len r) :verify-guards nil))
  (if (atom r) (list lines-left hb cur hrev)
    (fn-akh-fold-ind (fn-hc-drop 72 r) (1- lines-left)
                     (+ hb 1 (len (fn-hc-take 72 r)) 2)
                     (fn-article-add-fold cur (cons 9 (fn-hc-take 72 r)))
                     (fn-article-header-rev-add-line hrev (cons 9 (fn-hc-take 72 r))))))

(defthm fn-akh-next-line-of-a-fold-line
  (implies (and (fn-akh-vchars-p v) (<= (len v) 997))
           (equal (fn-article-next-line (cons 9 (append v (cons 13 (cons 10 r)))))
                  (list :ok (cons 9 v) r)))
  :hints (("Goal" :in-theory (disable fn-aka-next-line-of-a-line fn-article-next-line)
           :use ((:instance fn-aka-next-line-of-a-line (l (cons 9 v)))))))

(defthm fn-akh-vchars-have-vchar
  (implies (and (fn-akh-vchars-p v) (consp v)) (fn-article-has-vcharp v))
  :hints (("Goal" :expand ((fn-akh-vchars-p v) (fn-article-has-vcharp v))
           :in-theory (enable fn-ak-vcharp fn-article-vcharp))))

(defthm fn-akh-parse-lines-of-a-fold-line
  (implies (and (fn-akh-vchars-p v) (consp v) (<= (len v) 997)
                (posp lines-left) (natp hb) cur
                (<= (+ hb 3 (len v)) (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (cons 9 (append v (cons 13 (cons 10 rest))))
                                          limits lines-left hb nf frev cur hrev)
                  (fn-article-parse-lines rest limits (1- lines-left)
                                          (+ hb 3 (len v)) nf frev
                                          (fn-article-add-fold cur (cons 9 v))
                                          (fn-article-header-rev-add-line hrev (cons 9 v)))))
  :hints (("Goal" :expand ((:free (cur hrev)
                            (fn-article-parse-lines (cons 9 (append v (cons 13 (cons 10 rest))))
                                                    limits lines-left hb nf frev cur hrev)))
           :in-theory (e/d (fn-article-fold-linep fn-article-wspp fn-article-header-bytes-p
                            fn-article-header-bytep fn-article-has-vcharp)
                           (fn-article-parse-lines fn-article-next-line fn-article-add-fold
                            fn-article-header-rev-add-line binary-append))
           :do-not-induct t)))

(defthm fn-akh-len-take-plus-drop
  (equal (+ (len (fn-hc-take n r)) (len (fn-hc-drop n r))) (len r))
  :hints (("Goal" :in-theory (enable fn-hc-take fn-hc-drop))))

(defthm fn-akh-len-of-hc-drop
  (equal (len (fn-hc-drop n r)) (- (len r) (len (fn-hc-take n r))))
  :hints (("Goal" :use fn-akh-len-take-plus-drop
           :in-theory (disable fn-akh-len-take-plus-drop))))

(defthm fn-akh-len-of-fold-rest
  (equal (len (fn-hc-fold-rest r))
         (+ (* 3 (fn-akh-fold-count r)) (len r)))
  :hints (("Goal" :induct (fn-akh-fold-count r)
           :in-theory (e/d (fn-hc-fold-rest) (fn-hc-take fn-hc-drop)))))

(defthm fn-akh-parse-lines-of-fold-rest
  (implies (and (fn-akh-vchars-p r)
                (natp lines-left) (<= (fn-akh-fold-count r) lines-left)
                (natp hb) cur
                (<= (+ hb (len (fn-hc-fold-rest r))) (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (append (fn-hc-fold-rest r) x)
                                          limits lines-left hb nf frev cur hrev)
                  (fn-article-parse-lines x limits (- lines-left (fn-akh-fold-count r))
                                          (+ hb (len (fn-hc-fold-rest r))) nf frev
                                          (fn-akh-fold cur r)
                                          (fn-akh-fold-hrev hrev r))))
  :hints (("Goal" :induct (fn-akh-fold-ind r lines-left hb cur hrev)
           :in-theory (e/d (fn-hc-fold-rest)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-akh-len-of-fold-rest)))
          ("Subgoal *1/1" :in-theory (e/d (fn-hc-fold-rest)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line)))))

(defconst *fn-akh-authorship-name* '(70 78 45 65 117 116 104 111 114 115 104 105 112))

(defun fn-akh-auth-line (value)
  (declare (xargs :guard t :verify-guards nil))
  (append *fn-akh-authorship-name* (cons 58 (cons 32 (fn-hc-take 72 value)))))

(defun fn-akh-auth-field (value)
  (declare (xargs :guard t :verify-guards nil))
  (fn-akh-fold (fn-article-make-field (list (fn-akh-auth-line value))
                                      (fn-article-ascii-downcase *fn-akh-authorship-name*)
                                      (cons 32 (fn-hc-take 72 value)))
               (fn-hc-drop 72 value)))

(defun fn-akh-auth-hrev (hrev value)
  (declare (xargs :guard t :verify-guards nil))
  (fn-akh-fold-hrev (fn-article-header-rev-add-line hrev (fn-akh-auth-line value))
                    (fn-hc-drop 72 value)))

(defthm fn-akh-field-lines-is-line-and-folds
  (implies (consp value)
           (equal (fn-hc-field-lines value)
                  (append (fn-akh-auth-line value)
                          (cons 13 (cons 10 (fn-hc-fold-rest (fn-hc-drop 72 value)))))))
  :hints (("Goal" :in-theory (enable fn-hc-field-lines fn-akh-auth-line))))

(defthm fn-akh-vchars-are-text
  (implies (and (fn-akh-vchars-p v) (consp v)) (fn-ak-text-valuep v))
  :hints (("Goal" :expand ((fn-akh-vchars-p v))
           :in-theory (enable fn-ak-text-valuep))))

(defthm fn-akh-parse-lines-of-auth-line
  (implies (and (fn-akh-vchars-p value) (consp value)
                (posp lines-left) (natp hb) (natp nf)
                (or (null cur)
                    (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits))
                (<= (+ hb (len (fn-akh-auth-line value)) 2)
                    (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (append (fn-akh-auth-line value)
                                                  (cons 13 (cons 10 rest)))
                                          limits lines-left hb nf frev cur hrev)
                  (fn-article-parse-lines
                   rest limits (1- lines-left)
                   (+ hb (len (fn-akh-auth-line value)) 2)
                   (if cur (+ 1 nf) nf)
                   (if cur (cons cur frev) frev)
                   (fn-article-make-field (list (fn-akh-auth-line value))
                                          (fn-article-ascii-downcase *fn-akh-authorship-name*)
                                          (cons 32 (fn-hc-take 72 value)))
                   (fn-article-header-rev-add-line hrev (fn-akh-auth-line value)))))
  :hints (("Goal" :in-theory (e/d (fn-akh-auth-line)
                                  (fn-article-parse-lines fn-aka-parse-lines-of-a-field-line
                                   fn-article-header-rev-add-line fn-ak-text-valuep))
           :use ((:instance fn-aka-parse-lines-of-a-field-line
                            (name *fn-akh-authorship-name*)
                            (v (fn-hc-take 72 value)))))))

(defthm fn-akh-len-of-field-lines
  (implies (consp value)
           (equal (len (fn-hc-field-lines value))
                  (+ (len (fn-akh-auth-line value)) 2
                     (len (fn-hc-fold-rest (fn-hc-drop 72 value))))))
  :hints (("Goal" :in-theory (disable fn-akh-auth-line fn-hc-fold-rest fn-akh-len-of-fold-rest))))

(defthm fn-akh-parse-lines-of-field-lines
  (implies (and (fn-akh-vchars-p value) (consp value)
                (natp lines-left)
                (< (fn-akh-fold-count (fn-hc-drop 72 value)) lines-left)
                (natp hb) (natp nf)
                (or (null cur)
                    (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits))
                (<= (+ hb (len (fn-hc-field-lines value)))
                    (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (append (fn-hc-field-lines value) x)
                                          limits lines-left hb nf frev cur hrev)
                  (fn-article-parse-lines
                   x limits (- lines-left (+ 1 (fn-akh-fold-count (fn-hc-drop 72 value))))
                   (+ hb (len (fn-hc-field-lines value)))
                   (if cur (+ 1 nf) nf)
                   (if cur (cons cur frev) frev)
                   (fn-akh-auth-field value)
                   (fn-akh-auth-hrev hrev value))))
  :hints (("Goal" :in-theory (e/d (fn-akh-auth-field fn-akh-auth-hrev)
                                  (fn-article-parse-lines fn-hc-fold-rest fn-hc-field-lines
                                   fn-akh-fold fn-akh-fold-hrev fn-akh-auth-line
                                   fn-akh-len-of-fold-rest
                                   fn-article-header-rev-add-line fn-article-make-field)))))

(defthm fn-akh-rev-of-fold-hrev
  (implies (true-listp hrev)
           (equal (rev (fn-akh-fold-hrev hrev r))
                  (append (rev hrev) (fn-hc-fold-rest r))))
  :hints (("Goal" :induct (fn-akh-fold-hrev hrev r)
           :in-theory (enable fn-hc-fold-rest fn-article-header-rev-add-line))))

(defthm fn-akh-fold-keeps-a-visible-value
  (implies (fn-article-has-vcharp (fn-article-field-unfolded-value cur))
           (fn-article-has-vcharp (fn-article-field-unfolded-value (fn-akh-fold cur r))))
  :hints (("Goal" :induct (fn-akh-fold cur r)
           :in-theory (enable fn-article-add-fold))))

(defthm fn-akh-fold-is-a-cons
  (implies (consp cur) (consp (fn-akh-fold cur r)))
  :hints (("Goal" :induct (fn-akh-fold cur r)
           :in-theory (enable fn-article-add-fold))))

(defthm fn-akh-first-value-is-visible
  (implies (and (fn-akh-vchars-p v) (consp v))
           (fn-article-has-vcharp (cons 32 (fn-hc-take 72 v))))
  :hints (("Goal" :in-theory (disable fn-akh-vchars-have-vchar)
           :use ((:instance fn-akh-vchars-have-vchar (v (fn-hc-take 72 v)))))))

(defthm fn-akh-auth-field-is-closed
  (implies (and (fn-akh-vchars-p value) (consp value))
           (and (consp (fn-akh-auth-field value))
                (fn-article-has-vcharp
                 (fn-article-field-unfolded-value (fn-akh-auth-field value)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-akh-auth-field)
                                  (fn-akh-fold fn-akh-fold-keeps-a-visible-value))
           :use ((:instance fn-akh-fold-keeps-a-visible-value
                            (cur (fn-article-make-field
                                  (list (fn-akh-auth-line value))
                                  (fn-article-ascii-downcase *fn-akh-authorship-name*)
                                  (cons 32 (fn-hc-take 72 value))))
                            (r (fn-hc-drop 72 value)))))))

(defthm fn-akh-fold-rest-is-octets
  (implies (fn-akh-vchars-p r)
           (fn-cbor-octet-listp (fn-hc-fold-rest r)))
  :hints (("Goal" :induct (fn-akh-fold-count r)
           :in-theory (e/d (fn-hc-fold-rest) (fn-hc-take fn-hc-drop)))))

(defthm fn-akh-field-lines-are-octets
  (implies (fn-akh-vchars-p value)
           (fn-cbor-octet-listp (fn-hc-field-lines value)))
  :hints (("Goal" :cases ((consp value)))
          ("Subgoal 2" :in-theory (enable fn-hc-field-lines))
          ("Subgoal 1" :in-theory (e/d (fn-akh-auth-line)
                                       (fn-hc-field-lines fn-hc-take fn-hc-drop fn-hc-fold-rest)))))

(defthm fn-akh-rev-of-auth-hrev
  (implies (consp value)
           (equal (rev (fn-akh-auth-hrev nil value))
                  (fn-hc-field-lines value)))
  :hints (("Goal" :in-theory (e/d (fn-akh-auth-hrev fn-article-header-rev-add-line)
                                  (fn-akh-auth-line fn-hc-fold-rest)))))

(defthm fn-akh-field-lines-are-nonempty
  (implies (consp field) (consp (fn-hc-field-lines field)))
  :hints (("Goal" :in-theory (enable fn-hc-field-lines))))

(defthm fn-akh-render-rows-are-nonempty
  (implies (consp rows) (consp (fn-ak-render-rows rows vals)))
  :hints (("Goal" :in-theory (enable fn-ak-render-rows fn-ak-row-prefix))))

(defthm fn-akh-fold-hrev-is-true-list
  (implies (true-listp hrev) (true-listp (fn-akh-fold-hrev hrev r)))
  :hints (("Goal" :induct (fn-akh-fold-hrev hrev r)
           :in-theory (enable fn-article-header-rev-add-line))))

(defthm fn-akh-auth-hrev-is-true-list
  (true-listp (fn-akh-auth-hrev nil value))
  :hints (("Goal" :in-theory (e/d (fn-akh-auth-hrev fn-article-header-rev-add-line)
                                  (fn-akh-auth-line)))))

(defthm fn-akh-auth-field-is-closed-caddr
  (implies (and (fn-akh-vchars-p value) (consp value))
           (fn-article-has-vcharp (caddr (fn-akh-auth-field value))))
  :hints (("Goal" :use fn-akh-auth-field-is-closed
           :in-theory (disable fn-akh-auth-field-is-closed fn-akh-auth-field))))

(defthm fn-akh-parse-lines-of-carrier
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-article-body-crlfp body)
                (fn-akh-vchars-p field) (consp field)
                (natp lines-left)
                (< (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field))) lines-left)
                (<= 9 (fn-article-limit-fields limits))
                (<= (+ (len (fn-hc-field-lines field))
                       (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                    (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines
                   (append (fn-hc-field-lines field)
                           (append (fn-ak-render-rows *fn-ak-v1-rows* vals)
                                   (cons 13 (cons 10 body))))
                   limits lines-left 0 0 nil nil nil)
                  (fn-article-ok
                   (fn-article-make (append (fn-hc-field-lines field)
                                            (fn-ak-render-rows *fn-ak-v1-rows* vals))
                                    body
                                    (cons (fn-akh-auth-field field)
                                          (fn-ak-fields *fn-ak-v1-rows* vals))))))
  :hints (("Goal" :in-theory (e/d (fn-article-field-closedp)
                                  (fn-ak-rows-valuesp fn-ak-render-rows fn-ak-fields
                                   fn-article-parse-lines
                                   fn-hc-field-lines fn-akh-auth-field fn-akh-auth-hrev
                                   fn-akh-fold-count fn-hc-drop fn-akh-len-of-hc-drop
                                   fn-akh-len-of-field-lines fn-akh-auth-line
                                   fn-akh-field-lines-is-line-and-folds
                                   fn-article-limit-octets fn-article-limit-fields
                                   fn-article-limit-lines)))))

(defthm fn-ak-carrier-parses-under
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-cbor-octet-listp payload)
                (fn-akh-vchars-p field) (consp field)
                (<= (+ (len (fn-hc-field-lines field)) (len (fn-ak-layout vals payload)))
                    *fn-article-max-octets*)
                (<= 9 (fn-article-limit-fields limits))
                (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                    (fn-article-limit-lines limits))
                (<= (+ (len (fn-hc-field-lines field))
                       (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                    (fn-article-limit-octets limits)))
           (equal (fn-article-parse-under
                   (append (fn-hc-field-lines field) (fn-ak-layout vals payload)) limits)
                  (fn-article-ok
                   (fn-article-make (append (fn-hc-field-lines field)
                                            (fn-ak-render-rows *fn-ak-v1-rows* vals))
                                    (fn-ak-frame (fn-ot-b64-encode payload))
                                    (cons (fn-akh-auth-field field)
                                          (fn-ak-fields *fn-ak-v1-rows* vals))))))
  :hints (("Goal" :in-theory (e/d (fn-article-parse-under fn-ak-layout)
                                  (fn-ak-rows-valuesp fn-ak-render-rows fn-ak-fields
                                   fn-article-parse-lines fn-ak-frame fn-ot-b64-encode
                                   fn-hc-field-lines fn-akh-auth-field fn-akh-auth-hrev
                                   fn-akh-fold-count fn-hc-drop fn-akh-len-of-hc-drop
                                   fn-akh-len-of-field-lines fn-akh-auth-line
                                   fn-akh-field-lines-is-line-and-folds
                                   fn-article-limit-octets fn-article-limit-fields
                                   fn-article-limit-lines)))))

(defthm fn-akh-rows-shorter-than-layout
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-cbor-octet-listp payload))
           (< (len (fn-ak-render-rows *fn-ak-v1-rows* vals))
              (len (fn-ak-layout vals payload))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-ak-layout)
                                  (fn-ak-rows-valuesp fn-ak-render-rows fn-ak-frame
                                   fn-ot-b64-encode)))))

(defthm fn-ak-carrier-parses
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-cbor-octet-listp payload)
                (fn-akh-vchars-p field) (consp field)
                (<= (+ (len (fn-hc-field-lines field)) (len (fn-ak-layout vals payload)))
                    *fn-article-max-octets*))
           (equal (fn-article-parse
                   (append (fn-hc-field-lines field) (fn-ak-layout vals payload)))
                  (fn-article-ok
                   (fn-article-make (append (fn-hc-field-lines field)
                                            (fn-ak-render-rows *fn-ak-v1-rows* vals))
                                    (fn-ak-frame (fn-ot-b64-encode payload))
                                    (cons (fn-akh-auth-field field)
                                          (fn-ak-fields *fn-ak-v1-rows* vals))))))
  :hints (("Goal" :in-theory (e/d (fn-article-parse)
                                  (fn-ak-rows-valuesp fn-ak-render-rows fn-ak-fields
                                   fn-ak-layout fn-ak-frame fn-ot-b64-encode
                                   fn-hc-field-lines fn-akh-auth-field
                                   fn-akh-fold-count fn-hc-drop
                                   fn-article-parse-under
                                   fn-ak-carrier-parses-under fn-akh-auth-line
                                   fn-akh-field-lines-is-line-and-folds))
           :use ((:instance fn-ak-carrier-parses-under
                            (limits *fn-article-ceiling-limits*))))))

(defthm fn-akh-fold-keeps-the-name
  (equal (cadr (fn-akh-fold cur r)) (cadr cur))
  :hints (("Goal" :induct (fn-akh-fold cur r)
           :in-theory (enable fn-article-add-fold))))

(defthm fn-akh-auth-field-name
  (equal (fn-article-field-name (fn-akh-auth-field v))
         '(102 110 45 97 117 116 104 111 114 115 104 105 112))
  :hints (("Goal" :in-theory (e/d (fn-akh-auth-field) (fn-akh-fold fn-akh-auth-line)))))

(defthm fn-akh-fold-keeps-a-field
  (implies (and (fn-article-fieldp cur) (fn-akh-vchars-p r))
           (fn-article-fieldp (fn-akh-fold cur r)))
  :hints (("Goal" :induct (fn-akh-fold cur r)
           :in-theory (e/d (fn-article-fold-linep fn-article-wspp fn-article-header-bytes-p
                            fn-article-header-bytep)
                           (fn-article-add-fold fn-article-fieldp)))))

(defthm fn-akh-auth-field-is-a-field
  (implies (and (fn-akh-vchars-p v) (consp v))
           (fn-article-fieldp (fn-akh-auth-field v)))
  :hints (("Goal" :in-theory (e/d (fn-akh-auth-field fn-article-fieldp
                                   fn-article-header-bytes-p fn-article-header-bytep
                                   fn-article-wspp)
                                  (fn-akh-fold fn-akh-auth-line)))))

(defthm fn-akh-get-headers-skips-the-carrier
  (implies (not (equal (fn-article-ascii-downcase name)
                       '(102 110 45 97 117 116 104 111 114 115 104 105 112)))
           (equal (fn-article-get-headers-aux (cons (fn-akh-auth-field v) fields) name)
                  (fn-article-get-headers-aux fields name)))
  :hints (("Goal" :expand ((fn-article-get-headers-aux (cons (fn-akh-auth-field v) fields) name))
           :in-theory (e/d (fn-article-field-name-equalp) (fn-akh-auth-field)))))

(defthm fn-akh-field-encode-is-vchars
  (fn-akh-vchars-p (fn-hc-field-encode-at version principal keys signatures))
  :hints (("Goal" :in-theory (enable fn-hc-field-encode-at))))

(defthm fn-akh-carrier-fields-check
  (implies (fn-ak-valuesp from date groups subject msgid media-type)
           (let ((article (fn-article-make
                           h b (cons (fn-akh-auth-field v)
                                     (fn-ak-fields *fn-ak-v1-rows*
                                                   (fn-ak-values from date groups subject
                                                                 msgid media-type))))))
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
                                   fn-ak-text-valuep fn-article-header-bytes-p
                                   fn-article-header-bytep fn-article-wspp)
                                  (fn-mbx-mailbox-listp fn-af-newsgroup-list-parse
                                   fn-af-message-idp fn-af-trim-wsp
                                   fn-ak-sp-vchar-listp fn-akh-auth-field)))))

(defthm fn-akh-source-is-a-native-source
  (implies (and (fn-ak-valuesp from date groups subject msgid media-type)
                (fn-cbor-octet-listp payload))
           (let* ((vals (fn-ak-values from date groups subject msgid media-type))
                  (article (fn-article-make
                            (fn-ak-render-rows *fn-ak-v1-rows* vals)
                            (fn-ak-frame (fn-ot-b64-encode payload))
                            (fn-ak-fields *fn-ak-v1-rows* vals))))
             (and (fn-hc-required-sourcep article)
                  (fn-hc-fields-nativep (fn-article-fields article)))))
  :hints (("Goal" :in-theory (e/d (fn-hc-required-sourcep fn-hc-fields-nativep
                                   fn-hc-reserved-namep
                                   fn-af-message-id-status
                                   fn-af-newsgroups-status fn-af-message-id-field-value
                                   fn-af-newsgroups-field-value fn-af-status-kind
                                   fn-inj-single-fieldp
                                   fn-ak-valuesp fn-ak-values fn-ak-row-valuep
                                   fn-ak-text-valuep)
                                  (fn-mbx-mailbox-listp fn-af-newsgroup-list-parse
                                   fn-af-message-idp fn-af-trim-wsp fn-article-syntax-p
                                   fn-ak-sp-vchar-listp fn-ak-render-rows fn-ak-frame
                                   fn-ot-b64-encode))
           :use ((:instance fn-aka-layout-article-syntax)))))

(defthm fn-akh-article-make-parts
  (and (equal (car (fn-article-make h b f)) h)
       (equal (cadr (fn-article-make h b f)) b)
       (equal (caddr (fn-article-make h b f)) f)
       (true-listp (fn-article-make h b f)))
  :hints (("Goal" :in-theory (enable fn-article-make))))

(defthm fn-akh-kind-fields-are-native
  (implies (fn-ak-valuesp from date groups subject msgid media-type)
           (fn-hc-fields-nativep
            (fn-ak-fields *fn-ak-v1-rows*
                          (fn-ak-values from date groups subject msgid media-type))))
  :hints (("Goal" :use ((:instance fn-akh-source-is-a-native-source (payload nil)))
           :in-theory (disable fn-akh-source-is-a-native-source fn-ak-valuesp
                               fn-ak-fields fn-hc-fields-nativep))))

(defthm fn-akh-field-encode-is-bounded
  (implies (fn-hc-field-encode-at version principal keys signatures)
           (<= (len (fn-hc-field-encode-at version principal keys signatures)) 8192))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-hc-field-encode-at))))

(defthm fn-akh-layout-is-octets
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-cbor-octet-listp payload))
           (and (fn-cbor-octet-listp (fn-ak-layout vals payload))
                (consp (fn-ak-layout vals payload))))
  :hints (("Goal" :in-theory (e/d (fn-ak-layout)
                                  (fn-ak-rows-valuesp fn-ak-render-rows fn-ak-frame
                                   fn-ot-b64-encode)))))

(defthm fn-akh-consp-of-append
  (equal (consp (append a b)) (or (consp a) (consp b))))

(defthm fn-akh-carrier-is-nonempty
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-cbor-octet-listp payload))
           (consp (append x (fn-ak-layout vals payload))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (disable fn-ak-layout fn-ak-rows-valuesp))))

(defthm fn-akh-carrier-article-syntax
  (implies (and (fn-ak-valuesp from date groups subject msgid media-type)
                (fn-cbor-octet-listp payload)
                (fn-akh-vchars-p field) (consp field))
           (fn-article-syntax-p
            (fn-article-make
             (append (fn-hc-field-lines field)
                     (fn-ak-render-rows *fn-ak-v1-rows*
                                        (fn-ak-values from date groups subject msgid media-type)))
             (fn-ak-frame (fn-ot-b64-encode payload))
             (cons (fn-akh-auth-field field)
                   (fn-ak-fields *fn-ak-v1-rows*
                                 (fn-ak-values from date groups subject msgid media-type))))))
  :hints (("Goal" :in-theory (e/d (fn-article-syntax-p fn-ak-valuesp fn-article-make
                                   fn-article-field-listp)
                                  (fn-ak-values fn-ak-fields fn-ak-render-rows fn-hc-field-lines
                                   fn-ak-frame fn-ot-b64-encode fn-ak-rows-valuesp
                                   fn-akh-auth-field fn-article-fieldp fn-akh-auth-line
                                   fn-akh-field-lines-is-line-and-folds))
           :use ((:instance fn-aka-fields-are-fields)
                 (:instance fn-aka-layout-article-syntax)))))

(defthm fn-ak-layout-is-a-hybrid-injection
  (let* ((vals (fn-ak-values from date groups subject msgid media-type))
         (source (fn-ak-layout vals payload))
         (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                       principal keys signatures))
         (carrier (append (fn-hc-field-lines field) source))
         (names (cadr (fn-af-newsgroup-list-parse groups)))
         (octets (fn-inj-append (fn-inj-prefix nil msgid (fn-inj-config-agent config) nil nil)
                                carrier)))
    (implies (and (fn-ak-valuesp from date groups subject msgid media-type)
                  (fn-cbor-octet-listp payload)
                  field
                  (fn-inj-configp config)
                  (fn-inj-config-allow config)
                  (fn-clock-observationp observation)
                  (fn-clock-has-wall observation)
                  (< (floor (fn-clock-wall observation) *fn-inj-ms-per-day*)
                     *fn-inj-cycle-days*)
                  (<= 9 (fn-article-limit-fields (fn-inj-config-header-limits config)))
                  (<= (+ 9 (fn-akh-fold-count (fn-hc-drop 72 field)))
                      (fn-article-limit-lines (fn-inj-config-header-limits config)))
                  (<= (+ (len (fn-hc-field-lines field))
                         (len (fn-ak-render-rows *fn-ak-v1-rows* vals)))
                      (fn-article-limit-octets (fn-inj-config-header-limits config)))
                  (fn-inj-groups-admissiblep names (fn-inj-config-groups config))
                  (<= (len octets) (fn-inj-config-max-octets config)))
             (equal (fn-hsig-injected-carrier-plan source principal keys signatures
                                                   config observation)
                    (fn-inj-make-decision :injected nil msgid names octets))))
  :hints (("Goal"
           :in-theory (e/d (fn-hsig-injected-carrier-plan fn-hc-render-at-most fn-hc-render
                            fn-hc-native-plan fn-inj-supplies-pathp
                            fn-hc-okp fn-hc-value fn-hc-ok
                            fn-inj-decide fn-inj-configp fn-inj-prefix fn-inj-append
                            fn-inj-car fn-inj-cdr fn-inj-nth fn-ak-valuesp
                            fn-article-result-okp fn-article-result-article fn-article-ok
                            fn-cbor-at-mostp)
                           (fn-ak-layout fn-ak-rows-valuesp fn-ak-values fn-ak-fields
                            fn-ak-render-rows fn-ak-frame fn-ot-b64-encode
                            fn-article-parse fn-article-parse-under fn-article-make
                            fn-article-syntax-p fn-hc-required-sourcep fn-hc-fields-nativep
                            fn-af-proto-article-check fn-inj-mandatory-reason
                            fn-inj-absentp fn-inj-proto-reason
                            fn-article-header-census fn-article-census-refusal
                            fn-af-newsgroup-list-parse fn-inj-groups-admissiblep
                            fn-hc-field-lines fn-hc-field-encode-at fn-akh-auth-field
                            fn-akh-fold-count fn-hc-drop fn-akh-auth-line
                            fn-akh-field-lines-is-line-and-folds
                            fn-hsig-source-version fn-article-limit-fields
                            fn-article-limit-lines fn-article-limit-octets
                            fn-akh-len-of-field-lines fn-akh-len-of-hc-drop)))))
