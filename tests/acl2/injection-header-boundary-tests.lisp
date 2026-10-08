; PRF-1358: the old body edit, hardened refusal, and a real injected recipe.
(in-package "ACL2")
(include-book "../../books/injection-info-params-reference")
(include-book "../../books/post-header-local")
(include-book "must-fail-checked")

(defun phlt-codes (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars)) (phlt-codes (cdr chars)))
    nil))
(defmacro phlt-o (s) `(phlt-codes (coerce ,s 'list)))
(defconst *phlt-mid* (phlt-o "<x@y>"))
(defconst *phlt-params* (fn-ipp-complaints-param (phlt-o "a@b")))
(defconst *phlt-body*
  (append (make-list 28 :initial-element 65)
          (fn-inj-injection-info-line '(97))))
(defconst *phlt-stamp-head*
  (append *fn-inj-injection-date-field* '(120 13 10 13 10)))
(defconst *phlt-date-head*
  (append *fn-inj-date-field* '(120 13 10 13 10)))

(assert-event
 (let ((x (append *phlt-stamp-head* *phlt-body*)))
   (and (equal (fn-ipp-at-stamp x '(97) *phlt-mid* *phlt-params*) x)
        (not (equal (fn-ipp-at-stamp-old x '(97) *phlt-mid* *phlt-params*) x))
        (equal (fn-ipp-with-params x *phlt-mid* *phlt-params*) x)
        (not (equal (fn-ipp-with-params-old x *phlt-mid* *phlt-params*) x))
        (equal (fn-pb-block-agent x *phlt-mid*) nil)
        (equal (fn-pb-block-agent-old x *phlt-mid*) '(97)))))
(assert-event
 (let ((x (append *phlt-date-head* *phlt-body*)))
   (and (equal (fn-ipp-at-date x '(97) *phlt-params*) x)
        (not (equal (fn-ipp-at-date-old x '(97) *phlt-params*) x))
        (equal (fn-pb-block-agent x *phlt-mid*) nil)
        (equal (fn-pb-block-agent-old x *phlt-mid*) '(97)))))

(must-fail-checked
 (assert-event
  (let ((x (append *phlt-stamp-head* *phlt-body*)))
    (equal (fn-ipp-with-params-old x *phlt-mid* *phlt-params*) x))))

; A prefix containing a blank line cannot bypass the boundary via MSGID.
(assert-event
 (let* ((mid '(60 120 13 10 13 10 121 62))
        (x (append (fn-inj-message-id-line mid)
                   (fn-inj-injection-info-line '(97)))))
   (and (equal (fn-ipp-at-msgid x '(97) mid *phlt-params*) x)
        (not (equal (fn-ipp-at-msgid-old x '(97) mid *phlt-params*) x)))))

(defconst *phlt-source*
  (append (phlt-o "From: poster@example.invalid") '(13 10)
          (phlt-o "Subject: hello") '(13 10)
          (phlt-o "Newsgroups: fn.letters") '(13 10 13 10)
          (phlt-o "Hello, news.") '(13 10)))
(defconst *phlt-config*
  (fn-inj-make-config t (phlt-o "fn.example.invalid")
                      (list (phlt-o "fn.letters")) 32768))
(defconst *phlt-observation* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *phlt-decision*
  (fn-inj-decide *phlt-source* *phlt-config* *phlt-observation*))

(assert-event
 (let* ((d *phlt-decision*)
        (x (fn-inj-decision-octets d))
        (mid (fn-inj-decision-msgid d))
        (r (fn-ipp-with-params x mid *phlt-params*)))
   (and (fn-inj-injectedp d)
        (not (equal r x))
        (equal r (fn-ipp-with-params-old x mid *phlt-params*))
        (equal (fn-pb-path-agent x mid) (fn-pb-path-agent-old x mid)))))


(include-book "../../books/defkeystone")
(defteeth fn-ipp-with-params-head-local
  :claim (((head-boundary (fn-art-separated-headp head)))
          (equal (fn-ipp-with-params (append head body) msgid params)
                 (append (fn-ipp-with-params head msgid params) body)))
  :subject fn-ipp-with-params
  :witness
  ((head (fn-art-head (fn-art-of (fn-inj-decision-octets *phlt-decision*))))
   (body (fn-bch-unpack (fn-art-body (fn-art-of (fn-inj-decision-octets *phlt-decision*)))))
   (msgid (fn-inj-decision-msgid *phlt-decision*))
   (params *phlt-params*))
  :breaks
  ((head-boundary
    ((head nil) (body (fn-inj-decision-octets *phlt-decision*))
     (msgid (fn-inj-decision-msgid *phlt-decision*)) (params *phlt-params*))))
  :mutations
  ((old-unchecked-drops
    (:conclusion
     (equal (fn-ipp-with-params-old (append head body) msgid params)
            (append (fn-ipp-with-params-old head msgid params) body)))
    ((head *phlt-stamp-head*) (body *phlt-body*)
     (msgid *phlt-mid*) (params *phlt-params*))
    :fault "The old 49-octet prefix-only skip crosses the blank line and edits BODY.")))
