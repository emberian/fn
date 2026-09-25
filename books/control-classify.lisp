; fn: control-message recognition (design 2026-09-25, packet C1).
;
; RFC 5537 section 5: "Any article containing a Control header field ... is a
; control message", and a Subject starting "cmsg ", a newsgroup name ending in
; ".ctl" or an Also-Control field "MUST NOT cause the article to be
; interpreted as a control message".  So the classifier reads the Control
; field and nothing else, apart from the one other field RFC 5536 section
; 3.2.3 couples it to: "An article with a Control header field MUST NOT also
; have a Supersedes header field."
;
; The classifier consumes the fields of a successful `fn-article-parse' view;
; the parser's bounds (field count, field value length) apply before any verb
; or argument is read (RFC 5537 section 6.1).  Nothing here executes anything:
; C1 recognizes and files.  The filing step is `fn-pa-filing-plan'
; (books/peer-authored-accept.lisp), which every ingress calls.
(in-package "ACL2")
(include-book "article-fields")

; "control" and "supersedes" as the parser's lower-cased field names.
(defconst *fn-ctl-control-name* '(99 111 110 116 114 111 108))
(defconst *fn-ctl-supersedes-name* '(115 117 112 101 114 115 101 100 101 115))

(defun fn-ctl-field-name (field)
  (declare (xargs :guard t))
  (if (true-listp field) (fn-article-field-name field) nil))

; The fields named NAME, in order.  Guard t: it runs over any field list.
(defun fn-ctl-fields-named (name fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (if (equal (fn-ctl-field-name (car fields)) name)
          (cons (car fields) (fn-ctl-fields-named name (cdr fields)))
        (fn-ctl-fields-named name (cdr fields)))
    nil))

; ---------------------------------------------------------------------------
; control-command = verb *( 1*WSP argument )   (RFC 5536 section 3.2.3)
; verb = token (RFC 2045 section 5.1): US-ASCII, not SPACE, not a CTL, not a
; tspecial.  argument = 1*( %x21-7E ).

(defun fn-ctl-tspecialp (byte)
  (declare (xargs :guard t))
  (and (member byte '(40 41 60 62 64 44 59 58 92 34 47 91 93 63 61)) t))

(defun fn-ctl-token-charp (byte)
  (declare (xargs :guard t))
  (and (integerp byte) (<= 33 byte) (<= byte 126) (not (fn-ctl-tspecialp byte))))

(defun fn-ctl-tokenp (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (fn-ctl-token-charp (car bytes))
           (or (atom (cdr bytes)) (fn-ctl-tokenp (cdr bytes))))
    nil))

(defun fn-ctl-argument-charp (byte)
  (declare (xargs :guard t))
  (and (integerp byte) (<= 33 byte) (<= byte 126)))

(defun fn-ctl-argumentp (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (fn-ctl-argument-charp (car bytes))
           (or (atom (cdr bytes)) (fn-ctl-argumentp (cdr bytes))))
    nil))

(defun fn-ctl-argument-listp (words)
  (declare (xargs :guard t))
  (if (consp words)
      (and (fn-ctl-argumentp (car words)) (fn-ctl-argument-listp (cdr words)))
    t))

(defun fn-ctl-wspp (byte)
  (declare (xargs :guard t))
  (or (equal byte 32) (equal byte 9)))

; Maximal runs of non-WSP bytes.  Every non-WSP byte of the value lands in
; exactly one word, so checking the words checks the whole value.
(defun fn-ctl-words-aux (bytes cur acc)
  (declare (xargs :guard (and (true-listp cur) (true-listp acc))))
  (if (consp bytes)
      (if (fn-ctl-wspp (car bytes))
          (fn-ctl-words-aux (cdr bytes) nil
                            (if (consp cur) (cons (reverse cur) acc) acc))
        (fn-ctl-words-aux (cdr bytes) (cons (car bytes) cur) acc))
    (reverse (if (consp cur) (cons (reverse cur) acc) acc))))

(defun fn-ctl-words (bytes)
  (declare (xargs :guard t))
  (fn-ctl-words-aux bytes nil nil))

(defun fn-ctl-downcase (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (cons (let ((b (car bytes)))
              (if (and (integerp b) (<= 65 b) (<= b 90)) (+ b 32) b))
            (fn-ctl-downcase (cdr bytes)))
    nil))

; One Control field's command.  The grammar has SP, not FWS, after the
; colon, so a folded field (more than one raw line) is malformed.  The verb
; is compared in ASCII lower case (a local policy: the RFC gives verbs in
; lower case and says nothing of case).
(defun fn-ctl-parse-command (field)
  (declare (xargs :guard t))
  (if (not (and (true-listp field) (equal (len field) 3)))
      (list :malformed :control-syntax)
    (let ((raw-lines (fn-article-field-raw-lines field))
          (value (fn-article-field-unfolded-value field)))
      (if (not (and (consp raw-lines) (atom (cdr raw-lines))
                    (consp value) (equal (car value) 32)))
          (list :malformed :control-syntax)
        (let ((words (fn-ctl-words (cdr value))))
          (if (and (consp words)
                   (fn-ctl-tokenp (car words))
                   (fn-ctl-argument-listp (cdr words)))
              (list :control (fn-ctl-downcase (car words)) (cdr words))
            (list :malformed :control-syntax)))))))

; ---------------------------------------------------------------------------
; The classifier.  :ordinary, (:control VERB ARGS) or (:malformed REASON).

(defun fn-ctl-classify-fields (fields)
  (declare (xargs :guard t))
  (let ((controls (fn-ctl-fields-named *fn-ctl-control-name* fields)))
    (cond ((atom controls) :ordinary)
          ((consp (cdr controls)) (list :malformed :duplicate-control))
          ((consp (fn-ctl-fields-named *fn-ctl-supersedes-name* fields))
           (list :malformed :control-and-supersedes))
          (t (fn-ctl-parse-command (car controls))))))

(defun fn-ctl-classify (article)
  (declare (xargs :guard t))
  (if (true-listp article)
      (fn-ctl-classify-fields (fn-article-fields article))
    :ordinary))

; Over received octets: an article that does not parse is not classified
; here (:unparsed); every ingress refuses it at its own parse check.
(defun fn-ctl-classify-octets (received)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse received)))
    (if (fn-article-result-okp parsed)
        (fn-ctl-classify (fn-article-result-article parsed))
      :unparsed)))

; ---------------------------------------------------------------------------
; Filing groups.  control.<verb> for the verbs RFC 5537 section 5 defines and
; fn recognizes; `control' for an obsolete (section 5.6) or unknown verb.
; The group name comes from this table, never from the article's octets.

(defconst *fn-ctl-verb-groups*
  '(((99 97 110 99 101 108) . "control.cancel")
    ((110 101 119 103 114 111 117 112) . "control.newgroup")
    ((114 109 103 114 111 117 112) . "control.rmgroup")
    ((99 104 101 99 107 103 114 111 117 112 115) . "control.checkgroups")
    ((105 104 97 118 101) . "control.ihave")
    ((115 101 110 100 109 101) . "control.sendme")))

(defconst *fn-ctl-filing-groups*
  '("control" "control.cancel" "control.newgroup" "control.rmgroup"
    "control.checkgroups" "control.ihave" "control.sendme"))

(defun fn-ctl-filing-group (verb)
  (declare (xargs :guard t))
  (let ((hit (assoc-equal verb *fn-ctl-verb-groups*)))
    (if hit (cdr hit) "control")))

; Membership of a group name in the operator's domain.  Guard t.
(defun fn-ctl-memberp (name names)
  (declare (xargs :guard t))
  (if (consp names)
      (or (equal name (car names)) (fn-ctl-memberp name (cdr names)))
    nil))

; Every filing group is `control' or begins with `control.'.
(defun fn-ctl-control-group-namep (name)
  (declare (xargs :guard t))
  (and (stringp name)
       (let ((cs (coerce name 'list)))
         (or (equal cs (coerce "control" 'list))
             (and (< 8 (len cs))
                  (equal (take 8 cs) (coerce "control." 'list)))))))

(defun fn-ctl-all-control-group-namesp (names)
  (declare (xargs :guard t))
  (if (consp names)
      (and (fn-ctl-control-group-namep (car names))
           (fn-ctl-all-control-group-namesp (cdr names)))
    t))

(assert-event (fn-ctl-all-control-group-namesp *fn-ctl-filing-groups*))

(defthm fn-ctl-filing-group-is-a-filing-group
  (member-equal (fn-ctl-filing-group verb) *fn-ctl-filing-groups*))

(defthm fn-ctl-filing-group-is-a-control-group
  (fn-ctl-control-group-namep (fn-ctl-filing-group verb))
  :hints (("Goal" :in-theory (disable fn-ctl-control-group-namep))))

(defthm fn-ctl-filing-group-stringp
  (stringp (fn-ctl-filing-group verb))
  :rule-classes :type-prescription)

; ---------------------------------------------------------------------------
; KEYSTONE: the classifier reads only the Control field (and the Supersedes
; field RFC 5536 section 3.2.3 forbids beside it).  Inserting or removing
; any other field anywhere -- Subject "cmsg ...", Newsgroups naming a ".ctl"
; group, Also-Control, anything -- leaves the classification unchanged.  The
; body is not an argument at all.

(defthm fn-ctl-fields-named-of-append
  (equal (fn-ctl-fields-named name (append a b))
         (append (fn-ctl-fields-named name a) (fn-ctl-fields-named name b))))

(defthm fn-ctl-classify-reads-only-the-control-field
  (implies (and (not (equal (fn-ctl-field-name f) *fn-ctl-control-name*))
                (not (equal (fn-ctl-field-name f) *fn-ctl-supersedes-name*)))
           (equal (fn-ctl-classify-fields (append a (cons f b)))
                  (fn-ctl-classify-fields (append a b))))
  :hints (("Goal" :in-theory (disable fn-ctl-parse-command fn-ctl-field-name))))

; With no Control field an article is ordinary, whatever else it carries.
(defthm fn-ctl-classify-without-control-is-ordinary
  (implies (atom (fn-ctl-fields-named *fn-ctl-control-name* fields))
           (equal (fn-ctl-classify-fields fields) :ordinary)))

(in-theory (disable fn-ctl-classify-fields fn-ctl-parse-command
                    fn-ctl-filing-group fn-ctl-control-group-namep))
