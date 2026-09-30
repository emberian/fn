(in-package "ACL2")
(include-book "../../books/history-decode-size")

(defun hdszt-run (bytes s sizes prefix usable)
  (if (consp bytes)
      (mv-let (s sizes prefix usable) (fn-hds-feed (car bytes) s sizes prefix usable)
        (hdszt-run (cdr bytes) s sizes prefix usable))
    (list s sizes prefix usable)))

(defun hdszt-decode (bytes)
  (mv-let (s sizes prefix usable) (fn-hds-begin 0 (len bytes) 17 23)
    (hdszt-run bytes s sizes prefix usable)))

(defun hdszt-exact (bytes value)
  (let* ((r (hdszt-decode bytes)) (s (car r)) (sizes (cadr r)))
    (and (eq (car s) :done) (nth 3 r) (consp sizes) (null (cdr sizes))
         (equal (fn-hds-info-root (car sizes)) (fn-scs-summary value))
         (equal (nth 8 s) (len bytes))
         (equal (nth 10 s) 17) (equal (nth 11 s) 23))))

(assert-event
 (and (eq (symbol-class 'fn-hds-begin (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hds-feed (w state)) :common-lisp-compliant)))

; Nonempty tree, shared subtrees, all scalar shapes and canonical octet collapse.
(defconst *hdszt-tree*
  '(0 "<a@x>" 255 ("fn.test") :hstxa (1 2 3) "" #\A -256 nil))
(assert-event (hdszt-exact (fn-scc-encode *hdszt-tree*) *hdszt-tree*))

; Accepted nonminimal integer spelling must use the decoded value's width.
(assert-event (hdszt-exact '(1 2 7 0) 7))
; Both accepted NIL aliases collapse to the NIL opcode; keyword :NIL does not.
(assert-event (hdszt-exact '(4 1 1 3 78 73 76) nil))
(assert-event (hdszt-exact '(4 2 1 3 78 73 76) nil))
(assert-event (hdszt-exact '(4 0 1 3 78 73 76) :nil))
; Same length / one differing byte must not accidentally take the NIL size.
(assert-event (hdszt-exact '(4 1 1 3 78 73 77) 'nim))
; The decoder accepts zero OP6, whose canonical representation is NIL.
(assert-event (hdszt-exact '(6 0) nil))
; Uncompressed pair input is recomputed to the canonical octet-list size.
(assert-event (hdszt-exact '(1 1 1 1 1 2 0 5 5) '(1 2)))
(assert-event (hdszt-exact '(3 0) ""))

; Actual malformed stream refuses, never exposes a usable reserve.
(assert-event
 (let ((r (hdszt-decode '(5))))
   (and (eq (car (car r)) :refused) (not (nth 3 r)))))
; A corrupted size stack loses usability even though parser bytes are valid.
(assert-event
 (let* ((bytes '(1 1 1 0 5))
        (s (car (hdszt-run '(1 1 1 0) (fn-hdc-begin 0 5 17 23) nil nil t)))
        (r (mv-list 4 (fn-hds-feed 5 s nil nil t))))
   (and (equal (nth 0 r) (fn-hdc-feed 5 s))
        (eq (car (nth 0 r)) :done) (not (nth 3 r))
        (equal (len bytes) 5))))
; Once unusable, later input cannot silently bless the stale carry.
(assert-event
 (let* ((s (fn-hdc-begin 0 1 17 23))
        (r (mv-list 4 (fn-hds-feed 0 s '((999 nil nil)) nil nil))))
   (and (not nil) (not (nth 3 r))
        (equal (nth 0 r) (fn-hdc-feed 0 s)))))

; Executable witness vocabulary for the proof-only recursive relation.
(defun hdszt-info-correspondsp (info value)
  (declare (xargs :measure (acl2-count info) :verify-guards nil
                  :hints (("Goal" :in-theory
                           (e/d (fn-hds-info-car fn-hds-info-cdr fn-hds-at)
                                (fn-hds-info-root fn-scs-summary))))))
  (and (consp info)
       (equal (fn-hds-info-root info) (fn-scs-summary value))
       (if (null (cdr info)) t
         (and (consp (cdr info)) (consp value)
              (hdszt-info-correspondsp (fn-hds-info-car info) (car value))
              (hdszt-info-correspondsp (fn-hds-info-cdr info) (cdr value))))))
(defthm hdszt-info-correspondsp-is-logical-relation-by-definition
  (equal (hdszt-info-correspondsp info value)
         (fn-hds-info-correspondsp info value))
  :hints (("Goal" :induct (hdszt-info-correspondsp info value)
           :in-theory (enable fn-hds-info-correspondsp))))

; Literal pair-constructor antecedent and conclusion, nonempty shared child.
(defconst *hdszt-a* (fn-hds-info-leaf (fn-scs-summary "head")))
(defconst *hdszt-d* (fn-hds-info-leaf (fn-scs-summary '(3 4))))
(defconst *hdszt-bad-a* (fn-hds-info-leaf (fn-scs-summary nil)))
(defconst *hdszt-bad-d* (fn-hds-info-leaf (fn-scs-summary '(3))))
(assert-event
 (and (hdszt-info-correspondsp *hdszt-a* "head")
      (hdszt-info-correspondsp *hdszt-d* '(3 4))
      (hdszt-info-correspondsp (fn-hds-info-pair *hdszt-a* *hdszt-d*)
                               '("head" 3 4))))
; Corrupted annotation removes each hypothesis separately, retains the other.
(assert-event
 (and (not (hdszt-info-correspondsp *hdszt-bad-a* "head"))
      (hdszt-info-correspondsp *hdszt-d* '(3 4))
      (not (hdszt-info-correspondsp
             (fn-hds-info-pair *hdszt-bad-a* *hdszt-d*) '("head" 3 4)))))
(assert-event
 (and (hdszt-info-correspondsp *hdszt-a* "head")
      (not (hdszt-info-correspondsp *hdszt-bad-d* '(3 4)))
      (not (hdszt-info-correspondsp
             (fn-hds-info-pair *hdszt-a* *hdszt-bad-d*) '("head" 3 4)))))

; Six-field structural bootstrap over actual byte-fed borrowed descriptors.
; This is not an assertion that this fixture is a validated authority state.
(defconst *hdszt-six* '(:ok 7 ((snapshot 3)) ((verdict 5)) 3 :complete))
(defconst *hdszt-six-info*
  (car (cadr (hdszt-decode (fn-scc-encode *hdszt-six*)))))
(assert-event
 (let ((r (mv-list 2 (fn-hds-select-fields 6 *hdszt-six-info*))))
   (and (hdszt-info-correspondsp *hdszt-six-info* *hdszt-six*)
        (nth 1 r) (fn-scs-correspondsp (nth 0 r) *hdszt-six*)
        (fn-scs-fixed-carriesp 6 (nth 0 r)))))
; Omit usability: exact root-only leaf has no selected-child metadata.
(assert-event
 (let* ((info (fn-hds-info-leaf (fn-scs-summary *hdszt-six*)))
        (r (mv-list 2 (fn-hds-select-fields 6 info))))
   (and (hdszt-info-correspondsp info *hdszt-six*)
        (not (nth 1 r)) (not (fn-scs-correspondsp (nth 0 r) *hdszt-six*)))))
; Corrupted annotation: selection shape alone cannot bless a wrong field.
(assert-event
 (let* ((info (fn-hds-info-pair *hdszt-bad-a*
                               (fn-hds-info-cdr *hdszt-six-info*)))
        (r (mv-list 2 (fn-hds-select-fields 6 info))))
   (and (not (hdszt-info-correspondsp info *hdszt-six*))
        (nth 1 r) (not (fn-scs-correspondsp (nth 0 r) *hdszt-six*)))))

; Literal leaf correspondence witnesses. These are descriptor boundaries,
; not authority validation or a claim that corrupt nodes can be decoded.
(assert-event
 (and (integerp 256)
      (equal (fn-hds-leaf-carry (fn-hdc-atom 256) nil) (fn-scs-summary 256))))
; Corrupted atom descriptor: omitted scalar domain and conclusion both fail.
(assert-event
 (with-guard-checking :none
  (and (not (or (integerp '(1 2)) (characterp '(1 2))
                (stringp '(1 2)) (symbolp '(1 2))))
       (not (equal (fn-hds-leaf-carry (fn-hdc-atom '(1 2)) nil)
                    (fn-scs-summary '(1 2)))))))
(assert-event
 (and (fn-scc-octet-listp '(1 2 3)) (equal 3 (len '(1 2 3)))
      (equal (fn-hds-leaf-carry (fn-hdc-span 6 0 17 3) nil)
             (fn-scs-summary '(1 2 3)))))
; Omit octet domain, retain exact length; and vice versa.
(assert-event
 (and (not (fn-scc-octet-listp '(300))) (equal 1 (len '(300)))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span 6 0 17 1) nil)
                    (fn-scs-summary '(300))))))
(assert-event
 (and (fn-scc-octet-listp '(1 2 3)) (not (equal 2 (len '(1 2 3))))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span 6 0 17 2) nil)
                    (fn-scs-summary '(1 2 3))))))
(assert-event
 (and (stringp "ABC") (equal 3 (length "ABC"))
      (equal (fn-hds-leaf-carry (fn-hdc-span 3 0 17 3) nil)
             (fn-scs-summary "ABC"))))
(assert-event
 (and (not (stringp '(1 2 3))) (equal 3 (length '(1 2 3)))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span 3 0 17 3) nil)
                    (fn-scs-summary '(1 2 3))))))
(assert-event
 (and (stringp "ABC") (not (equal 2 (length "ABC")))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span 3 0 17 2) nil)
                    (fn-scs-summary "ABC")))))
(assert-event
 (and (symbolp 'abc) (equal 3 (length (symbol-name 'abc)))
      (iff nil (null 'abc))
      (equal (fn-hds-leaf-carry (fn-hdc-span 4 1 17 3) nil)
             (fn-scs-summary 'abc))))
(assert-event
 (with-guard-checking :none
  (and (not (symbolp "ABC")) (equal 0 (length (symbol-name "ABC")))
       (iff nil (null "ABC"))
       (not (equal (fn-hds-leaf-carry (fn-hdc-span 4 1 17 0) nil)
                    (fn-scs-summary "ABC"))))))
(assert-event
 (and (symbolp 'abc) (not (equal 2 (length (symbol-name 'abc))))
      (iff nil (null 'abc))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span 4 1 17 2) nil)
                    (fn-scs-summary 'abc)))))
(assert-event
 (and (symbolp nil) (equal 3 (length (symbol-name nil)))
      (not (iff nil (null nil)))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span 4 1 17 3) nil)
                    (fn-scs-summary nil)))))

; Literal final NIL matcher hypotheses, including matched prefix provenance.
(defun hdszt-nil-premises (s prefix name byte)
  (list (eq (nth 0 s) :payload) (equal (nth 1 s) 4)
        (member-equal (nth 2 s) '(1 2)) (equal (nth 5 s) 3)
        (equal (nth 6 s) 1) (equal prefix (equal (take 2 name) '(78 73)))
        (equal byte (nth 2 name))))
; Positive actual matcher completion.
(assert-event
 (let* ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0)
                         17 3 1 19 20 nil 17 23))
        (name '(78 73 76)) (prefix t) (byte 76)
        (hs (hdszt-nil-premises s prefix name byte)))
   (and (nth 0 hs)
        (nth 1 hs)
        (nth 2 hs)
        (nth 3 hs)
        (nth 4 hs)
        (nth 5 hs)
        (nth 6 hs)
        (equal (fn-hds-nil-byte byte s prefix) (equal (take 3 name) '(78 73 76))))))
; Corrupted matched-state/prefix witness: omit literal hypothesis 1.
(assert-event
 (let* ((s (fn-hdc-state :op 4 1 (fn-hdc-number-begin 0)
                         17 3 1 19 20 nil 17 23))
        (name '(78 73 76)) (prefix t) (byte 76)
        (hs (hdszt-nil-premises s prefix name byte)))
   (and (not (nth 0 hs))
        (nth 1 hs)
        (nth 2 hs)
        (nth 3 hs)
        (nth 4 hs)
        (nth 5 hs)
        (nth 6 hs)
        (not (equal (fn-hds-nil-byte byte s prefix) (equal (take 3 name) '(78 73 76)))))))
; Corrupted matched-state/prefix witness: omit literal hypothesis 2.
(assert-event
 (let* ((s (fn-hdc-state :payload 3 1 (fn-hdc-number-begin 0)
                         17 3 1 19 20 nil 17 23))
        (name '(78 73 76)) (prefix t) (byte 76)
        (hs (hdszt-nil-premises s prefix name byte)))
   (and (nth 0 hs)
        (not (nth 1 hs))
        (nth 2 hs)
        (nth 3 hs)
        (nth 4 hs)
        (nth 5 hs)
        (nth 6 hs)
        (not (equal (fn-hds-nil-byte byte s prefix) (equal (take 3 name) '(78 73 76)))))))
; Corrupted matched-state/prefix witness: omit literal hypothesis 3.
(assert-event
 (let* ((s (fn-hdc-state :payload 4 0 (fn-hdc-number-begin 0)
                         17 3 1 19 20 nil 17 23))
        (name '(78 73 76)) (prefix t) (byte 76)
        (hs (hdszt-nil-premises s prefix name byte)))
   (and (nth 0 hs)
        (nth 1 hs)
        (not (nth 2 hs))
        (nth 3 hs)
        (nth 4 hs)
        (nth 5 hs)
        (nth 6 hs)
        (not (equal (fn-hds-nil-byte byte s prefix) (equal (take 3 name) '(78 73 76)))))))
; Corrupted matched-state/prefix witness: omit literal hypothesis 4.
(assert-event
 (let* ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0)
                         17 4 1 19 20 nil 17 23))
        (name '(78 73 76)) (prefix t) (byte 76)
        (hs (hdszt-nil-premises s prefix name byte)))
   (and (nth 0 hs)
        (nth 1 hs)
        (nth 2 hs)
        (not (nth 3 hs))
        (nth 4 hs)
        (nth 5 hs)
        (nth 6 hs)
        (not (equal (fn-hds-nil-byte byte s prefix) (equal (take 3 name) '(78 73 76)))))))
; Corrupted matched-state/prefix witness: omit literal hypothesis 5.
(assert-event
 (let* ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0)
                         17 3 2 19 20 nil 17 23))
        (name '(78 73 76)) (prefix t) (byte 76)
        (hs (hdszt-nil-premises s prefix name byte)))
   (and (nth 0 hs)
        (nth 1 hs)
        (nth 2 hs)
        (nth 3 hs)
        (not (nth 4 hs))
        (nth 5 hs)
        (nth 6 hs)
        (not (equal (fn-hds-nil-byte byte s prefix) (equal (take 3 name) '(78 73 76)))))))
; Corrupted matched-state/prefix witness: omit literal hypothesis 6.
(assert-event
 (let* ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0)
                         17 3 1 19 20 nil 17 23))
        (name '(78 73 76)) (prefix nil) (byte 76)
        (hs (hdszt-nil-premises s prefix name byte)))
   (and (nth 0 hs)
        (nth 1 hs)
        (nth 2 hs)
        (nth 3 hs)
        (nth 4 hs)
        (not (nth 5 hs))
        (nth 6 hs)
        (not (equal (fn-hds-nil-byte byte s prefix) (equal (take 3 name) '(78 73 76)))))))
; Corrupted matched-state/prefix witness: omit literal hypothesis 7.
(assert-event
 (let* ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0)
                         17 3 1 19 20 nil 17 23))
        (name '(78 73 76)) (prefix t) (byte 77)
        (hs (hdszt-nil-premises s prefix name byte)))
   (and (nth 0 hs)
        (nth 1 hs)
        (nth 2 hs)
        (nth 3 hs)
        (nth 4 hs)
        (nth 5 hs)
        (not (nth 6 hs))
        (not (equal (fn-hds-nil-byte byte s prefix) (equal (take 3 name) '(78 73 76)))))))
