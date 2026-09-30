(in-package "ACL2")
(include-book "../../books/post-identity-source-cursor-refinement")
(include-book "../../books/records-shape")
(defun fn-psc-test-run (fuel c incoming held)
 (declare (xargs :guard (and (true-listp c) (true-listp incoming) (true-listp held)) :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (equal (fn-psc-result c) :pending))
     (if (zp fuel) c
       (let* ((d (fn-psc-demand c))
              (byte (if (and (consp d) (equal (car d) :held)) (nth (cadr d) held)
                      (if (consp d) (nth (cadr d) incoming) nil))))
        (fn-psc-test-run (1- fuel) (fn-psc-step c byte) incoming held)))
   c))
(defun fn-psc-test-agent (xs msgid)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-result (fn-psc-test-run 10000
   (fn-psc-begin :agent (len xs) msgid nil (len xs)) xs nil)))
(defun fn-psc-test-source (xs incoming agent-span msgid)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-result (fn-psc-test-run 10000
   (fn-psc-begin :source-held (len xs) msgid agent-span (len incoming))
   incoming xs)))
(assert-event
 (let* ((agent '(97 98 99)) (msgid "<a@b>")
        (xs (append (fn-inj-path-line agent) '(88 13 10))))
  (equal (fn-psc-test-agent xs msgid) '(:agent 6 9))))
(assert-event
 (let* ((agent '(97 98 99)) (msgid "<a@b>")
        (xs (append (fn-inj-injection-info-line agent) '(88 13 10))))
  (equal (fn-psc-test-agent xs msgid) '(:agent 16 19))))
(assert-event
 (let* ((agent '(97 98 99)) (msgid "<a@b>")
        (xs (append (fn-inj-path-line agent)
                    (fn-inj-injection-info-line agent) '(88 13 10)))
        (a (fn-psc-test-agent xs msgid)))
  (equal (fn-psc-test-source xs xs a msgid) '(:source 45 45 45))))

; Ghost-only descriptor projection, never used by the served parser.
(defun fn-psc-test-projection (r xs)
 (declare (xargs :guard t :verify-guards nil))
 (if (and (consp r) (equal (car r) :source))
     (cons t (append (take (- (caddr r) (cadr r)) (nthcdr (cadr r) xs))
                     (nthcdr (cadddr r) xs))) nil))
(defun fn-psc-test-exact-v2 (xs incoming agent msgid)
 (declare (xargs :guard t :verify-guards nil))
 (equal (fn-psc-test-projection
         (fn-psc-test-source xs incoming (fn-psc-test-agent incoming msgid) msgid) xs)
        (fn-inj-source-of (fn-cll-skip xs) agent (fn-record-string-octets msgid))))
(defconst *fn-psc-test-date* '(65 65 65 65 65 65 65 65 65 65 65 65 65 65 65 65
                             65 65 65 65 65 65 65 65 65 65 65 65 65 65 65))
(defconst *fn-psc-test-agent* '(97 98 99))
(defconst *fn-psc-test-body* '(88 58 32 89 13 10 13 10 0 255))
(defconst *fn-psc-test-incoming*
 (append (fn-inj-path-line *fn-psc-test-agent*)
         (fn-inj-injection-info-line *fn-psc-test-agent*) *fn-psc-test-body*))
(assert-event
 (fn-psc-test-exact-v2
  (append (fn-inj-path-line *fn-psc-test-agent*)
          (fn-inj-injection-date-line *fn-psc-test-date*)
          (fn-inj-message-id-line '(60 97 64 98 62))
          (fn-inj-date-line *fn-psc-test-date*)
          (fn-inj-injection-info-line *fn-psc-test-agent*) *fn-psc-test-body*)
  *fn-psc-test-incoming* *fn-psc-test-agent* "<a@b>"))
(assert-event
 (fn-psc-test-exact-v2
  (append (fn-inj-path-line *fn-psc-test-agent*)
          (fn-inj-injection-date-line *fn-psc-test-date*)
          (fn-inj-injection-info-line *fn-psc-test-agent*) *fn-psc-test-body*)
  *fn-psc-test-incoming* *fn-psc-test-agent* "<a@b>"))
; Ambiguous v1 authored/generated Message-ID and Date fail back exactly.
(assert-event
 (fn-psc-test-exact-v2
  (append (fn-inj-path-line *fn-psc-test-agent*)
          (fn-inj-injection-date-line *fn-psc-test-date*)
          (fn-inj-injection-info-line *fn-psc-test-agent*)
          (fn-inj-message-id-line '(60 97 64 98 62)) *fn-psc-test-body*)
  *fn-psc-test-incoming* *fn-psc-test-agent* "<a@b>"))
(assert-event
 (fn-psc-test-exact-v2
  (append (fn-inj-path-line *fn-psc-test-agent*)
          (fn-inj-injection-date-line *fn-psc-test-date*)
          (fn-inj-injection-info-line *fn-psc-test-agent*)
          (fn-inj-date-line *fn-psc-test-date*) *fn-psc-test-body*)
  *fn-psc-test-incoming* *fn-psc-test-agent* "<a@b>"))
; v3 unsplice case-insensitive Path after a retained prefix field.
(assert-event
 (fn-psc-test-exact-v2
  (append (fn-inj-injection-info-line *fn-psc-test-agent*)
          '(88 58 32 89 13 10 112 65 116 72 58 32)
          '(97 98 99 33 120 33 121 13 10 13 10 90))
  *fn-psc-test-incoming* *fn-psc-test-agent* "<a@b>"))
; Full generated line skip, authored Cancel-Lock after block is retained.
(assert-event
 (fn-psc-test-exact-v2
  (append '(67 97 110 99 101 108 45 76 111 99 107 58 32 88 13 10)
          '(67 97 110 99 101 108 45 75 101 121 58 32 89 13 10)
          *fn-psc-test-incoming*)
  *fn-psc-test-incoming* *fn-psc-test-agent* "<a@b>"))
(assert-event
 (fn-psc-test-exact-v2
  (append (fn-inj-path-line *fn-psc-test-agent*)
          (fn-inj-injection-info-line-with *fn-psc-test-agent* '(59 32 120 61 121))
          *fn-psc-test-body*)
  *fn-psc-test-incoming* *fn-psc-test-agent* "<a@b>"))
(assert-event
 (equal (fn-psc-test-agent
         (append (fn-inj-injection-info-line-with *fn-psc-test-agent*
                                                  '(59 32 120 61 121))
                 *fn-psc-test-body*) "<a@b>") '(:agent 16 19)))
; Incoming derives from the v3 block: optional fixed stamp and Message-ID.
(assert-event
 (equal (fn-psc-test-agent
  (append (fn-inj-injection-date-line *fn-psc-test-date*)
          (fn-inj-message-id-line '(60 97 64 98 62))
          (fn-inj-date-line *fn-psc-test-date*)
          (fn-inj-injection-info-line *fn-psc-test-agent*)
          *fn-psc-test-body*) "<a@b>") '(:agent 123 126)))
; A bad leading Path is not authoritative; fallback block still determines agent.
(assert-event
 (equal (fn-psc-test-agent '(80 97 116 104 58 32 120 13 10) "<a@b>") :no-source))
(assert-event
 (equal (fn-psc-test-agent '(73 110 106 101 99 116 105 111 110 45 73 110 102 111
                            58 32 97 59 120 13 88 10) "<a@b>") :no-source))
(assert-event
 (equal (fn-psc-test-agent '(73 110 106 101 99 116 105 111 110 45 73 110 102 111
                            58 32 13 10) "<a@b>") :no-source))
; One incoming agent governs held inverse: a held different agent fails source.
(assert-event
 (fn-psc-test-exact-v2
  (append (fn-inj-path-line '(120 121 122))
          (fn-inj-injection-info-line '(120 121 122)) *fn-psc-test-body*)
  *fn-psc-test-incoming* *fn-psc-test-agent* "<a@b>"))
; EOF is not a synthetic LF: malformed unterminated info stays NIL agent.
(assert-event
 (equal (fn-psc-test-agent '(73 110 106 101 99 116 105 111 110 45 73 110 102 111
                            58 32 97 98 99 13) "<a@b>") :no-source))

; Literal whole antecedent and conclusion for the general actual comparison.
(assert-event
 (let* ((incoming '(65)) (held '(65))
        (c (fn-psc-agent-compare 0 :source-found
            (fn-psc-begin :source-held 1 "<a@b>" '(:agent 0 1) 1)))
        (byte 65))
  (and (member-eq (fn-psc-get phase c) '(:compare :target))
       (natp (fn-psc-get index c)) (natp (fn-psc-get ref-len c))
       (<= (fn-psc-get index c) (fn-psc-get ref-len c))
       (or (equal (fn-psc-get phase c) :compare)
           (< (fn-psc-get index c) (fn-psc-get ref-len c)))
       (equal byte (fn-psc-model-demanded-byte c incoming held))
       (fn-psc-model-compare-value c incoming held)
       (equal (fn-psc-model-compare-value (fn-psc-step c byte) incoming held)
              (fn-psc-model-compare-value c incoming held)))))
; Exact-demand hypothesis removal: every other retained premise is true.
(assert-event
 (let* ((incoming '(65)) (held nil)
        (c (fn-psc-literal 0 '(65) :source-found
            (fn-psc-begin :source-incoming 1 "<a@b>" nil 1)))
        (byte 66))
  (and (member-eq (fn-psc-get phase c) '(:compare :target))
       (natp (fn-psc-get index c)) (natp (fn-psc-get ref-len c))
       (<= (fn-psc-get index c) (fn-psc-get ref-len c))
       (or (equal (fn-psc-get phase c) :compare)
           (< (fn-psc-get index c) (fn-psc-get ref-len c)))
       (not (equal byte (fn-psc-model-demanded-byte c incoming held)))
       (not (equal (fn-psc-model-compare-value (fn-psc-step c byte) incoming held)
                   (fn-psc-model-compare-value c incoming held))))))
(assert-event
 (let* ((c (fn-psc-agent-compare 0 :source-found
            (fn-psc-begin :source-held 1 "<a@b>" '(:agent 0 1) 1)))
        (next (fn-psc-step c 65)))
  (and (equal (len c) 24) (equal (len next) 24)
       (equal (fn-psc-configuration next) (fn-psc-configuration c))
       (fn-psc-referencep (fn-psc-get ref c))
       (fn-psc-referencep (fn-psc-get ref next))
       (<= (len (fn-psc-get ref next)) 16))))

; Arbitrary malformed agent bytes in a finite fixture matrix, against actual reference.
(defun fn-psc-test-agent-projection (r xs)
 (declare (xargs :guard t :verify-guards nil))
 (if (and (consp r) (equal (car r) :agent))
  (take (- (caddr r) (cadr r)) (nthcdr (cadr r) xs)) nil))
(defun fn-psc-test-agent-reference (xs msgid)
 (declare (xargs :guard t :verify-guards nil))
 (equal (fn-psc-test-agent-projection (fn-psc-test-agent xs msgid) xs)
        (fn-pb-path-agent xs (fn-record-string-octets msgid))))
(defun fn-psc-test-agent-fixtures (agents)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom agents) t
  (let* ((agent (car agents)) (msgid "<a@b>")
         (path (fn-inj-path-line agent))
         (info (fn-inj-injection-info-line agent)))
   (and (fn-psc-test-agent-reference path msgid)
        (fn-psc-test-agent-reference info msgid)
        (fn-psc-test-agent-reference (append path info) msgid)
        (fn-psc-test-agent-reference (append info '(59 112 13 10)) msgid)
        (fn-psc-test-agent-fixtures (cdr agents))))))
(assert-event (fn-psc-test-agent-fixtures
 '(nil (97) (13) (10) (59) (97 13) (97 10) (97 59) (59 97)
   (97 59 13) (97 59 10) (97 13 10) (97 10 13) (97 59 97)
   (97 59 13 10) (97 13 10 59) (97 10 13 59))))
; Reachable scan fixtures: the generated Cancel-Lock line starts the line scan;
; Injection-Info with a semicolon starts the parameter scan.
(assert-event
 (let* ((xs '(97 13 10 88))
        (c (fn-psc-set phase :line (fn-psc-set resume :after-lock
             (fn-psc-begin :agent (len xs) "<a@b>" nil (len xs)))))
        (byte (fn-psc-model-demanded-byte c xs nil))
        (next (fn-psc-step c byte)) (fuel (fn-psc-line-rank c))
        (done (fn-psc-model-line-run fuel c xs nil)))
  (and (equal (fn-psc-get phase c) :line)
       (natp (fn-psc-get pos c))
       (equal (fn-psc-get n c) (len (fn-psc-model-source c xs nil)))
       (<= (fn-psc-get pos c) (fn-psc-get n c))
       (equal byte (fn-psc-model-demanded-byte c xs nil))
       (equal (fn-psc-model-line-end next xs nil) (fn-psc-model-line-end c xs nil))
       (fn-psc-line-statep c xs nil) (fn-psc-line-statep next xs nil)
       (< (fn-psc-line-rank next) (fn-psc-line-rank c))
       (equal (fn-psc-model-line-end done xs nil) (fn-psc-model-line-end c xs nil))
       (natp fuel) (<= (fn-psc-line-rank c) fuel)
       (not (equal (fn-psc-get phase done) :line))
       (equal (nfix (fn-psc-get pos done))
              (+ (fn-psc-get pos c) (len (fn-pb-line (nthcdr (fn-psc-get pos c) xs))))))))
; Hypothesis removal: supplied observation must be the demanded byte.
(assert-event
 (let* ((xs '(97 13 10 88))
        (c (fn-psc-set phase :line
             (fn-psc-begin :agent (len xs) "<a@b>" nil (len xs))))
        (byte 10))
  (and (equal (fn-psc-get phase c) :line) (natp (fn-psc-get pos c))
       (equal (fn-psc-get n c) (len (fn-psc-model-source c xs nil)))
       (<= (fn-psc-get pos c) (fn-psc-get n c))
       (not (equal byte (fn-psc-model-demanded-byte c xs nil)))
       (not (equal (fn-psc-model-line-end (fn-psc-step c byte) xs nil)
                   (fn-psc-model-line-end c xs nil))))))
; Hypothesis removal: insufficient quantum yields the exact active scan.
(assert-event
 (let* ((xs '(97 13 10 88))
        (c (fn-psc-set phase :line
             (fn-psc-begin :agent (len xs) "<a@b>" nil (len xs))))
        (fuel 0))
  (and (fn-psc-line-statep c xs nil) (natp fuel)
       (not (<= (fn-psc-line-rank c) fuel))
       (equal (fn-psc-get phase (fn-psc-model-line-run fuel c xs nil)) :line))))
(assert-event
 (let* ((xs '(59 112 13 10 88))
        (c (fn-psc-set phase :params (fn-psc-set resume :info-tail
             (fn-psc-begin :source-incoming (len xs) "<a@b>" nil (len xs)))))
        (byte (fn-psc-model-demanded-byte c xs nil))
        (next (fn-psc-step c byte)) (fuel (fn-psc-param-rank c))
        (done (fn-psc-model-param-run fuel c xs nil)))
  (and (member-eq (fn-psc-get phase c) '(:params :params-lf))
       (fn-psc-line-statep c xs nil)
       (equal byte (fn-psc-model-demanded-byte c xs nil))
       (equal (fn-psc-model-param-value next xs nil) (fn-psc-model-param-value c xs nil))
       (fn-psc-line-statep next xs nil)
       (< (fn-psc-param-rank next) (fn-psc-param-rank c))
       (equal (fn-psc-model-param-value done xs nil) (fn-psc-model-param-value c xs nil))
       (natp fuel) (<= (fn-psc-param-rank c) fuel)
       (not (member-eq (fn-psc-get phase done) '(:params :params-lf)))
       (equal (fn-psc-model-param-value done xs nil) '(88)))))
; Hypothesis removal: wrong supplied LF refuses an otherwise valid parameter tail.
(assert-event
 (let* ((xs '(59 112 13 10 88))
        (c (fn-psc-set phase :params
             (fn-psc-begin :source-incoming (len xs) "<a@b>" nil (len xs))))
        (byte 10))
  (and (member-eq (fn-psc-get phase c) '(:params :params-lf))
       (fn-psc-line-statep c xs nil)
       (not (equal byte (fn-psc-model-demanded-byte c xs nil)))
       (not (equal (fn-psc-model-param-value (fn-psc-step c byte) xs nil)
                   (fn-psc-model-param-value c xs nil))))))
(assert-event
 (let* ((xs '(59 112 13 10 88))
        (c (fn-psc-set phase :params
             (fn-psc-begin :source-incoming (len xs) "<a@b>" nil (len xs))))
        (fuel 0))
  (and (fn-psc-line-statep c xs nil) (natp fuel)
       (not (<= (fn-psc-param-rank c) fuel))
       (member-eq (fn-psc-get phase (fn-psc-model-param-run fuel c xs nil)) '(:params :params-lf)))))

(assert-event
 (let* ((xs '(97 98 13 10))
        (c (fn-psc-compare 0 '(97 98) 0 2 :agent-path-field
             (fn-psc-begin :agent (len xs) "<a@b>" nil (len xs))))
        (fuel (fn-psc-comparison-rank c))
        (done (fn-psc-model-comparison-run fuel c xs nil)))
  (and (equal (fn-psc-get phase c) :compare)
       (fn-psc-comparison-statep c) (natp (fn-psc-get pos c))
       (not (equal (fn-psc-get ref c) :path))
       (true-listp (fn-psc-model-source c xs nil))
       (equal (fn-psc-get n c) (len (fn-psc-model-source c xs nil)))
       (<= (fn-psc-get pos c) (fn-psc-get n c))
       (natp fuel) (<= (fn-psc-comparison-rank c) fuel)
       (equal (fn-psc-get phase done) :control)
       (equal (if (fn-psc-get ok done) t nil) (fn-psc-model-compare-value c xs nil))
       (equal (if (fn-psc-get ok done) t nil)
        (not (equal (fn-inj-strip
         (fn-psc-model-reference-octets
          (nfix (- (fn-psc-get ref-len c) (fn-psc-get index c)))
          (fn-psc-get index c) c xs nil)
         (nthcdr (fn-psc-get pos c) (fn-psc-model-source c xs nil))) :no)))
       (fn-psc-comparison-positionp c) (fn-psc-comparison-positionp done)
       (equal (fn-psc-comparison-origin done) (fn-psc-comparison-origin c))
       (fn-psc-get ok done)
       (equal (fn-psc-get pos done) (+ (fn-psc-get base c) (fn-psc-get ref-len c))))))
; Hypothesis removal: improper source sentinel, every other strip premise retained.
(assert-event
 (with-guard-checking :none
 (let* ((xs :no)
        (c (fn-psc-compare 0 nil 0 0 :agent-path-field
             (fn-psc-begin :agent (len xs) "<a@b>" nil (len xs))))
        (remaining 0) (index 0) (pos 0))
  (and (not (equal (fn-psc-get ref c) :path)) (natp pos) (natp index)
       (not (true-listp (fn-psc-model-source c xs nil)))
       (equal (fn-psc-get n c) (len (fn-psc-model-source c xs nil)))
       (<= pos (fn-psc-get n c))
       (not (equal (fn-psc-model-prefix remaining index pos c xs nil)
                   (not (equal
                    (fn-inj-strip (fn-psc-model-reference-octets remaining index c xs nil)
                     (nthcdr pos (fn-psc-model-source c xs nil))) :no)))))))
)
; Corrupted-state witness: the origin/position relation cannot be discarded.
(assert-event
 (let* ((xs '(97 98 13 10))
        (c (fn-psc-set base 99
             (fn-psc-compare 0 '(97 98) 0 2 :agent-path-field
              (fn-psc-begin :agent (len xs) "<a@b>" nil (len xs)))))
        (fuel (fn-psc-comparison-rank c))
        (done (fn-psc-model-comparison-run fuel c xs nil)))
  (and (fn-psc-comparison-statep c)
       (not (fn-psc-comparison-positionp c))
       (member-eq (fn-psc-get phase c) '(:compare :target))
       (natp fuel) (<= (fn-psc-comparison-rank c) fuel)
       (fn-psc-get ok done)
       (not (equal (fn-psc-get pos done) (+ (fn-psc-get base c) (fn-psc-get ref-len c)))))))
(assert-event
 (let* ((xs '(97 59 112 13 10 88))
        (c (fn-psc-set phase :line (fn-psc-set resume :agent-info-line
             (fn-psc-begin :agent (len xs) "<a@b>" nil (len xs)))))
        (done (fn-psc-model-line-complete c xs nil)))
  (and (fn-psc-line-statep c xs nil) (equal (fn-psc-get phase c) :line)
       (equal (fn-psc-get phase done) :control)
       (equal (fn-psc-get prev done) (fn-psc-model-line-prev c xs nil))
       (equal (fn-psc-get semi done) (fn-psc-model-line-semi c xs nil))
       (equal (if (fn-psc-get ok done) t nil) (fn-psc-model-line-ok c xs nil))
       (equal (fn-psc-get prev done) 13) (equal (fn-psc-get semi done) 1)
       (equal done (fn-psc-model-byte-run (fn-psc-model-line-cost c xs nil) c xs nil))
       (equal (fn-psc-model-macro-run 2 c xs nil)
              (fn-psc-model-byte-run (fn-psc-model-macro-charge 2 c xs nil) c xs nil)))))
(assert-event
 (let* ((xs '(97 98))
        (c (fn-psc-return nil (fn-psc-set resume :source-v1-date
             (fn-psc-begin :source-incoming (len xs) "<a@b>" nil (len xs)))))
        (d (fn-psc-set pos 999 c)) (fuel 8))
  (and (equal (fn-psc-get phase c) :control) (not (fn-psc-get ok c))
       (fn-psc-failed-direct-resumep (fn-psc-get resume c))
       (equal (fn-psc-result (fn-psc-model-byte-run fuel c xs nil))
              (fn-psc-result (fn-psc-model-byte-run fuel d xs nil))))))
(assert-event
 (let* ((xs '(97 98))
        (c (fn-psc-return nil (fn-psc-set resume :date-content
            (fn-psc-set aux :source-v1-date
             (fn-psc-begin :source-incoming (len xs) "<a@b>" nil (len xs))))))
        (d (fn-psc-set pos 999 c)) (fuel 9))
  (and (equal (fn-psc-get phase c) :control) (not (fn-psc-get ok c))
       (fn-psc-failed-wrapper-resumep (fn-psc-get resume c))
       (fn-psc-failed-direct-resumep (fn-psc-get aux c))
       (equal (fn-psc-result (fn-psc-model-byte-run fuel c xs nil))
              (fn-psc-result (fn-psc-model-byte-run fuel d xs nil))))))
(assert-event
 (let* ((xs '(97 98 13 10)) (bytes '(97 98))
        (base (fn-psc-begin :source-incoming (len xs) "<a@b>" nil (len xs)))
        (c (fn-psc-literal 0 bytes :source-v1-date base))
        (done (fn-psc-model-comparison-complete c xs nil)) (fuel 8))
  (and (true-listp bytes) (natp 0) (true-listp (fn-psc-model-source base xs nil))
       (equal (fn-psc-get n base) (len (fn-psc-model-source base xs nil)))
       (equal (fn-psc-model-compare-value c xs nil)
              (not (equal (fn-inj-strip bytes (nthcdr 0 xs)) :no)))
       (fn-psc-comparison-statep c) (fn-psc-comparison-positionp c)
       (member-eq (fn-psc-get phase c) '(:compare :target))
       (fn-psc-failed-direct-resumep (fn-psc-get resume c))
       (fn-psc-model-equivalent done
        (fn-psc-return (fn-psc-get ok done) (fn-psc-set pos (fn-psc-get pos done) c)))
       (equal (fn-psc-result (fn-psc-model-byte-run fuel done xs nil))
              (fn-psc-result (fn-psc-model-byte-run fuel
                 (fn-psc-model-comparison-callback c xs nil) xs nil))))))
; Positive malformed-position case: no narrowing to POS<=source extent.
(assert-event
 (let* ((xs '(97 98)) (bytes '(97))
        (c (fn-psc-begin :agent (len xs) "" nil (len xs))) (pos 999))
  (and (true-listp bytes) (natp pos) (true-listp (fn-psc-model-source c xs nil))
       (equal (fn-psc-get n c) (len (fn-psc-model-source c xs nil)))
       (> pos (fn-psc-get n c))
       (equal (fn-psc-model-compare-value (fn-psc-literal pos bytes :agent-path-field c) xs nil)
              (not (equal (fn-inj-strip bytes (nthcdr pos xs)) :no)))
       (not (fn-psc-model-compare-value (fn-psc-literal pos bytes :agent-path-field c) xs nil)))))
(assert-event
 (let* ((incoming '(97 98 13 10)) (held '(120 121 13 10))
        (span '(:agent 0 2)) (fuel 25)
        (ci (fn-psc-begin :source-incoming (len incoming) "<a@b>" span (len incoming)))
        (ch (fn-psc-begin :source-held (len held) "<a@b>" span (len incoming)))
        (di (fn-psc-model-byte-run fuel ci incoming held))
        (dh (fn-psc-model-byte-run fuel ch incoming held)))
  (and (fn-psc-source-resumep ci) (fn-psc-source-resumep ch)
       (fn-psc-source-resumep (fn-psc-step ci nil))
       (equal (fn-psc-get agent-start (fn-psc-step ci nil)) (fn-psc-get agent-start ci))
       (equal (fn-psc-get agent-end (fn-psc-step ci nil)) (fn-psc-get agent-end ci))
       (fn-psc-source-resumep di) (fn-psc-source-resumep dh)
       (member-eq :source-incoming '(:source-incoming :source-held))
       (member-eq :source-held '(:source-incoming :source-held))
       (equal (fn-psc-get agent-start di) (nfix (cadr span)))
       (equal (fn-psc-get agent-end di) (nfix (caddr span)))
       (equal (fn-psc-get agent-start dh) (nfix (cadr span)))
       (equal (fn-psc-get agent-end dh) (nfix (caddr span))))))

(assert-event
 (let* ((xs (append *fn-inj-injection-info-field* '(97 13 10)))
        (begin (fn-psc-begin :agent (len xs) "<a@b>" nil (len xs)))
        (c (fn-psc-model-macro-run 16 begin xs nil))
        (fuel (fn-psc-model-macro-charge 17 begin xs nil))
        (done (fn-psc-model-byte-run fuel begin xs nil)))
  (and (equal c (fn-psc-model-byte-run
                 (fn-psc-model-macro-charge 16 begin xs nil) begin xs nil))
       (equal (fn-psc-get phase c) :control)
       (equal (fn-psc-get resume c) :agent-info-field) (fn-psc-get ok c)
       (not (fn-psc-source-resumep c))
       (not (equal (fn-psc-get agent-start (fn-psc-step c nil)) (fn-psc-get agent-start c)))
       (not (member-eq :agent '(:source-incoming :source-held)))
       (not (equal (fn-psc-get agent-start done) (nfix (cadr nil)))))))

(assert-event
 (let* ((xs (append *fn-inj-injection-info-field* '(97 59 112 13 10)))
        (begin (fn-psc-begin :agent (len xs) "<a@b>" nil (len xs)))
        (c (fn-psc-model-macro-run 19 begin xs nil))
        (done (fn-psc-step (fn-psc-model-param-complete c xs nil) nil))
        (agent '(97)) (params '(59 112 13 10)))
  (and (equal (fn-psc-get phase c) :params)
       (equal (fn-psc-get resume c) :agent-params)
       (fn-psc-line-statep c xs nil) (true-listp (fn-psc-model-source c xs nil))
       (equal (fn-psc-get phase done) :done)
       (equal (fn-psc-result done)
        (if (equal (fn-inj-param-rest (nthcdr (fn-psc-get pos c) xs)) :no)
            :no-source (list :agent (fn-psc-get agent-start c) (fn-psc-get agent-end c))))
       (consp agent) (true-listp agent) (not (member-equal 10 agent)) (not (member-equal 59 agent))
       (true-listp params) (consp params) (equal (car params) 59)
       (equal (fn-pb-params-line-agent (fn-pb-line (append *fn-inj-injection-info-field* (append agent params))))
              (if (equal (fn-inj-param-rest params) :no) nil agent))
       (equal (fn-pb-path-agent xs (fn-record-string-octets "<a@b>")) agent)
       (equal (fn-psc-result done) '(:agent 16 17)))))
(defun fn-psc-test-path-entry (fuel c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (and (equal (fn-psc-get phase c) :path-scan) (fn-psc-get aux c))) c
  (fn-psc-test-path-entry (1- fuel)
   (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held)))
; Reachable positive: actual source controller, retained prefix, mixed-case Path.
(defthm fn-psc-path-finder-reachable-positive
 (let* ((incoming *fn-psc-test-incoming*)
        (xs (append (fn-inj-injection-info-line *fn-psc-test-agent*)
               '(88 58 32 89 13 10 112 65 116 72 58 32 97 98 99 33 120 13 10)))
        (begin (fn-psc-begin :source-held (len xs) "<a@b>" '(:agent 6 9) (len incoming)))
        (c (fn-psc-test-path-entry 1000 begin incoming xs))
        (done (fn-psc-model-path-finder-complete c incoming xs)))
  (and (equal (fn-psc-get phase c) :path-scan) (fn-psc-get aux c)
       (fn-psc-path-finder-statep c incoming xs) (fn-psc-path-finder-activep c)
       (fn-psc-path-finder-statep (fn-psc-step c nil) incoming xs)
       (< (fn-psc-path-finder-rank (fn-psc-step c nil)) (fn-psc-path-finder-rank c))
       (not (fn-psc-path-finder-activep done)) (fn-psc-path-finder-statep done incoming xs)
       (equal (fn-psc-model-path-finder-result done)
              (fn-pbb-path-scan (fn-psc-get pos c) t xs))
       (equal (fn-psc-model-path-finder-result done) 33)
       (equal done (fn-psc-model-byte-run (fn-psc-model-path-finder-cost c incoming xs) c incoming xs))))
 :rule-classes nil)
; Hypothesis removal: exact supplied byte, with every retained comparison premise.
(assert-event
 (let* ((incoming *fn-psc-test-incoming*)
        (xs (append (fn-inj-injection-info-line *fn-psc-test-agent*)
                    '(80 97 116 104 58 32 97 98 99 33 120 13 10)))
        (begin (fn-psc-begin :source-held (len xs) "<a@b>" '(:agent 6 9) (len incoming)))
        (entry (fn-psc-test-path-entry 1000 begin incoming xs))
        (c (fn-psc-step entry nil)) (bad 0))
  (and (fn-psc-path-finder-statep c incoming xs)
       (equal (fn-psc-get phase c) :compare)
       (not (equal bad (fn-psc-model-demanded-byte c incoming xs)))
       (not (equal (fn-psc-model-path-finder-value (fn-psc-step c bad) incoming xs)
                   (fn-psc-model-path-finder-value c incoming xs))))))
; Literal full-premise v3 composition and exact actual paid trace.
(defthm fn-psc-v3-unsplice-reachable-positive
 (let* ((incoming *fn-psc-test-incoming*)
        (xs (append (fn-inj-injection-info-line *fn-psc-test-agent*)
               '(88 58 32 89 13 10 112 65 116 72 58 32 97 98 99 33 120 13 10)))
        (begin (fn-psc-begin :source-held (len xs) "<a@b>" '(:agent 6 9) (len incoming)))
        (c (fn-psc-test-path-entry 1000 begin incoming xs))
        (agent (fn-inj-take (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))
                           (nthcdr (fn-psc-get agent-start c) incoming)))
        (desc (fn-pbb-unsplice-at (fn-psc-get k c) agent xs))
        (done (fn-psc-model-v3-unsplice-complete c incoming xs)))
  (and (fn-psc-path-finder-statep c incoming xs)
       (equal (fn-psc-get phase c) :path-scan) (fn-psc-get aux c)
       (equal (fn-psc-get k c) (fn-psc-get pos c))
       (true-listp incoming) (natp (fn-psc-get agent-start c)) (natp (fn-psc-get agent-end c))
       (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
       (<= (fn-psc-get agent-end c) (len incoming))
       (equal (fn-psc-result done) (if desc (cons :source desc) :no-source))
       (equal (fn-psc-result done) '(:source 21 33 37))
       (equal done (fn-psc-model-byte-run (fn-psc-model-v3-unsplice-cost c incoming xs) c incoming xs))))
 :rule-classes nil)
; Positive empty incoming-derived agent: NIL still compares the literal bang.
(defthm fn-psc-v3-unsplice-empty-agent-positive
 (let* ((incoming nil)
        (xs (append (fn-inj-injection-info-line nil) '(80 97 116 104 58 32 33 120 13 10)))
        (begin (fn-psc-begin :source-held (len xs) "<a@b>" '(:agent 0 0) 0))
        (c (fn-psc-test-path-entry 1000 begin incoming xs))
        (desc (fn-pbb-unsplice-at (fn-psc-get k c) nil xs))
        (done (fn-psc-model-v3-unsplice-complete c incoming xs)))
  (and (fn-psc-path-finder-statep c incoming xs)
       (equal (fn-psc-get phase c) :path-scan) (fn-psc-get aux c)
       (equal (fn-psc-get k c) (fn-psc-get pos c)) (true-listp incoming)
       (natp (fn-psc-get agent-start c)) (natp (fn-psc-get agent-end c))
       (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
       (<= (fn-psc-get agent-end c) (len incoming))
       (equal (fn-psc-result done) (if desc (cons :source desc) :no-source))
       (equal done (fn-psc-model-byte-run (fn-psc-model-v3-unsplice-cost c incoming xs) c incoming xs))))
 :rule-classes nil)
; Corrupted span / hypothesis removal: incoming extent, all retained strip premises.
(defthm fn-psc-unsplice-incoming-extent-removal
 (let* ((incoming '(97)) (held '(97 33)) (pos 0)
        (c (fn-psc-set agent-end 2
            (fn-psc-begin :source-held 2 "" '(:agent 0 1) 1)))
        (agent (fn-inj-take (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))
                           (nthcdr (fn-psc-get agent-start c) incoming)))
        (b (fn-pbb-strip-at (fn-inj-path-insert agent) pos held))
        (entry (fn-psc-agent-compare pos :unsplice-agent (fn-psc-set date pos c)))
        (actual (fn-psc-result (fn-psc-model-byte-run 4
                   (fn-psc-model-comparison-complete entry incoming held) incoming held))))
  (and (natp pos) (true-listp incoming) (natp (fn-psc-get agent-start c))
       (natp (fn-psc-get agent-end c)) (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
       (not (<= (fn-psc-get agent-end c) (len incoming)))
       (true-listp (fn-psc-model-source c incoming held))
       (<= pos (len (fn-psc-model-source c incoming held)))
       (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
       (not (equal actual (if (equal b :no) :no-source (list :source (fn-psc-get k c) pos b))))))
 :rule-classes nil)
(defthm fn-psc-leading-path-positive-literal
 (let* ((incoming (append (fn-inj-path-line '(97 98 99)) '(88 13 10)))
        (begin (fn-psc-begin :agent (len incoming) "<a@b>" nil (len incoming)))
        (c (fn-psc-model-byte-run 13 begin incoming nil))
        (a (fn-psc-get pos c))
        (end (+ a (len (fn-pb-line (nthcdr a incoming))) -15))
        (agent (fn-pb-path-line-agent (nthcdr (fn-psc-get skip c) incoming))))
  (and (fn-psc-leading-path-statep c incoming)
       (equal (fn-psc-result (fn-psc-model-leading-path-complete c incoming))
              (if agent (list :agent a end) :pending))
       (implies agent (equal (fn-inj-take (- end a) (nthcdr a incoming)) agent))
       (equal agent '(97 98 99))
       (equal (fn-psc-result (fn-psc-model-leading-path-complete c incoming)) '(:agent 6 9))))
 :rule-classes nil)
(defthm fn-psc-leading-path-malformed-tail-literal
 (let* ((incoming '(80 97 116 104 58 32 97 98 99 33 110 111 116 45 102 111 114 45 109 97 105 108 13 88 10))
        (begin (fn-psc-begin :agent (len incoming) "<a@b>" nil (len incoming)))
        (c (fn-psc-model-byte-run 13 begin incoming nil))
        (a (fn-psc-get pos c))
        (end (+ a (len (fn-pb-line (nthcdr a incoming))) -15))
        (agent (fn-pb-path-line-agent (nthcdr (fn-psc-get skip c) incoming))))
  (and (fn-psc-leading-path-statep c incoming)
       (equal (fn-psc-result (fn-psc-model-leading-path-complete c incoming))
              (if agent (list :agent a end) :pending))
       (implies agent (equal (fn-inj-take (- end a) (nthcdr a incoming)) agent))
       (not agent)
       (equal (fn-psc-get resume (fn-psc-model-leading-path-complete c incoming)) :agent-stamp)))
 :rule-classes nil)
; Corrupted state: remove only the source extent equality.
(defthm fn-psc-leading-path-source-extent-removal
 (let* ((incoming (fn-inj-path-line '(97 98 99)))
        (begin (fn-psc-begin :agent (len incoming) "<a@b>" nil (len incoming)))
        (c (fn-psc-set n 6 (fn-psc-model-byte-run 13 begin incoming nil)))
        (a (fn-psc-get pos c))
        (end (+ a (len (fn-pb-line (nthcdr a incoming))) -15))
        (agent (fn-pb-path-line-agent (nthcdr (fn-psc-get skip c) incoming))))
  (and (equal (fn-psc-get mode c) :agent) (equal (fn-psc-get phase c) :control)
       (equal (fn-psc-get resume c) :agent-path-field) (fn-psc-get ok c)
       (true-listp incoming) (not (equal (fn-psc-get n c) (len incoming)))
       (natp (fn-psc-get pos c)) (<= (fn-psc-get pos c) (len incoming))
       (natp (fn-psc-get skip c)) (equal (fn-psc-get pos c) (+ 6 (fn-psc-get skip c)))
       (not (equal (fn-inj-strip *fn-inj-path-field* (nthcdr (fn-psc-get skip c) incoming)) :no))
       (not (and (equal (fn-psc-result (fn-psc-model-leading-path-complete c incoming))
                        (if agent (list :agent a end) :pending))
                 (implies agent (equal (fn-inj-take (- end a) (nthcdr a incoming)) agent))))))
 :rule-classes nil)
(defthm fn-psc-leading-path-actual-trace-positive-literal
 (let* ((incoming (append (fn-inj-path-line '(97 98 99)) '(88 13 10)))
        (begin (fn-psc-begin :agent (len incoming) "<a@b>" nil (len incoming)))
        (c (fn-psc-model-byte-run 13 begin incoming nil)))
  (and (fn-psc-leading-path-statep c incoming)
       (equal (fn-psc-model-leading-path-complete c incoming)
              (fn-psc-model-byte-run (fn-psc-model-leading-path-cost c incoming) c incoming nil))))
 :rule-classes nil)
