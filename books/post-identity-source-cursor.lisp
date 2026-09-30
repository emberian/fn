; D25 bounded virtual-source inverse. Every call performs one byte demand or
; one fixed control transition. The incoming agent is retained as a span.
(in-package "ACL2")
(include-book "injection")
(include-book "cancel-lock-lines")

; Fixed state slots; no source octets or variable-size agent are retained.
(defmacro fn-psc-get (field c)
 (list 'nth (cdr (assoc-eq field '((phase . 0)(mode . 1)(n . 2)(incoming-n . 3)
 (msgid . 4)(agent-start . 5)(agent-end . 6)(pos . 7)(base . 8)(ref . 9)
 (ref-start . 10)(ref-len . 11)(index . 12)(cached . 13)(resume . 14)(ok . 15)
 (skip . 16)(date . 17)(k . 18)(has-path . 19)(aux . 20)(prev . 21)
 (semi . 22)(result . 23)))) c))
(defmacro fn-psc-set (field value c)
 (list 'update-nth (cdr (assoc-eq field '((phase . 0)(mode . 1)(n . 2)(incoming-n . 3)
 (msgid . 4)(agent-start . 5)(agent-end . 6)(pos . 7)(base . 8)(ref . 9)
 (ref-start . 10)(ref-len . 11)(index . 12)(cached . 13)(resume . 14)(ok . 15)
 (skip . 16)(date . 17)(k . 18)(has-path . 19)(aux . 20)(prev . 21)
 (semi . 22)(result . 23)))) value c))

(defun fn-psc-finish (result c)
 (declare (xargs :guard (true-listp c)))
 (fn-psc-set phase :done (fn-psc-set result result c)))
(defun fn-psc-compare (pos ref start count resume c)
 (declare (xargs :guard (true-listp c)))
 (fn-psc-set phase :compare
 (fn-psc-set pos (nfix pos) (fn-psc-set base (nfix pos)
 (fn-psc-set ref ref (fn-psc-set ref-start (nfix start)
 (fn-psc-set ref-len (nfix count) (fn-psc-set index 0
 (fn-psc-set resume resume c)))))))))
(defun fn-psc-literal (pos bytes resume c)
 (declare (xargs :guard (true-listp c)))
 (fn-psc-compare pos bytes 0 (len bytes) resume c))
(defun fn-psc-return (ok c)
 (declare (xargs :guard (true-listp c)))
 (fn-psc-set phase :control (fn-psc-set ok ok c)))
(defun fn-psc-agent-compare (pos resume c)
 (declare (xargs :guard (true-listp c)))
 (fn-psc-compare pos :incoming (fn-psc-get agent-start c)
  (nfix (- (nfix (fn-psc-get agent-end c))
           (nfix (fn-psc-get agent-start c)))) resume c))
(defun fn-psc-msgid-compare (pos resume c)
 (declare (xargs :guard (true-listp c)))
 (fn-psc-literal pos *fn-inj-message-id-field* :msgid-field
  (fn-psc-set k (nfix pos) (fn-psc-set aux resume c))))
(defun fn-psc-date-compare (pos resume c)
 (declare (xargs :guard (true-listp c)))
 (fn-psc-literal pos *fn-inj-date-field* :date-field
  (fn-psc-set k (nfix pos) (fn-psc-set aux resume c))))
(defun fn-psc-info-compare (pos resume c)
 (declare (xargs :guard (true-listp c)))
 (fn-psc-literal pos *fn-inj-injection-info-field* :info-field
  (fn-psc-set aux resume c)))

(defun fn-psc-begin (mode n msgid agent-span incoming-n)
 (declare (xargs :guard (true-listp agent-span)))
 (let ((c (list :control mode (nfix n) (nfix incoming-n)
               (if (stringp msgid) msgid "")
               (nfix (cadr agent-span)) (nfix (caddr agent-span))
               0 0 nil 0 0 0 nil :start nil 0 0 0 nil nil nil nil :pending)))
  (if (and (member-eq mode '(:agent :source-incoming :source-held))
           (or (equal mode :agent)
               (and (<= (nfix (cadr agent-span)) (nfix (caddr agent-span)))
                    (<= (nfix (caddr agent-span)) (nfix incoming-n)))))
      c (fn-psc-finish :no-source c))))

(defun fn-psc-demand (c)
 (declare (xargs :guard (true-listp c)))
 (let* ((phase (fn-psc-get phase c))
        (pos (nfix (fn-psc-get pos c))) (n (nfix (fn-psc-get n c)))
        (ref (fn-psc-get ref c))
        (index (nfix (fn-psc-get index c)))
        (count (nfix (fn-psc-get ref-len c))))
  (cond ((equal phase :done) :none)
        ((equal phase :control) :control)
        ((and (equal phase :path-scan) (fn-psc-get aux c)) :control)
        ((and (equal phase :compare) (< index count) (< pos n)
              (member-eq ref '(:incoming :self)))
         (list (if (or (equal ref :incoming)
                       (not (equal (fn-psc-get mode c) :source-held)))
                   :incoming :held)
               (+ (nfix (fn-psc-get ref-start c)) index)))
        ((and (member-eq phase '(:compare :target :line :params :params-lf
                                 :info-choice :path-scan :path-cr))
              (< pos n)
              (or (not (equal phase :compare)) (< index count)))
         (list (if (equal (fn-psc-get mode c) :source-held) :held :incoming) pos))
        (t :control))))

(defun fn-psc-result (c)
 (declare (xargs :guard (true-listp c)))
 (if (equal (fn-psc-get phase c) :done) (fn-psc-get result c) :pending))

; Byte comparison never constructs the requested agent, date, or message ID.
(defun fn-psc-expected (c)
 (declare (xargs :guard (true-listp c)))
 (let* ((i (+ (nfix (fn-psc-get ref-start c))
              (nfix (fn-psc-get index c))))
        (ref (fn-psc-get ref c)) (msgid (fn-psc-get msgid c)))
  (if (equal ref :msgid)
      (if (and (stringp msgid) (< i (length msgid)))
          (char-code (char msgid i)) nil)
    (if (equal ref :path) (nth i '(112 97 116 104 58 32))
      (if (true-listp ref) (nth i ref) nil)))))

; All continuations below are fixed control transitions, charged by caller.
(defun fn-psc-control (c)
 (declare (xargs :guard (true-listp c)))
 (let* ((r (fn-psc-get resume c)) (ok (fn-psc-get ok c))
        (p (nfix (fn-psc-get pos c))) (b (nfix (fn-psc-get base c)))
        (s (nfix (fn-psc-get skip c))) (n (nfix (fn-psc-get n c)))
        (mode (fn-psc-get mode c)))
  (case r
   (:start (fn-psc-literal 0 *fn-cll-lock-field* :skip-lock c))
   (:skip-lock
    (if ok (fn-psc-set phase :line (fn-psc-set resume :after-lock c))
      (fn-psc-literal 0 *fn-cll-key-field* :skip-key c)))
   (:after-lock (fn-psc-literal p *fn-cll-key-field* :skip-key c))
   (:skip-key
    (if ok (fn-psc-set phase :line (fn-psc-set resume :after-key c))
      (fn-psc-return t (fn-psc-set resume :after-key
                       (fn-psc-set pos b c)))))
   (:after-key
    (let ((c (fn-psc-set skip p c)))
     (if (equal mode :agent)
         (fn-psc-literal p *fn-inj-path-field* :agent-path-field c)
       (fn-psc-literal p *fn-inj-path-field* :source-path-field c))))
   (:agent-path-field
    (if ok (fn-psc-set phase :line (fn-psc-set resume :agent-path-line
            (fn-psc-set agent-start p c)))
      (fn-psc-literal s *fn-inj-injection-date-field* :agent-stamp c)))
   (:agent-path-line
    (let ((a (nfix (fn-psc-get agent-start c))))
     (if (< (+ a 15) p)
         (fn-psc-literal (- p 15) '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
          :agent-path-tail (fn-psc-set agent-end (- p 15) c))
       (fn-psc-literal s *fn-inj-injection-date-field* :agent-stamp c))))
   (:agent-path-tail
    (if ok (fn-psc-finish (list :agent (fn-psc-get agent-start c)
                                     (fn-psc-get agent-end c)) c)
      (fn-psc-literal s *fn-inj-injection-date-field* :agent-stamp c)))
   (:agent-stamp
    (fn-psc-msgid-compare (if ok (min (+ s 49) n) s) :agent-msgid c))
   (:agent-msgid
    (fn-psc-literal (if ok p (nfix (fn-psc-get k c)))
                    *fn-inj-date-field* :agent-date c))
   (:agent-date
    (fn-psc-literal (if ok (min (+ b 39) n) b)
                    *fn-inj-injection-info-field* :agent-info-field c))
   (:agent-info-field
    (if ok (fn-psc-set phase :line (fn-psc-set resume :agent-info-line
            (fn-psc-set agent-start p (fn-psc-set semi nil
            (fn-psc-set prev nil c)))))
      (fn-psc-finish :no-source c)))
   (:agent-info-line
    (let ((a (nfix (fn-psc-get agent-start c))) (semi (fn-psc-get semi c)))
     (if (and ok (equal (fn-psc-get prev c) 13) (< (+ a 2) p))
         (if semi
             (if (< a (nfix semi))
                 (fn-psc-set phase :params (fn-psc-set pos (nfix semi)
                  (fn-psc-set agent-end semi (fn-psc-set resume :agent-params c))))
               (fn-psc-finish :no-source c))
           (fn-psc-finish (list :agent a (- p 2)) c))
       (fn-psc-finish :no-source c))))
   (:agent-params
    (if ok (fn-psc-finish (list :agent (fn-psc-get agent-start c)
                                     (fn-psc-get agent-end c)) c)
      (fn-psc-finish :no-source c)))
   (:source-path-field
    (if ok (fn-psc-agent-compare p :source-path-agent c)
      (fn-psc-literal s *fn-inj-injection-date-field* :source-stamp
                      (fn-psc-set has-path nil c))))
   (:source-path-agent
    (if ok (fn-psc-literal p '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
                           :source-path-tail c)
      (fn-psc-literal s *fn-inj-injection-date-field* :source-stamp
                      (fn-psc-set has-path nil c))))
   (:source-path-tail
    (fn-psc-literal (if ok p s) *fn-inj-injection-date-field* :source-stamp
                   (fn-psc-set has-path ok c)))
   (:source-stamp
    (if ok (fn-psc-literal (+ p 31) '(13 10) :source-stamp-tail
                          (fn-psc-set date p c))
      (fn-psc-info-compare b :source-info-simple c)))
   (:source-stamp-tail
    (if ok (fn-psc-info-compare p :source-info-v1 (fn-psc-set k p c))
      (fn-psc-finish :no-source c)))
   (:source-info-simple
    (if ok (fn-psc-return t (fn-psc-set resume :source-found c))
      (fn-psc-finish :no-source c)))
   (:source-info-v1
    (if ok (fn-psc-msgid-compare p :source-v1-msgid (fn-psc-set k p c))
      (fn-psc-msgid-compare (fn-psc-get k c) :source-optional-msgid c)))
   (:source-v1-msgid
    (if ok (fn-psc-finish :no-source c)
      (fn-psc-date-compare (fn-psc-get k c) :source-v1-date c)))
   (:source-v1-date
    (if ok (fn-psc-finish :no-source c)
      (fn-psc-return t (fn-psc-set pos (fn-psc-get k c)
                       (fn-psc-set resume :source-found c)))))
   (:source-optional-msgid
    (fn-psc-date-compare (if ok p (nfix (fn-psc-get k c)))
                         :source-optional-date c))
   (:source-optional-date
    (fn-psc-info-compare (if ok p (nfix (fn-psc-get k c)))
                         :source-info-simple c))
   (:source-found
    (if (fn-psc-get has-path c) (fn-psc-finish (list :source p p p) c)
      (fn-psc-set phase :path-scan (fn-psc-set k p
       (fn-psc-set prev :bol (fn-psc-set aux t c))))))
   (:msgid-field
    (if ok (fn-psc-compare p :msgid 0
             (if (stringp (fn-psc-get msgid c)) (length (fn-psc-get msgid c)) 0)
             :msgid-content c)
      (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c)
                          (fn-psc-set pos (fn-psc-get k c) c)))))
   (:msgid-content
    (if ok (fn-psc-literal p '(13 10) :msgid-tail c)
      (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c) c))))
   (:msgid-tail (fn-psc-return ok (fn-psc-set resume (fn-psc-get aux c) c)))
   (:date-field
    (if ok (fn-psc-compare p :self (fn-psc-get date c) 31 :date-content c)
      (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c) c))))
   (:date-content
    (if ok (fn-psc-literal p '(13 10) :date-tail c)
      (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c) c))))
   (:date-tail (fn-psc-return ok (fn-psc-set resume (fn-psc-get aux c) c)))
   (:info-field
    (if ok (fn-psc-agent-compare p :info-agent c)
      (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c) c))))
   (:info-agent
    (if ok (fn-psc-set phase :info-choice c)
      (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c) c))))
   (:info-tail (fn-psc-return ok (fn-psc-set resume (fn-psc-get aux c) c)))
   (:unsplice-field
    (if ok (fn-psc-agent-compare p :unsplice-agent
                            (fn-psc-set date p c))
      (fn-psc-set phase :path-scan (fn-psc-set pos b
       (fn-psc-set aux nil c)))))
   (:unsplice-agent
    (if ok (fn-psc-literal p '(33) :unsplice-tail c)
      (fn-psc-finish :no-source c)))
   (:unsplice-tail
    (if ok (fn-psc-finish (list :source (fn-psc-get k c)
                              (fn-psc-get date c) p) c)
      (fn-psc-finish :no-source c)))
   (otherwise (fn-psc-finish :no-source c)))))

(defun fn-psc-step (c byte)
 (declare (xargs :guard (true-listp c)))
 (let* ((phase (fn-psc-get phase c)) (p (nfix (fn-psc-get pos c)))
        (n (nfix (fn-psc-get n c)))
        (i (nfix (fn-psc-get index c)))
        (count (nfix (fn-psc-get ref-len c)))
        (ref (fn-psc-get ref c)))
  (cond
   ((equal phase :done) c)
   ((equal phase :control) (fn-psc-control c))
   ((and (equal phase :path-scan) (fn-psc-get aux c))
    (if (< p n)
        (fn-psc-compare p :path 0 6 :unsplice-field c)
      (fn-psc-finish :no-source c)))
   ((and (equal phase :compare) (>= i count)) (fn-psc-return t c))
   ((>= p n)
    (if (equal phase :line)
        (fn-psc-return
         (not (member-eq (fn-psc-get resume c)
                         '(:agent-info-line :agent-path-line))) c)
      (if (member-eq phase '(:params :params-lf))
          (fn-psc-return nil c)
        (if (member-eq phase '(:compare :target)) (fn-psc-return nil c)
          (fn-psc-finish :no-source c)))))
   ((and (equal phase :compare) (member-eq ref '(:incoming :self)))
    (fn-psc-set phase :target (fn-psc-set cached byte c)))
   ((member-eq phase '(:compare :target))
    (let* ((expected (if (equal phase :target) (fn-psc-get cached c)
                      (fn-psc-expected c)))
           (actual (if (and (equal ref :path) (< i 4)
                            (integerp byte) (<= 65 byte) (<= byte 90))
                       (+ byte 32) byte)))
     (if (equal actual expected)
         (fn-psc-set phase :compare
          (fn-psc-set index (+ i 1) (fn-psc-set pos (+ p 1) c)))
       (fn-psc-return nil c))))
   ((equal phase :line)
    (let ((c1 (fn-psc-set pos (+ p 1) c)))
     (if (equal byte 10) (fn-psc-return t c1)
       (fn-psc-set prev byte
        (if (and (equal (fn-psc-get resume c) :agent-info-line)
                 (equal byte 59) (not (fn-psc-get semi c)))
            (fn-psc-set semi p c1) c1)))))
   ((equal phase :info-choice)
    (cond ((equal byte 13)
           (fn-psc-literal (+ p 1) '(10) :info-tail c))
          ((equal byte 59)
           (fn-psc-set phase :params (fn-psc-set resume :info-tail c)))
          (t (fn-psc-return nil
              (fn-psc-set resume (fn-psc-get aux c) c)))))
   ((equal phase :params)
    (cond ((equal byte 13) (fn-psc-set phase :params-lf
                           (fn-psc-set pos (+ p 1) c)))
          ((equal byte 10) (fn-psc-return nil c))
          (t (fn-psc-set pos (+ p 1) c))))
   ((equal phase :params-lf)
    (fn-psc-return (equal byte 10) (fn-psc-set pos (+ p 1) c)))
   ((equal phase :path-scan)
    (cond ((and (equal byte 13) (equal (fn-psc-get prev c) :bol))
           (fn-psc-finish :no-source c))
          ((equal byte 13) (fn-psc-set phase :path-cr
                            (fn-psc-set pos (+ p 1) c)))
          (t (fn-psc-set prev nil (fn-psc-set pos (+ p 1) c)))))
   ((equal phase :path-cr)
    (if (equal byte 10)
        (fn-psc-set phase :path-scan (fn-psc-set pos (+ p 1)
         (fn-psc-set prev :bol (fn-psc-set aux t c))))
      (fn-psc-set phase :path-scan (fn-psc-set prev nil c))))
   (t (fn-psc-finish :no-source c)))))

; Closed by default; whole-array reference functions above are specifications.
(in-theory (disable fn-psc-begin fn-psc-demand fn-psc-step fn-psc-result
                    fn-psc-control fn-psc-expected fn-psc-compare
                    fn-psc-literal fn-psc-return fn-psc-finish
                    fn-psc-agent-compare fn-psc-msgid-compare
                    fn-psc-date-compare fn-psc-info-compare))
