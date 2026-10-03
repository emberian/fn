; Shared ARTICLE/HEAD/BODY producer. Payloads remain captured arena handles;
; preflight and rendering each consume a bounded number of octets per step.
; The logical list source is retained by its tail, never copied or indexed
; repeatedly. A READY cursor has no session or authorization effects.
(in-package "ACL2")
(include-book "nntp-responses")
(include-book "nov-piece-window")

(defun fn-ast-at (i xs)
  (declare (xargs :guard (natp i) :measure (nfix i)))
  (if (consp xs)
      (if (zp i) (car xs) (fn-ast-at (- i 1) (cdr xs)))
    nil))

; Source = (handle offset remaining literal-tail). NIL handle denotes the
; logical/literal representation. Length is captured once with the handle.
(defun fn-ast-source (article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((p (fn-article-payload article)))
    (if (and (natp p) (< p (fn-arena-count fn-arena)))
        (list p 0 (fn-arena-payload-len p fn-arena) nil)
      (let ((bytes (fn-nntp-article-bytes article fn-arena)))
        (list nil 0 (len bytes) bytes)))))

(defun fn-ast-source-byte (source fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((h (fn-ast-at 0 source)) (at (nfix (fn-ast-at 1 source))))
    (if (and (natp h) (< h (fn-arena-count fn-arena))
             (< at (fn-arena-payload-len h fn-arena)))
        (fn-arena-get h at fn-arena)
      (if (null h) (fn-cbor-ag-car (fn-ast-at 3 source)) nil))))

(defun fn-ast-source-next (source)
  (declare (xargs :guard t))
  (list (fn-ast-at 0 source) (+ 1 (nfix (fn-ast-at 1 source)))
        (nfix (- (nfix (fn-ast-at 2 source)) 1)) (fn-cbor-ag-cdr (fn-ast-at 3 source))))

(defun fn-ast-source-left (source left)
  (declare (xargs :guard (natp left)))
  (list (fn-ast-at 0 source) (nfix (fn-ast-at 1 source)) left (fn-ast-at 3 source)))

; Preflight = (source original pending-CR line-start separator-state
;              body-source bad). Separator state recognizes CR LF CR LF.
(defun fn-ast-preflight (source)
  (declare (xargs :guard t))
  (list source source nil t 0 nil nil))

(defun fn-ast-refused-preflight (source)
  (declare (xargs :guard t))
  (list (fn-ast-source-left source 0) source nil t 0 nil t))

(defun fn-ast-separator-next (matched byte)
  (declare (xargs :guard t))
  (cond ((equal matched 0) (if (equal byte 13) 1 0))
        ((equal matched 1) (cond ((equal byte 10) 2) ((equal byte 13) 1) (t 0)))
        ((equal matched 2) (if (equal byte 13) 3 0))
        (t (cond ((equal byte 10) 4) ((equal byte 13) 1) (t 0)))))

(defun fn-ast-scan-one (scan fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let* ((source (fn-ast-at 0 scan)) (byte (fn-ast-source-byte source fn-arena))
         (next (fn-ast-source-next source)) (pending (fn-ast-at 2 scan))
         (sep (fn-ast-separator-next (fn-ast-at 4 scan) byte)))
    (list next (fn-ast-at 1 scan) (equal byte 13) (equal byte 10) sep
          (or (fn-ast-at 5 scan) (and (equal sep 4) next))
          (or (fn-ast-at 6 scan) (not (fn-octetp byte))
              (if pending (not (equal byte 10))
                (or (equal byte 0) (equal byte 10)))))))

(defun fn-ast-scan-step (scan fuel fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp fuel) :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (zp (nfix (fn-ast-at 2 (fn-ast-at 0 scan)))))
      (mv scan 0)
    (mv-let (next used)
      (fn-ast-scan-step (fn-ast-scan-one scan fn-arena) (- fuel 1) fn-arena)
      (mv next (+ 1 used)))))

(defthm fn-ast-scan-used-natural
  (natp (mv-nth 1 (fn-ast-scan-step scan fuel fn-arena)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-ast-scan-step scan fuel fn-arena)
                  :in-theory (disable fn-ast-scan-one fn-ast-at))))

(verify-guards fn-ast-scan-step
  :hints (("Goal" :in-theory (disable fn-ast-scan-one fn-ast-at))))

(defun fn-ast-scan-donep (scan)
  (declare (xargs :guard t))
  (zp (nfix (fn-ast-at 2 (fn-ast-at 0 scan)))))

(defun fn-ast-scan-validp (scan)
  (declare (xargs :guard t))
  (and (fn-ast-scan-donep scan) (not (fn-ast-at 6 scan))
       (not (fn-ast-at 2 scan)) (fn-ast-at 3 scan) (consp (fn-ast-at 5 scan))))

; No decimal field is expanded wholesale: the existing proved numerical
; piece setup divides once per work unit, then emits one digit per unit.
(defun fn-ast-initial-pieces (kind number article)
  (declare (xargs :guard t))
  (list (cond ((eq kind :article) "220 ") ((eq kind :head) "221 ")
              ((eq kind :body) "222 ") (t "223 "))
        (list :decimal (nfix number) nil) " "
        (if (stringp (fn-article-msgid article)) (fn-article-msgid article) "")
        (cond ((eq kind :article) " article follows")
              ((eq kind :head) " headers follow")
              ((eq kind :body) " body follows") (t " retrieved")) '(13 10)))

; Cursor = (phase pieces position pairs source line-start). Synthetic Xref
; locations are opened one pair at a time; the original pair list persists
; across replay. The caller passes pairs from the captured selected article.
(defun fn-ast-ready (scan kind number article server pairs)
  (declare (xargs :guard t))
  (let* ((original (fn-ast-at 1 scan)) (body (fn-ast-at 5 scan))
         (source (cond ((eq kind :body) body)
                       ((eq kind :head)
                        (fn-ast-source-left original
                          (nfix (- (nfix (fn-ast-at 1 body)) 2))))
                       (t original))))
    (list :initial (fn-ast-initial-pieces kind number article) 0
          (and (not (eq kind :body)) pairs) source t server)))

; Xref filtering retains the original membership spine. Word validation and
; the reference's first matching group lookup each advance one character or
; one membership per transition, including duplicate/corrupted memberships.
; Iterator = (:xref-source remaining all phase pair position lookup compare).
(defun fn-ast-xref-state (remaining all phase pair at lookup compare)
  (declare (xargs :guard t))
  (list :xref-source remaining all phase pair at lookup compare))

(defun fn-ast-xref-one (it)
  (declare (xargs :verify-guards nil))
  (let* ((remaining (fn-ast-at 1 it)) (all (fn-ast-at 2 it))
         (phase (fn-ast-at 3 it)) (pair (fn-ast-at 4 it))
         (at (nfix (fn-ast-at 5 it))) (lookup (fn-ast-at 6 it))
         (compare (nfix (fn-ast-at 7 it)))
         (skip (fn-ast-xref-state (cdr remaining) all :next nil 0 nil 0)))
    (cond
     ((eq phase :next)
      (if (atom remaining) (mv :end nil it)
        (let ((candidate (car remaining)))
          (if (and (consp candidate) (stringp (car candidate))
                   (< 0 (length (car candidate)))
                   (integerp (cdr candidate)) (< 0 (cdr candidate))
                   (<= (cdr candidate) *fn-nntp-max-article-number*))
              (mv :wait nil (fn-ast-xref-state remaining all :word candidate 0 nil 0))
            (mv :wait nil skip)))))
     ((eq phase :word)
      (if (>= at (length (car pair)))
          (mv :wait nil (fn-ast-xref-state remaining all :lookup pair 0 all 0))
        (if (let ((byte (char-code (char (car pair) at))))
              (and (<= 33 byte) (<= byte 126) (not (equal byte 58))))
            (mv :wait nil (fn-ast-xref-state remaining all :word pair (+ 1 at) nil 0))
          (mv :wait nil skip))))
     ((eq phase :lookup)
      (if (atom lookup) (mv :wait nil skip)
        (let ((row (car lookup)))
          (if (and (consp row) (stringp (car row))
                   (equal (length (car row)) (length (car pair))))
              (mv :wait nil (fn-ast-xref-state remaining all :compare pair 0 lookup 0))
            (mv :wait nil (fn-ast-xref-state remaining all :lookup pair 0 (cdr lookup) 0))))))
     (t
      (if (>= compare (length (car pair)))
          (mv (if (equal (cdr (car lookup)) (cdr pair)) :pair :wait) pair skip)
        (if (equal (char (car pair) compare) (char (car (car lookup)) compare))
            (mv :wait nil (fn-ast-xref-state remaining all :compare pair 0 lookup (+ 1 compare)))
          (mv :wait nil (fn-ast-xref-state remaining all :lookup pair 0 (cdr lookup) 0))))))))

(defun fn-ast-ready-memberships (scan kind number article server)
  (declare (xargs :verify-guards nil))
  (let ((cur (fn-ast-ready scan kind number article server nil)))
    (list (fn-ast-at 0 cur) (fn-ast-at 1 cur) (fn-ast-at 2 cur)
          (and server (not (eq kind :body)) (fn-nntp-article-idp article)
               (fn-ast-xref-state (fn-article-memberships article)
                                  (fn-article-memberships article) :next nil 0 nil 0))
          (fn-ast-at 4 cur) (fn-ast-at 5 cur) (fn-ast-at 6 cur))))

; Each transition spends one unit, even when numerical setup or a phase
; transition produces no bytes. The payload branch emits at most two octets
; (a leading dot is doubled); it never scans for the end of a line.
(defun fn-ast-render-one (cur fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((phase (fn-ast-at 0 cur)) (pieces (fn-ast-at 1 cur)) (pos (nfix (fn-ast-at 2 cur))))
    (cond
     ((eq phase :done) (mv nil cur))
     ((consp pieces)
      (mv-let (out next at) (fn-npw-one pieces pos fn-arena)
        (mv out (list phase next at (fn-ast-at 3 cur) (fn-ast-at 4 cur) (fn-ast-at 5 cur) (fn-ast-at 6 cur)))))
     ((eq phase :initial)
      (if (eq (fn-ast-at 0 (fn-ast-at 3 cur)) :xref-source)
          (mv nil (list :xref-seek-first nil 0 (fn-ast-at 3 cur) (fn-ast-at 4 cur) t (fn-ast-at 6 cur)))
       (if (consp (fn-ast-at 3 cur))
          (mv nil (list :xref (list "Xref: " (fn-ast-at 6 cur)) 0
                        (fn-ast-at 3 cur) (fn-ast-at 4 cur) t nil))
        (mv nil (list :payload nil 0 nil (fn-ast-at 4 cur) t nil)))))
     ((member-eq phase '(:xref-seek-first :xref-seek))
      (mv-let (word pair next) (fn-ast-xref-one (fn-ast-at 3 cur))
        (cond
         ((eq word :pair)
          (mv nil (list :xref-seek
                    (append (and (eq phase :xref-seek-first) (list "Xref: " (fn-ast-at 6 cur)))
                            (list " " (car pair) ":" (list :decimal (nfix (cdr pair)) nil)))
                    0 next (fn-ast-at 4 cur) t nil)))
         ((eq word :end)
          (mv nil (list :payload (and (eq phase :xref-seek) (list '(13 10)))
                        0 nil (fn-ast-at 4 cur) t nil)))
         (t (mv nil (list phase nil 0 next (fn-ast-at 4 cur) t (fn-ast-at 6 cur)))))))
     ((eq phase :xref)
      (if (consp (fn-ast-at 3 cur))
          (let ((pair (car (fn-ast-at 3 cur))))
            (mv nil (list :xref
                          (list " " (car pair) ":" (list :decimal (nfix (cdr pair)) nil))
                          0 (cdr (fn-ast-at 3 cur)) (fn-ast-at 4 cur) t nil)))
        (mv nil (list :payload (list '(13 10)) 0 nil (fn-ast-at 4 cur) t nil))))
     ((eq phase :payload)
      (let ((source (fn-ast-at 4 cur)))
        (if (zp (nfix (fn-ast-at 2 source)))
            (mv nil (list :end (list '(46 13 10)) 0 nil nil t nil))
          (let ((byte (fn-ast-source-byte source fn-arena)))
            (mv (if (and (fn-ast-at 5 cur) (equal byte 46)) '(46 46) (list byte))
                (list :payload nil 0 nil (fn-ast-source-next source) (equal byte 10) nil))))))
     (t (mv nil (list :done nil 0 nil nil nil nil))))))

(defun fn-ast-render-step-aux (cur fuel acc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (eq (car cur) :done))
      (mv (revappend acc nil) cur 0)
    (mv-let (out next) (fn-ast-render-one cur fn-arena)
      (mv-let (bytes rest used)
        (fn-ast-render-step-aux next (- fuel 1) (revappend out acc) fn-arena)
        (mv bytes rest (+ 1 used))))))

(defun fn-ast-render-step (cur fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-ast-render-step-aux cur fuel nil fn-arena))

; A window retains an emitted fragment separately from the immutable cursor.
; Reading a leading dot may produce two octets even for a one-octet window.
; Neither byte is lost: publication drains the fragment one byte per unit.
(defun fn-ast-window-cur (window)
  (declare (xargs :guard t))
  (if (eq (fn-ast-at 0 window) :window) (fn-ast-at 2 window) window))

(defun fn-ast-window-pending (window)
  (declare (xargs :guard t))
  (and (eq (fn-ast-at 0 window) :window) (fn-ast-at 1 window)))

(defun fn-ast-window-donep (window)
  (declare (xargs :guard t))
  (and (not (consp (fn-ast-window-pending window)))
       (eq (fn-ast-at 0 (fn-ast-window-cur window)) :done)))

(defun fn-ast-render-window-aux (cur pending fuel left acc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil :measure (nfix fuel)))
  (cond
   ((or (zp fuel) (zp left)
        (and (not (consp pending)) (eq (fn-ast-at 0 cur) :done)))
    (mv (revappend acc nil) (list :window pending cur)))
   ((consp pending)
    (fn-ast-render-window-aux cur (cdr pending) (- fuel 1) (- left 1)
                              (cons (car pending) acc) fn-arena))
   (t
    (mv-let (out next) (fn-ast-render-one cur fn-arena)
      (fn-ast-render-window-aux next out (- fuel 1) left acc fn-arena)))))

(defun fn-ast-render-window (window fuel octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-ast-render-window-aux (fn-ast-window-cur window)
                            (fn-ast-window-pending window)
                            (nfix fuel) (nfix octets) nil fn-arena))

(defthm fn-ast-render-window-acc-bound
  (<= (len (mv-nth 0 (fn-ast-render-window-aux cur pending fuel left acc fn-arena)))
      (+ (len acc) (nfix left)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-ast-render-window-aux cur pending fuel left acc fn-arena)
                  :in-theory (disable fn-ast-render-one))))

(defthm fn-ast-render-window-byte-bound
  (<= (len (mv-nth 0 (fn-ast-render-window window fuel octets fn-arena)))
      (nfix octets))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance fn-ast-render-window-acc-bound
                            (cur (fn-ast-window-cur window))
                            (pending (fn-ast-window-pending window))
                            (fuel (nfix fuel)) (left (nfix octets)) (acc nil)))
           :in-theory (disable fn-ast-render-window-aux
                               fn-ast-window-cur fn-ast-window-pending))))

(defthm fn-ast-scan-work-bounded
  (<= (mv-nth 1 (fn-ast-scan-step scan fuel fn-arena)) (nfix fuel))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-ast-scan-step scan fuel fn-arena)
                  :in-theory (disable fn-ast-scan-one))))

(defthm fn-ast-render-work-bounded
  (<= (mv-nth 2 (fn-ast-render-step-aux cur fuel acc fn-arena)) (nfix fuel))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-ast-render-step-aux cur fuel acc fn-arena)
                  :in-theory (disable fn-ast-render-one revappend))))
