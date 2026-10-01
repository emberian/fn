; FNRB1 is a remote-only inner collection in the existing FNCT poll field.
; No cursor is published until ONE dense event and every target are exhausted.
; Metadata preparation is bounded; actual source/funding/physical joins remain
; obligations of the installed caller, not grants supplied by these values.
(in-package "ACL2")
(include-book "consumer-remote-visible-buffer")
(include-book "consumer-remote-withdrawal-buffer")

(defconst *fn-crcol-magic* '(70 78 82 66)) ; FNRB
(defconst *fn-crcol-version* 1)

(defun fn-crcol-profilep (items bytes)
 (declare (xargs :guard t))
 (and (posp items) (fn-cp-uintp items) (posp bytes) (fn-cp-uintp bytes)
      (<= bytes *fn-stxa-max-octets*)
      (<= (+ 9 346 bytes) *fn-ncl-poll-max-payload*)
      (<= (+ 9 346 bytes) *fn-frame-max-payload*)))

; Fixed14: exact source/READ keys, semantic child, phase, saved resume,
; report writer child, reversed descriptors, count, sum of item lengths,
; required operator dimensions, next scanner, ordered descriptors.
(defun fn-crcol-state (key scope semantic phase resume child rev count width items bytes next ordered)
 (declare (xargs :guard t))
 (list :remote-collection key scope semantic phase resume child rev count width items bytes next ordered))

(defun fn-crcol-begin (semantic items bytes)
 (declare (xargs :guard t))
 (if (fn-crcol-profilep items bytes)
  (list :yield (fn-crcol-state (fn-cp-nth 1 semantic) (fn-cp-nth 2 semantic)
      semantic :semantic nil nil nil 0 0 items bytes nil nil))
  '(:refused :remote-report-profile)))

(defun fn-crcol-save (s descriptor resume)
 (declare (xargs :guard t))
 (let* ((count (1+ (nfix (fn-cp-nth 8 s))))
        (width (+ (nfix (fn-cp-nth 9 s)) (nfix (fn-cp-nth 1 descriptor))))
        (size (if (equal count 1) width (+ 9 (* 4 count) width))))
  (if (or (< (nfix (fn-cp-nth 10 s)) count)
          (< (nfix (fn-cp-nth 11 s)) size)
          (not (eq (fn-cp-nth 0 resume) :yield)))
      '(:refused :oversize)
   (list :yield (fn-crcol-state (fn-cp-nth 1 s) (fn-cp-nth 2 s)
     (fn-cp-nth 1 resume) :semantic nil nil
     (cons descriptor (fn-cp-nth 7 s)) count width
     (fn-cp-nth 10 s) (fn-cp-nth 11 s) nil nil)))))

; No bytes are emitted by preparation, including an interrupted aggregation.
; A returned next scanner is only a proposal; no durable/visible advancement.
(defun fn-crcol-tick (s key scope query-limit fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (let ((phase (fn-cp-nth 4 s)) (semantic (fn-cp-nth 3 s)))
  (cond
   ((not (and (equal key (fn-cp-nth 1 s)) (equal scope (fn-cp-nth 2 s))))
    '(:refused :remote-semantic-source-changed))
   ((not (fn-crcol-profilep (fn-cp-nth 10 s) (fn-cp-nth 11 s)))
    '(:refused :remote-report-profile))
   ((eq phase :semantic)
    (let* ((answer (fn-crm-tick semantic key scope query-limit))
           (word (fn-cp-nth 0 answer)))
     (cond
      ((eq word :yield)
       (list :yield (fn-crcol-state key scope (fn-cp-nth 1 answer) phase nil nil
         (fn-cp-nth 7 s) (fn-cp-nth 8 s) (fn-cp-nth 9 s)
         (fn-cp-nth 10 s) (fn-cp-nth 11 s) nil nil)))
      ((eq word :report-input)
       (let* ((kind (fn-cp-nth 1 answer)) (projection (fn-cp-nth 2 answer))
              (resume (fn-cp-nth 3 answer))
              (writer (if (eq kind :visible)
                          (fn-crvp-begin key kind projection (fn-cp-nth 15 semantic)
                                         (fn-cp-nth 11 s) 0 fn-arena)
                        (fn-crwd-begin key kind projection (fn-cp-nth 11 s) 0))))
        (if (not (eq (fn-cp-nth 0 writer) :yield)) writer
         (if (eq kind :visible)
          (list :yield (fn-crcol-state key scope semantic :visible-size resume
           (fn-cp-nth 1 writer) (fn-cp-nth 7 s) (fn-cp-nth 8 s) (fn-cp-nth 9 s)
           (fn-cp-nth 10 s) (fn-cp-nth 11 s) nil nil))
          (fn-crcol-save s (list :withdrawal (fn-cp-nth 2 writer) (fn-cp-nth 1 writer)) resume)))))
      ((eq word :event-complete)
       (list :yield (fn-crcol-state key scope semantic :reverse nil nil
         (fn-cp-nth 7 s) (fn-cp-nth 8 s) (fn-cp-nth 9 s)
         (fn-cp-nth 10 s) (fn-cp-nth 11 s) (fn-cp-nth 1 answer) nil)))
      (t answer))))
   ((eq phase :visible-size)
    (let* ((child (fn-cp-nth 6 s))
           (answer (fn-crvp-plan child key 0 (fn-cp-nth 11 s) fn-arena)))
     (if (not (eq (fn-cp-nth 0 answer) :yield)) answer
      (let ((next (fn-cp-nth 1 answer)))
       (if (eq (fn-cp-nth 2 next) :bytes)
        (fn-crcol-save s (list :visible (fn-cp-nth 14 next) next) (fn-cp-nth 5 s))
        (list :yield (fn-crcol-state key scope semantic phase (fn-cp-nth 5 s) next
         (fn-cp-nth 7 s) (fn-cp-nth 8 s) (fn-cp-nth 9 s)
         (fn-cp-nth 10 s) (fn-cp-nth 11 s) nil nil)))))))
   ((eq phase :reverse)
    (let ((rev (fn-cp-nth 7 s)))
     (cond ((consp rev)
            (list :yield (fn-crcol-state key scope semantic phase nil nil
             (cdr rev) (fn-cp-nth 8 s) (fn-cp-nth 9 s)
             (fn-cp-nth 10 s) (fn-cp-nth 11 s) (fn-cp-nth 12 s)
             (cons (car rev) (fn-cp-nth 13 s)))))
           ((null rev)
            (list :collection-ready (fn-cp-nth 8 s)
             (if (<= (nfix (fn-cp-nth 8 s)) 1) (fn-cp-nth 9 s)
               (+ 9 (* 4 (nfix (fn-cp-nth 8 s))) (nfix (fn-cp-nth 9 s))))
             (fn-cp-nth 13 s) (fn-cp-nth 12 s)))
           (t '(:refused :remote-report-descriptors)))))
   (t '(:refused :remote-collection-phase)))))

; Recovery/client fixture observation only, not a served payload writer.
(defun fn-crcol-parts-reference (parts)
 (declare (xargs :guard t))
 (if (consp parts)
     (ec-call (binary-append (ec-call (fn-cbor-u32-bytes (len (car parts))))
      (ec-call (binary-append (car parts) (fn-crcol-parts-reference (cdr parts)))))) nil))

(defun fn-crcol-encode-reference (parts items bytes)
 (declare (xargs :guard t))
 (let ((result (if (<= (len parts) 1) (fn-cp-nth 0 parts)
              (append *fn-crcol-magic* (list *fn-crcol-version*)
                      (ec-call (fn-cbor-u32-bytes (len parts))) (fn-crcol-parts-reference parts)))))
  (if (and (fn-crcol-profilep items bytes) (true-listp parts)
           (<= (len parts) items) (<= (len result) bytes)
           (fn-cbor-octet-listp result)) result :bad)))

(in-theory (disable fn-crcol-profilep fn-crcol-state fn-crcol-begin fn-crcol-save
 fn-crcol-tick fn-crcol-parts-reference fn-crcol-encode-reference))
