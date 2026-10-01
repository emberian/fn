(in-package "ACL2")
(include-book "ninep-version")

; Cursor fixed8: tag, phase, retained tail, current actual bucket, input name
; span, next name character, comparison character, emitted bucket ordinal.
; Remaining tail is borrowed. One scheduler action handles at most one bucket
; or compares one octet character. No name-wide EQUAL or list recognition.
(defun fn-9pb-groups-begin (buckets)
 (declare (xargs :guard t))
 (list :ninep-groups :enumerate buckets nil nil 0 0 0))

(defun fn-9pb-group-walk-begin (buckets begin count)
 (declare (xargs :guard t))
 (if (and (natp begin) (natp count))
     (list :ninep-groups :lookup buckets nil
           (list begin count) 0 0 0)
   nil))

(defun fn-9pb-groups-step (cursor fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (let* ((phase (fn-9p-metadata-at 1 cursor)) (tail (fn-9p-metadata-at 2 cursor))
        (bucket (fn-9p-metadata-at 3 cursor)) (span (fn-9p-metadata-at 4 cursor))
        (pos (fn-9p-metadata-at 5 cursor)) (ordinal (fn-9p-metadata-at 7 cursor))
        (name (fn-9p-metadata-at 0 bucket)))
  (cond
   ((not (and (eq (fn-9p-metadata-at 0 cursor) :ninep-groups)
              (natp pos) (natp ordinal)))
    (mv :recovery-required nil cursor))
   ((eq phase :enumerate)
    (if (not (consp tail)) (mv :complete nil cursor)
      (let ((bucket (car tail)))
       (if (not (stringp (fn-9p-metadata-at 0 bucket)))
           (mv :recovery-required nil cursor)
         (mv :group bucket
          (list :ninep-groups :enumerate (cdr tail) nil nil 0 0 (1+ ordinal)))))))
   ((eq phase :lookup)
    (if (not (consp tail)) (mv :missing nil cursor)
      (let ((bucket (car tail)))
       (if (not (stringp (fn-9p-metadata-at 0 bucket)))
           (mv :recovery-required nil cursor)
         (mv :yield nil
          (list :ninep-groups :compare (cdr tail) bucket span 0 0 ordinal))))))
   ((eq phase :compare)
    (let ((begin (fn-9p-metadata-at 0 span)) (count (fn-9p-metadata-at 1 span)))
     (cond
      ((not (and (stringp name) (natp begin) (natp count)
                 (<= pos count) (<= (+ begin count) (fn-octets-len fn-octets))))
       (mv :recovery-required nil cursor))
      ((not (equal count (length name)))
       (mv :yield nil (list :ninep-groups :lookup tail nil span 0 0 (1+ ordinal))))
      ((equal pos count) (mv :group bucket cursor))
      ((not (equal (char-code (char name pos)) (fn-octets-get (+ begin pos) fn-octets)))
       (mv :yield nil (list :ninep-groups :lookup tail nil span 0 0 (1+ ordinal))))
      (t (mv :yield nil
           (list :ninep-groups :compare tail bucket span (1+ pos) 0 ordinal))))))
   (t (mv :recovery-required nil cursor)))))


(defthm fn-9pb-enumeration-complete-source-boundary
 (implies (and (eq (fn-9p-metadata-at 0 cursor) :ninep-groups)
               (eq (fn-9p-metadata-at 1 cursor) :enumerate)
               (natp (fn-9p-metadata-at 5 cursor))
               (natp (fn-9p-metadata-at 7 cursor))
               (consp (fn-9p-metadata-at 2 cursor))
               (stringp (fn-9p-metadata-at 0 (car (fn-9p-metadata-at 2 cursor)))))
  (equal (fn-9pb-groups-step cursor fn-octets)
   (list :group (car (fn-9p-metadata-at 2 cursor))
    (list :ninep-groups :enumerate (cdr (fn-9p-metadata-at 2 cursor))
          nil nil 0 0 (1+ (fn-9p-metadata-at 7 cursor))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-9pb-groups-step))))

(defthm fn-9pb-lookup-terminal-is-exact-retained-bucket
 (implies (and (equal (mv-nth 0 (fn-9pb-groups-step cursor fn-octets)) :group)
               (equal (fn-9p-metadata-at 1 cursor) :compare))
  (equal (mv-nth 1 (fn-9pb-groups-step cursor fn-octets))
         (fn-9p-metadata-at 3 cursor)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-9pb-groups-step))))
