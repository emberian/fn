; Process-visible effects of the actual file-device trace: one thread performs
; Writes and Fences, a pool performs Reads (host/device.lisp).
; This checker does not turn a Fence return into power-loss evidence.
; In-flight/error Writes are overapproximated by arbitrary bytes IN their
; requested span; outside that span they cannot explain a changed image.
(in-package "ACL2")

(defun fn2-nde-octetsp (xs)
 (if (atom xs) (null xs)
  (and (unsigned-byte-p 8 (car xs)) (fn2-nde-octetsp (cdr xs)))))
(defun fn2-nde-descriptorp (d fd)
 (and (true-listp d) (equal (len d) 10) (equal (nth 0 d) fd)
      (or (null (nth 1 d)) (natp (nth 1 d)))
      (or (null (nth 2 d)) (natp (nth 2 d)))
      (member-eq (nth 3 d) '(:read :write :fence))
      (natp (nth 7 d)) (posp (nth 8 d))
      (or (null (nth 9 d)) (posp (nth 9 d)))
      (natp (nth 4 d)) (natp (nth 5 d))
      (if (eq (nth 3 d) :write)
          (and (fn2-nde-octetsp (nth 6 d)) (equal (len (nth 6 d)) (nth 5 d)))
        (null (nth 6 d)))))
(defun fn2-nde-uncertain-write (d reason)
 (and (eq (nth 3 d) :write) (list :uncertain (nth 4 d) (nth 5 d) reason (nth 6 d))))
(defun fn2-nde-return-effect (d result errno read-bytes)
 (cond ((eq (nth 3 d) :write)
        (if (< result 0) (fn2-nde-uncertain-write d (list :error result errno))
          (list :write (nth 4 d) result (nth 6 d))))
       ((eq (nth 3 d) :fence) (list :fence result errno))
       ((and (eq (nth 3 d) :read) (<= 0 result))
        (list :read (nth 4 d) result read-bytes))
       (t nil)))
; The device hazards. Two jobs are ordered unless both are Reads or one is a
; Read and the other a Fence. An ordered pair never overlaps: the later one
; begins only after the earlier one returns, and the host posts them in
; submission order. So no Read overlaps a Write, Writes and Fences run one at
; a time in submission order, and Reads may overlap each other and a Fence.
(defun fn2-nde-ordered-p (a b)
 (or (eq a :write) (eq b :write) (and (eq a :fence) (eq b :fence))))
; JOBS pairs ids with descriptors, oldest first. ID, of KIND, is in JOBS and
; no job before it is ordered with it. Over submitted unreturned jobs this
; is begin-readiness; over returned unposted jobs, post-readiness.
(defun fn2-nde-ready-p (id kind jobs)
 (and (consp jobs)
      (or (equal (caar jobs) id)
          (and (not (fn2-nde-ordered-p (nth 3 (cdar jobs)) kind))
               (fn2-nde-ready-p id kind (cdr jobs))))))
; Begun Writes with no recorded return. No other job overlaps a Write.
(defun fn2-nde-in-flight (active pending)
 (if (atom active) nil
  (let ((w (fn2-nde-uncertain-write (cdr (assoc-equal (car active) pending)) :pending)))
   (if w (cons w (fn2-nde-in-flight (cdr active) pending))
     (fn2-nde-in-flight (cdr active) pending)))))
; SEEN prevents job-id reuse even after return. PENDING retains submitted,
; unreturned jobs in submission order; ACTIVE names the begun ones. A begin
; that overlaps or passes an ordered job is refused rather than given an
; invented serial order. Effects take return order, which is submission
; order for every Read/Write pair; unordered pairs commute on the image.
(defun fn2-nde-decode (records fd seen pending active effects)
 (declare (xargs :verify-guards nil))
 (if (atom records)
  (if records (mv :malformed nil)
   (mv :ok (append (reverse effects) (fn2-nde-in-flight active pending))))
  (let* ((r (car records)) (tag (car r)) (id (nth 1 r)))
   (cond
    ((and (member-eq tag '(:submit :direct)) (true-listp r) (equal (len r) 3)
          (posp id) (not (member-equal id seen)) (fn2-nde-descriptorp (nth 2 r) fd))
     (fn2-nde-decode (cdr records) fd (cons id seen)
       (append pending (list (cons id (nth 2 r)))) active effects))
    ((and (eq tag :begin) (true-listp r) (equal (len r) 2)
          (not (member-equal id active))
          (fn2-nde-ready-p id (nth 3 (cdr (assoc-equal id pending))) pending))
     (fn2-nde-decode (cdr records) fd seen pending (cons id active) effects))
    ((and (eq tag :return) (true-listp r) (equal (len r) 5)
          (member-equal id active) (assoc-equal id pending)
          (integerp (nth 2 r)) (natp (nth 3 r))
          (if (and (eq (nth 3 (cdr (assoc-equal id pending))) :read) (<= 0 (nth 2 r)))
              (and (fn2-nde-octetsp (nth 4 r)) (equal (len (nth 4 r)) (nth 2 r)))
            (null (nth 4 r)))
          (or (< (nth 2 r) 0)
              (and (equal (nth 3 r) 0)
                   (if (eq (nth 3 (cdr (assoc-equal id pending))) :fence)
                       (equal (nth 2 r) 0)
                     (<= (nth 2 r) (nth 5 (cdr (assoc-equal id pending))))))))
     (let ((effect (fn2-nde-return-effect (cdr (assoc-equal id pending)) (nth 2 r) (nth 3 r) (nth 4 r))))
      (fn2-nde-decode (cdr records) fd seen (remove1-assoc-equal id pending)
        (remove1-equal id active) (if effect (cons effect effects) effects))))
    (t (mv :malformed nil))))))
(defun fn2-native-device-effects (records fd)
 (declare (xargs :verify-guards nil))
 (fn2-nde-decode records fd nil nil nil nil))

; Streaming image comparison: callers must cover the WHOLE image in disjoint
; slices and compare total sizes. Filtering once per slice avoids image-size
; times trace-length byte work. This helper alone does not prove coverage.
(defun fn2-nde-span-effects (effects start size)
 (declare (xargs :verify-guards nil))
 (if (atom effects) nil
  (let ((e (car effects)))
   (if (and (member-eq (car e) '(:write :uncertain :read))
            (< (nth 1 e) (+ start size)) (< start (+ (nth 1 e) (nth 2 e))))
       (cons e (fn2-nde-span-effects (cdr effects) start size))
     (fn2-nde-span-effects (cdr effects) start size)))))
(defun fn2-nde-byte-observations-p (effects address prior after)
 (declare (xargs :verify-guards nil))
 (if (atom effects) (or (eq prior :unknown) (equal prior after))
  (let* ((e (car effects))
         (hit (and (member-eq (car e) '(:write :uncertain :read))
                   (<= (nth 1 e) address) (< address (+ (nth 1 e) (nth 2 e)))))
         (observed (and hit (eq (car e) :read)))
         (next (if hit
                   (if (eq (car e) :uncertain) :unknown
                     (nth (- address (nth 1 e)) (nth 3 e))) prior)))
   (and (or (not observed) (eq prior :unknown)
            (equal prior (nth (- address (nth 1 e)) (nth 3 e))))
        (fn2-nde-byte-observations-p (cdr effects) address next after)))))
(defun fn2-native-device-effects-uncertain-p (effects)
 (if (atom effects) nil
  (or (eq (caar effects) :uncertain)
      (fn2-native-device-effects-uncertain-p (cdr effects)))))
(defun fn2-nde-slice (effects address before after)
 (declare (xargs :verify-guards nil :measure (acl2-count before)))
 (if (atom before) (and (null before) (null after))
  (and (consp after)
       (fn2-nde-byte-observations-p effects address (car before) (car after))
       (fn2-nde-slice effects (+ 1 address) (cdr before) (cdr after)))))
(defun fn2-native-device-image-slice-p (effects address before after)
 (declare (xargs :verify-guards nil))
 (and (natp address) (fn2-nde-octetsp before) (fn2-nde-octetsp after)
      (fn2-nde-slice (fn2-nde-span-effects effects address (len before)) address before after)))

; Positive completed transfer spans must exist in the observed fixed image.
; Empty reads beyond EOF are harmless. An unresolved requested span may cross
; EOF without any effect; it remains an uncertain bound, never exact evidence.
(defun fn2-native-device-effects-bounded-p (effects image-size)
 (declare (xargs :verify-guards nil))
 (if (atom effects) (null effects)
  (let ((e (car effects)))
   (and (case (car e)
          ((:read :write)
           (and (natp (nth 1 e)) (natp (nth 2 e))
                (or (equal (nth 2 e) 0) (<= (+ (nth 1 e) (nth 2 e)) image-size))))
          (:uncertain (and (natp (nth 1 e)) (natp (nth 2 e))))
          (:fence t)
          (otherwise nil))
        (fn2-native-device-effects-bounded-p (cdr effects) image-size)))))

; The streaming consumer starts at cursor 0, requires identical observed image
; sizes, admits each nonempty slice only at the returned cursor, and finishes
; ONLY at image-size. A sampling caller cannot obtain the complete verdict.
(defun fn2-native-device-image-chunk (effects image-size cursor address before after)
 (declare (xargs :verify-guards nil))
 (if (and (natp image-size) (natp cursor) (equal address cursor)
          (fn2-native-device-effects-bounded-p effects image-size)
          (consp before) (<= (+ cursor (len before)) image-size)
          (fn2-native-device-image-slice-p effects address before after))
     (mv :ok (+ cursor (len before)))
   (mv :mismatch cursor)))
(defun fn2-native-device-image-finish (effects before-size after-size cursor)
 (declare (xargs :verify-guards nil))
 (if (and (natp before-size) (equal before-size after-size) (equal cursor before-size))
     (if (not (fn2-native-device-effects-bounded-p effects before-size)) :out-of-image-effect
       (if (fn2-native-device-effects-uncertain-p effects) :uncertain-effect-bound :exact-process-view))
   :incomplete-image))
