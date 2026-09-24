; Decode the pinned ION helper's published observation. This is transport
; evidence for one durable sender attempt, never an application receipt.
(in-package "ACL2")
(include-book "bp-outbound")

(defun fn-bpio-digitp (c)
  (declare (xargs :guard t))
  (and (characterp c) (<= (char-code #\0) (char-code c))
       (<= (char-code c) (char-code #\9))))

(defun fn-bpio-decimal-aux (chars value limit)
  (declare (xargs :guard (and (character-listp chars) (natp value)
                              (posp limit))
                  :measure (acl2-count chars)))
  (if (endp chars)
      value
    (if (not (fn-bpio-digitp (car chars)))
        nil
      (let ((next (+ (* 10 value) (- (char-code (car chars)) 48))))
        (if (< next limit)
            (fn-bpio-decimal-aux (cdr chars) next limit)
          nil)))))

(defun fn-bpio-decimal (text limit)
  (declare (xargs :guard (posp limit)))
  (if (or (not (stringp text)) (equal text "")
          (and (< 1 (length text)) (equal (char text 0) #\0)))
      nil
    (fn-bpio-decimal-aux (coerce text 'list) 0 limit)))

; A helper line has exactly six nonempty fields and one final LF. The C helper
; rejects a pipe and LF in all three EIDs before it publishes this line.
(defun fn-bpio-fields-aux (chars current fields)
  (declare (xargs :guard (and (character-listp chars)
                              (character-listp current) (true-listp fields))
                  :measure (acl2-count chars)))
  (if (endp chars)
      nil
    (let ((c (car chars)))
      (cond
       ((equal c #\|)
        (if (endp current) nil
          (fn-bpio-fields-aux (cdr chars) nil
                              (cons (coerce (reverse current) 'string) fields))))
       ((equal c #\Newline)
        (if (or (consp (cdr chars)) (endp current)) nil
          (reverse (cons (coerce (reverse current) 'string) fields))))
       (t (fn-bpio-fields-aux (cdr chars) (cons c current) fields))))))

(defun fn-bpio-eid-fieldp (s)
  (declare (xargs :guard t))
  (and (stringp s) (< 0 (length s)) (<= (length s) 255)
       (not (member-equal #\Newline (coerce s 'list)))
       (not (member-equal #\| (coerce s 'list)))))

(defun fn-bpio-decode (line)
  (declare (xargs :guard t))
  (if (or (not (stringp line)) (> (length line) 1023))
      nil
    (let ((fields (fn-bpio-fields-aux (coerce line 'list) nil nil)))
      (if (and (equal (len fields) 6)
               (equal (nth 0 fields) "observed-v1")
               (fn-bpio-eid-fieldp (nth 1 fields))
               (fn-bpio-eid-fieldp (nth 2 fields))
               (fn-bpio-eid-fieldp (nth 3 fields))
               (natp (fn-bpio-decimal (nth 4 fields) 18446744073709551616))
               (natp (fn-bpio-decimal (nth 5 fields) 4294967296)))
          (list (nth 1 fields) (nth 2 fields) (nth 3 fields)
                (fn-bpio-decimal (nth 4 fields) 18446744073709551616)
                (fn-bpio-decimal (nth 5 fields) 4294967296))
        nil))))

; The append-only FNWF record stores the exact ION bundle identity alongside
; the local durable attempt key. It neither changes transport status nor
; discharges any receipt/retention obligation.
(defun fn-bpio-recordp (record)
  (declare (xargs :guard t))
  (and (true-listp record) (equal (len record) 9)
       (equal (nth 0 record) :ion-observed)
       (fn-bp-journal-textp (nth 1 record))
       (fn-bp-journal-textp (nth 2 record))
       (fn-bp-u64p (nth 3 record))
       (fn-bpio-eid-fieldp (nth 4 record))
       (fn-bpio-eid-fieldp (nth 5 record))
       (fn-bpio-eid-fieldp (nth 6 record))
       (fn-bp-u64p (nth 7 record))
       (natp (nth 8 record)) (< (nth 8 record) 4294967296)))

(defun fn-bpio-bound-recordp (bpo-state record)
  (declare (xargs :guard t))
  (if (not (fn-bpio-recordp record)) nil
    (let ((request (fn-bpo-request-message
                    bpo-state (nth 1 record) (nth 2 record) (nth 3 record))))
      (and (consp request)
           (equal (nth 4 record)
                  (fn-bpa-request-destination-eid request))))))

; The destination route is supplied independently from trusted configuration.
; It is deliberately distinct from the durable work's application peer EID.
(defun fn-bpio-bound-observation (bpo-state work-id attempt-id generation
                                       configured-bp-destination own-bp-eid line)
  (declare (xargs :guard t))
  (let* ((observation (fn-bpio-decode line))
         (request (fn-bpo-request-message
                   bpo-state work-id attempt-id generation)))
    (if (and (consp observation) (consp request)
             (fn-bp-journal-textp work-id)
             (fn-bp-journal-textp attempt-id)
             (fn-bp-u64p generation)
             (fn-bpio-eid-fieldp configured-bp-destination)
             (fn-bpio-eid-fieldp own-bp-eid)
             (equal (nth 0 observation)
                    (fn-bpa-request-destination-eid request))
             (equal (nth 1 observation) configured-bp-destination)
             (equal (nth 2 observation) own-bp-eid))
        (list :ok (list :ion-observed work-id attempt-id generation
                        (nth 0 observation) (nth 1 observation)
                        (nth 2 observation) (nth 3 observation)
                        (nth 4 observation)))
      (list :error :observation-refused))))

(defthm fn-bpio-bound-observation-binds-current-request-and-route
  (implies (equal (car (fn-bpio-bound-observation
                         bpo-state work-id attempt-id generation
                         bp-destination own-eid line)) :ok)
           (let ((request (fn-bpo-request-message
                           bpo-state work-id attempt-id generation))
                 (observed (fn-bpio-decode line)))
             (and (consp request)
                  (consp observed)
                  (equal (nth 0 observed)
                         (fn-bpa-request-destination-eid request))
                  (equal (nth 1 observed) bp-destination)
                  (equal (nth 2 observed) own-eid))))
  :hints (("Goal" :in-theory (enable fn-bpio-bound-observation))))
