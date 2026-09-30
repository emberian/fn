; R child2: one consumer decision and its retained committed publication.
; Fixed shape is a format boundary, not a proof of account authorization.
(in-package "ACL2")
(include-book "snapshot-source-token")

(defun fn-cpub-make (cp root fence-count)
 (declare (xargs :guard t))
 (list :ok cp root fence-count))

(defun fn-cpub-cp7p (cp)
 (declare (xargs :guard t))
 (and (fn-omk-widthp cp 7) (eq (fn-omk-at 0 cp) :consumer-state)
      (fn-omk-widthp (fn-omk-at 6 cp) 6)
      (eq (fn-omk-at 0 (fn-omk-at 6 cp)) :authority)))

(defun fn-cpub-priorlessp (cp)
 ; A new4 may retain an in-progress first adoption. No committed root yet.
 (declare (xargs :guard t))
 (let ((a (fn-omk-at 6 cp)))
  (or (null cp)
   (and (fn-cpub-cp7p cp) (equal (fn-omk-at 1 a) 0)
       (equal (fn-omk-at 2 a) 1) (null (fn-omk-at 3 a))
       (null (fn-omk-at 4 a))))))

(defun fn-cpub-untouchedp (cp)
 ; Legacy2 supplies no persisted policy. Only this exact initial authority
 ; is rootless. Entries and the other CP fields remain their own types.
 (declare (xargs :guard t))
 (and (fn-cpub-priorlessp cp) (null (fn-omk-at 5 (fn-omk-at 6 cp)))))

(defun fn-cpub-root-shapep (root)
 (declare (xargs :guard t))
 (and (fn-omk-widthp root 4) (eq (fn-omk-at 0 root) :account-root)
      (natp (fn-omk-at 1 root)) (< (fn-omk-at 1 root) 8)))

(defun fn-cpub-readout (consumer)
 ; Same-parser provenance and full CP/root correspondence are carried by
 ; the caller. This checks only the fixed discriminator and scalar fields.
 (declare (xargs :guard t))
 (let ((cp (fn-omk-at 1 consumer)) (root (fn-omk-at 2 consumer))
       (count (fn-omk-at 3 consumer)))
  (cond
   ((not (and (eq (fn-omk-at 0 consumer) :ok)
              (or (null cp) (fn-cpub-cp7p cp))))
    '(:refused :consumer-publication-shape))
   ((fn-omk-widthp consumer 2)
    (if (fn-cpub-untouchedp cp) (fn-cpub-make cp nil nil)
      '(:refused :consumer-publication-missing)))
   ((not (fn-omk-widthp consumer 4))
    '(:refused :consumer-publication-width))
   ((and (null root) (null count) (fn-cpub-priorlessp cp)) consumer)
   ((and (fn-cpub-cp7p cp) (fn-cpub-root-shapep root) (natp count)) consumer)
   (t '(:refused :consumer-publication-fields)))))

(defun fn-cpub-retain-produced (prior produced)
 ; PRODUCED is the one actual paired decision full6. A non-fence event
 ; returns NIL publication; retain the previous root/count literally.
 (declare (xargs :guard t))
 (let* ((old (fn-cpub-readout prior)) (cp (fn-omk-at 1 produced))
        (root (fn-omk-at 2 produced)) (count (fn-omk-at 3 produced)))
  (cond
   ((not (and (eq (fn-omk-at 0 old) :ok)
              (fn-omk-widthp produced 6) (eq (fn-omk-at 0 produced) :ok)
              (or (null cp) (fn-cpub-cp7p cp))))
    '(:refused :consumer-produced-shape))
   ((null root)
    (fn-cpub-readout (fn-cpub-make cp (fn-omk-at 2 old) (fn-omk-at 3 old))))
   ((and (fn-cpub-cp7p cp) (fn-cpub-root-shapep root) (natp count))
    (fn-cpub-make cp root count))
   (t '(:refused :consumer-produced-publication)))))

(defun fn-cpub-namespace-match (a b n)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (and (null a) (null b))
  (and (consp a) (consp b) (natp (car a)) (< (car a) 256)
       (natp (car b)) (< (car b) 256) (equal (car a) (car b))
       (fn-cpub-namespace-match (cdr a) (cdr b) (1- n)))))

(defun fn-cpub-capture (cp sidecar epoch event-count)
 ; Capture is under the actual owner's same mutation fence. Sidecar/CP
 ; semantic correspondence is maintained by its publication producer.
 (declare (xargs :guard t))
 (let ((a (fn-omk-at 6 cp)))
  (cond
   ((not (and (natp epoch) (natp event-count)))
    '(:refused :consumer-capture-coordinate))
   ((null sidecar)
    (if (fn-cpub-priorlessp cp) (fn-cpub-make cp nil nil)
      '(:refused :consumer-publication-missing)))
   ((and (fn-cpub-cp7p cp) (fn-omk-widthp sidecar 6)
         (eq (fn-omk-at 0 sidecar) :ready)
         (equal (fn-omk-at 1 sidecar) epoch)
         (fn-cpub-namespace-match (fn-omk-at 2 sidecar) (fn-omk-at 3 a) 40)
         (natp (fn-omk-at 3 sidecar))
         (equal (fn-omk-at 3 sidecar) (fn-omk-at 1 a))
         (natp (fn-omk-at 4 sidecar))
         (<= (fn-omk-at 4 sidecar) event-count)
         (fn-cpub-root-shapep (fn-omk-at 5 sidecar)))
    (fn-cpub-make cp (fn-omk-at 5 sidecar) (fn-omk-at 4 sidecar)))
   (t '(:refused :consumer-publication-coordinate)))))

(in-theory (disable fn-cpub-make fn-cpub-cp7p fn-cpub-priorlessp
 fn-cpub-untouchedp fn-cpub-root-shapep fn-cpub-readout
 fn-cpub-retain-produced fn-cpub-namespace-match fn-cpub-capture))
