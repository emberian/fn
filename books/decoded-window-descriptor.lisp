; Full stored-window identity. Distinct from a raw :window token.
(in-package "ACL2")
(include-book "payload-lz-dicts")
(include-book "payload-window")

(defun fn-pwz-nth (index fields)
  (declare (xargs :guard (natp index)))
  (if (consp fields)
      (if (zp index) (car fields) (fn-pwz-nth (1- index) (cdr fields)))
    nil))

; Admission examines a fixed number of descriptor cells.
(defun fn-pwz-naturals (count fields)
  (declare (xargs :guard (natp count)))
  (if (zp count) (null fields)
    (and (consp fields) (natp (car fields))
         (fn-pwz-naturals (1- count) (cdr fields)))))

(defun fn-pwz-shipped-idp (id entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (or (and (consp (car entries)) (equal id (caar entries)))
          (fn-pwz-shipped-idp id (cdr entries)))
    nil))

(defun fn-pwz-shipped-dictionary (id entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (if (and (consp (car entries)) (equal id (caar entries)))
          (fn-pwz-nth 2 (car entries))
        (fn-pwz-shipped-dictionary id (cdr entries)))
    nil))

; (file eoff elen poff C decoded-offset trailer N dictionary-ID)
(defun fn-pwz-descriptorp (d)
  (declare (xargs :guard t))
  (and (fn-pwz-naturals 9 d)
       (posp (nfix (fn-pwz-nth 0 d)))
       (<= (nfix (fn-pwz-nth 1 d)) (nfix (fn-pwz-nth 3 d)))
       (<= (+ (nfix (fn-pwz-nth 3 d)) (nfix (fn-pwz-nth 4 d))) (+ (nfix (fn-pwz-nth 1 d)) (nfix (fn-pwz-nth 2 d))))
       (<= (nfix (fn-pwz-nth 5 d)) (nfix (fn-pwz-nth 7 d)))
       (fn-pzw-stored-admissiblep (nfix (fn-pwz-nth 4 d)) (nfix (fn-pwz-nth 7 d)))
       (or (equal (fn-pwz-nth 8 d) 0)
           (fn-pwz-shipped-idp (fn-pwz-nth 8 d) (fn-lzd-shipped)))))

(defun fn-pwz-tokenp (token)
  (declare (xargs :guard t))
  (and (consp token) (eq (car token) :decoded-window)
       (consp (cdr token)) (natp (cadr token))
       (fn-pwz-descriptorp (cddr token))))

; Lookup is a core choice over the immutable shipped table. The empty
; dictionary has ID0; an unknown ID must never be treated as that empty preset.
(defun fn-pwz-dictionary (token)
  (declare (xargs :guard t))
  (and (fn-pwz-tokenp token)
       (fn-pwz-shipped-dictionary (fn-pwz-nth 10 token) (fn-lzd-shipped))))

(defun fn-pwz-dict-id-in (dict entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (if (and (consp (car entries)) (equal dict (fn-pwz-nth 2 (car entries))))
          (caar entries)
        (fn-pwz-dict-id-in dict (cdr entries)))
    :unknown-dictionary))

; Captured scalar request identity, including fixed shipped-preset lookup.
; The selected-runtime demand must fund this lookup on each actual call.
(defun fn-pwz-cold-descriptor (file eoff elen poff compressed trailer decoded dict i)
  (declare (xargs :guard t))
  (list file eoff elen poff compressed i trailer decoded
        (if (null dict) 0 (fn-pwz-dict-id-in dict (fn-lzd-shipped)))))

(in-theory (disable fn-pwz-nth fn-pwz-shipped-idp fn-pwz-shipped-dictionary fn-pwz-naturals fn-pwz-descriptorp fn-pwz-tokenp
                    fn-pwz-dictionary fn-pwz-dict-id-in fn-pwz-cold-descriptor))
