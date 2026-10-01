; One bounded primitive input selection from an existing canonical command.
; No action ticket/current grant, state advance, I/O or completion is minted.
(in-package "ACL2")
(include-book "bpsec-input-plan")

; RFC9173 input literals are at most three uint64 heads (27 octets).
; This grammar bound never limits source data; invalid huge literal lists are
; rejected after27 cells rather than measured/revalidated in full.
(defun fn-bps-input-literal-length (left octets)
 (declare (xargs :guard t :measure (nfix left)))
 (cond ((atom octets) (if (null octets) 0 -1))
       ((or (zp (nfix left)) (not (fn-cbor-octetp (car octets)))) -1)
       (t (let ((rest (fn-bps-input-literal-length (1- (nfix left)) (cdr octets))))
            (if (< rest 0) -1 (1+ rest))))))

(defun fn-bps-input-command-length (command)
 (declare (xargs :guard t))
 (cond ((and (fn-bps-fixed-recordp 2 command)
             (eq (fn-bps-field 0 command) :bps-literal))
        (fn-bps-input-literal-length 27 (fn-bps-field 1 command)))
       ((fn-bps-input-spanp command) (nfix (fn-bps-field 3 command)))
       (t -1)))

; Bounded literal copy only. Source spans are never materialized here.
(defun fn-bps-input-literal-window (offset count octets)
 (declare (xargs :guard t :measure (+ (nfix offset) (nfix count))))
 (cond ((zp (nfix count)) nil)
       ((zp (nfix offset))
        (cons (fn-cbor-ag-car octets)
              (fn-bps-input-literal-window 0 (1- (nfix count)) (fn-cbor-ag-cdr octets))))
       (t (fn-bps-input-literal-window (1- (nfix offset)) count (fn-cbor-ag-cdr octets)))))

(local (defthm fn-bps-input-literal-length-integer
 (integerp (fn-bps-input-literal-length left octets))
 :hints (("Goal" :induct (fn-bps-input-literal-length left octets)))))
(local (defthm fn-bps-input-command-length-integer
 (integerp (fn-bps-input-command-length command))))

; Ready fixed6:tag,descriptor,role,exact selected literal/span,count,nextoffset.
; The caller retains the original command and pending action identity, obtains
; source bytes only through its issued token and commits the returned offset
; only after the matching actual primitive update. A ready shape is no grant.
(defun fn-bps-input-fragment (descriptor role command offset quantum)
 (declare (xargs :guard t))
 (let ((total (fn-bps-input-command-length command)))
  (cond
   ((not (fn-bps-opp descriptor)) (list :refused :invalid-descriptor))
   ((not (if (eq (fn-bps-field 1 descriptor) :verify-bib) (eq role :hmac)
           (member-equal role '(:aad :ciphertext)))) (list :refused :input-role))
   ((or (< total 0) (and (eq role :ciphertext) (not (fn-bps-input-spanp command))))
    (list :refused :input-command))
   ((or (not (fn-bps-uintp offset)) (< total (nfix offset))) (list :refused :input-offset))
   ((or (not (fn-bps-uintp quantum)) (< 64 (nfix quantum))) (list :refused :input-quantum))
   ((equal total offset) (list :input-complete descriptor role))
   ((equal quantum 0) (list :yield descriptor role))
   (t
    (let* ((count (min (nfix quantum) (- total (nfix offset))))
           (fragment
            (if (eq (fn-bps-field 0 command) :bps-literal)
             (list :bps-literal (fn-bps-input-literal-window offset count (fn-bps-field 1 command)))
             (list :bps-span (fn-bps-field 1 command)
                    (+ (nfix (fn-bps-field 2 command)) (nfix offset)) count))))
     (list :bps-input-fragment descriptor role fragment count (+ (nfix offset) count)))))))

(defthm fn-bps-input-fragment-ready-count-bounded
 (let ((result (fn-bps-input-fragment descriptor role command offset quantum)))
  (implies (eq (fn-bps-field 0 result) :bps-input-fragment)
   (and (natp (fn-bps-field 4 result))
        (< 0 (fn-bps-field 4 result))
        (<= (fn-bps-field 4 result) (nfix quantum))
        (<= (fn-bps-field 4 result) 64)
        (equal (fn-bps-field 5 result)
               (+ (nfix offset) (fn-bps-field 4 result))))))
 :hints (("Goal" :in-theory (e/d (fn-bps-input-fragment fn-bps-field)
  (fn-bps-opp fn-bps-input-spanp fn-bps-input-command-length
   fn-bps-input-literal-window fn-bps-input-literal-length)))))
