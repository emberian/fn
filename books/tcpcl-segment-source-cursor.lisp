; Bounded completion of the actual reversed TCPCL segment chain. Internal
; registered producer component, never an installed source/constructor grant.
; The chain stays borrowed until concrete publication and alias joins.
(in-package "ACL2")
(include-book "cbor")
(set-verify-guards-eagerness 2)

; job9(tag,phase,count,copied,reversed,forward,current,reason,original-root).
; Original segment root stays retained through publication/abort and real joins.
; Begin requires the exact maintained TCPCL count, not LEN of the source.
(defun fn-tsc-begin (reverse-segments count)
 (declare (xargs :guard t))
 (if (and (integerp count) (<= 0 count) (<= count 18446744073709551615))
  (list :tcl-source :reverse count 0 reverse-segments nil nil nil reverse-segments)
  (list :tcl-source :refused 0 0 reverse-segments nil nil :source-count-domain reverse-segments)))
(defun fn-tsc-at (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (fn-cbor-ag-car x) (fn-tsc-at (1- n) (fn-cbor-ag-cdr x))))
(defun fn-tsc-next (job phase count copied reversed forward current reason)
 (declare (xargs :guard t))
 (list :tcl-source phase count copied reversed forward current reason (fn-tsc-at 8 job)))

; One unit is one chunk-spine move, one chunk selection, or one byte. Invalid
; internal source bytes/counts refuse; no truncation and no sanitization.
(defun fn-tsc-one (job)
 (declare (xargs :guard t))
 (let ((phase (fn-tsc-at 1 job)) (count (fn-tsc-at 2 job))
       (copied (fn-tsc-at 3 job)) (reversed (fn-tsc-at 4 job))
       (forward (fn-tsc-at 5 job)) (current (fn-tsc-at 6 job)))
  (cond
   ((not (and (eq (fn-tsc-at 0 job) :tcl-source)
              (natp count) (natp copied) (<= copied count)))
    (mv :refused nil job))
   ((eq phase :reverse)
    (cond ((consp reversed)
           (mv :yield nil (fn-tsc-next job :reverse count copied (cdr reversed)
                            (cons (car reversed) forward) current nil)))
          ((null reversed)
           (mv :yield nil (fn-tsc-next job :copy count copied nil forward current nil)))
          (t (mv :refused nil (fn-tsc-next job :refused count copied reversed forward current
                              :source-chain)))))
   ((eq phase :copy)
    (cond
     ((consp current)
      (cond ((not (fn-cbor-octetp (car current)))
             (mv :refused nil (fn-tsc-next job :refused count copied nil forward current
                                 :source-octet)))
            ((equal copied count)
             (mv :refused nil (fn-tsc-next job :refused count copied nil forward current
                                 :source-count-overrun)))
            (t (mv :source-byte (car current)
                   (fn-tsc-next job :copy count (1+ copied) nil forward (cdr current) nil)))))
     ((not (null current))
      (mv :refused nil (fn-tsc-next job :refused count copied nil forward current :source-chunk)))
     ((consp forward)
      (mv :yield nil (fn-tsc-next job :copy count copied nil (cdr forward) (car forward) nil)))
     ((not (null forward))
      (mv :refused nil (fn-tsc-next job :refused count copied nil forward nil :source-chain)))
     ((equal copied count)
      (mv :source-complete nil (fn-tsc-next job :done count copied nil nil nil nil)))
     (t (mv :refused nil (fn-tsc-next job :refused count copied nil nil nil :source-count-short)))))
   ((eq phase :done) (mv :source-complete nil job))
   (t (mv :refused nil job)))))

; Return at most64 source bytes and charge every nonterminal cursor action
; against caller quantum. A yielded empty result is NOT a parser window.
(defun fn-tsc-turn-loop (job quantum reverse-bytes used)
 (declare (xargs :guard (and (natp quantum) (<= quantum 64) (true-listp reverse-bytes)
                            (natp used)) :measure (nfix quantum)))
 (if (zp quantum)
  (mv :yield job (reverse reverse-bytes) used)
  (mv-let (word octet next) (fn-tsc-one job)
   (cond
    ((or (eq word :source-complete) (eq word :refused))
     (mv word next (reverse reverse-bytes) (1+ used)))
    (t (fn-tsc-turn-loop next (1- quantum)
          (if (eq word :source-byte) (cons octet reverse-bytes) reverse-bytes)
          (1+ used)))))))
(defun fn-tsc-turn (job quantum)
 (declare (xargs :guard (and (natp quantum) (<= quantum 64))))
 (fn-tsc-turn-loop job quantum nil 0))
