; One tagged source byte stream shared by census and image emission.
; Resident children retain their existing representation and exact API.
(in-package "ACL2")
(include-book "history-record-cursor")
(include-book "history-cold-record-runtime")

(defun fn-hsrcb-coldp (c)
  (declare (xargs :guard t))
  (and (fn-hrcur-widthp c 2) (eq (fn-hrcur-field 0 c) :cold)))

(defun fn-hsrcb-begin (source capture lease)
  (declare (xargs :guard t))
  (if (and (fn-hrcur-widthp source 2) (eq (fn-hrcur-field 0 source) :decoded))
      (list :cold (fn-hrcur-cold-begin source capture lease))
    (fn-hrcur-byte-begin source capture lease)))

(defun fn-hsrcb-demandp (v)
  (declare (xargs :guard t))
  (and (fn-hrcur-widthp v 4) (eq (fn-hrcur-field 0 v) :need-byte)))

(defun fn-hsrcb-tick (c)
  (declare (xargs :guard t))
  (if (not (fn-hsrcb-coldp c)) (fn-hrcur-byte-tick c)
    (mv-let (v byte next) (fn-hrcur-cold-tick (fn-hrcur-field 1 c))
      (if (fn-hsrcb-demandp v) (mv v nil c)
        (mv v byte (list :cold next))))))

(defun fn-hsrcb-supply (c position byte)
  (declare (xargs :guard t))
  ; Upstream fn-ocb authenticates the source/pin/kind/coordinate/serial and
  ; actual byte. This child additionally requires its current demand position.
  (if (not (fn-hsrcb-coldp c)) (mv '(:refused :no-cold-demand) nil c)
    (mv-let (demand ignored next) (fn-hsrcb-tick c)
      (declare (ignore ignored next))
      (if (not (and (fn-hsrcb-demandp demand)
                    (equal position (fn-hrcur-field 1 demand))))
          (mv '(:refused :cold-demand-position) nil c)
        (mv-let (v emitted child)
          (fn-hrcur-cold-supply (fn-hrcur-field 1 c) position byte)
          (if (member-eq v '(:continue :emit))
              (mv v emitted (list :cold child))
            (mv v nil c)))))))

(defun fn-hsrcc-begin (source capture lease)
  (declare (xargs :guard t))
  (list :active (fn-hsrcb-begin source capture lease) 0))

(defun fn-hsrcc-tick (c)
  (declare (xargs :guard t))
  (if (not (fn-hsrcb-coldp (fn-hrcur-field 1 c)))
      (fn-hrcur-census-tick c)
  (let ((phase (fn-hrcur-field 0 c)) (bytes (fn-hrcur-field 1 c))
        (n (fn-hrcur-field 2 c)))
    (cond
     ((not (and (fn-hrcur-widthp c 3) (natp n) (< n *fn-hrcur-u64-bound*)))
      (mv '(:refused :census-cursor) nil c))
     ((eq phase :done) (mv :prepared n c))
     ((not (eq phase :active)) (mv '(:refused :census-cursor) nil c))
     (t
      (mv-let (v byte next) (fn-hsrcb-tick bytes)
        (cond
         ((fn-hsrcb-demandp v) (mv v nil c))
         ((eq v :emit)
          (if (and (fn-scc-octetp byte) (< (+ 1 n) *fn-hrcur-u64-bound*))
              (mv :continue nil (list :active next (+ 1 n)))
            (mv '(:refused :codec-width-or-octet) nil c)))
         ((eq v :continue) (mv :continue nil (list :active next n)))
         ((eq v :prepared) (mv :prepared n (list :done next n)))
         (t (mv v nil c)))))))))

(defun fn-hsrcc-supply (c position byte)
  (declare (xargs :guard t))
  (let ((n (fn-hrcur-field 2 c)))
    (if (not (and (fn-hrcur-widthp c 3) (eq (fn-hrcur-field 0 c) :active)
                  (natp n) (< n *fn-hrcur-u64-bound*)))
        (mv '(:refused :census-cursor) c)
      (mv-let (v emitted next) (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)
        (cond
         ((eq v :emit)
          (if (and (fn-scc-octetp emitted) (< (+ 1 n) *fn-hrcur-u64-bound*))
              (mv :continue (list :active next (+ 1 n)))
            (mv '(:refused :codec-width-or-octet) c)))
         ((eq v :continue) (mv :continue (list :active next n)))
         (t (mv v c)))))))

; Exact resident compatibility: cold support does not broaden old byte proofs.
(defthm fn-hsrcb-resident-begin-by-definition
  (equal (fn-hsrcb-begin (list :resident row) capture lease)
         (fn-hrcur-byte-begin (list :resident row) capture lease)))

(defthm fn-hsrcc-resident-begin-by-definition
  (equal (fn-hsrcc-begin (list :resident row) capture lease)
         (fn-hrcur-census-begin (list :resident row) capture lease))
  :hints (("Goal" :in-theory (enable fn-hrcur-census-begin))))

(defthm fn-hsrcb-resident-invariant-not-cold
  (implies (fn-hrcur-byte-invariantp c) (not (fn-hsrcb-coldp c)))
  :hints (("Goal" :in-theory (enable fn-hrcur-byte-invariantp fn-hrcur-widthp))))

(defthm fn-hsrcb-resident-tick-by-definition
  (implies (not (fn-hsrcb-coldp c))
           (equal (fn-hsrcb-tick c) (fn-hrcur-byte-tick c))))

(defthm fn-hsrcc-resident-tick-by-definition
  (implies (fn-hrcur-census-invariantp c)
           (equal (fn-hsrcc-tick c) (fn-hrcur-census-tick c)))
  :hints (("Goal" :in-theory (e/d (fn-hrcur-census-invariantp)
                  (fn-hrcur-byte-invariantp fn-hrcur-census-tick)))))

(in-theory (disable fn-hsrcb-coldp fn-hsrcb-begin fn-hsrcb-tick
                    fn-hsrcb-supply fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply))
