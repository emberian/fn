; PRF-1079: executable physical replay witnesses using a constrained, finite
; test disk. The attached functions discharge the original durable constraints.
(in-package "ACL2")
(include-book "statement-recover-stream-tests")

(defconst *sspt-r1* (fn-record-encode-impl *ssrt-article1*))
(defconst *sspt-r2* (fn-record-encode-impl *ssrt-article2*))
(defconst *sspt-k1* (- (len *sspt-r1*) (+ 3 (fn-arx-record-suffix-len *ssrt-article1*))))
(defconst *sspt-z1*
 (fn-lzr-frame 0 *sspt-k1* 3
  (append (take *sspt-k1* *sspt-r1*) (nthcdr (+ 3 *sspt-k1*) *sspt-r1*))
  '(1 3 0 252 255 65 13 10)))
(make-event `(defconst *sspt-file3* ',(fn-lg-frame (make-list 32 :initial-element 0) (list *sspt-r1*))))
(make-event `(defconst *sspt-file4* ',(fn-lg-frame (make-list 32 :initial-element 0) (list *sspt-r2*))))
(make-event `(defconst *sspt-file5* ',(fn-lg-frame (make-list 32 :initial-element 0) (list *sspt-z1*))))
(defun sspt-octet (file pos)
 (declare (xargs :guard t))
 (let ((x (nth (nfix pos) (cond ((equal file 3) *sspt-file3*)
                               ((equal file 4) *sspt-file4*)
                               ((equal file 5) *sspt-file5*) (t nil)))))
  (if (fn-cbor-octetp x) x 0)))
(defun sspt-octets (file off len)
 (declare (xargs :guard t :measure (nfix len)))
 (if (zp (nfix len)) nil
  (cons (sspt-octet file off) (sspt-octets file (+ 1 (nfix off)) (1- (nfix len))))))
(defun sspt-realize-octet (file eoff elen poff plen trailer i)
 (declare (xargs :guard t) (ignore eoff elen trailer))
 (nth (nfix i) (sspt-octets file poff plen)))
(defun sspt-realize-octets (file eoff elen poff plen trailer)
 (declare (xargs :guard t) (ignore eoff elen trailer))
 (sspt-octets file poff plen))
(defattach (fn-durable-octet sspt-octet)
            (fn-durable-octets sspt-octets)
            (fn-durable-realize-octet sspt-realize-octet)
            (fn-durable-realize-octets sspt-realize-octets)
 :hints (("Goal" :in-theory (enable fn-cbor-octetp))))

(defun sspt-realize-lz (file eoff elen poff plen trailer n dict)
 (declare (xargs :guard t) (ignore eoff elen trailer))
 (ec-call (fn-lzr-lz-value dict (fn-durable-octets file poff plen) n)))
(defattach (fn-durable-realize-lz sspt-realize-lz)
 :hints (("Goal" :in-theory (enable sspt-realize-lz))))

(defconst *sspt-pos3*
 (list 0 (len *sspt-file3*) 42 (len *sspt-r1*)
       (fn-arx-trailer-nat (fn-lg-trailer *sspt-file3*))))
(defconst *sspt-pos4*
 (list 0 (len *sspt-file4*) 42 (len *sspt-r2*)
       (fn-arx-trailer-nat (fn-lg-trailer *sspt-file4*))))
(defconst *sspt-pos5*
 (list 0 (len *sspt-file5*) 42 (len *sspt-z1*)
       (fn-arx-trailer-nat (fn-lg-trailer *sspt-file5*))))
(defconst *sspt-rs* (list nil *sspt-r1* nil *sspt-r2*))
(defconst *sspt-zs* (list nil *sspt-z1* nil *sspt-r2*))
(defconst *sspt-ps* (list nil (cons 3 *sspt-pos3*) nil (cons 4 *sspt-pos4*)))
(defconst *sspt-zps* (list nil (cons 5 *sspt-pos5*) nil (cons 4 *sspt-pos4*)))
(defconst *sspt-dicts* (list (cons 0 nil)))
(defthm sspt-nthcdr-at-end
 (implies (and (true-listp xs) (natp i) (<= (len xs) i))
          (equal (nthcdr i xs) nil)))
(defthm sspt-nthcdr-step
 (implies (and (natp i) (< i (len xs)))
          (equal (cons (nth i xs) (nthcdr (1+ i) xs)) (nthcdr i xs))))
(defthm sspt-arena-observation-is-complete
 (implies (and (true-listp fn-arena) (natp i) (<= i (len fn-arena)))
  (equal (ssrt-arena-list i fn-arena) (nthcdr i fn-arena)))
 :hints (("Goal" :induct (ssrt-arena-list i fn-arena)
                 :in-theory (e/d (ssrt-arena-list) (nthcdr nth)))))

(defun sspt-run-in (rs ps mode fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((good (fn-arena-p fn-arena)))
  (mv-let (acc fn-arena)
   (fn-ssr-intern-step (fn-ssr-seed (fn-stxk-initial-context 0))
                      (append *ssrt-a* *ssrt-b*) rs ps mode *sspt-dicts* fn-arena)
   (mv (list good acc (ssrt-arena-list 0 fn-arena) (fn-arena-p fn-arena)) fn-arena))))
(defun sspt-run (rs ps mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (out fn-arena) (sspt-run-in rs ps mode fn-arena) out)))
(defun sspt-faithful-p (rs ps)
 (declare (xargs :verify-guards nil))
 (if (atom rs) t
  (and (or (atom (car ps))
           (equal (fn-durable-octets (nfix (caar ps))
                     (nfix (nth 2 (cdar ps))) (len (car rs))) (car rs)))
       (sspt-faithful-p (cdr rs) (cdr ps)))))
(defthm sspt-faithful-is-literal-hypothesis
 (equal (sspt-faithful-p rs ps) (fn-arx-faithful-p rs ps))
 :hints (("Goal" :in-theory (enable fn-arx-faithful-p))))
(assert-event
 (and (fn-arx-extent-of 3 *sspt-pos3* *sspt-r1* *ssrt-article1*)
      (car (sspt-run *sspt-rs* *sspt-ps* :extent))
      (cadddr (sspt-run *sspt-rs* *sspt-ps* :extent))
      (cadddr (sspt-run nil nil :resident))
      (sspt-faithful-p *sspt-rs* *sspt-ps*)
      (equal (sspt-run *sspt-rs* *sspt-ps* :extent)
             (sspt-run nil nil :resident))))
(assert-event
 (and (fn-lzr-extent-of 5 *sspt-pos5* *sspt-z1* '(65 13 10) *sspt-dicts*)
      (car (sspt-run *sspt-zs* *sspt-zps* :lz))
      (cadddr (sspt-run *sspt-zs* *sspt-zps* :lz))
      (cadddr (sspt-run nil nil :resident))
      (sspt-faithful-p *sspt-zs* *sspt-zps*)
      (equal (sspt-run *sspt-zs* *sspt-zps* :lz)
             (sspt-run nil nil :resident))))

; Hypothesis removal, separately for each physical theorem. The descriptor
; is structurally valid but names the zero-filled absent file 9 instead of
; the committed record. This is a modeled unfaithful read, not proof search.
(assert-event
 (let ((ps (list nil (cons 9 *sspt-pos3*) nil (cons 4 *sspt-pos4*))))
  (and (not (sspt-faithful-p *sspt-rs* ps))
       (car (sspt-run *sspt-rs* ps :extent))
       (cadddr (sspt-run *sspt-rs* ps :extent))
       (cadddr (sspt-run nil nil :resident))
       (not (equal (sspt-run *sspt-rs* ps :extent)
                   (sspt-run nil nil :resident))))))
(assert-event
 (let ((ps (list nil (cons 9 *sspt-pos5*) nil (cons 4 *sspt-pos4*))))
  (and (not (sspt-faithful-p *sspt-zs* ps))
       (car (sspt-run *sspt-zs* ps :lz))
       (cadddr (sspt-run *sspt-zs* ps :lz))
       (cadddr (sspt-run nil nil :resident))
       (not (equal (sspt-run *sspt-zs* ps :lz)
                   (sspt-run nil nil :resident))))))
