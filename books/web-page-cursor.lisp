; The native web page continuation. The segment vocabulary and escaping are
; web-render's. The guards are verified; the byte refinement to fn-wr-seq is
; not yet proved, and the raw consumer compares its exact bytes to that
; reference.
(in-package "ACL2")
(include-book "web-render")

; (remaining-segments active-kind list-source span-start span-end bol pending)
; List sources and segment tails share the retained plan. Pending is at most
; one escaped source octet (or one percent-encoded source octet).
(defun fn-wpc-cursor (segs)
  (declare (xargs :guard t))
  (list segs nil nil 0 0 t nil))

; What fn-wpc-next may read.  A segment is (KIND . REST); a span segment
; (:s :d :w) names [S, E) with E within the N octets of fn-web-in.  The other
; kinds' REST is a list, only ever taken apart by car/cdr.
(defun fn-wpc-segs-okp (segs n)
  (declare (xargs :guard (natp n)))
  (if (consp segs)
      (let ((seg (car segs)))
        (and (consp seg)
             (or (consp (cdr seg)) (null (cdr seg)))
             (implies (member (car seg) '(:s :d :w))
                      (<= (nfix (cddr seg)) n))
             (fn-wpc-segs-okp (cdr segs) n)))
    (null segs)))

; A cursor over a buffer of N octets: seven fields, a segment list fn-wpc-next
; can pop, and, while a span is open (:s :d), an end within the buffer.
(defun fn-wpc-cursorp (cursor n)
  (declare (xargs :guard (natp n)))
  (and (true-listp cursor)
       (equal (len cursor) 7)
       (fn-wpc-segs-okp (fn-wrq-nth 0 cursor) n)
       (implies (member (fn-wrq-nth 1 cursor) '(:s :d))
                (<= (nfix (fn-wrq-nth 4 cursor)) n))))

; What ONE fn-wpc-next step reads of an N-octet buffer, and no more: the octet
; at S of an open span (and the one after it where a dot may be stuffed), or
; the span of the next :w segment when it is sliced.  The windowed cursor
; (web-article-stream) hands fn-wpc-next such a step over a buffer that holds
; only part of the span list, so this is weaker than fn-wpc-cursorp.
(defun fn-wpc-readyp (cursor n)
  (declare (xargs :guard (natp n)))
  (let ((segs (fn-wrq-nth 0 cursor)) (kind (fn-wrq-nth 1 cursor))
        (s (nfix (fn-wrq-nth 3 cursor))) (e (nfix (fn-wrq-nth 4 cursor)))
        (bol (fn-wrq-nth 5 cursor)) (pending (fn-wrq-nth 6 cursor)))
    (cond
     ((consp pending) t)
     ((member kind '(:m :t :u)) t)
     ((member kind '(:s :d))
      (and (implies (< s e) (< s n))
           (implies (and (equal kind :d) bol (< (1+ s) e)) (< (1+ s) n))))
     ((consp segs)
      (let ((seg (car segs)))
        (and (or (consp seg) (null seg))
             (or (consp (cdr seg)) (null (cdr seg)))
             (implies (and (equal (car seg) :w)
                           (< (nfix (cadr seg)) (nfix (cddr seg)))
                           (<= (- (nfix (cddr seg)) (nfix (cadr seg))) *fn-w47-max*))
                      (<= (nfix (cddr seg)) n)))))
     (t t))))

(defthm fn-wpc-cursorp-readyp
  (implies (fn-wpc-cursorp cursor n) (fn-wpc-readyp cursor n)))

; Total reads of the reply, so that a step needs no evaluated guard: an index
; past the buffer reads nil, exactly the logical value of fn-octets-get there
; (fn-oct-get-is-nth).  Where the cursor is ready (fn-wpc-readyp) the read is
; in range and these are the octets themselves.
(defun fn-wpc-get (i fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard t))
  (if (and (natp i) (< i (fn-octets-len fn-web-in)))
      (fn-octets-get i fn-web-in)
    nil))

(defthm fn-wpc-get-is-octets-get
  (implies (natp i) (equal (fn-wpc-get i fn-web-in) (fn-octets-get i fn-web-in)))
  :hints (("Goal" :in-theory (enable fn-oct-get-is-nth fn-oct-len-is-len))))

; The reverse of the octets emitted, guard t: the traversal is handed nil and
; conses, so its list is always a true list, and the old (reverse rev) is this
; (fn-wpc-rev-is-reverse).
(defun fn-wpc-rev (x acc)
  (declare (xargs :guard t))
  (if (consp x) (fn-wpc-rev (cdr x) (cons (car x) acc)) acc))

(defthm fn-wpc-rev-is-revappend
  (equal (fn-wpc-rev x acc) (revappend x acc)))

(defthm fn-wpc-rev-is-reverse
  (implies (true-listp rev) (equal (fn-wpc-rev rev nil) (reverse rev))))

(defun fn-wpc-slice-loop (i n fn-web-in acc)
  (declare (xargs :stobjs fn-web-in :guard t :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      (fn-wpc-rev acc nil)
    (fn-wpc-slice-loop (1+ i) n fn-web-in (cons (fn-wpc-get i fn-web-in) acc))))

(local
 (defthm fn-wpc-slice-loop-is-slice
   (equal (fn-wpc-slice-loop i n fn-web-in acc)
          (revappend acc (fn-oct-slice-list i n fn-web-in)))
   :hints (("Goal" :induct (fn-wpc-slice-loop i n fn-web-in acc)
                   :in-theory (enable fn-oct-slice-list)))))

(defun fn-wpc-slice (i n fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard t))
  (fn-wpc-slice-loop i n fn-web-in nil))

(defthm fn-wpc-slice-is-slice-list
  (equal (fn-wpc-slice i n fn-web-in) (fn-oct-slice-list i n fn-web-in)))

; Total car and cdr (guard t), the logical car and cdr.
(defun fn-wpc-car (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (if (consp x) (car x) nil)))

(defun fn-wpc-cdr (x)
  (declare (xargs :guard t))
  (mbe :logic (cdr x) :exec (if (consp x) (cdr x) nil)))

(defun fn-wpc-next (cursor fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard t))
  (let* ((segs (fn-wrq-nth 0 cursor)) (kind (fn-wrq-nth 1 cursor))
         (xs (fn-wrq-nth 2 cursor)) (s (nfix (fn-wrq-nth 3 cursor)))
         (e (nfix (fn-wrq-nth 4 cursor))) (bol (fn-wrq-nth 5 cursor))
         (pending (fn-wrq-nth 6 cursor)))
    (cond
     ((consp pending)
      (mv t (car pending) (list segs kind xs s e bol (cdr pending)) nil))
     ((member kind '(:m :t :u))
      (if (consp xs)
          (mv nil nil
              (list segs kind (cdr xs) s e bol
                    (case kind
                      (:m (list (car xs)))
                      (:u (fn-wr-escape (fn-wr-pct-encode (list (car xs)))))
                      (otherwise (fn-wr-escape-octet (car xs))))) nil)
        (mv nil nil (fn-wpc-cursor segs) nil)))
     ((member kind '(:s :d))
      (if (< s e)
          (let ((o (fn-wpc-get s fn-web-in)))
            (if (and (equal kind :d) bol (equal o 46) (< (1+ s) e)
                     (equal (fn-wpc-get (1+ s) fn-web-in) 46))
                (mv nil nil (list segs kind nil (1+ s) e nil nil) nil)
              (mv nil nil (list segs kind nil (1+ s) e (equal o 10)
                               (fn-wr-escape-octet o)) nil)))
        (mv nil nil (fn-wpc-cursor segs) nil)))
     ((consp segs)
      (let* ((seg (car segs)) (kind (fn-wpc-car seg))
             (s (nfix (fn-wpc-car (fn-wpc-cdr seg)))) (e (nfix (fn-wpc-cdr (fn-wpc-cdr seg)))))
        (mv nil nil
            (case kind
              ((:m :t :u) (list (cdr segs) kind (fn-wpc-cdr seg) 0 0 t nil))
              (:w (if (<= (- e s) *fn-w47-max*)
                      (list (cdr segs) :t (fn-w47-decode (if (< s e) (fn-wpc-slice s e fn-web-in) nil)) 0 0 t nil)
                    (list (cdr segs) :s nil s e t nil)))
              (otherwise (list (cdr segs) kind nil s e t nil))) nil)))
     (t (mv nil nil cursor t)))))

(defthm fn-wpc-next-cursorp
  ; The step keeps the cursor inside the buffer it reads.
  (implies (and (fn-wpc-cursorp cursor n) (equal n (fn-octets-len fn-web-in)))
           (fn-wpc-cursorp (mv-nth 2 (fn-wpc-next cursor fn-web-in)) n)))

(defthm fn-wpc-next-open-span
  ; A step that leaves a span open (:s :d) leaves a seven-field cursor whose
  ; span is two naturals: what the windowed cursor re-bases.
  (let ((next (mv-nth 2 (fn-wpc-next cursor fn-web-in))))
    (implies (member (fn-wrq-nth 1 next) '(:s :d))
             (and (true-listp next) (equal (len next) 7)
                  (natp (fn-wrq-nth 3 next)) (natp (fn-wrq-nth 4 next))))))

;; fn-wpc-next-open-span in the shape the guard obligations take.
(defthm fn-wpc-next-open-span-numbers
  (implies (member (nth 1 (mv-nth 2 (fn-wpc-next cursor fn-web-in))) '(:s :d))
           (and (acl2-numberp (nth 3 (mv-nth 2 (fn-wpc-next cursor fn-web-in))))
                (acl2-numberp (nth 4 (mv-nth 2 (fn-wpc-next cursor fn-web-in))))
                (consp (mv-nth 2 (fn-wpc-next cursor fn-web-in)))
                (true-listp (mv-nth 2 (fn-wpc-next cursor fn-web-in)))))
  :hints (("Goal" :use (fn-wpc-next-open-span)
                  :in-theory (e/d (fn-wrq-nth-is-nth) (fn-wpc-next-open-span)))))

;; The windowed cursor (web-article-stream) drives fn-wpc-next over segment
;; lists whose spans are not bounded by the buffer: only their shape is
;; known.  A segment is a list headed by one of the vocabulary's kinds; the
;; cursor's kind is one of those or none.
(defconst *fn-wpc-kinds* '(:m :t :u :w :s :d :v-u :v-list))

(defun fn-wpc-wsegsp (segs)
  (declare (xargs :guard t))
  (if (consp segs)
      (let ((seg (car segs)))
        (and (consp seg)
             (member (car seg) *fn-wpc-kinds*)
             (or (consp (cdr seg)) (null (cdr seg)))
             (fn-wpc-wsegsp (cdr segs))))
    (null segs)))

;; What the windowed cursor knows when it hands fn-wpc-next one step.
(defthm fn-wpc-readyp-of-open-span
  ; A cursor on an open span (:s :d) of the N octets in hand.
  (implies (and (natp n) (member kind '(:s :d))
                (or (consp pending)
                    (and (implies (< (nfix s) (nfix e)) (< (nfix s) n))
                         (implies (and (equal kind :d) bol (< (1+ (nfix s)) (nfix e)))
                                  (< (1+ (nfix s)) n)))))
           (fn-wpc-readyp (list segs kind xs s e bol pending) n))
  :hints (("Goal" :in-theory (enable fn-wpc-readyp))))

(defthm fn-wpc-readyp-of-whole-word
  ; A :w segment next, all of whose octets are in hand if it is sliced.
  (implies (and (natp n)
                (implies (and (< (nfix s) (nfix e)) (<= (- (nfix e) (nfix s)) *fn-w47-max*))
                         (<= (nfix e) n)))
           (fn-wpc-readyp (list (cons (cons :w (cons s e)) rest) nil xs s2 e2 bol nil) n))
  :hints (("Goal" :in-theory (enable fn-wpc-readyp))))

(defthm fn-wpc-readyp-of-text-kind
  (implies (member kind '(:m :t :u))
           (fn-wpc-readyp (list segs kind xs s e bol pending) n))
  :hints (("Goal" :in-theory (enable fn-wpc-readyp))))

(defthm fn-wpc-readyp-of-popped-segment
  ; A cursor between segments whose next segment is not a :w slice.
  (implies (and (true-listp cursor) (equal (len cursor) 7)
                (fn-wpc-wsegsp (fn-wrq-nth 0 cursor))
                (not (member (fn-wrq-nth 1 cursor) '(:s :d)))
                (not (equal (car (car (fn-wrq-nth 0 cursor))) :w)))
           (fn-wpc-readyp cursor n))
  :hints (("Goal" :in-theory (enable fn-wpc-readyp))))

(defthm fn-wpc-next-shape
  ; A step keeps a seven-field cursor of the same vocabulary.
  (implies (and (true-listp cursor) (equal (len cursor) 7)
                (fn-wpc-wsegsp (fn-wrq-nth 0 cursor))
                (member (fn-wrq-nth 1 cursor) (cons nil (remove :w *fn-wpc-kinds*)))
                (implies (null (fn-wrq-nth 1 cursor)) (null (fn-wrq-nth 6 cursor))))
           (let ((next (mv-nth 2 (fn-wpc-next cursor fn-web-in))))
             (and (true-listp next) (equal (len next) 7)
                  (fn-wpc-wsegsp (fn-wrq-nth 0 next))
                  (member (fn-wrq-nth 1 next) (cons nil (remove :w *fn-wpc-kinds*)))
                  (implies (null (fn-wrq-nth 1 next)) (null (fn-wrq-nth 6 next)))))))

(defthm fn-wpc-next-not-v-list
  ; Only popping a :v-list segment opens a :v-list span.
  (implies (and (true-listp cursor) (equal (len cursor) 7)
                (fn-wpc-wsegsp (fn-wrq-nth 0 cursor))
                (not (equal (fn-wrq-nth 1 cursor) :v-list))
                (or (member (fn-wrq-nth 1 cursor) '(:m :t :u :s :d))
                    (not (equal (car (car (fn-wrq-nth 0 cursor))) :v-list))))
           (not (equal (fn-wrq-nth 1 (mv-nth 2 (fn-wpc-next cursor fn-web-in))) :v-list))))

(defun fn-wpc-drive (fuel cursor count emitp rev fn-web-in)
  ; The guard is a natural number: fn-wpc-next is total, so the scheduling
  ; quantum needs no recognizer over the segments or the emitted octets.
  (declare (xargs :stobjs fn-web-in :guard (natp fuel)))
  (if (zp fuel)
      (mv (fn-wpc-rev rev nil) cursor (nfix count) nil)
    (mv-let (present octet next done) (fn-wpc-next cursor fn-web-in)
      (if done
          (mv (fn-wpc-rev rev nil) next (nfix count) t)
        (fn-wpc-drive (1- fuel) next (if present (1+ (nfix count)) (nfix count))
                      emitp (if (and present emitp) (cons octet rev) rev) fn-web-in)))))

(defun fn-wpc-step (cursor count emitp fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard t))
  ; Fixed scheduling quantum, not a response length ceiling. The bounded
  ; RFC2047 decoder may additionally inspect at most *fn-w47-max* bytes.
  (fn-wpc-drive 4096 cursor count emitp nil fn-web-in))

; A step is a bounded scheduling quantum: one call emits at most FUEL octets
; (4096 from the host's fn-wpc-step) beyond what it was handed.  The byte
; refinement to fn-wr-seq (driving the cursor to done emits exactly
; fn-wr-seq of the segments over fn-web-in's octets) is proof-owed; the raw
; consumer tests compare those bytes.
(defthm fn-wpc-len-revappend
  (equal (len (revappend a b)) (+ (len a) (len b))))

(defthm fn-wpc-drive-emits-at-most-fuel
  (<= (len (mv-nth 0 (fn-wpc-drive fuel cursor count emitp rev fn-web-in)))
      (+ (len rev) (nfix fuel)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-wpc-next))))
