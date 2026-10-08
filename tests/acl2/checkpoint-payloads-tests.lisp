; Witnesses and teeth for books/checkpoint-payloads.lisp (lane s-cpl).
;
; Ground store: a 10-octet file F (committed length L = 10), a delta of three
; payloads (one empty).  (Attachments evaluate in assert-event: the seal is
; fn-blake3's.)  Each keystone has a reachable positive witness asserting the
; whole antecedent and conclusion; each tooth names the omitted hypothesis,
; checks the retained ones, the failure of the omitted one and of the
; conclusion.  Corrupted-state witnesses are labelled.

(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/checkpoint-payloads")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *cpl-f* '(9 9 9 9 9 9 9 9 9 9))
(defconst *cpl-ps* '((1 2 3) (4 5) ()))
(defconst *cpl-plan* (fn-cpl-append-plan (len *cpl-f*) *cpl-ps*))
(defconst *cpl-bytes* (car *cpl-plan*))
(defconst *cpl-refs* (cadr *cpl-plan*))
(defconst *cpl-full* (append *cpl-f* *cpl-bytes*))

; CPL-1 positive: premises hold, the plan is the delta's frames, O(delta), the
; refs resolve to the delta's payloads in the file after the append.
(assert-event
 (and (true-listp *cpl-f*) (fn-cpl-payload-listp *cpl-ps*)
      (equal *cpl-bytes* (fn-cpl-frames *cpl-ps*))
      (equal (len *cpl-bytes*) (fn-cpl-delta-octets *cpl-ps*))
      (equal (fn-cpl-delta-octets *cpl-ps*) (+ 5 (* 69 3)))
      (equal *cpl-refs* '((47 3) (119 2) (190 0)))
      (equal (fn-cpl-open-all *cpl-refs* *cpl-full*) (fn-cpl-wrap *cpl-ps*))))

; CPL-1 tooth: refs planned at offset 0 instead of the committed length L
; (the hypothesis (equal l (len f)) omitted): premises hold, l /= (len f), the
; refs do not resolve.
(assert-event
 (let ((bad (fn-cpl-refs 0 *cpl-ps*)))
   (and (true-listp *cpl-f*) (fn-cpl-payload-listp *cpl-ps*)
        (not (equal 0 (len *cpl-f*)))
        (not (equal (fn-cpl-open-all bad *cpl-full*) (fn-cpl-wrap *cpl-ps*))))))

; CPL-2 positive: a root of committed length C = 82 (F and the first frame)
; resolves its refs identically in the full file and in the file cut at C with
; ANY tail (here zeros, as a filesystem may expose after a crash).
(assert-event
 (let* ((c 82) (root-refs (list (car *cpl-refs*)))
        (cut (append (take c *cpl-full*) '(0 0 0 0 0 0 0 0 0 0 0 0))))
   (and (<= c (len *cpl-full*)) (<= c (len cut))
        (equal (take c cut) (take c *cpl-full*))
        (fn-cpl-refs-coveredp root-refs c)
        (fn-cpl-durable-rootp c root-refs cut)
        (equal (fn-cpl-open-all root-refs cut) (fn-cpl-open-all root-refs *cpl-full*))
        (equal (fn-cpl-open-all root-refs cut) '(((1 2 3)))))))

; CPL-2 tooth: a root whose committed length counts frames not yet durable
; (C = the full length, the file cut after the first frame).  The retained
; hypotheses hold (the refs are covered by C, the cut agrees with the full file
; on its own length); the omitted one, C <= (len cut), fails, and so does the
; conclusion: the second and third refs do not resolve in the cut.
(assert-event
 (let* ((c (len *cpl-full*)) (cut (take 82 *cpl-full*)))
   (and (fn-cpl-refs-coveredp *cpl-refs* c)
        (equal cut (take (len cut) *cpl-full*))
        (not (<= c (len cut)))
        (not (fn-cpl-durable-rootp c *cpl-refs* cut))
        (not (equal (fn-cpl-open-all *cpl-refs* cut)
                    (fn-cpl-open-all *cpl-refs* *cpl-full*))))))

; CPL-2 tooth: the coverage hypothesis omitted.  A ref past C resolves in the
; full file and not in the cut that agrees with it below C.
(assert-event
 (let* ((c 82) (cut (take c *cpl-full*)))
   (and (<= c (len cut)) (equal (take c cut) (take c *cpl-full*))
        (not (fn-cpl-refs-coveredp (list (cadr *cpl-refs*)) c))
        (not (equal (fn-cpl-open-all (list (cadr *cpl-refs*)) cut)
                    (fn-cpl-open-all (list (cadr *cpl-refs*)) *cpl-full*))))))

; The verified read agrees with the interface's resolve (books/checkpoint-payload-ref).
(assert-event
 (and (equal (fn-cpl-open (car *cpl-refs*) *cpl-full*)
             (list (fn-cpl-resolve (car *cpl-refs*) *cpl-full*)))
      (equal (fn-cpl-resolve (cadr *cpl-refs*) *cpl-full*) '(4 5))
      (eq (fn-cpl-resolve (cadr *cpl-refs*) (take 100 *cpl-full*)) :absent)))

; CPL-2 labelled corrupted-state witness: one flipped payload octet inside a
; committed frame is refused by the trailer, not returned.
(assert-event
 (let ((bad (update-nth 48 77 *cpl-full*)))
   (and (equal (fn-cpl-open (car *cpl-refs*) *cpl-full*) '((1 2 3)))
        (equal (fn-cpl-open (car *cpl-refs*) bad) nil))))

; CPL-3 positive: compaction of the live refs {first, third} into a fresh file.
(assert-event
 (let* ((live (list (car *cpl-refs*) (caddr *cpl-refs*)))
        (cp (fn-cpl-compact-plan *cpl-full* live))
        (nf (car cp)) (m (cadr cp)))
   (and (fn-cpl-all-openp live *cpl-full*)
        (equal (fn-cpl-open-all m nf) (fn-cpl-open-all live *cpl-full*))
        (equal (len nf) (+ (fn-cpl-ref-lens live) (* 69 (len live))))
        (< (len nf) (len *cpl-full*))
        (equal m '((37 3) (109 0))))))

; CPL-3 concurrent delta: the compacted file followed by one delta append.
(assert-event
 (let* ((live (list (car *cpl-refs*) (caddr *cpl-refs*)))
        (cp (fn-cpl-compact-plan *cpl-full* live))
        (nf (car cp)) (ap (fn-cpl-append-plan (len nf) '((7))))
        (g (append nf (car ap))))
   (equal (fn-cpl-open-all (append (cadr cp) (cadr ap)) g)
          '(((1 2 3)) (NIL) ((7))))))

; CPL-3 tooth: the all-open hypothesis omitted.  A dead ref (past the end of
; the file) is among the refs: the premises hold, the hypothesis fails, and the
; map does not give the same answers before and after.
(assert-event
 (let* ((dead '(500 4))
        (refs (list (car *cpl-refs*) dead))
        (cp (fn-cpl-compact-plan *cpl-full* refs)))
   (and (true-listp *cpl-full*) (true-list-listp refs)
        (not (fn-cpl-all-openp refs *cpl-full*))
        (not (equal (fn-cpl-open-all (cadr cp) (car cp))
                    (fn-cpl-open-all refs *cpl-full*))))))
