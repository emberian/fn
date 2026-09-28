; Witnesses and teeth for books/owner-time-journal-writer.lisp (lane
; health-truth-journal, 2026-09-28; PKT-872, PRF-360).  Every file below is
; one the host's calls make (fn-otm-jw-sim composes fn-otm-jw-init, -plan,
; -after, -truncated and -drop) over a segment the host offers (the start
; entry, then a reached run's entries).
(in-package "ACL2")
(include-book "../../books/owner-time-journal-writer")
(include-book "must-fail-checked")

(defun otjw-text (s) (declare (xargs :mode :program)) (fn-osch-text s))
(defun otjw-verdict (s es) (mv-let (v s2) (fn-otm-replay s es) (declare (ignore s2)) v))
(defun otjw-state (s es) (mv-let (v s2) (fn-otm-replay s es) (declare (ignore v)) s2))
(defun otjw-status (file) (mv-let (st es) (fn-otm-jparse file nil nil nil) (declare (ignore es)) st))
(defun otjw-file (e0 es fates)
  (mv-let (w file)
    (fn-otm-jw-sim (fn-otm-jw-init (len (fn-otm-jlines e0))) (fn-otm-jlines e0) es fates)
    (declare (ignore w))
    file))
(defun otjw-whole (e0 es fates)
  (fn-otm-jw-whole (fn-otm-jw-init (len (fn-otm-jlines e0))) es fates))

; A reached segment: the start entry and a run of the host's disk events
; and a note (an issue, two clock events past D and H, the stall's note, the
; completion).
(defconst *otjw-steps*
  (list (list :event :issue 10000 '(2000 6000 250))
        (list :event :clock 12000 nil)
        (list :event :clock 16000 nil)
        (list :note 2 1)
        (list :event :return 40000 nil)))
(defconst *otjw-es*
  (cons (fn-otm-jw-start-entry 9000 1234)
        (mv-let (es s) (fn-otm-run (fn-otm-init) *otjw-steps*) (declare (ignore s)) es)))
(assert-event (equal *otjw-es*
                     '((0 0 9000 1234 0 0 0)
                       (1 3 10000 2000 6000 250 1)
                       (2 1 12000 0 0 0 5)
                       (3 1 16000 0 0 0 6)
                       (4 5 16000 2 1 0 0)
                       (5 4 40000 0 0 0 4))))
; An earlier segment the open's cut left whole (the same run, an earlier start).
(defconst *otjw-e0* (cons (fn-otm-jw-start-entry 100 1000) (cdr *otjw-es*)))
(defconst *otjw-ok* '(t 0 t))
(assert-event (and (fn-otm-run-okp *otjw-steps*)
                   (fn-otm-nat-lists-p *otjw-e0*) (fn-otm-nat-lists-p *otjw-es*)
                   (equal (otjw-verdict (fn-otm-init) *otjw-e0*) :agrees)
                   (equal (otjw-verdict (otjw-state (fn-otm-init) *otjw-e0*) *otjw-es*) :agrees)))

; KEYSTONE fn-otm-jw-file-reads-agrees-or-gap, positive witness (every
; append whole): the file is E0 and the segment, whole, agreeing.
(defconst *otjw-f-all* (otjw-file *otjw-e0* *otjw-es* (list *otjw-ok* *otjw-ok* *otjw-ok* *otjw-ok* *otjw-ok* *otjw-ok*)))
(assert-event (and (equal *otjw-f-all* (fn-otm-jlines (append *otjw-e0* *otjw-es*)))
                   (equal (otjw-status *otjw-f-all*) :whole)
                   (equal (otjw-verdict (fn-otm-init) (fn-otm-journal-read *otjw-f-all*)) :agrees)))

; ENOSPC mid-line, the truncation holding (fate (nil 5 t) on entry 2): the
; five octets are cut back, entry 3 carries the mark, and the replay names
; the gap at 2 -- the first entry lost (fn-otm-jw-gap-is-the-first-lost).
(defconst *otjw-fates-enospc* (list *otjw-ok* *otjw-ok* '(nil 5 t) *otjw-ok* *otjw-ok* *otjw-ok*))
(defconst *otjw-f-enospc* (otjw-file *otjw-e0* *otjw-es* *otjw-fates-enospc*))
(assert-event
 (let ((x (otjw-whole *otjw-e0* *otjw-es* *otjw-fates-enospc*)))
   (and (equal x (list (nth 0 *otjw-es*) (nth 1 *otjw-es*) *fn-otm-mark-entry*
                       (nth 3 *otjw-es*) (nth 4 *otjw-es*) (nth 5 *otjw-es*)))
        (equal *otjw-f-enospc* (fn-otm-jlines (append *otjw-e0* x)))
        (equal (otjw-status *otjw-f-enospc*) :whole)
        (equal (fn-otm-jw-pm-len x *otjw-es*) 2)
        (equal (otjw-verdict (fn-otm-init) (fn-otm-journal-read *otjw-f-enospc*))
               (list :gap (car (nth 2 *otjw-es*))))
        (equal (otjw-verdict (fn-otm-init) (fn-otm-journal-read *otjw-f-enospc*)) '(:gap 2)))))

; The same with the truncation failing (fate (nil 5 nil)): the journal is
; closed for the run, the five octets stay as the tail, the file reads
; :torn and replays to agreement over what landed whole.
(defconst *otjw-f-closed* (otjw-file *otjw-e0* *otjw-es*
                                     (list *otjw-ok* *otjw-ok* '(nil 5 nil) *otjw-ok* *otjw-ok* *otjw-ok*)))
(assert-event (and (equal *otjw-f-closed*
                          (append (fn-otm-jlines (append *otjw-e0* (take 2 *otjw-es*)))
                                  (take 5 (fn-otm-jline (nth 2 *otjw-es*)))))
                   (equal (otjw-status *otjw-f-closed*) :torn)
                   (equal (otjw-verdict (fn-otm-init) (fn-otm-journal-read *otjw-f-closed*)) :agrees)))

; A process death mid-append is that fate as the last: the same file.
(assert-event (equal (otjw-file *otjw-e0* (take 3 *otjw-es*)
                                (list *otjw-ok* *otjw-ok* '(nil 5 nil)))
                     *otjw-f-closed*))

; The sink dropped entry 3 (a :journal-gap item): entry 4 carries the mark.
(assert-event (equal (otjw-verdict (fn-otm-init)
                                   (fn-otm-journal-read
                                    (otjw-file *otjw-e0* *otjw-es*
                                               (list *otjw-ok* *otjw-ok* *otjw-ok* :drop *otjw-ok* *otjw-ok*))))
                     '(:gap 3)))

; The mark itself torn (fate (nil 3 nil) after a loss): nothing but whole
; lines and a fragment; the replay stops where the whole lines stop.
(defconst *otjw-f-mark-torn*
  (otjw-file *otjw-e0* *otjw-es* (list *otjw-ok* :drop '(nil 3 nil) *otjw-ok* *otjw-ok* *otjw-ok*)))
(assert-event (and (equal (otjw-status *otjw-f-mark-torn*) :torn)
                   (equal (otjw-verdict (fn-otm-init) (fn-otm-journal-read *otjw-f-mark-torn*)) :agrees)))

; Mutation witness: the writer before PKT-872 (a failed append left its
; octets and the next line was appended after them) -- the fitness f2-full
; file.  The torn prefix of entry 2 runs into entry 3's line: not a gap.
(defconst *otjw-f-old-writer*
  (append (fn-otm-jlines (append *otjw-e0* (take 2 *otjw-es*)))
          (take 9 (fn-otm-jline (nth 2 *otjw-es*)))
          (fn-otm-jlines (nthcdr 3 *otjw-es*))))
(assert-event (let ((v (otjw-verdict (fn-otm-init) (fn-otm-journal-read *otjw-f-old-writer*))))
                (not (or (equal v :agrees) (and (consp v) (equal (car v) :gap))))))

; The open's cut: the torn file above is cut back to its whole lines
; (fn-otm-jw-open-cut-of-a-written-file), and the chunked step agrees with
; the whole-file cut (fn-otm-jw-open-step-is-the-cut): one chunk here.
(assert-event (equal (fn-otm-jw-open-cut *otjw-f-closed*)
                     (len (fn-otm-jlines (append *otjw-e0* (take 2 *otjw-es*))))))
(assert-event (equal (fn-otm-jw-open-step *otjw-f-closed* 0)
                     (list :cut (fn-otm-jw-open-cut *otjw-f-closed*))))
(assert-event (equal (fn-otm-jw-open-step (otjw-text "12 3") 4096) (list :more 0)))
(assert-event (equal (fn-otm-jw-open-step (otjw-text "12 3") 0) (list :cut 0)))
(assert-event (equal (fn-otm-jw-open-first 10000) (- 10000 4096)))
(assert-event (equal (fn-otm-jw-open-first 100) 0))

; -----------------------------------------------------------------------------
; Teeth: each hypothesis of the keystone removed, the retained ones checked,
; the removed one false, and the conclusion false.
(defun otjw-conclusion (r e0 es fates)
  (let* ((file (otjw-file e0 es fates))
         (x (otjw-whole e0 es fates))
         (m (fn-otm-jw-pm-len x es)))
    (and (not (equal (otjw-status file) :malformed))
         (equal (fn-otm-journal-read file) (append e0 x))
         (equal (otjw-verdict r (fn-otm-journal-read file))
                (if (consp (nthcdr m x))
                    (list :gap (+ 1 (fn-otm-jseq (otjw-state (otjw-state r e0) (take m es)))))
                  :agrees)))))
(assert-event (otjw-conclusion (fn-otm-init) *otjw-e0* *otjw-es* *otjw-fates-enospc*))

; -----------------------------------------------------------------------------
; Teeth: each hypothesis of the keystone removed -- the retained one holds,
; the removed one fails, and the conclusion fails.
(defun otjw-h-e0 (r e0) (equal (otjw-verdict r e0) :agrees))
(defun otjw-h-es (r e0 es) (equal (otjw-verdict (otjw-state r e0) es) :agrees))
(defun otjw-conclusion (r e0 es fates)
  (let* ((file (otjw-file e0 es fates))
         (x (otjw-whole e0 es fates))
         (m (fn-otm-jw-pm-len x es)))
    (and (not (equal (otjw-status file) :malformed))
         (equal (fn-otm-journal-read file) (append e0 x))
         (equal (otjw-verdict r (fn-otm-journal-read file))
                (if (consp (nthcdr m x))
                    (list :gap (+ 1 (fn-otm-jseq (otjw-state (otjw-state r e0) (take m es)))))
                  :agrees)))))
(assert-event (and (otjw-h-e0 (fn-otm-init) *otjw-e0*)
                   (otjw-h-es (fn-otm-init) *otjw-e0* *otjw-es*)
                   (otjw-conclusion (fn-otm-init) *otjw-e0* *otjw-es* *otjw-fates-enospc*)))

; The earlier segment E0 does not replay to agreement (a journaled word the
; event does not decide): its divergence is the file's verdict.
(defconst *otjw-e0-diverged*
  (list (car *otjw-e0*) (cadr *otjw-e0*) '(2 1 12000 0 0 0 7)))
(assert-event (and (not (otjw-h-e0 (fn-otm-init) *otjw-e0-diverged*))
                   (otjw-h-es (fn-otm-init) *otjw-e0-diverged* *otjw-es*)
                   (not (otjw-conclusion (fn-otm-init) *otjw-e0-diverged* *otjw-es* *otjw-fates-enospc*))))
(must-fail-checked
 (defthm otjw-without-the-earlier-segment-agreeing
   (implies (equal (mv-nth 0 (fn-otm-replay (mv-nth 1 (fn-otm-replay r e0)) es)) :agrees)
            (equal (mv-nth 0 (fn-otm-replay r (fn-otm-journal-read
                                                (mv-nth 1 (fn-otm-jw-sim
                                                           (fn-otm-jw-init (len (fn-otm-jlines e0)))
                                                           (fn-otm-jlines e0) es fates)))))
                   (if (consp (nthcdr (fn-otm-jw-pm-len (fn-otm-jw-whole (fn-otm-jw-init (len (fn-otm-jlines e0)))
                                                                         es fates)
                                                        es)
                                      (fn-otm-jw-whole (fn-otm-jw-init (len (fn-otm-jlines e0))) es fates)))
                       (list :gap (+ 1 (fn-otm-jseq
                                        (mv-nth 1 (fn-otm-replay
                                                   (mv-nth 1 (fn-otm-replay r e0))
                                                   (take (fn-otm-jw-pm-len
                                                          (fn-otm-jw-whole (fn-otm-jw-init (len (fn-otm-jlines e0)))
                                                                           es fates)
                                                          es)
                                                         es))))))
                     :agrees)))))

; The offered segment does not replay to agreement (entry 2's word
; tampered): the file's verdict is that divergence, not agreement or a gap.
(defconst *otjw-es-diverged*
  (list (nth 0 *otjw-es*) (nth 1 *otjw-es*) '(2 1 12000 0 0 0 7) (nth 3 *otjw-es*)))
(assert-event (and (otjw-h-e0 (fn-otm-init) *otjw-e0*)
                   (not (otjw-h-es (fn-otm-init) *otjw-e0* *otjw-es-diverged*))
                   (not (otjw-conclusion (fn-otm-init) *otjw-e0* *otjw-es-diverged*
                                         (list *otjw-ok* *otjw-ok* *otjw-ok* *otjw-ok*)))
                   (equal (otjw-verdict (fn-otm-init)
                                        (fn-otm-journal-read
                                         (otjw-file *otjw-e0* *otjw-es-diverged*
                                                    (list *otjw-ok* *otjw-ok* *otjw-ok* *otjw-ok*))))
                          '(:diverged 2))))
(must-fail-checked
 (defthm otjw-without-the-segment-agreeing
   (implies (equal (mv-nth 0 (fn-otm-replay r e0)) :agrees)
            (not (equal (mv-nth 0 (mv-nth 0 (fn-otm-replay r (fn-otm-journal-read
                                                              (mv-nth 1 (fn-otm-jw-sim
                                                                         (fn-otm-jw-init (len (fn-otm-jlines e0)))
                                                                         (fn-otm-jlines e0) es fates))))))
                        :diverged)))))

; fn-otm-jw-gap-is-the-first-lost's own hypothesis: when the first entry
; lost is a start, the gap names the previous segment's successor, not the
; start's 0.
(defconst *otjw-fates-start-lost* (list '(nil 3 t) *otjw-ok* *otjw-ok* *otjw-ok* *otjw-ok* *otjw-ok*))
(assert-event
 (let* ((x (otjw-whole *otjw-e0* *otjw-es* *otjw-fates-start-lost*))
        (m (fn-otm-jw-pm-len x *otjw-es*))
        (v (otjw-verdict (fn-otm-init) (fn-otm-journal-read (otjw-file *otjw-e0* *otjw-es* *otjw-fates-start-lost*)))))
   (and (equal m 0) (consp (nthcdr m x))
        (equal (nth 1 (nth m *otjw-es*)) 0)
        (equal v '(:gap 6))
        (not (equal v (list :gap (car (nth m *otjw-es*))))))))

; The segment corollary (fn-otm-jw-segment-agrees): the host's start line is
; the start entry's line.
(assert-event (equal (fn-otm-start-line 9000 1234) (fn-otm-jline (car *otjw-es*))))

; fn-otm-jw-open-step-cuts-a-written-file: the whole file as one chunk (the
; first chunk of a short file) is cut at its whole lines; teeth for the
; read's invariant: a chunk whose following octets hold an LF (post not
; LF-free) answers :cut 0, not the whole lines.
(defconst *otjw-lines-2* (fn-otm-jlines (append *otjw-e0* (take 2 *otjw-es*))))
(defconst *otjw-frag-2* (take 5 (fn-otm-jline (nth 2 *otjw-es*))))
(assert-event (and (fn-otm-jw-fragp *otjw-frag-2* nil)
                   (equal (append *otjw-lines-2* *otjw-frag-2*) *otjw-f-closed*)
                   (equal (fn-otm-jw-open-step *otjw-f-closed* 0) (list :cut (len *otjw-lines-2*)))))
(assert-event (let ((chunk (take 3 *otjw-f-closed*)) (post (nthcdr 3 *otjw-f-closed*)))
                (and (fn-otm-jw-fragp *otjw-frag-2* nil)
                     (equal (append nil (append chunk post)) *otjw-f-closed*)
                     (equal 0 (len nil))
                     (equal (car (fn-otm-jw-open-step chunk 0)) :cut)
                     (not (fn-otm-jw-no-lf-p post))
                     (not (equal (cadr (fn-otm-jw-open-step chunk 0)) (len *otjw-lines-2*))))))
