; Witnesses and teeth for books/charged-totals-header.lisp (Builder A, lane
; vertical, 2026-10-10; packet build/vertical-runs/ct2/packet-v31.md, whose
; ct31-testq.lsp these are, the test? searches left in the packet).
;
; Two histories: M's two interned HELD rows plus a retention event, and two
; retention events.  The header run of each capture decodes to its fold; the
; file the writer admits is read whole with the fold; the publication input
; Codex found (197,120 octets with H against 197,073) is deferred by the
; setup and refused by the reader; a schema-3 header is refused by name; the
; arena and table writers' admission from a carried total is the reader's;
; a mixed file's header seeds an invalid cache, one capture's a valid one.
(in-package "ACL2")
(include-book "../../books/charged-totals-header")
(include-book "../../books/records-attach")
(include-book "../../books/catalog-record")

(defun htct-row (n)
  (declare (xargs :guard t :verify-guards nil))
  (let ((n (nfix n)))
    (fn-record-make (mod n 3) (mod n 5) (mod n 7)
                    (concatenate 'string "<htct-" (coerce (explode-nonnegative-integer n 10 nil) 'string) "@example.invalid>")
                    (make-list (mod n 11) :initial-element (+ 65 (mod n 26)))
                    (if (evenp n) '("fn.test") '("fn.test" "fn.other"))
                    "o0" "s0" "e0" 4 (+ 841000000 n))))

(defun htct-intern-all (ns fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom ns)
      (mv nil fn-arena)
    (mv-let (row fn-arena) (fn-cat-intern-list (htct-row (car ns)) nil 0 fn-arena)
      (mv-let (rest fn-arena) (htct-intern-all (cdr ns) fn-arena)
        (mv (cons row rest) fn-arena)))))

(defun htct-held-rows (ns)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (htct-intern-all ns fn-arena)
      rows)))

(defconst *ct2-held*
  (append (htct-held-rows '(11 5))
          (list (fn-store-retention-event-make :undertake 2 2 2 "forward" "fwd-subject" "evidence" 4))))
(defconst *ct2-events*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-sct" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-sct" "subject" "evidence" 0)))
(defconst *ct2-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))

(defconst *ct2-cap-held* (fn-sco-capture *ct2-configs* *ct2-held*))
(defconst *ct2-cap-ev* (fn-sco-capture *ct2-configs* *ct2-events*))
(defconst *ct2-tab-ev* (fn-sct-tables-of-capture *ct2-cap-ev* 9 "rev" nil))
(defconst *ct2-progs-ev* (fn-sct-table-programs *ct2-tab-ev* (fn-sco-event-index *ct2-cap-ev*)))
(defconst *ct2-segs* (fn-sct-file-segments *ct2-progs-ev* 64 2))
(defconst *ct2-open-ev*
  (fn-sco-open (fn-sco-capture *ct2-configs* (take 1 *ct2-events*)) *ct2-configs* 8
               (nthcdr 1 *ct2-events*)))
(assert-event (fn-sn-open-okp *ct2-open-ev*))
(defun ct2-seed-no-residency (s header residency)
  (if (and (natp s) (fn-mm-tot-p header) (equal (fn-mm-tot-records header) s))
      (cons s header)
    (cons 0 (fn-ct-zero-tot residency))))


; --- K1/K1w, ground, both histories, any REST (here a stray segment and the
; event file's own segments)
(defconst *ct3-h-ev* (fn-cth-header-of-capture *ct2-cap-ev*))
(defconst *ct3-h-held* (fn-cth-header-of-capture *ct2-cap-held*))
(assert-event (fn-cth-header-rowp *ct3-h-ev*))
(assert-event (fn-cth-header-rowp *ct3-h-held*))
(assert-event (equal (caddr *ct3-h-held*) '(3 5 100 4 40 3489 456 45 :resident)))
(defconst *ct3-hsegs-ev* (fn-cth-header-segments *ct3-h-ev* 2))
(defconst *ct3-hsegs-held* (fn-cth-header-segments *ct3-h-held* 3))
(assert-event (equal (len *ct3-hsegs-ev*) 1))
(assert-event (equal (fn-cth-header-tot *ct3-hsegs-held*) '(3 5 100 4 40 3489 456 45 :resident)))
(assert-event (equal (fn-cth-header-tot (append *ct3-hsegs-ev* *ct2-segs*))
                     (fn-ct-charged *ct2-events* :resident)))
(value-triple (list :header-octets (len (fn-scc-concat *ct3-hsegs-held*))))
; teeth: a flipped octet in the header's chunk, a framing S that is not the
; row's, and a header run of two segments each yield NIL
(defun ct3-flip (segs i)
  (declare (xargs :verify-guards nil))
  (cons (update-nth i (logxor 1 (nth i (car segs))) (car segs)) (cdr segs)))
(assert-event (null (fn-cth-header-tot (ct3-flip *ct3-hsegs-held* 40))))
(assert-event (null (fn-cth-header-tot (fn-sct-run-segments (fn-scc-encode *ct3-h-held*) 1000 99))))
(assert-event (null (fn-cth-header-tot (fn-sct-run-segments (fn-scc-encode *ct3-h-held*) 16 3))))
; tooth: a writer folding (cdr records) writes a row the recognizer refuses
(assert-event (not (fn-cth-header-rowp (fn-cth-header-row 3 (fn-ct-charged (cdr *ct2-held*) :resident)))))

; --- K2, ground (the open over the event history's first record)
(assert-event (equal (fn-mm-tot-plus (caddr (fn-cth-header-of-capture (fn-sco-capture *ct2-configs* (take 1 *ct2-events*))))
                                     (fn-ct-charged (nthcdr 1 *ct2-events*) :resident))
                     (fn-ct-charged (fn-sf-records (fn-sn-files (fn-sn-open-state *ct2-open-ev*))) :resident)))

; --- K3: search, ground, and the fallback tooth (Codex ct2 F2)

(defconst *ct3-other-header*
  (fn-ct-charged (list (fn-store-retention-event-make :undertake 0 0 0 "other" "subject" "evidence" 20)) :resident))
(assert-event (not (fn-ct-totals-cache-validp (fn-cth-installed-seed t 1 *ct3-other-header* :resident)
                                              *ct2-events* :resident)))
(assert-event (fn-ct-totals-cache-validp (fn-cth-installed-seed nil 1 *ct3-other-header* :resident)
                                         *ct2-events* :resident))
(assert-event (fn-ct-totals-cache-validp
               (fn-cth-installed-seed t 2 (fn-ct-charged (take 2 *ct2-held*) :resident) :resident)
               *ct2-held* :resident))
; tooth: M's residency condition removed
(assert-event (not (fn-ct-totals-cache-validp
                    (ct2-seed-no-residency 3 (fn-ct-charged *ct2-held* :paged) :resident)
                    *ct2-held* :resident)))

; --- K4: ground, and the search over the RECORDS clause
(assert-event (not (fn-cth-header-rowp (fn-cth-header-row 3 '(3 5 100)))))
(assert-event (not (fn-cth-header-rowp (fn-cth-header-row 4 '(3 5 100 4 40 3489 456 45 :resident)))))
(assert-event (not (fn-cth-header-rowp (list (1- *fn-scc-schema*) 3 '(3 5 100 4 40 3489 456 45 :resident)))))


; --- K5/K7, ground: the event file with its header run is read whole on the
; small profile; its total the file's octets; within the budget
(defconst *ct3-file-ev* (append *ct3-hsegs-ev* *ct2-segs*))
(defconst *ct3-r* (fn-cth-read-file *ct3-file-ev* *fn-heap-small-profile* nil))
(assert-event (equal *ct3-r* (list :ok (len (fn-scc-concat *ct3-file-ev*)) (fn-ct-charged *ct2-events* :resident))))
(assert-event (<= (len (fn-scc-concat *ct3-file-ev*))
                  (fn-cth-publication-budget *fn-heap-small-profile* *ct2-cap-ev* nil)))
(value-triple (list :read *ct3-r* :budget (fn-cth-publication-budget *fn-heap-small-profile* *ct2-cap-ev* nil)))
; tooth (Codex round 2, X1): a file past the budget is refused :bound with the
; header's total carried; the same REST restarted at 0 would be admitted
(defconst *ct3-x1-cap* (fn-sco-capture *ct2-configs* nil))
(defconst *ct3-x1-cfg* (update-nth 12 132 nil))
(defconst *ct3-x1-pad* (fn-sct-run-segments (make-list 196908 :initial-element 7) 196608 0))
(defconst *ct3-x1-file* (append (fn-cth-header-segments (fn-cth-header-of-capture *ct3-x1-cap*) 0) *ct3-x1-pad*))
(value-triple (list :x1-file (len (fn-scc-concat *ct3-x1-file*))
                    :x1-budget (fn-cth-publication-budget *fn-heap-small-profile* *ct3-x1-cap* *ct3-x1-cfg*)))
(assert-event (not (<= (len (fn-scc-concat *ct3-x1-file*))
                       (fn-cth-publication-budget *fn-heap-small-profile* *ct3-x1-cap* *ct3-x1-cfg*))))
(assert-event (equal (fn-cth-read-file *ct3-x1-file* *fn-heap-small-profile* *ct3-x1-cfg*) '(:refused :rest :exceeds-bound)))
(assert-event (natp (fn-cth-admit-run (cdr *ct3-x1-file*) 0 (fn-cth-segment-bound *fn-heap-small-profile*)
                                      (fn-mm-checkpoint-load-octets *fn-heap-small-profile*
                                                                    (fn-ct-zero-tot :resident) *ct3-x1-cfg*))))

; --- K6: ground on the small profile at the empty TOT (tight), and search
(assert-event (equal (fn-cth-segment-bound *fn-heap-small-profile*)
                     (fn-mm-checkpoint-load-octets *fn-heap-small-profile* (fn-ct-zero-tot :resident) nil)))

; tooth: today's reader's header-phase bound (the profile's file bound) is
; above the load bound on the small profile at the empty TOT
(assert-event (< (fn-mm-checkpoint-load-octets *fn-heap-small-profile* (fn-ct-zero-tot :resident) nil)
                 (fn-sccr-file-read-bound (fn-bs-profile-max-history-octets *fn-heap-small-profile*)
                                          (fn-bs-profile-max-record-octets *fn-heap-small-profile*))))

; ===========================================================================
; v3.1 (Codex round 3's findings)
(defconst *sb* (fn-cth-segment-bound *fn-heap-small-profile*))
(defconst *ct31-rest* (append (fn-scka-run-segments nil nil 2) *ct2-segs*))   ; A (empty) + F/P/E/R
(defconst *ct31-file* (append *ct3-hsegs-ev* *ct31-rest*))
(defconst *ct31-budget* (fn-cth-publication-budget *fn-heap-small-profile* *ct2-cap-ev* nil))

; --- K7 (admitted file), ground: the H + A + tables file the writer admits
; from 0 under (SB, budget) is read whole with the same total and the fold.
(defconst *ct31-w* (fn-cth-admit-run *ct31-file* 0 *sb* *ct31-budget*))
(assert-event (equal *ct31-w* (len (fn-scc-concat *ct31-file*))))
(assert-event (equal (fn-cth-read-file *ct31-file* *fn-heap-small-profile* nil)
                     (list :ok *ct31-w* (fn-ct-charged *ct2-events* :resident))))
; tooth (the admission premise): Codex r3's publication witness, a file the
; old setup planned (197,004 without H) is 197,120 with H against 197,073:
; the writer's admission refuses it, and so does the reader
(defun ct31-revision-rest (n)
  (declare (xargs :verify-guards nil))
  (let* ((c (fn-sco-capture *ct2-configs* nil))
         (tab (fn-sct-tables-of-capture c 8 (coerce (make-list n :initial-element #\a) 'string) nil))
         (p (fn-sct-table-programs tab (fn-sco-event-index c))))
    (append (fn-scka-run-segments nil nil 0) (fn-sct-file-segments p 196608 0))))
(defconst *ct31-pub-cfg* (update-nth 12 132 nil))
(defconst *ct31-pub-cap* (fn-sco-capture *ct2-configs* nil))
(defconst *ct31-pub-h* (fn-cth-header-segments (fn-cth-header-of-capture *ct31-pub-cap*) 0))
(defconst *ct31-pub-file* (append *ct31-pub-h* (ct31-revision-rest 196500)))
(defconst *ct31-pub-budget* (fn-cth-publication-budget *fn-heap-small-profile* *ct31-pub-cap* *ct31-pub-cfg*))
(value-triple (list :pub-whole (len (fn-scc-concat *ct31-pub-file*)) :pub-budget *ct31-pub-budget*))
(assert-event (not (natp (fn-cth-admit-run *ct31-pub-file* 0 *sb* *ct31-pub-budget*))))
(assert-event (equal (car (fn-cth-read-file *ct31-pub-file* *fn-heap-small-profile* *ct31-pub-cfg*)) :refused))
; tooth (the configuration premise): the writer's configuration larger than
; the reader's; a REST the writer admits at 132 octets of configuration
; the reader at 0 refuses
(defconst *ct31-cfgw* (update-nth 12 2000 nil))
(defconst *ct31-cfgw-budget* (fn-cth-publication-budget *fn-heap-small-profile* *ct31-pub-cap* *ct31-cfgw*))
(value-triple (list :cfgw-budget *ct31-cfgw-budget*
                    :cfg0-bound (fn-mm-checkpoint-load-octets *fn-heap-small-profile*
                                                              (fn-ct-charged nil :resident) nil)))
(assert-event (natp (fn-cth-admit-run *ct31-pub-file* 0 *sb* *ct31-cfgw-budget*)))
(assert-event (equal (fn-cth-read-file *ct31-pub-file* *fn-heap-small-profile* *ct31-cfgw*)
                     (list :ok (len (fn-scc-concat *ct31-pub-file*)) (fn-ct-charged nil :resident))))
(assert-event (equal (car (fn-cth-read-file *ct31-pub-file* *fn-heap-small-profile* nil)) :refused))

; --- K5b (every admitted prefix): ground on Codex's padded file and on the
; refused publication file at each prefix before its refusal; search
(assert-event (natp (fn-cth-read-prefix *ct31-file* 3 *fn-heap-small-profile* nil)))
(assert-event (<= (fn-cth-read-prefix *ct31-file* 3 *fn-heap-small-profile* nil)
                  (fn-mm-checkpoint-load-octets *fn-heap-small-profile* (fn-cth-header-tot *ct31-file*) nil)))
(defun ct31-prefixes-within (segs n profile cfg)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      t
    (and (let ((p (fn-cth-read-prefix segs n profile cfg)))
           (or (not (natp p))
               (<= p (fn-mm-checkpoint-load-octets profile (fn-cth-header-tot segs) cfg))))
         (ct31-prefixes-within segs (1- n) profile cfg))))
(assert-event (ct31-prefixes-within *ct31-pub-file* (len *ct31-pub-file*) *fn-heap-small-profile* *ct31-pub-cfg*))
(value-triple (list :pub-prefixes (len *ct31-pub-file*)
                    :pub-prefix-1 (fn-cth-read-prefix *ct31-pub-file* 1 *fn-heap-small-profile* *ct31-pub-cfg*)))


; --- K4b (the schema refusal by name): the schema-3 header (literal byte 3
; at schema 4), alone and before the rest
(assert-event (equal *fn-scc-schema* 4))
(defconst *ct31-old-h* (update-nth 4 3 (car *ct3-hsegs-ev*)))
(assert-event (fn-sccr-other-schemap *ct31-old-h*))
(assert-event (equal (fn-cth-read-file (list *ct31-old-h*) *fn-heap-small-profile* nil)
                     '(:refused :header-segment :schema)))
(assert-event (equal (fn-cth-read-file (cons *ct31-old-h* *ct31-rest*) *fn-heap-small-profile* nil)
                     '(:refused :header-segment :schema)))
; tooth: a header that is not the codec's magic is refused :header, not :schema
(assert-event (equal (fn-cth-read-file (list (update-nth 0 0 (car *ct3-hsegs-ev*))) *fn-heap-small-profile* nil)
                     '(:refused :header-segment :header)))

; --- K8 (the setup counts H): Codex r3's input; the old setup plans, the
; header-counting setup defers; the event capture plans
(defconst *ct31-hlen* (len (fn-scc-concat *ct31-pub-h*)))
(defconst *ct31-alen* (len (fn-scc-concat (fn-scka-run-segments nil nil 0))))
(defconst *ct31-rev* (coerce (make-list 196500 :initial-element #\a) 'string))
(defconst *ct31-old-setup*
  (fn-scka-publication-setup *ct31-pub-cap* 8 *ct31-rev* nil 196608 *ct31-pub-budget* 100000000 *ct31-alen*))
(defconst *ct31-new-setup*
  (fn-cth-publication-setup *ct31-pub-cap* 8 *ct31-rev* nil 196608 *fn-heap-small-profile* *ct31-pub-cfg*
                            100000000 *ct31-alen* *ct31-hlen*))
(value-triple (list :old (car *ct31-old-setup*) (nth 6 *ct31-old-setup*)
                    :new (car *ct31-new-setup*) (nth 6 *ct31-new-setup*) :hlen *ct31-hlen*))
(assert-event (equal (car (car *ct31-old-setup*)) :plan))
(assert-event (not (equal (car (car *ct31-new-setup*)) :plan)))
(assert-event (equal (nth 6 *ct31-new-setup*) (len (fn-scc-concat *ct31-pub-file*))))
(defconst *ct31-ev-setup*
  (fn-cth-publication-setup *ct2-cap-ev* 9 "rev" nil 64 *fn-heap-small-profile* nil 100000000
                            (len (fn-scc-concat (fn-scka-run-segments nil nil 2)))
                            (len (fn-scc-concat *ct3-hsegs-ev*))))
(assert-event (equal (car *ct31-ev-setup*) (list :plan (len (fn-scc-concat *ct31-file*)))))

; --- K8a (the arena writer's admission from a carried total): ground over
; real payloads through the arena writer, from T0 = the header's octets
(defun ct31-arena-run (ps t0 fb)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-octets
        (mv-let (result fn-arena fn-octets)
          (let* ((ks (fn-scka-batches (fn-scka-lens ps) 64))
                 (pst (fn-scka-initial-state ps ks t0)))
            (mv-let (v bytes fn-octets)
              (fn-scka-write-run pst (len ps) (+ 1 (len ks)) 2 *sb* fb (+ 1 (len ks)) fn-arena fn-octets)
              (mv (list v (len bytes)
                        (fn-cth-admit-run (fn-scka-run-segments ps ks 2) t0 *sb* fb)
                        (and (fn-arena-p fn-arena) (fn-scka-srcs-okp ps fn-arena)
                             (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))))
                  fn-arena fn-octets)))
          (mv result fn-arena)))
      result)))
(defconst *ct31-ps* (list (make-list 50 :initial-element 65) (make-list 30 :initial-element 66)
                          (make-list 90 :initial-element 67)))
(defconst *ct31-a* (ct31-arena-run *ct31-ps* 116 *ct31-budget*))
(value-triple (list :arena *ct31-a*))
(assert-event (and (eq (car *ct31-a*) :ok) (equal (nth 2 *ct31-a*) (+ 116 (nth 1 *ct31-a*)))
                   (nth 3 *ct31-a*)))
; tooth (the source guard, Codex r4): SRCS = ((256)) is outside fn-scka-srcs-okp
(defun ct31-srcs-okp (ps)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (ok fn-arena) (mv (fn-scka-srcs-okp ps fn-arena) fn-arena) ok)))
(assert-event (ct31-srcs-okp *ct31-ps*))
(assert-event (not (ct31-srcs-okp (list (list 256)))))
; tooth (the :ok premise): a file bound below T0 + the run refuses both
(defconst *ct31-a-small* (ct31-arena-run *ct31-ps* 116 300))
(value-triple (list :arena-small *ct31-a-small*))
(assert-event (and (not (eq (car *ct31-a-small*) :ok)) (not (natp (nth 2 *ct31-a-small*)))))

; --- K8t (the table writer's admission from a carried total): ground over
; the event capture's tables from T1
(defun ct31-table-run (next t1 fb)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (let* ((setup (fn-cth-publication-setup next 9 "rev" nil 64 *fn-heap-small-profile* nil 100000000 0 0))
             (tables (fn-sct-tables-of-capture next 9 "rev" nil)))
        (mv-let (v bytes fn-octets)
          (fn-ockp-run setup (fn-cth-table-initial-state tables t1 fn-octets) 4 4096 64 2 *sb* fb 1000 fn-octets)
          (mv (list v (len bytes)
                    (fn-cth-admit-run (fn-sct-file-segments
                                       (fn-sct-table-programs tables (fn-sco-event-index next)) 64 2)
                                      t1 *sb* fb))
              fn-octets)))
      result)))
(assert-event (fn-sct-programs-widthp *ct2-progs-ev*))
; the width premise's reason (Codex r4 F3): a header declaring 2^64 octets
; parses with length 0 and is admitted at 69
(assert-event (equal (fn-sccr-admit-segment (fn-scc-header 0 1 *fn-scc-u64-bound* 0) 0 1000 1000) '(:ok 69 0)))
(defconst *ct31-t* (ct31-table-run *ct2-cap-ev* 500 *ct31-budget*))
(value-triple (list :tables *ct31-t*))
(assert-event (and (eq (car *ct31-t*) :ok) (equal (nth 2 *ct31-t*) (+ 500 (nth 1 *ct31-t*)))))
(defconst *ct31-t-small* (ct31-table-run *ct2-cap-ev* 500 900))
(value-triple (list :tables-small *ct31-t-small*))
(assert-event (and (not (eq (car *ct31-t-small*) :ok)) (not (natp (nth 2 *ct31-t-small*)))))

; --- K8c (composition): ground and search
(assert-event (equal (fn-cth-admit-run *ct31-file* 0 *sb* *ct31-budget*)
                     (fn-cth-admit-run *ct31-rest* (fn-cth-admit-run *ct3-hsegs-ev* 0 *sb* *ct31-budget*)
                                       *sb* *ct31-budget*)))
; the counterexample without (natp T0): X = NIL, T0 = -1
(assert-event (not (equal (fn-cth-admit-run (append nil *ct31-rest*) -1 *sb* *ct31-budget*)
                          (fn-cth-admit-run *ct31-rest* (fn-cth-admit-run nil -1 *sb* *ct31-budget*)
                                            *sb* *ct31-budget*))))


; --- K9 (one capture's seed): ground over the event history's first record,
; and the tooth: Codex r3's mixed file (another history's header, this
; REST) seeds an invalid cache with the open's own verdict as the flag
(defconst *ct31-c1* (fn-sco-capture *ct2-configs* (take 1 *ct2-events*)))
(defconst *ct31-file1* (append (fn-cth-header-segments (fn-cth-header-of-capture *ct31-c1*) 1) *ct31-rest*))
(assert-event (fn-sn-open-okp *ct2-open-ev*))
(assert-event (fn-ct-totals-cache-validp
               (fn-cth-installed-seed (fn-sn-open-okp *ct2-open-ev*) 1 (fn-cth-header-tot *ct31-file1*) :resident)
               (fn-sf-records (fn-sn-files (fn-sn-open-state *ct2-open-ev*))) :resident))
(defconst *ct31-mixed*
  (append (fn-cth-header-segments (fn-cth-header-row 1 *ct3-other-header*) 1) *ct31-rest*))
(assert-event (not (fn-ct-totals-cache-validp
                    (fn-cth-installed-seed (fn-sn-open-okp *ct2-open-ev*) 1 (fn-cth-header-tot *ct31-mixed*) :resident)
                    (fn-sf-records (fn-sn-files (fn-sn-open-state *ct2-open-ev*))) :resident)))

; --- K10 (one segment): both histories
(assert-event (equal (cdr *ct31-file*) *ct31-rest*))
(assert-event (equal (len (fn-cth-header-segments *ct3-h-held* 3)) 1))
