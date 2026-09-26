; fn: teeth for books/owner-checkpoint-stream.lisp (checkpoint-capture-stream,
; PRF-183; PKT-492).
;
; The witness is owner-checkpoint-open-tests' image: two retention events and
; two configuration records, the capture of the whole history frozen and
; encoded at segment size 64, which cuts it into more than one segment.  The
; exec path runs on a live local buffer, and once on the PUBLICATION buffer
; `fn-octets-pub' (the congruent stobj the owner's thread uses), the way the
; host runs it.  Per keystone hypothesis: a witness on which every retained
; hypothesis holds, the omitted one fails and the conclusion fails, and the
; `must-fail'.  (Attachments evaluate in assert-event, not in defconst: the
; seal is fn-sha256's.)

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/owner-checkpoint-stream")

; Every executable function the host may reach is guard-verified: the host
; runs the compiled stobj code.
(assert-event
 (and (eq (symbol-class 'fn-ockb-len-acc (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockb-program-len (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockb-file-len (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ock-capture-budget (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ock-publication-blockedp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ock-publication-stream (w state)) :common-lisp-compliant)))

(defconst *ocst-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-ock" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-ock" "subject" "evidence" 0)))
(defconst *ocst-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defconst *ocst-prefix* (list (car *ocst-events*)))
(defconst *ocst-base* (fn-sco-capture *ocst-configs* *ocst-prefix*))
(defconst *ocst-capture* (fn-sco-capture *ocst-configs* *ocst-events*))
(defconst *ocst-frozen* (fn-sco-freeze *ocst-capture*))
(defconst *ocst-seg* 64)

; The exec path: (NEXT VERDICT OCTETS FILL) of the entry on a live local
; buffer; OCTETS the plan's octets over the buffer it leaves when the
; verdict is a plan.
(defun ocst-run (base configs records seg budget)
  (declare (xargs :guard (and (natp seg) (natp budget))))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (mv-let (next verdict fn-octets)
        (fn-ock-publication-stream base configs records seg budget fn-octets)
        (mv (list next verdict
                  (if (and (consp verdict) (eq (car verdict) :plan)
                           (consp (cdr verdict)) (true-list-listp (cadr verdict)))
                      (fn-sccb-plan-octets (cadr verdict) fn-octets)
                    nil)
                  (fn-octets-len fn-octets))
            fn-octets))
      result)))

; The same run on the publication buffer, the congruent stobj.
(defun ocst-run-pub (base configs records seg budget)
  (declare (xargs :guard (and (natp seg) (natp budget))))
  (with-local-stobj fn-octets-pub
    (mv-let (result fn-octets-pub)
      (mv-let (next verdict fn-octets-pub)
        (fn-ock-publication-stream base configs records seg budget fn-octets-pub)
        (mv (list next verdict
                  (if (and (consp verdict) (eq (car verdict) :plan)
                           (consp (cdr verdict)) (true-list-listp (cadr verdict)))
                      (fn-sccb-plan-octets (cadr verdict) fn-octets-pub)
                    nil)
                  (fn-octets-pub-len fn-octets-pub))
            fn-octets-pub))
      result)))

; The estimate is the file's length, and the file has more than one segment.
(assert-event
 (let ((file (fn-scc-file-octets *ocst-frozen* *ocst-seg*)))
   (and (fn-sccb-treep *ocst-frozen*)
        (consp file)
        (equal (fn-ockb-file-len *ocst-frozen* *ocst-seg*) (len file))
        (equal (fn-ockb-program-len *ocst-frozen*) (len (fn-scc-encode *ocst-frozen*)))
        (< 1 (len (fn-scc-segments *ocst-frozen* *ocst-seg*)))
        (equal (len file)
               (+ (len (fn-scc-encode *ocst-frozen*))
                  (* 69 (len (fn-scc-segments *ocst-frozen* *ocst-seg*))))))))

; KEYSTONE fn-ock-publication-stream-writes-the-file, the positive witness
; at the budget boundary (budget = the file's length: not deferred): the
; antecedent (a plan), the conclusion (the plan's octets are
; fn-ock-publication's file octets, fn-scc-file-octets of the frozen
; capture), non-degenerate (a nonempty file of several segments that the
; unchanged reader decodes to the capture), NEXT the capture, the estimate
; the file's length, the buffer's fill the program's length.
(assert-event
 (let* ((file (fn-scc-file-octets *ocst-frozen* *ocst-seg*))
        (r (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg* (len file)))
        (next (nth 0 r)) (verdict (nth 1 r)) (octets (nth 2 r)) (used (nth 3 r)))
   (and (equal (car verdict) :plan)
        (equal octets file)
        (equal octets (cadr (fn-ock-publication *ocst-base* *ocst-configs* *ocst-events*
                                                *ocst-seg*)))
        (consp octets)
        (< 1 (len (cadr verdict)))
        (equal next *ocst-capture*)
        (equal next (car (fn-ock-publication *ocst-base* *ocst-configs* *ocst-events*
                                             *ocst-seg*)))
        (equal (caddr verdict) (len file))
        (equal used (len (fn-scc-encode *ocst-frozen*)))
        (equal (fn-sco-thaw (cadr (fn-scc-decode-segments
                                   (fn-scc-segments *ocst-frozen* *ocst-seg*))))
               *ocst-capture*))))

; The same on the publication buffer: the congruent stobj executes the
; entry and leaves the same plan, octets and fill.
(assert-event
 (let* ((file (fn-scc-file-octets *ocst-frozen* *ocst-seg*))
        (r (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg* (len file)))
        (p (ocst-run-pub *ocst-base* *ocst-configs* *ocst-events* *ocst-seg* (len file))))
   (and (equal p r) (equal (nth 2 p) file))))

; The deferral at the budget boundary, the other side (budget = the file's
; length less one): deferred by name, with the file's length and the budget,
; and NOTHING encoded (the buffer's fill is 0).  A larger budget: the plan.
(assert-event
 (let* ((file (fn-scc-file-octets *ocst-frozen* *ocst-seg*))
        (r (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg* (1- (len file))))
        (verdict (nth 1 r)))
   (and (equal verdict (list :deferred :exceeds-budget (len file) (1- (len file))))
        (equal (nth 0 r) *ocst-capture*)
        (equal (nth 2 r) nil)
        (equal (nth 3 r) 0)
        (equal (car (nth 1 (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg*
                                     (+ 1000 (len file)))))
               :plan)
        (equal (car (nth 1 (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg* 0)))
               :deferred))))

; The blocked rule over that deferral: blocked while the budget is below the
; estimate, not at it.
(assert-event
 (let* ((file (fn-scc-file-octets *ocst-frozen* *ocst-seg*))
        (verdict (nth 1 (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg*
                                  (1- (len file))))))
   (and (fn-ock-publication-blockedp verdict (1- (len file)))
        (fn-ock-publication-blockedp verdict 0)
        (fn-ock-publication-blockedp verdict nil)
        (not (fn-ock-publication-blockedp verdict (len file)))
        (not (fn-ock-publication-blockedp nil 0))
        (not (fn-ock-publication-blockedp '(:plan) 0)))))

; The budget from a profile: the reader's file bound (three times H plus one
; segment's framing), on the development preset and on a hand-made profile.
(assert-event
 (and (equal (fn-ock-capture-budget *fn-bs-profile-development*)
             (fn-sccr-file-read-bound
              (fn-bs-profile-max-history-octets *fn-bs-profile-development*)
              (fn-bs-profile-max-record-octets *fn-bs-profile-development*)))
      (equal (fn-ock-capture-budget *fn-bs-profile-development*)
             (+ (* 3 (fn-bs-profile-max-history-octets *fn-bs-profile-development*))
                69 (fn-bs-profile-max-record-octets *fn-bs-profile-development*)))
      (natp (fn-ock-capture-budget nil))))

; The refusal agrees with the codec: a history holding a value no atom of
; the codec encodes (a natural whose digits do not fit one octet's count) is
; :unencodable on both entries, and nothing is encoded.
(defconst *ocst-untree-records* (list (expt 2 2040)))
(assert-event
 (let ((r (ocst-run *ocst-base* *ocst-configs* *ocst-untree-records* *ocst-seg* 1000000)))
   (and (not (fn-scc-treep (fn-sco-freeze (fn-ock-next-checkpoint
                                           *ocst-base* *ocst-configs* *ocst-untree-records*))))
        (equal (nth 1 r) :unencodable)
        (equal (cadr (fn-ock-publication *ocst-base* *ocst-configs* *ocst-untree-records*
                                         *ocst-seg*))
               :unencodable)
        (equal (nth 3 r) 0))))

; -----------------------------------------------------------------------------
; Per hypothesis.  (Each must-fail closes the entry and the codec in its
; hint: a doomed search over them cost the book thirteen seconds; the
; refutation is the witness beside it, never the failed search.)

; fn-ock-publication-stream-writes-the-file, its one hypothesis (the verdict
; is a plan): a deferred verdict carries no plan, so its "octets" are nil
; and not the file.
(assert-event
 (let* ((file (fn-scc-file-octets *ocst-frozen* *ocst-seg*))
        (r (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg* 0)))
   (and (not (equal (car (nth 1 r)) :plan))
        (consp file)
        (not (equal (nth 2 r) file)))))
(must-fail
 (defthm ocst-r-writes-the-file-without-a-plan
   (equal (fn-sccb-plan-octets
           (cadr (mv-nth 1 (fn-ock-publication-stream base configs records seg budget fn-octets)))
           (mv-nth 2 (fn-ock-publication-stream base configs records seg budget fn-octets)))
          (cadr (fn-ock-publication base configs records seg)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ock-publication fn-scc-file-octets fn-sccb-plan-octets
                                fn-sccb-plan fn-ock-next-checkpoint fn-sco-freeze
                                fn-sccb-treep fn-scc-treep fn-scc-program
                                fn-ockb-file-len-is-len-file-octets
                                fn-ock-publication-stream-defers-by-the-estimate
                                fn-ock-publication-stream-writes-the-file
                                fn-ock-publication-stream-refuses-what-the-codec-refuses
                                fn-ock-publication-blockedp-by-definition)))))

; fn-ock-publication-stream-refuses-what-the-codec-refuses, its one
; hypothesis (the codec refuses): on the encodable witness the verdict is a
; plan, not :unencodable.
(assert-event
 (let ((r (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg* 1000000)))
   (and (fn-scc-treep *ocst-frozen*)
        (not (equal (nth 1 r) :unencodable)))))
(must-fail
 (defthm ocst-r-refuses-without-the-codec-refusal
   (equal (mv-nth 1 (fn-ock-publication-stream base configs records seg budget fn-octets))
          :unencodable)
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ock-publication fn-scc-file-octets fn-sccb-plan-octets
                                fn-sccb-plan fn-ock-next-checkpoint fn-sco-freeze
                                fn-sccb-treep fn-scc-treep fn-scc-program
                                fn-ockb-file-len-is-len-file-octets
                                fn-ock-publication-stream-defers-by-the-estimate
                                fn-ock-publication-stream-writes-the-file
                                fn-ock-publication-stream-refuses-what-the-codec-refuses
                                fn-ock-publication-blockedp-by-definition)))))

; fn-ock-publication-stream-defers-by-the-estimate, its one hypothesis (the
; frozen value is encodable): on the unencodable history with budget 0 the
; verdict is :unencodable, whose car is neither :deferred nor :plan, so the
; conclusion's third conjunct fails while the "estimate" (the length of
; :unencodable) is 0.  A tree the list codec admits and the buffer codec
; refuses (a leaf of 2^2040 octets) is not constructible, so the
; hypothesis is toothed at the codec's refusal only.
(assert-event
 (let* ((frozen (fn-sco-freeze (fn-ock-next-checkpoint *ocst-base* *ocst-configs*
                                                       *ocst-untree-records*)))
        (estimate (len (fn-scc-file-octets frozen *ocst-seg*)))
        (verdict (nth 1 (ocst-run *ocst-base* *ocst-configs* *ocst-untree-records*
                                  *ocst-seg* 0))))
   (and (not (fn-sccb-treep frozen))
        (equal estimate 0)
        (not (< 0 estimate))
        ;; (car :unencodable) is nil in the logic, never :plan.
        (equal verdict :unencodable))))
(must-fail
 (defthm ocst-r-defers-without-treep
   (implies (not (< budget (len (fn-scc-file-octets
                                 (fn-sco-freeze (fn-ock-next-checkpoint base configs records))
                                 seg))))
            (equal (car (mv-nth 1 (fn-ock-publication-stream base configs records seg
                                                             budget fn-octets)))
                   :plan))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ock-publication fn-scc-file-octets fn-sccb-plan-octets
                                fn-sccb-plan fn-ock-next-checkpoint fn-sco-freeze
                                fn-sccb-treep fn-scc-treep fn-scc-program
                                fn-ockb-file-len-is-len-file-octets
                                fn-ock-publication-stream-defers-by-the-estimate
                                fn-ock-publication-stream-writes-the-file
                                fn-ock-publication-stream-refuses-what-the-codec-refuses
                                fn-ock-publication-blockedp-by-definition)))))

; fn-ockb-file-len-is-len-file-octets, its one hypothesis (fn-sccb-treep):
; on the unencodable value the file is :unencodable (length 0) and the walk
; still counts the rest of the tree.
(assert-event
 (let ((frozen (fn-sco-freeze (fn-ock-next-checkpoint *ocst-base* *ocst-configs*
                                                      *ocst-untree-records*))))
   (and (not (fn-sccb-treep frozen))
        (equal (len (fn-scc-file-octets frozen *ocst-seg*)) 0)
        (< 0 (fn-ockb-file-len frozen *ocst-seg*))
        (not (equal (len (fn-scc-file-octets frozen *ocst-seg*))
                    (fn-ockb-file-len frozen *ocst-seg*))))))
(must-fail
 (defthm ocst-r-file-len-without-treep
   (equal (len (fn-scc-file-octets c seg)) (fn-ockb-file-len c seg))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ock-publication fn-scc-file-octets fn-sccb-plan-octets
                                fn-sccb-plan fn-ock-next-checkpoint fn-sco-freeze
                                fn-sccb-treep fn-scc-treep fn-scc-program
                                fn-ockb-file-len-is-len-file-octets
                                fn-ock-publication-stream-defers-by-the-estimate
                                fn-ock-publication-stream-writes-the-file
                                fn-ock-publication-stream-refuses-what-the-codec-refuses
                                fn-ock-publication-blockedp-by-definition)))))

; fn-ockb-len-acc-is-len-program, its one hypothesis (fn-scc-treep): the
; walk does not measure a value no atom encodes, and the program of that
; natural (which the codec's atom writer still lists, 258 octets) is longer.
(defthm ocst-w-len-acc-without-treep
  (and (not (fn-scc-treep (expt 2 2040)))
       (equal (fn-ockb-len-acc (expt 2 2040) 0 0) 0)
       (not (equal (fn-ockb-len-acc (expt 2 2040) 0 0)
                   (+ 0 0 (len (fn-scc-program (expt 2 2040)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ockb-len-acc))))
(must-fail
 (defthm ocst-r-len-acc-without-treep
   (equal (fn-ockb-len-acc x n acc)
          (+ (fix acc) (nfix n) (len (fn-scc-program x))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ock-publication fn-scc-file-octets fn-sccb-plan-octets
                                fn-sccb-plan fn-ock-next-checkpoint fn-sco-freeze
                                fn-sccb-treep fn-scc-treep fn-scc-program
                                fn-ockb-file-len-is-len-file-octets
                                fn-ock-publication-stream-defers-by-the-estimate
                                fn-ock-publication-stream-writes-the-file
                                fn-ock-publication-stream-refuses-what-the-codec-refuses
                                fn-ock-publication-blockedp-by-definition)))))

; fn-ock-publication-blockedp-by-definition, its one hypothesis (a deferred
; verdict): a plan verdict never blocks, whatever the later budget.
(assert-event
 (let* ((file (fn-scc-file-octets *ocst-frozen* *ocst-seg*))
        (verdict (nth 1 (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg*
                                  (len file)))))
   (and (equal (car verdict) :plan)
        (< 0 (len file))
        (not (fn-ock-publication-blockedp verdict 0)))))
(must-fail
 (defthm ocst-r-blocked-without-a-deferral
   (iff (fn-ock-publication-blockedp
         (mv-nth 1 (fn-ock-publication-stream base configs records seg budget fn-octets))
         later-budget)
        (< (nfix later-budget)
           (len (fn-scc-file-octets
                 (fn-sco-freeze (fn-ock-next-checkpoint base configs records)) seg))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ock-publication fn-scc-file-octets fn-sccb-plan-octets
                                fn-sccb-plan fn-ock-next-checkpoint fn-sco-freeze
                                fn-sccb-treep fn-scc-treep fn-scc-program
                                fn-ockb-file-len-is-len-file-octets
                                fn-ock-publication-stream-defers-by-the-estimate
                                fn-ock-publication-stream-writes-the-file
                                fn-ock-publication-stream-refuses-what-the-codec-refuses
                                fn-ock-publication-blockedp-by-definition)))))

; fn-ock-publication-stream-next-is-the-capture, its hypothesis (an admitted
; history): as for fn-ock-next-checkpoint-is-the-capture
; (owner-checkpoint-open-tests), the identity fold's fault is absorbing and
; non-admitted histories give the capture too; reported untoothed there and
; here.
(assert-event
 (and (fn-sn-observed-historyp 8 *ocst-events*)
      (equal (nth 0 (ocst-run *ocst-base* *ocst-configs* *ocst-events* *ocst-seg* 0))
             *ocst-capture*)))
