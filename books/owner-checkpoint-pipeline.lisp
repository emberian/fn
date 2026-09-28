; fn: the one resumable checkpoint pipeline: the schema-3 tables
; (books/store-checkpoint-tables.lisp) written in bounded batches through
; the publication buffer, decided before anything is allocated (lane
; checkpoint-pipeline, 2026-09-26; D33; design section 2.2).
;
; Before this book the owner's automatic publication and the verb each
; encoded the WHOLE frozen checkpoint into the publication buffer before the
; first write (`fn-sccb-plan': 315 MB resident at N = 40,000), after a walk
; of every payload octet for the estimate (`fn-ockb-file-len', 54 s at
; N = 40,000 and linear in the payload).  This book replaces both with one
; pipeline the owner's thread and the verb run alike:
;
;   capture (under the mutex, host/owner-host.lisp fn-owner-sco-capture: the
;     base, the configuration history, the record list by pointer, S, the
;     budget, the free space)
;   -> `fn-ockp-estimate' (off the mutex): the file's length from the tables'
;      rows without encoding them: a walk over the METADATA (a payload leaf
;      costs its length, never a copy; a referenced payload costs its
;      reference), equal to the length of the file the pipeline writes
;      (`fn-ockp-estimate-is-len-file-octets')
;   -> `fn-ockp-decide': the deferral by name BEFORE any allocation, against
;      the profile's checkpoint budget (`fn-ock-capture-budget', the reader's
;      file bound, STO-024) and the space (the free octets the host observed
;      by statvfs less the maintenance reserve `fn-smr-reserve-octets')
;   -> `fn-ockp-batch' (the resumable step): the next B rows of the current
;      table encoded into the buffer after the residue the last step left,
;      the full SEG-octet chunks framed and chained, the residue (under SEG
;      octets) kept for the next step; at a table's end its last chunk; then
;      the next table.  The buffer holds at most one batch's rows and one
;      segment's residue, never the file.  Each frame is admitted by the
;      reader's own rule (`fn-sccr-admit-segment') before it is handed to
;      the host: a file the open would refuse is never completed.
;
; The host (host/native/owner.lisp `fnn-owner-publish-captured';
; host/native/io.lisp `fnn-command-state-checkpoint') loops on
; `fn-ockp-batch' and writes each step's frames through `fnn-write-staged-at'
; between the `created' and `written' cuts of `fn-bs-scp-program' (its
; :write-all is the loop of writes), then renames and fences as before.
; `fn-ockp-run' is that loop in the logic, its result the file's octets.
;
; KEYSTONE `fn-ockp-run-writes-the-file' (PRF-199 with the tables book's
; `fn-sct-decode-file-of-file-is-the-capture'): the octets the batched
; pipeline writes, at ANY batch size and any segment size, are
; `fn-sct-file-octets' of the tables' programs, whose reader gives the
; tables and the capture.  PRF-200 `fn-ockp-decide-defers-by-the-estimate':
; the pipeline defers exactly when the file it would write exceeds the
; budget or the space, naming the file's length and the bound, else it
; answers the plan.

(in-package "ACL2")
(include-book "owner-checkpoint-writer")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-scc-atomp)
                          (:definition fn-scc-frames)
                          (:definition fn-scc-nat-encodablep)
                          (:definition fn-scc-seal)
                          (:definition fn-scc-treep)
                          (:definition fn-sccb-frame-octets)
                          (:rewrite fn-sccr-cbor-octet-listp-is-scc-octet-listp)
                          (:rewrite fn-sccr-scc-octet-listp-is-cbor-octet-listp))))

; The definitions, the estimate, the decision, the writer's step-level twins
; and the cut lemmas are books/owner-checkpoint-writer.lisp (split there by
; checkpoint-pipeline-5, D26).  This book composes them into the loop
; keystone and carries the invariants between steps.

(local
 (defthm fn-ockp-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-ockp-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-ockp-concat-append
   (equal (fn-scc-concat (append a b))
          (append (fn-scc-concat a) (fn-scc-concat b)))))

; The list facts the writer book proves locally and the loop proofs use.
(local
 (defthm fn-ockp-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

(local
 (defthm fn-ockp-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-ockp-len-take
   (equal (len (take k x)) (nfix k))))

(local
 (defthm fn-ockp-nthcdr-of-nil
   (equal (nthcdr n nil) nil)))

(local
 (defthm fn-ockp-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

(local
 (defthm fn-ockp-take-of-append
   (implies (and (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-ockp-nthcdr-of-append
   (implies (and (natp k) (<= k (len a)))
            (equal (nthcdr k (append a b)) (append (nthcdr k a) b)))))

(local
 (defthm fn-ockp-genesis-octets
   (fn-scc-octet-listp *fn-scc-genesis*)))

; The codec's leaf functions, the pack-id bound and the imported true-listp
; backchainers stay closed here as in the writer book (its local disables do
; not export): see the note there.
(local (in-theory (disable fn-sccb-treep fn-scc-atom-octets fn-scc-string-octets fn-scc-le-digits
                           fn-scc-nat-octets fn-cp-idp fn-cp-id-length-bound floor
                           fn-nntp-response-text-true-listp fn-nntp-clean-line-is-response-text
                           fn-nov-clean-linep fn-nntp-response-textp fn-scc-octet-listp-true
                           fn-nntp-article-idp-is-consp fn-oct-bufp-true-listp fn-octets$c-bufp
                           fn-ockp-rows-encodablep fn-ockp-tables-encodablep
                           fn-ockp-rows-program-octets fn-ockp-program-octets)))

; -----------------------------------------------------------------------------
; The loop KEYSTONE (PRF-199's buffer half): the octets of the steps, in
; order, are `fn-sct-file-octets' of the tables' programs, at any batch size
; and any segment size.  The residue invariant: what remains of a run is
; the chunks of the residue [W, fill) in the buffer followed by the program
; of the rows not yet encoded, framed from INDEX with the chain at PREV;
; a step emits the full chunks of the residue and its batch and leaves the
; rest as the new residue (`fn-ockp-chunks-of-append-cut',
; `fn-ockp-frames-of-append'); the last step of a run emits the residue as
; the run's last frame.

(local
 (defthm fn-ockp-plan-octets-of-append
   (equal (fn-sccb-plan-octets (append x y) fn-octets)
          (append (fn-sccb-plan-octets x fn-octets) (fn-sccb-plan-octets y fn-octets)))))

(local
 (defthm fn-ockp-plan-octets-true-listp
   (true-listp (fn-sccb-plan-octets plan fn-octets))))

(local
 (defthm fn-ockp-revappend-is-append
   (implies (syntaxp (not (equal y ''nil)))
            (equal (revappend acc y) (append (revappend acc nil) y)))))

(local
 (defthm fn-ockp-nthcdr-of-nthcdr
   (implies (and (natp n) (natp m))
            (equal (nthcdr n (nthcdr m x)) (nthcdr (+ n m) x)))))

(local
 (defthm fn-ockp-len-of-nthcdr
   (implies (natp n)
            (equal (len (nthcdr n x)) (nfix (- (len x) n))))))

(local
 (defthm fn-ockp-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr n x)))))

(local
 (defthm fn-ockp-take-of-len
   (implies (true-listp x) (equal (take (len x) x) x))))

(local
 (defthm fn-ockp-true-listp-take
   (true-listp (take n x))))

(local
 (defthm fn-ockp-len-of-take
   (equal (len (take n x)) (nfix n))))

(local
 (defthm fn-ockp-true-list-fix-of-append
   (equal (true-list-fix (append a b))
          (append (true-list-fix a) (true-list-fix b)))))

; The residue of the cut is one chunk, and it is the suffix of P after the
; full chunks.
(local
 (defthm fn-ockp-chunks-of-cut-residue
   (implies (true-listp p)
            (equal (fn-scc-chunks (mv-nth 1 (fn-ockp-cut p seg)) seg)
                   (list (mv-nth 1 (fn-ockp-cut p seg)))))
   :hints (("Goal" :induct (fn-ockp-cut p seg)
            :in-theory (enable fn-ockp-cut)))))

; The list-level cut, opened by length: nothing when P is at most one
; segment, else one full chunk and the cut of the rest.
(local
 (defthm fn-ockp-cut-short
   (implies (or (zp seg) (<= (len p) seg))
            (equal (fn-ockp-cut p seg) (list nil p)))
   :hints (("Goal" :in-theory (enable fn-ockp-cut)))))

(local
 (defthm fn-ockp-cut-long
   (implies (and (not (zp seg)) (< seg (len p)))
            (equal (fn-ockp-cut p seg)
                   (list (cons (take seg p) (car (fn-ockp-cut (nthcdr seg p) seg)))
                         (mv-nth 1 (fn-ockp-cut (nthcdr seg p) seg)))))
   :hints (("Goal" :in-theory (enable fn-ockp-cut)))))

(local
 (defthm fn-ockp-u64-true-listp
   (true-listp (fn-scc-u64 n k))
   :hints (("Goal" :in-theory (enable fn-scc-u64)))))

(local
 (defthm fn-ockp-header-true-listp
   (true-listp (fn-scc-header index count length sequence))
   :hints (("Goal" :in-theory (enable fn-scc-header)))))

(local
 (defthm fn-ockp-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-ockp-nthcdr-len
   (implies (true-listp x) (equal (nthcdr (len x) x) nil))))

(local
 (defthm fn-ockp-admit-frames-consp
   (consp (fn-ockp-admit-frames frames total segment-bound file-bound))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-ockp-admit-frames)))))

(local
 (defthm fn-ockp-rows-program-of-atom
   (implies (not (consp rows))
            (equal (fn-sct-rows-program rows i selfp mtrie n table) nil))
   :hints (("Goal" :in-theory (enable fn-sct-rows-program)))))

; The buffer's cut is the list's cut: the frames' octets, where the residue
; begins (the residue is the buffer from there), the chain's end and the
; next index.
(local
 (defthm fn-ockp-cut-frames-is-cut
   (implies (and (natp a) (<= a (len fn-octets)) (true-listp fn-octets)
                 (natp index) (natp seg))
            (let ((r (fn-ockp-cut-frames a index count s prev seg acc fn-octets))
                  (c (fn-ockp-cut (nthcdr a fn-octets) seg)))
              (and (equal (fn-sccb-plan-octets (mv-nth 0 r) fn-octets)
                          (append (fn-sccb-plan-octets (revappend acc nil) fn-octets)
                                  (fn-scc-concat (fn-scc-frames (car c) index count s prev))))
                   (natp (mv-nth 1 r)) (<= (mv-nth 1 r) (len fn-octets))
                   (equal (nthcdr (mv-nth 1 r) fn-octets) (mv-nth 1 c))
                   (equal (mv-nth 2 r) (fn-ockp-chain-end (car c) index count s prev))
                   (equal (mv-nth 3 r) (+ index (len (car c)))))))
   :hints (("Goal" :induct (fn-ockp-cut-frames a index count s prev seg acc fn-octets)
            :in-theory (e/d (fn-ockp-cut-frames fn-ockp-chain-end
                             fn-sccb-slice-acc-is-slice-list)
                            (fn-scc-header fn-scc-seal fn-ockp-cut))))))

; The same frames' octets, as the rewriter meets them: `mv-nth 0' is `car'.
(local
 (defthm fn-ockp-cut-frames-octets
   (implies (and (natp a) (<= a (len fn-octets)) (true-listp fn-octets)
                 (natp index) (natp seg))
            (equal (fn-sccb-plan-octets
                    (car (fn-ockp-cut-frames a index count s prev seg acc fn-octets))
                    fn-octets)
                   (append (fn-sccb-plan-octets (revappend acc nil) fn-octets)
                           (fn-scc-concat
                            (fn-scc-frames (car (fn-ockp-cut (nthcdr a fn-octets) seg))
                                           index count s prev)))))
   :hints (("Goal" :use fn-ockp-cut-frames-is-cut
            :in-theory (disable fn-ockp-cut-frames-is-cut)))))

; Where the residue begins is within the buffer, as a linear fact (the
; buffer's length meets the prover as a sum).
(local
 (defthm fn-ockp-cut-frames-bound
   (implies (and (natp a) (<= a (len fn-octets)) (true-listp fn-octets)
                 (natp index) (natp seg))
            (<= (mv-nth 1 (fn-ockp-cut-frames a index count s prev seg acc fn-octets))
                (len fn-octets)))
   :rule-classes :linear
   :hints (("Goal" :use fn-ockp-cut-frames-is-cut
            :in-theory (disable fn-ockp-cut-frames-is-cut)))))

(local
 (defthm fn-ockp-last-frame-octets
   (implies (and (natp a) (<= a (len fn-octets)) (true-listp fn-octets))
            (equal (fn-sccb-plan-octets (fn-ockp-last-frame a index count s prev fn-octets)
                                        fn-octets)
                   (fn-scc-concat (fn-scc-frames (list (nthcdr a fn-octets)) index count s prev))))
   :hints (("Goal" :in-theory (e/d (fn-ockp-last-frame fn-sccb-slice-acc-is-slice-list)
                                   (fn-scc-header fn-scc-seal))))))

(local
 (defthm fn-ockp-residue-is-nthcdr
   (implies (and (natp w) (<= w (len fn-octets)) (true-listp fn-octets))
            (equal (fn-sccb-slice-acc w (len fn-octets) nil fn-octets) (nthcdr w fn-octets)))
   :hints (("Goal" :in-theory (enable fn-sccb-slice-acc-is-slice-list)))))

; A rows program splits at any batch.
(local
 (defun fn-ockp-take-ind (b rows i)
   (if (or (zp b) (not (consp rows))) (list rows i)
     (fn-ockp-take-ind (1- b) (cdr rows) (+ 1 i)))))

(local
 (defthm fn-ockp-rows-program-take-drop
   (implies (natp i)
            (equal (fn-sct-rows-program rows i selfp mtrie n table)
                   (append (fn-sct-rows-program (fn-ockp-take b rows) i selfp mtrie n table)
                           (fn-sct-rows-program (fn-ockp-drop b rows)
                                                (+ i (len (fn-ockp-take b rows)))
                                                selfp mtrie n table))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ockp-take-ind b rows i)
            :in-theory (e/d (fn-sct-rows-program) (fn-sct-program))))))

; Without a candidate and without the trie (F and P) the encoder never
; reads the event index: the step passes the index to every table, the
; specification passes nil to F and P.
(local
 (defthm fn-ockp-candidate-without-trie
   (equal (fn-sct-candidate x nil n table) nil)
   :hints (("Goal" :in-theory (enable fn-sct-candidate fn-cei-trie-records)))))

(local
 (defthm fn-ockp-program-table-irrelevant
   (implies (syntaxp (not (equal table ''nil)))
            (equal (fn-sct-program x nil nil n table) (fn-sct-program x nil nil n nil)))
   :hints (("Goal" :induct (fn-sct-program x nil nil n table)
            :in-theory (e/d (fn-sct-program)
                            (fn-scc-program fn-scc-atom-octets fn-sct-refp
                             fn-scc-octets-valuep))))))

(local
 (defthm fn-ockp-rows-program-table-irrelevant
   (implies (syntaxp (not (equal table ''nil)))
            (equal (fn-sct-rows-program rows i nil nil n table)
                   (fn-sct-rows-program rows i nil nil n nil)))
   :hints (("Goal" :in-theory (e/d (fn-sct-rows-program) (fn-sct-program))))))

; What remains of one run from a state within it: the residue [W, fill) of
; the buffer followed by the program of the rows not yet encoded, cut into
; segments and framed from INDEX with the chain at PREV.  The encoder is
; handed the event index for every table (`fn-ockp-batch'); F and P never
; read it (`fn-ockp-rows-program-table-irrelevant' relates this to the
; specification's nil where the runs meet `fn-sct-table-programs').
(defun fn-ockp-run-remaining (rest i selfp mtrie n table index count s prev w seg buf)
  (declare (xargs :guard t :verify-guards nil))
  (fn-scc-concat
   (fn-scc-frames (fn-scc-chunks (append (nthcdr w buf)
                                         (fn-sct-rows-program rest i selfp mtrie n table))
                                 seg)
                  index count s prev)))

; What remains to be written from a state: the run K from its residue and
; the rows not yet encoded, then the runs after it whole (each from its
; first row, the genesis and an empty residue).
(defun fn-ockp-later (tables k n mtrie table counts seg s)
  (declare (xargs :guard t :measure (nfix (- 4 (nfix k))) :verify-guards nil))
  (if (or (not (natp k)) (>= k 4))
      nil
    (append (fn-ockp-run-remaining (fn-ockp-table-rows tables k) 0 (eql k 2)
                                   (if (eql k 3) mtrie nil) n table
                                   0 (fn-ockp-count counts k) s *fn-scc-genesis* 0 seg nil)
            (fn-ockp-later tables (+ 1 k) n mtrie table counts seg s))))

(defun fn-ockp-remaining (tables k rest i index prev w n mtrie table counts seg s buf)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (natp k)) (>= k 4))
      nil
    (append (fn-ockp-run-remaining rest i (eql k 2) (if (eql k 3) mtrie nil) n table
                                   index (fn-ockp-count counts k) s prev w seg buf)
            (fn-ockp-later tables (+ 1 k) n mtrie table counts seg s))))

(in-theory (disable fn-ockp-run-remaining fn-ockp-later fn-ockp-remaining))

; The two specifications open by these rules, never by their definitions:
; a run is written while K is one of the four, and K reaches 4 as a
; constant in the step lemma's last case (the unfold of `fn-ockp-later'
; stops at (+ 1 K), whose bound the rule cannot relieve).
(local
 (defthm fn-ockp-later-done
   (implies (or (not (natp k)) (>= k 4))
            (equal (fn-ockp-later tables k n mtrie table counts seg s) nil))
   :hints (("Goal" :in-theory (enable fn-ockp-later)))))

(local
 (defthm fn-ockp-remaining-done
   (implies (or (not (natp k)) (>= k 4))
            (equal (fn-ockp-remaining tables k rest i index prev w n mtrie table counts seg s buf)
                   nil))
   :hints (("Goal" :in-theory (enable fn-ockp-remaining)))))

(local
 (defthm fn-ockp-later-unfold
   (implies (and (natp k) (< k 4))
            (equal (fn-ockp-later tables k n mtrie table counts seg s)
                   (append (fn-ockp-run-remaining (fn-ockp-table-rows tables k) 0 (eql k 2)
                                                  (if (eql k 3) mtrie nil) n table
                                                  0 (fn-ockp-count counts k) s *fn-scc-genesis*
                                                  0 seg nil)
                           (fn-ockp-later tables (+ 1 k) n mtrie table counts seg s))))
   :hints (("Goal" :expand ((fn-ockp-later tables k n mtrie table counts seg s))))))

(local
 (defthm fn-ockp-remaining-unfold
   (implies (and (natp k) (< k 4))
            (equal (fn-ockp-remaining tables k rest i index prev w n mtrie table counts seg s buf)
                   (append (fn-ockp-run-remaining rest i (eql k 2) (if (eql k 3) mtrie nil) n table
                                                  index (fn-ockp-count counts k) s prev w seg buf)
                           (fn-ockp-later tables (+ 1 k) n mtrie table counts seg s))))
   :hints (("Goal" :in-theory (enable fn-ockp-remaining)))))

; The residue after a run's last frame is empty: W' is the buffer's fill,
; which the prover holds as a sum.
(local
 (defthm fn-ockp-nthcdr-past-end
   (implies (and (true-listp x) (natp n) (<= (len x) n))
            (equal (nthcdr n x) nil))))

; A run whose residue begins at the buffer's fill has no residue: it is the
; run from its rows alone.
(local
 (defthm fn-ockp-run-remaining-at-fill
   (implies (and (true-listp buf) (natp w) (<= (len buf) w)
                 (syntaxp (not (and (equal w ''0) (equal buf ''nil)))))
            (equal (fn-ockp-run-remaining rest i selfp mtrie n table index count s prev w seg buf)
                   (fn-ockp-run-remaining rest i selfp mtrie n table index count s prev 0 seg nil)))
   :hints (("Goal" :in-theory (e/d (fn-ockp-run-remaining)
                                   (fn-scc-chunks fn-scc-frames fn-scc-concat
                                    fn-sct-rows-program))))))

; A run's start over any buffer whose residue begins at its fill: what
; remains from there is the runs from K whole.
(local
 (defthm fn-ockp-remaining-at-start-k
   (implies (and (true-listp buf) (natp w) (<= (len buf) w))
            (equal (fn-ockp-remaining tables k (fn-ockp-table-rows tables k) 0 0 *fn-scc-genesis* w
                                      n mtrie table counts seg s buf)
                   (fn-ockp-later tables k n mtrie table counts seg s)))
   :hints (("Goal" :cases ((and (natp k) (< k 4)))
            :in-theory (disable fn-scc-chunks fn-scc-frames fn-scc-concat fn-sct-rows-program
                                fn-ockp-table-rows fn-ockp-count)))))

(local
 (defthm fn-ockp-true-listp-append-program
   (true-listp (append (nthcdr w buf) (fn-sct-rows-program rest i selfp mtrie n table)))))

; One step within a run, for any table's parameters (the step lemma below
; instantiates them from K once, so the frame algebra is proved once, not
; per table): the frames of the cut over the buffer as the encoder leaves
; it, then what remains of the run from the state the cut leaves, is what
; remained of the run before the step.
(local
 (defthm fn-ockp-run-step-continues
   (implies (and (natp w) (<= w (len buf)) (true-listp buf) (natp index) (natp seg) (natp i))
            (let* ((buf2 (append (nthcdr w buf)
                                 (fn-sct-rows-program (fn-ockp-take b rest) i selfp mtrie n table)))
                   (c (fn-ockp-cut-frames 0 index count s prev seg nil buf2)))
              (equal (fn-ockp-run-remaining rest i selfp mtrie n table index count s prev w seg
                                            buf)
                     (append (fn-sccb-plan-octets (car c) buf2)
                             (fn-ockp-run-remaining (fn-ockp-drop b rest)
                                                    (+ i (len (fn-ockp-take b rest)))
                                                    selfp mtrie n table (mv-nth 3 c) count s
                                                    (mv-nth 2 c) (mv-nth 1 c) seg buf2)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ockp-cut-frames-is-cut (a 0) (acc nil)
                             (fn-octets (append (nthcdr w buf)
                                                (fn-sct-rows-program (fn-ockp-take b rest) i selfp
                                                                     mtrie n table))))
                  (:instance fn-ockp-rows-program-take-drop (rows rest))
                  (:instance fn-ockp-chunks-of-append-cut
                             (p (append (nthcdr w buf)
                                        (fn-sct-rows-program (fn-ockp-take b rest) i selfp mtrie n
                                                             table)))
                             (q (fn-sct-rows-program (fn-ockp-drop b rest)
                                                     (+ i (len (fn-ockp-take b rest)))
                                                     selfp mtrie n table)))
                  (:instance fn-ockp-frames-of-append
                             (c1 (car (fn-ockp-cut (append (nthcdr w buf)
                                                           (fn-sct-rows-program (fn-ockp-take b rest)
                                                                                i selfp mtrie n table))
                                                   seg)))
                             (c2 (fn-scc-chunks
                                  (append (mv-nth 1 (fn-ockp-cut
                                                     (append (nthcdr w buf)
                                                             (fn-sct-rows-program (fn-ockp-take b rest)
                                                                                  i selfp mtrie n table))
                                                     seg))
                                          (fn-sct-rows-program (fn-ockp-drop b rest)
                                                               (+ i (len (fn-ockp-take b rest)))
                                                               selfp mtrie n table))
                                  seg))))
            :in-theory (e/d (fn-ockp-run-remaining)
                            (fn-scc-header fn-scc-seal fn-scc-chunks fn-scc-frames fn-scc-concat
                             fn-sct-rows-program fn-ockp-cut fn-ockp-cut-frames fn-ockp-chain-end
                             fn-ockp-take fn-ockp-drop fn-ockp-cut-frames-is-cut
                             fn-ockp-cut-frames-octets fn-ockp-cut-frames-bound
                             fn-ockp-chunks-of-append-cut fn-ockp-frames-of-append))))))

; The run's last step: the cut's frames and the residue as the last frame
; are what remained of the run.
(local
 (defthm fn-ockp-run-step-ends
   (implies (and (natp w) (<= w (len buf)) (true-listp buf) (natp index) (natp seg) (natp i)
                 (not (consp (fn-ockp-drop b rest))))
            (let* ((buf2 (append (nthcdr w buf)
                                 (fn-sct-rows-program (fn-ockp-take b rest) i selfp mtrie n table)))
                   (c (fn-ockp-cut-frames 0 index count s prev seg nil buf2)))
              (equal (fn-ockp-run-remaining rest i selfp mtrie n table index count s prev w seg
                                            buf)
                     (fn-sccb-plan-octets
                      (append (car c)
                              (fn-ockp-last-frame (mv-nth 1 c) (mv-nth 3 c) count s (mv-nth 2 c) buf2))
                      buf2))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ockp-cut-frames-is-cut (a 0) (acc nil)
                             (fn-octets (append (nthcdr w buf)
                                                (fn-sct-rows-program (fn-ockp-take b rest) i selfp
                                                                     mtrie n table))))
                  (:instance fn-ockp-rows-program-take-drop (rows rest))
                  (:instance fn-ockp-chunks-of-append-cut
                             (p (append (nthcdr w buf)
                                        (fn-sct-rows-program (fn-ockp-take b rest) i selfp mtrie n
                                                             table)))
                             (q nil))
                  (:instance fn-ockp-frames-of-append
                             (c1 (car (fn-ockp-cut (append (nthcdr w buf)
                                                           (fn-sct-rows-program (fn-ockp-take b rest)
                                                                                i selfp mtrie n table))
                                                   seg)))
                             (c2 (list (mv-nth 1 (fn-ockp-cut
                                                  (append (nthcdr w buf)
                                                          (fn-sct-rows-program (fn-ockp-take b rest)
                                                                               i selfp mtrie n table))
                                                  seg))))))
            :in-theory (e/d (fn-ockp-run-remaining)
                            (fn-scc-header fn-scc-seal fn-scc-chunks fn-scc-frames fn-scc-concat
                             fn-sct-rows-program fn-ockp-cut fn-ockp-cut-frames fn-ockp-chain-end
                             fn-ockp-take fn-ockp-drop fn-ockp-cut-frames-is-cut
                             fn-ockp-cut-frames-octets fn-ockp-cut-frames-bound
                             fn-ockp-chunks-of-append-cut fn-ockp-frames-of-append))))))

; Where the cut leaves the residue and the next index are naturals (the
; cut theorem says so; these two rules say only that, and rewrite nothing
; else, so the step lemma's terms keep their shape).
(local
 (defthm fn-ockp-cut-frames-a-natp
   (implies (and (natp a) (<= a (len fn-octets)) (true-listp fn-octets) (natp index) (natp seg))
            (natp (mv-nth 1 (fn-ockp-cut-frames a index count s prev seg acc fn-octets))))
   :hints (("Goal" :use fn-ockp-cut-frames-is-cut
            :in-theory (disable fn-ockp-cut-frames-is-cut)))))

(local
 (defthm fn-ockp-cut-frames-index-natp
   (implies (and (natp a) (<= a (len fn-octets)) (true-listp fn-octets) (natp index) (natp seg))
            (natp (mv-nth 3 (fn-ockp-cut-frames a index count s prev seg acc fn-octets))))
   :hints (("Goal" :use fn-ockp-cut-frames-is-cut
            :in-theory (disable fn-ockp-cut-frames-is-cut)))))

; One step: its frames' octets over the buffer it leaves, then what remains
; from the state it leaves, is what remained before it.  K stays a
; variable: the run lemmas above take the table's parameters as K gives
; them, and a run that ends hands the next run its start.
(local
 (defthm fn-ockp-batch-writes-the-remaining
   (implies (and (natp k) (< k 4) (natp i) (natp index) (natp w) (<= w (len fn-octets))
                 (true-listp fn-octets) (natp seg))
            (let ((r (fn-ockp-batch tables k rest i index prev w b bytes seg s counts n mtrie table
                                    total segment-bound file-bound fn-octets)))
              (implies (equal (mv-nth 0 r) :ok)
                       (and (equal (fn-ockp-remaining tables k rest i index prev w n mtrie table
                                                      counts seg s fn-octets)
                                   (append (fn-sccb-plan-octets (mv-nth 1 r) (mv-nth 9 r))
                                           (fn-ockp-remaining tables (mv-nth 2 r) (mv-nth 3 r)
                                                              (mv-nth 4 r) (mv-nth 5 r)
                                                              (mv-nth 6 r) (mv-nth 7 r)
                                                              n mtrie table counts seg s
                                                              (mv-nth 9 r))))
                            (natp (mv-nth 2 r)) (natp (mv-nth 4 r)) (natp (mv-nth 5 r))
                            (natp (mv-nth 7 r)) (<= (mv-nth 7 r) (len (mv-nth 9 r)))
                            (true-listp (mv-nth 9 r))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ockp-run-step-continues
                             (selfp (eql k 2)) (mtrie (if (eql k 3) mtrie nil))
                             (count (fn-ockp-count counts k)) (buf fn-octets)
                             (b (fn-ockp-batch-rows rest i b bytes (eql k 2) (if (eql k 3) mtrie nil)
                                                    n table (+ (- w) (len fn-octets)))))
                  (:instance fn-ockp-run-step-ends
                             (selfp (eql k 2)) (mtrie (if (eql k 3) mtrie nil))
                             (count (fn-ockp-count counts k)) (buf fn-octets)
                             (b (fn-ockp-batch-rows rest i b bytes (eql k 2) (if (eql k 3) mtrie nil)
                                                    n table (+ (- w) (len fn-octets))))))
            :in-theory (e/d (fn-ockp-batch)
                            (fn-ockp-remaining fn-ockp-later fn-ockp-run-remaining
                             fn-scc-header fn-scc-seal fn-scc-chunks fn-scc-frames fn-scc-concat
                             fn-sct-rows-program fn-ockp-table-rows fn-ockp-count fn-ockp-batch-rows
                             fn-ockp-admit-frames fn-ockp-cut fn-ockp-cut-frames fn-ockp-last-frame
                             fn-ockp-chain-end fn-ockp-take fn-ockp-drop
                             fn-ockp-chunks-of-append-cut fn-ockp-frames-of-append
                             fn-ockp-cut-frames-is-cut fn-ockp-cut-frames-octets
                             fn-ockp-last-frame-octets fn-sccb-plan-octets fn-sccb-frame-octets
                             fn-ockp-nthcdr-past-end nthcdr))))))

; The step fact as the rewriter meets it in the loop's induction: over
; `fn-ockp-step' and the state list's components, in normal form (`nth',
; `nfix' kept closed so that `(nfix (nth 5 setup))' matches itself; `nfix'
; opens only where a natural is known).
(local
 (defthm fn-ockp-nfix-when-natp
   (implies (natp x) (equal (nfix x) x))))

(local
 (defthm fn-ockp-step-writes-the-remaining
   (implies (and (natp (nth 0 pst)) (< (nth 0 pst) 4) (natp (nth 2 pst)) (natp (nth 3 pst))
                 (natp (nth 5 pst)) (<= (nth 5 pst) (len fn-octets)) (true-listp fn-octets)
                 (natp seg)
                 (equal (mv-nth 0 (fn-ockp-step setup pst b bytes seg s segment-bound file-bound
                                                fn-octets))
                        :ok))
            (let ((r (fn-ockp-step setup pst b bytes seg s segment-bound file-bound fn-octets)))
              (and (equal (append (fn-sccb-plan-octets (mv-nth 1 r) (mv-nth 3 r))
                                  (fn-ockp-remaining (nth 1 setup)
                                                     (nth 0 (mv-nth 2 r)) (nth 1 (mv-nth 2 r))
                                                     (nth 2 (mv-nth 2 r)) (nth 3 (mv-nth 2 r))
                                                     (nth 4 (mv-nth 2 r)) (nth 5 (mv-nth 2 r))
                                                     (nfix (nth 5 setup)) (nth 3 setup)
                                                     (nth 4 setup) (nth 2 setup) seg s
                                                     (mv-nth 3 r)))
                          (fn-ockp-remaining (nth 1 setup) (nth 0 pst) (nth 1 pst)
                                             (nth 2 pst) (nth 3 pst) (nth 4 pst) (nth 5 pst)
                                             (nfix (nth 5 setup)) (nth 3 setup)
                                             (nth 4 setup) (nth 2 setup) seg s
                                             fn-octets))
                   (natp (nth 0 (mv-nth 2 r))) (natp (nth 2 (mv-nth 2 r)))
                   (natp (nth 3 (mv-nth 2 r))) (natp (nth 5 (mv-nth 2 r)))
                   (<= (nth 5 (mv-nth 2 r)) (len (mv-nth 3 r))) (true-listp (mv-nth 3 r)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ockp-batch-writes-the-remaining
                             (tables (nth 1 setup)) (k (nth 0 pst)) (rest (nth 1 pst))
                             (i (nth 2 pst)) (index (nth 3 pst)) (prev (nth 4 pst))
                             (w (nth 5 pst)) (counts (nth 2 setup))
                             (n (nfix (nth 5 setup))) (mtrie (nth 3 setup))
                             (table (nth 4 setup)) (total (nth 6 pst))))
            :in-theory (e/d (fn-ockp-step fn-sco-at)
                            (nth nfix fn-scc-header fn-scc-seal fn-scc-chunks fn-scc-frames
                             fn-scc-concat fn-sct-rows-program fn-ockp-table-rows fn-ockp-count
                             fn-ockp-batch fn-ockp-remaining fn-ockp-later fn-ockp-run-remaining
                             fn-ockp-remaining-unfold fn-ockp-later-unfold
                             fn-ockp-remaining-at-start-k))))))


; -----------------------------------------------------------------------------
; The invariants carried between steps (PKT-583 (a)).  The shape the host's
; entry checks (`fn-ockp-statep', O(1)) is preserved by an :ok step, so the
; host's loop meets no guard violation at the *1* entry; the encodability of
; the rows not yet encoded (`fn-ockp-state-encodablep'), established at the
; start from the setup's one check, is preserved by every step, and a step
; over an encodable state never refuses a row: after a :plan the pipeline's
; only refusals are the reader's.

(local
 (defthm fn-ockp-admit-frames-total-natp
   (implies (and (natp total)
                 (equal (car (fn-ockp-admit-frames frames total segment-bound file-bound)) :ok))
            (natp (nth 1 (fn-ockp-admit-frames frames total segment-bound file-bound))))
   :hints (("Goal" :induct (fn-ockp-admit-frames frames total segment-bound file-bound)
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(fn-ockp-admit-frames natp nth zp car-cons cdr-cons
                                         (:executable-counterpart zp)
                                         (:executable-counterpart nth)
                                         (:executable-counterpart natp)))))))

(local
 (defthm fn-ockp-batch-total-natp
   (implies (and (natp total)
                 (equal (mv-nth 0 (fn-ockp-batch tables k rest i index prev w b bytes seg s counts n mtrie
                                                 table total segment-bound file-bound fn-octets))
                        :ok))
            (natp (mv-nth 8 (fn-ockp-batch tables k rest i index prev w b bytes seg s counts n mtrie
                                           table total segment-bound file-bound fn-octets))))
   :hints (("Goal" :in-theory (e/d (fn-ockp-batch)
                                   (fn-ockp-encode-batch fn-ockp-cut-frames fn-ockp-last-frame
                                    fn-ockp-admit-frames fn-ockp-table-rows fn-ockp-count
                                    fn-ockp-encode-batch-is-rows-program
                                    fn-ockp-encode-batch-ok-is-encodable
                                    fn-sccb-slice-acc-is-slice-list fn-ockp-residue-is-nthcdr))))))

(defthm fn-ockp-step-preserves-statep
  (implies (and (fn-ockp-statep pst fn-octets) (not (fn-ockp-donep pst))
                (true-listp fn-octets) (natp seg)
                (equal (mv-nth 0 (fn-ockp-step setup pst b bytes seg s segment-bound file-bound fn-octets))
                       :ok))
           (fn-ockp-statep (mv-nth 2 (fn-ockp-step setup pst b bytes seg s segment-bound file-bound
                                                   fn-octets))
                           (mv-nth 3 (fn-ockp-step setup pst b bytes seg s segment-bound file-bound
                                                   fn-octets))))
  :hints (("Goal" :do-not-induct t
           :use (fn-ockp-step-writes-the-remaining
                 (:instance fn-ockp-batch-total-natp
                            (tables (nth 1 setup)) (k (nth 0 pst)) (rest (nth 1 pst))
                            (i (nth 2 pst)) (index (nth 3 pst)) (prev (nth 4 pst))
                            (w (nth 5 pst)) (counts (nth 2 setup))
                            (n (nfix (nth 5 setup))) (mtrie (nth 3 setup))
                            (table (nth 4 setup)) (total (nth 6 pst))))
           :in-theory (e/d (fn-ockp-step fn-ockp-statep fn-ockp-donep fn-sco-at)
                           (nth nfix fn-ockp-batch fn-ockp-remaining fn-ockp-later
                            fn-ockp-run-remaining fn-ockp-remaining-unfold fn-ockp-later-unfold
                            fn-ockp-remaining-at-start-k fn-ockp-step-writes-the-remaining
                            fn-ockp-batch-total-natp fn-scc-header fn-scc-seal fn-scc-chunks
                            fn-scc-frames fn-scc-concat fn-sct-rows-program fn-ockp-table-rows
                            fn-ockp-count)))))

(local
 (defthm fn-ockp-encode-batch-rest-encodable
   (implies (fn-ockp-rows-encodablep rest)
            (fn-ockp-rows-encodablep
             (mv-nth 1 (fn-ockp-encode-batch rest i b bytes selfp mtrie n table fn-octets))))
   :hints (("Goal" :induct (fn-ockp-encode-batch rest i b bytes selfp mtrie n table fn-octets)
            :in-theory (e/d (fn-ockp-encode-batch fn-ockp-rows-encodablep)
                            (fn-sct-renc fn-ockp-encode-batch-is-rows-program
                             fn-ockp-encode-batch-ok-is-encodable))))))

(local
 (defthm fn-ockp-table-rows-encodable
   (implies (fn-ockp-tables-encodablep tables)
            (fn-ockp-rows-encodablep (fn-ockp-table-rows tables k)))
   :hints (("Goal" :in-theory (e/d (fn-ockp-table-rows fn-ockp-tables-encodablep
                                    fn-ockp-rows-encodablep)
                                   (fn-sct-tables-f fn-sct-tables-p fn-sct-tables-e
                                    fn-sct-tables-r))))))

(local
 (defthm fn-ockp-slice-acc-true-listp
   (implies (true-listp acc)
            (true-listp (fn-sccb-slice-acc i n acc fn-octets)))
   :hints (("Goal" :induct (fn-sccb-slice-acc i n acc fn-octets)
            :in-theory (e/d (fn-sccb-slice-acc) (fn-sccb-slice-acc-is-slice-list))))))

(local
 (defthm fn-ockp-batch-preserves-encodable
   (implies (and (fn-ockp-tables-encodablep tables) (fn-ockp-rows-encodablep rest))
            (let ((r (fn-ockp-batch tables k rest i index prev w b bytes seg s counts n mtrie table
                                    total segment-bound file-bound fn-octets)))
              (and (not (equal (car r) :unencodable))
                   (fn-ockp-rows-encodablep (mv-nth 3 r)))))
   :hints (("Goal" :in-theory (e/d (fn-ockp-batch)
                                   (fn-ockp-encode-batch fn-ockp-cut-frames fn-ockp-last-frame
                                    fn-ockp-admit-frames fn-ockp-table-rows fn-ockp-count
                                    fn-sccb-treep fn-ockp-tables-encodablep
                                    fn-ockp-encode-batch-is-rows-program
                                    fn-sccb-slice-acc-is-slice-list fn-ockp-residue-is-nthcdr))))))

(defthm fn-ockp-initial-state-encodable
  (implies (fn-ockp-tables-encodablep tables)
           (fn-ockp-state-encodablep (fn-ockp-initial-state tables fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-ockp-initial-state fn-ockp-state-encodablep)
                                  (fn-ockp-table-rows fn-ockp-tables-encodablep)))))

(defthm fn-ockp-step-preserves-encodable
  (implies (and (fn-ockp-tables-encodablep (fn-sco-at 1 setup))
                (fn-ockp-state-encodablep pst))
           (let ((r (fn-ockp-step setup pst b bytes seg s segment-bound file-bound fn-octets)))
             (and (not (equal (car r) :unencodable))
                  (fn-ockp-state-encodablep (mv-nth 2 r)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ockp-batch-preserves-encodable
                            (tables (nth 1 setup)) (k (nth 0 pst)) (rest (nth 1 pst))
                            (i (nth 2 pst)) (index (nth 3 pst)) (prev (nth 4 pst))
                            (w (nth 5 pst)) (counts (nth 2 setup))
                            (n (nfix (nth 5 setup))) (mtrie (nth 3 setup))
                            (table (nth 4 setup)) (total (nth 6 pst))))
           :in-theory (e/d (fn-ockp-step fn-ockp-state-encodablep fn-sco-at)
                           (nth nfix fn-ockp-batch fn-ockp-tables-encodablep
                            fn-ockp-rows-encodablep fn-ockp-batch-preserves-encodable)))))

(defthm fn-ockp-run-is-the-remaining
  (implies (and (natp (nth 0 pst)) (natp (nth 2 pst)) (natp (nth 3 pst)) (natp (nth 5 pst))
                (<= (nth 5 pst) (len fn-octets)) (true-listp fn-octets) (natp seg)
                (equal (mv-nth 0 (fn-ockp-run setup pst b bytes seg s segment-bound file-bound fuel
                                              fn-octets))
                       :ok))
           (equal (mv-nth 1 (fn-ockp-run setup pst b bytes seg s segment-bound file-bound fuel
                                         fn-octets))
                  (fn-ockp-remaining (fn-sco-at 1 setup) (nth 0 pst) (nth 1 pst) (nth 2 pst)
                                     (nth 3 pst) (nth 4 pst) (nth 5 pst)
                                     (nfix (fn-sco-at 5 setup)) (fn-sco-at 3 setup)
                                     (fn-sco-at 4 setup) (fn-sco-at 2 setup) seg s fn-octets)))
  :hints (("Goal" :induct (fn-ockp-run setup pst b bytes seg s segment-bound file-bound fuel fn-octets)
           :in-theory (e/d (fn-ockp-run fn-ockp-donep fn-sco-at)
                           (nth nfix fn-scc-header fn-scc-seal fn-scc-chunks fn-scc-frames
                            fn-scc-concat fn-sct-rows-program fn-ockp-table-rows fn-ockp-count
                            fn-ockp-batch fn-ockp-step fn-ockp-remaining fn-ockp-later
                            fn-ockp-run-remaining fn-ockp-remaining-unfold fn-ockp-later-unfold
                            fn-ockp-remaining-at-start-k)))))

(local
 (defthm fn-ockp-later-from-0-is-the-file
   (implies (fn-sct-tables-treep tables)
            (equal (fn-ockp-later tables 0 (len (fn-sct-tables-e tables)) (fn-cei-msgid-trie index)
                                  index (fn-ockp-counts tables index seg) seg s)
                   (fn-sct-file-octets (fn-sct-table-programs tables index) seg s)))
   :hints (("Goal" :in-theory (e/d (fn-ockp-later fn-ockp-run-remaining fn-sct-file-octets
                                    fn-sct-file-segments fn-sct-run-segments fn-sct-table-programs
                                    fn-ockp-table-rows fn-ockp-count fn-sco-at)
                                   (fn-scc-chunks fn-scc-frames fn-scc-concat fn-sct-rows-program
                                    fn-sccb-chunk-count fn-ockp-counts fn-cei-msgid-trie))))))

(defthm fn-ockp-run-writes-the-file
  (let* ((setup (fn-ockp-setup next frontier revision log seg budget free))
         (tables (fn-sct-tables-of-capture next frontier revision log))
         (run (fn-ockp-run setup (fn-ockp-initial-state tables fn-octets)
                           b bytes seg s segment-bound file-bound fuel fn-octets)))
    (implies (and (fn-ockp-tables-encodablep tables)
                  (true-listp fn-octets) (natp seg)
                  (equal (mv-nth 0 run) :ok))
             (equal (mv-nth 1 run)
                    (fn-sct-file-octets (fn-sct-table-programs tables (fn-sco-event-index next))
                                        seg s))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ockp-setup fn-ockp-initial-state fn-sco-at)
                           (fn-scc-chunks fn-scc-frames fn-scc-concat fn-sct-rows-program
                            fn-ockp-table-rows fn-ockp-count fn-ockp-counts fn-ockp-estimate
                            fn-ockp-decide fn-sct-tables-of-capture fn-sct-file-octets
                            fn-sct-table-programs fn-ockp-remaining fn-ockp-later
                            fn-cei-msgid-trie fn-sct-tables-e fn-sct-tables-f fn-sct-tables-p
                            fn-sct-tables-r fn-ockp-tables-encodablep fn-sco-event-index
                            fn-sct-tables-treep fn-ockp-counts-are-chunk-counts)))))

; The loop over an encodable state never refuses a row (its verdicts are
; :ok, :fuel and the reader's refusals), and after a setup that did not
; answer :unencodable neither does the run the host starts from it.  The
; verdict is written `car' (the rewriter's form of `mv-nth 0').
(defthm fn-ockp-run-of-encodable-never-refuses-a-row
  (implies (and (fn-ockp-tables-encodablep (fn-sco-at 1 setup))
                (fn-ockp-state-encodablep pst))
           (not (equal (car (fn-ockp-run setup pst b bytes seg s segment-bound file-bound fuel fn-octets))
                       :unencodable)))
  :hints (("Goal" :induct (fn-ockp-run setup pst b bytes seg s segment-bound file-bound fuel fn-octets)
           :in-theory (e/d (fn-ockp-run)
                           (fn-ockp-step fn-ockp-donep fn-ockp-tables-encodablep
                            fn-ockp-state-encodablep fn-sccb-plan-octets)))))

(defthm fn-ockp-setup-not-unencodable-never-refuses-a-row
  (let* ((setup (fn-ockp-setup next frontier revision log seg budget free))
         (tables (fn-sct-tables-of-capture next frontier revision log)))
    (implies (not (equal (car setup) :unencodable))
             (not (equal (car (fn-ockp-run setup (fn-ockp-initial-state tables fn-octets)
                                           b bytes seg s segment-bound file-bound fuel fn-octets))
                         :unencodable))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ockp-setup fn-sco-at)
                           (nth fn-ockp-run fn-ockp-initial-state fn-ockp-tables-encodablep
                            fn-sct-tables-of-capture fn-ockp-estimate fn-ockp-counts
                            fn-ockp-decide fn-cei-msgid-trie fn-sco-event-index
                            fn-ockp-state-encodablep)))))

; -----------------------------------------------------------------------------
; The host's entries are guard-verified (here, after the cut lemmas they
; need): the per-step entry runs raw, and its guard (`fn-ockp-statep',
; O(1)) is checked once per step at the *1* entry.  The frames the cut and
; the last frame produce are lists of lists, which the admission's guard
; asks.
(local
 (defthm fn-ockp-true-list-listp-revappend
   (implies (and (true-list-listp x) (true-list-listp y))
            (true-list-listp (revappend x y)))
   :hints (("Goal" :in-theory (disable revappend-removal)))))

(local
 (defthm fn-ockp-true-list-listp-append
   (implies (and (true-list-listp x) (true-list-listp y))
            (true-list-listp (append x y)))))

(local
 (defthm fn-ockp-cut-frames-true-list-listp
   (implies (true-list-listp acc)
            (true-list-listp (car (fn-ockp-cut-frames a index count s prev seg acc fn-octets))))
   :hints (("Goal" :induct (fn-ockp-cut-frames a index count s prev seg acc fn-octets)
            :in-theory (e/d (fn-ockp-cut-frames) (fn-scc-header fn-scc-seal))))))

(local
 (defthm fn-ockp-last-frame-true-list-listp
   (true-list-listp (fn-ockp-last-frame a index count s prev fn-octets))
   :hints (("Goal" :in-theory (enable fn-ockp-last-frame)))))

(local
 (defthm fn-ockp-true-list-listp-true-listp
   (implies (true-list-listp x) (true-listp x))))

(verify-guards fn-ockp-batch
  :hints (("Goal" :in-theory (disable fn-scc-header fn-scc-seal fn-ockp-cut-frames
                                      fn-ockp-last-frame fn-ockp-cut fn-ockp-chain-end
                                      fn-ockp-take fn-ockp-drop fn-sct-rows-program
                                      fn-ockp-chunks-of-append-cut fn-ockp-frames-of-append))))

(verify-guards fn-ockp-step
  :hints (("Goal" :in-theory (enable fn-ockp-statep fn-sco-at))))

