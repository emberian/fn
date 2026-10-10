; fn: D40 raw-dispatch verdicts, judged in the ACL2 world and carried as data
; (lane extract, 2026-10-05; decisions.md D40 and item 8).
;
; WHY.  D40's raw dispatch rests on a judgment only the ACL2 world can make:
; books/definterface.lisp fn-di-raw-with-problem (for `:raw-with (:carried
; N)', def-carried's fn-cd-raw-problem: the row re-checked, every generated
; statement regenerated from the world and compared) and the :raw-guarded
; checks.  host/native/raw-trap.lisp fnn-install-raw-dispatch used to run
; them itself at installation.  In the ACL2 image that works; in the
; extracted bare-SBCL core (tools/extract/core.sh) the world is a snapshot of
; selected properties, and the judgment cannot run there: the core died at
; load with "Selected ACL2 table metadata is unavailable for FN-CARRIED"
; (rehearsal R1, 2026-10-05; broken since 633e3cdec).
;
; WHAT.  The judgment moves to the world and becomes a table:
;
;   fn-raw-dispatch-verdicts   NAME -> (DIGEST PROBLEM TARGET CREATORP)
;
; one row per fn-interfaces entry that declares :raw-with or :raw-guarded,
; written once by host/raw-dispatch-verdicts.lisp after the last
; declaration, in every world a host is built or extracted from.  PROBLEM is
; nil or the msg of the first check the world refutes; TARGET and CREATORP
; are the raw function a dispatcher call applies and whether NAME is a
; registered startup creator; DIGEST is fn-blake3 of the canonical octets
; (books/state-digest.lisp fn-sdg-canon) of the JUDGED ROW, fn-rdv-row: the
; declaration and what the host dispatches under -- formals, stobjs in and
; out, guard, symbol-class.  The table's guard re-judges every pair it is
; given, so no event can write a verdict the world does not give.
;
; The host has one path in the image and the core (fnn-install-raw-dispatch):
; for each raw-declared row of the fn-interfaces table it computes the row's
; digest from the world it has (the live world, or the core's snapshot) and
; asks fn-rdv-admit, which dispatches raw only on a verdict for that name,
; judged with no problem, over a row with exactly that digest.  The
; extractor's export (tools/extract/core-export.lisp) re-judges at export,
; refuses when its judgment is not the world's table, and ships the table in
; the core's snapshot.  fn-rdv-admits-only-a-clean-judged-row is the
; statement: a row judged problematic, unjudged or changed since it was
; judged is never admitted.
;
; What the digest does not cover: the compiled code of the target (the
; extracted definition is the extractor's, A-TARGET-COMPILER), and the parts
; of the world the judgment read beyond the row (the carried row, its
; theorems, the other declarations).  The core holds none of those; it holds
; the verdict made over them in the world its snapshot was taken from.

(in-package "ACL2")
(include-book "definterface")
(include-book "blake3")
(include-book "state-digest")

; -----------------------------------------------------------------------------
; The judged row and its digest (program mode: they read the world).

(defun fn-rdv-row (name kvs w)
  (declare (xargs :mode :program))
  ; what a verdict binds: the declaration and the entry as the host
  ; dispatches it.  Every accessor here is one the core's runtime
  ; (tools/extract/clruntime.lisp) answers from the exported snapshot.
  (list name kvs
        (getpropc name 'formals :none w)
        (stobjs-in name w)
        (stobjs-out name w)
        (guard name nil w)
        (symbol-class name w)))

(defun fn-rdv-row-digest (name kvs w)
  (declare (xargs :mode :program))
  (fn-blake3 (fn-sdg-canon (fn-rdv-row name kvs w))))

(defun fn-rdv-raw-declared-p (kvs)
  (declare (xargs :guard (keyword-value-listp kvs)))
  (or (assoc-keyword :raw-with kvs) (assoc-keyword :raw-guarded kvs)))

(defun fn-rdv-judge (name kvs w)
  (declare (xargs :mode :program))
  ; (DIGEST PROBLEM TARGET CREATORP): the checks fnn-install-raw-dispatch
  ; made against the loaded world, in its order
  (let* ((guarded (assoc-keyword :raw-guarded kvs))
         (with (fn-di-get :raw-with kvs))
         (digest (fn-rdv-row-digest name kvs w))
         (guarded-problem (and guarded (fn-di-raw-guarded-problem name kvs w)))
         (with-problem (and (not guarded-problem) with
                            (fn-di-raw-with-problem name kvs w))))
    (mv-let (target-problem target)
      (if (or guarded-problem with-problem (not guarded))
          (mv nil name)
        (fn-di-raw-guarded-target name kvs w))
      (let ((problem
             (cond (guarded-problem (msg "a refused guarded declaration: ~@0" guarded-problem))
                   (with-problem (msg "a refused declaration: ~@0" with-problem))
                   (target-problem (msg "a refused creator target: ~@0" target-problem))
                   ((not (eq (symbol-class name w) :common-lisp-compliant))
                    (msg "a raw declaration, but ~x0 is ~x1, not guard-verified"
                         name (symbol-class name w)))
                   (t nil))))
        (list digest problem (and (not problem) target)
              (and (not problem) guarded (fn-di-raw-creatorp name kvs w) t))))))

(defun fn-rdv-verdicts (entries w)
  (declare (xargs :mode :program))
  ; ENTRIES: the fn-interfaces table; one verdict per raw-declared entry
  (cond ((atom entries) nil)
        ((and (consp (car entries)) (fn-rdv-raw-declared-p (cdar entries)))
         (cons (cons (caar entries) (fn-rdv-judge (caar entries) (cdar entries) w))
               (fn-rdv-verdicts (cdr entries) w)))
        (t (fn-rdv-verdicts (cdr entries) w))))

(defun fn-rdv-refused-names (verdicts)
  (declare (xargs :mode :program))
  (cond ((atom verdicts) nil)
        ((cadr (cdar verdicts)) (cons (caar verdicts) (fn-rdv-refused-names (cdr verdicts))))
        (t (fn-rdv-refused-names (cdr verdicts)))))

(defun fn-rdv-verdict-okp (key val w)
  (declare (xargs :mode :program))
  ; the table's guard: KEY is a raw-declared entry of this world and VAL is
  ; this world's verdict on it
  (let ((entry (assoc-eq key (table-alist 'fn-interfaces w))))
    (and entry
         (fn-rdv-raw-declared-p (cdr entry))
         (equal val (fn-rdv-judge key (cdr entry) w)))))

(table fn-raw-dispatch-verdicts nil nil
       :guard (fn-rdv-verdict-okp key val world))

; -----------------------------------------------------------------------------
; Admission (logic mode: the host's decision, over data).

(defun fn-rdv-lookup (name verdicts)
  (declare (xargs :guard t))
  ; the first pair of VERDICTS whose key is NAME (assoc-equal, total)
  (cond ((atom verdicts) nil)
        ((and (consp (car verdicts)) (equal (caar verdicts) name)) (car verdicts))
        (t (fn-rdv-lookup name (cdr verdicts)))))

(defun fn-rdv-verdict-digest (v)
  (declare (xargs :guard t))
  (nth 0 (true-list-fix v)))

(defun fn-rdv-verdict-problem (v)
  (declare (xargs :guard t))
  (nth 1 (true-list-fix v)))

(defun fn-rdv-verdict-target (v)
  (declare (xargs :guard t))
  (nth 2 (true-list-fix v)))

(defun fn-rdv-verdict-creatorp (v)
  (declare (xargs :guard t))
  (nth 3 (true-list-fix v)))

(defun fn-rdv-admit (name digest verdicts)
  (declare (xargs :guard t))
  ; (mv PROBLEM TARGET CREATORP).  PROBLEM is nil only when VERDICTS judged
  ; NAME, over a row whose digest is DIGEST, and found nothing wrong.
  (let* ((hit (fn-rdv-lookup name verdicts))
         (v (cdr hit)))
    (cond ((not hit)
           (mv (msg "no raw-dispatch verdict for ~x0: the row was not judged in ~
                     the world this host was built from" name)
               nil nil))
          ((not (and (consp digest) (equal (fn-rdv-verdict-digest v) digest)))
           (mv (msg "the row of ~x0 is not the row its verdict judged (digest ~
                     ~x1, judged ~x2)" name digest (fn-rdv-verdict-digest v))
               nil nil))
          ((fn-rdv-verdict-problem v)
           (mv (msg "~x0 was judged refused: ~@1" name (fn-rdv-verdict-problem v))
               nil nil))
          (t (mv nil (fn-rdv-verdict-target v) (fn-rdv-verdict-creatorp v))))))

; KEYSTONE: what is admitted was judged, over exactly this row, clean.
(defthm fn-rdv-admits-only-a-clean-judged-row
  (implies (not (mv-nth 0 (fn-rdv-admit name digest verdicts)))
           (let ((v (cdr (fn-rdv-lookup name verdicts))))
             (and (fn-rdv-lookup name verdicts)
                  (consp digest)
                  (equal (fn-rdv-verdict-digest v) digest)
                  (not (fn-rdv-verdict-problem v)))))
  :rule-classes nil)

; ... and what it admits is the judged target and role, nothing the caller
; supplies.
(defthm fn-rdv-admit-returns-the-judged-target
  (implies (not (mv-nth 0 (fn-rdv-admit name digest verdicts)))
           (and (equal (mv-nth 1 (fn-rdv-admit name digest verdicts))
                       (fn-rdv-verdict-target (cdr (fn-rdv-lookup name verdicts))))
                (equal (mv-nth 2 (fn-rdv-admit name digest verdicts))
                       (fn-rdv-verdict-creatorp (cdr (fn-rdv-lookup name verdicts))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Carried tables (X3: every table the extracted closure and host read).
;
; The extractor's export ships each such table in the core's snapshot with a
; digest per row, computed HERE, in the world: fn-rdv-table-digests.  At
; load the host reads each manifest table as the core holds it and asks
; fn-rdv-carried-problem, which names the first table absent from the core,
; the first row missing, added or changed since its digest was taken.  A
; table the export dropped, or one edited after the digests, never reaches a
; later crash.  What it does not cover: a table dropped from the manifest and
; the snapshot together (the runtime's own table-alist refusal names it at
; its first read, tools/extract/clruntime.lisp).

(defun fn-rdv-row-key (e)
  (declare (xargs :guard t))
  (if (consp e) (car e) nil))

(defun fn-rdv-table-row-digest (table e)
  (declare (xargs :guard t))
  ; one table row, E = (KEY . VALUE), as (KEY . DIGEST)
  (cons (fn-rdv-row-key e) (fn-blake3 (fn-sdg-canon (list table e)))))

(defun fn-rdv-table-digests (table alist)
  (declare (xargs :guard t))
  (if (atom alist)
      nil
    (cons (fn-rdv-table-row-digest table (car alist))
          (fn-rdv-table-digests table (cdr alist)))))

(defun fn-rdv-table-problem (table carried alist)
  (declare (xargs :guard t))
  ; nil, or (:row-missing|:row-added|:row-changed TABLE KEY), or
  ; (:digests-malformed TABLE TAIL) for a digest list that is not a list: CARRIED is the
  ; digests the world took, ALIST the table as the core holds it
  (cond ((atom carried)
         (cond (carried (list :digests-malformed table carried))
               ((atom alist) nil)
               (t (list :row-added table (fn-rdv-row-key (car alist))))))
        ((atom alist) (list :row-missing table (fn-rdv-row-key (car carried))))
        ((not (equal (car carried) (fn-rdv-table-row-digest table (car alist))))
         (list :row-changed table (fn-rdv-row-key (car alist))))
        (t (fn-rdv-table-problem table (cdr carried) (cdr alist)))))

(defun fn-rdv-carried-problem (manifest held)
  (declare (xargs :guard t))
  ; MANIFEST: ((TABLE . DIGESTS) ...) as the export carried it; HELD:
  ; ((TABLE . ALIST) ...) for the tables the core holds.  nil, or the first
  ; problem, a table absent from HELD named as (:table-missing TABLE).
  (if (atom manifest)
      nil
    (let* ((m (car manifest))
           (table (fn-rdv-row-key m))
           (hit (fn-rdv-lookup table held)))
      (cond ((not hit) (list :table-missing table))
            ((fn-rdv-table-problem table (if (consp m) (cdr m) nil) (cdr hit)))
            (t (fn-rdv-carried-problem (cdr manifest) held))))))

; KEYSTONE: a table the check passes is exactly the table whose row digests
; the world took.
(defthm fn-rdv-table-verified-only-if-it-is-the-digested-table
  (implies (not (fn-rdv-table-problem table carried alist))
           (equal carried (fn-rdv-table-digests table alist)))
  :hints (("Goal" :induct (fn-rdv-table-problem table carried alist)))
  :rule-classes nil)

; ... and its premise is inhabited: a table passes against its own digests.
(defthm fn-rdv-table-problem-of-its-own-digests
  (not (fn-rdv-table-problem table (fn-rdv-table-digests table alist) alist))
  :hints (("Goal" :induct (fn-rdv-table-digests table alist))))
