; fn: the compaction verb's decisions over one link's window, not the whole
; history (lane compact-arena, 2026-09-27; PKT-686 item 2).
;
; Measured (planning/evidence/openbsd-release-fixes-2026-09-27.md section
; 3.1): `store compact' and `store reclaim' held up to 5.13 list copies of
; the history (sixteen octets per octet), where the open holds 1.61.  The
; host handed ACL2 every committed record as an octet list for every
; decision: `fn-cverb-decide' at the start and again before every link, and
; `fn-ccc-capture-link' for every link.  Both read only the history's length
; and ONE LINK'S WINDOW -- the records above the chain's coverage that fit
; one link (`fn-ccc-fit': at most *fn-cc-max-events* events and
; *fn-cc-max-octets* octets, and at least one event).
;
; Here the same decisions are stated over (USED LOWER WINDOW): USED the
; history's length, WINDOW the records the link takes.  Which records those
; are is ACL2's too: `fn-scw-window-count' over the records' LENGTHS (a list
; of naturals, one per record, sixteen octets each whatever the record's
; size) is `fn-ccc-fit' of the uncovered records
; (`fn-scw-window-count-is-fit').  So the host holds the records as it read
; them (octet vectors, one octet per octet), hands ACL2 their lengths, and
; converts only the window it names to octet lists: one link, at most 4 MiB
; and one record, not the history.
;
; KEYSTONES (the host-called subjects are the twins; host/checkpoint-host.lisp
; `fn-store-compact-decide-window' and `fn-store-checkpoint-chain-capture-window'
; call them, from host/native/checkpoint.lisp `fnn-compact-decide' and
; `fnn-pack-publish-generation'):
;   fn-cverb-decide-window-is-cverb-decide
;   fn-ccc-capture-link-window-is-capture-link
; each: when USED is (len RECORDS) and WINDOW is (fn-scw-window RECORDS LOWER),
; the twin's answer is the list decision's, so every theorem of
; books/store-compact-verb.lisp and books/checkpoint-pack-chain.lisp about
; `fn-cverb-decide' and `fn-ccc-capture-link' (the capture succeeds, the pack
; fits the disk, the chain reconstructs the history, the publication crash
; walks the old or new chain) holds of what the host now calls.
;
; The relation the host establishes: it passes (fn-scw-lens RECORDS) as the
; lengths of the octet vectors it holds (`length' of each), and as WINDOW the
; octet lists of the COUNT records from LOWER that `fn-scw-window-count'
; named.  Both are the host's reading of the same records the decision
; would otherwise receive whole; the theorems state it as their hypotheses.
(in-package "ACL2")
(include-book "store-compact-verb")

; -----------------------------------------------------------------------------
; The fit over lengths.

(defun fn-scw-lens (records)
  (declare (xargs :guard t))
  (if (consp records)
      (cons (len (car records)) (fn-scw-lens (cdr records)))
    nil))

(defun fn-scw-fit-aux (lens size octets count)
  (declare (xargs :guard (and (natp size) (natp count))
                  :verify-guards nil))
  (if (or (not (consp lens)) (zp count))
      0
    (let ((next (+ size (nfix (car lens)) 5)))
      (if (< octets next) 0
        (+ 1 (fn-scw-fit-aux (cdr lens) next octets (1- count)))))))

(defthm fn-scw-fit-aux-of-lens
  (equal (fn-scw-fit-aux (fn-scw-lens events) size octets count)
         (fn-ccc-fit-aux events size octets count))
  :hints (("Goal" :induct (fn-ccc-fit-aux events size octets count)
           :in-theory (enable fn-ccc-fit-aux))))

(defthm fn-scw-len-of-lens
  (equal (len (fn-scw-lens records)) (len records)))

(defthm fn-scw-nthcdr-of-lens
  (equal (nthcdr n (fn-scw-lens records))
         (fn-scw-lens (nthcdr n records))))

; How many uncovered records the next link takes: `fn-ccc-fit' of the records
; above LOWER, read from their lengths.  The host-called subject.
(defun fn-scw-window-count (lens lower)
  (declare (xargs :guard t :verify-guards nil))
  (let ((rest (nthcdr (nfix lower) lens)))
    (min (len rest)
         (max 1 (fn-scw-fit-aux rest 32 *fn-cc-max-octets* *fn-cc-max-events*)))))

(defthm fn-scw-window-count-is-fit
  (equal (fn-scw-window-count (fn-scw-lens records) lower)
         (fn-ccc-fit (nthcdr (nfix lower) records)))
  :hints (("Goal" :in-theory (e/d (fn-ccc-fit) (fn-scw-lens)))))

; The window the link takes.
(defun fn-scw-window (records lower)
  (declare (xargs :guard t :verify-guards nil))
  (let ((rest (nthcdr (nfix lower) records)))
    (take (fn-ccc-fit rest) rest)))

; -----------------------------------------------------------------------------
; The decision (store-compact-verb.lisp `fn-cverb-decide') over the window.

(defun fn-cverb-link-octets-window (window)
  (declare (xargs :guard t :verify-guards nil))
  (+ *fn-ccc-link-header-octets*
     (fn-cc-event-octets-size window)
     *fn-frame-trailer-octets*))

(defun fn-cverb-decide-window (profile used lower window names generations selected
                                       disk-free)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((used (nfix used))
         (reclaim (fn-bs-pack-reclaim-plan names (fn-bs-profile-max-transactions profile)
                                           lower))
         (older (fn-cverb-older-count generations selected)))
    (cond ((not (fn-bs-profile-admittedp profile)) (list :refused :profile))
          ((or (not (natp lower)) (< used lower) (equal reclaim :invalid))
           (list :refused :observation))
          ((equal lower used)
           (cond ((zp used) (list :refused :empty-history))
                 ((and (atom reclaim) (zp older)) (list :refused :already-compact))
                 (t (list :compact *fn-cverb-resume-steps*))))
          ((not (fn-cverb-disk-admitsp disk-free (fn-cverb-link-octets-window window)))
           (list :refused :temporary-space))
          (t (list :compact *fn-cverb-pack-steps*)))))

(defthm fn-cverb-link-octets-of-window
  (equal (fn-cverb-link-octets-window (fn-scw-window records lower))
         (fn-cverb-link-octets records lower))
  :hints (("Goal" :in-theory (enable fn-cverb-link-octets))))

(local (defthm fn-scw-nfix-len (equal (nfix (len x)) (len x))))

; KEYSTONE.  Over the history's length and the window, the decision is the
; decision over the whole history.
(defthm fn-cverb-decide-window-is-cverb-decide
  (implies (and (equal used (len records))
                (equal window (fn-scw-window records lower)))
           (equal (fn-cverb-decide-window profile used lower window names generations
                                          selected disk-free)
                  (fn-cverb-decide profile records lower names generations selected
                                   disk-free)))
  :hints (("Goal" :in-theory (union-theories '(fn-cverb-decide fn-cverb-decide-window
                                               fn-cverb-link-octets-of-window
                                               fn-scw-nfix-len)
                                             (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The capture (checkpoint-pack-chain.lisp `fn-ccc-capture-link') over the
; window.

(defun fn-ccc-capture-link-window (used window lower lower-frontier pred-generation
                                        pred-digest)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((k (len window))
         (link (fn-ccc-make (nfix lower) (+ (nfix lower) k) lower-frontier
                            (if (consp window)
                                (+ 1 (nfix (fn-ccc-event-txid (car (last window)))))
                              0)
                            (if (zp lower) 0 pred-generation)
                            (if (zp lower) nil pred-digest)
                            (true-list-fix window))))
    (cond ((and (natp lower) (< lower (nfix used)) (fn-ccc-linkp link))
           (list :ok link))
          ((equal lower (nfix used)) (list :nothing-uncovered lower))
          (t (list :error :history)))))

(local
 (defthm fn-scw-len-of-take
   (equal (len (take n l)) (nfix n))))

(local
 (defthm fn-scw-len-of-take-fit
   (equal (len (take (fn-ccc-fit rest) rest))
          (fn-ccc-fit rest))
   :hints (("Goal" :in-theory (enable fn-ccc-fit)))))

; KEYSTONE.  Over the history's length and the window, the captured link is
; the link captured over the whole history.
(defthm fn-ccc-capture-link-window-is-capture-link
  (implies (and (equal used (len records))
                (equal window (fn-scw-window records lower)))
           (equal (fn-ccc-capture-link-window used window lower lower-frontier
                                              pred-generation pred-digest)
                  (fn-ccc-capture-link records lower lower-frontier pred-generation
                                       pred-digest)))
  :hints (("Goal" :in-theory (e/d (fn-ccc-capture-link fn-scw-window)
                                  (fn-ccc-make fn-ccc-linkp fn-ccc-event-txid
                                   fn-ccc-fit)))))
