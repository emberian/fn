; fn: the committed-history marker as a byte program (crash model v2).
;
; P-MARKER is host/native/io.lisp `fnn-mark-committed', which every commit
; site runs after its record's transaction-directory barrier (fnn-publish
; returned :durable) and before fnn-finish (the acknowledgement): the
; FNSM kind-3 frame of books/store-history-marker.lisp `fn-hm-after-commit'
; is staged in :staging under a `.stage-' name (the recovery sweep owns a
; stage a death leaves there, books/store-sweep.lisp), fenced, renamed onto
; committed-history.json in the root, and the root directory fenced.  It is
; P-PROFILE's shape (books/byte-store-profile-program.lisp) onto another
; root name, and like it has no kernel observation: the file kernel has no
; marker, so the program changes no fn-sf state.  A :cut follows every
; durable syscall; the cut names are fn-hm-marker-cut-names, each an
; `fnn-at' site of the developer image (tests/campaign/native_cuts.py
; POST_CUTS, between fn-bs-record-program and fn-bs-finish-program).
;
; This book gives the program and its crash keystone over the marker name;
; books/byte-store-k0-marker.lisp carries K0 over its cuts.
(in-package "ACL2")
(include-book "byte-store-programs")
(include-book "store-history-marker")
(local (include-book "byte-store-invariants"))

(defconst *fn-bs-history-marker-name* "committed-history.json")

(defun fn-bs-marker-program (stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)
        (list :cut "marker-created")
        (list :write-all :staging stage octets)
        (list :cut "marker-written")
        (list :fsync-file :staging stage)
        (list :cut "marker-staged-durable")
        (list :rename :staging stage :root *fn-bs-history-marker-name*)
        (list :cut "marker-replaced")
        (list :fsync-dir :root)
        (list :cut "marker-durable")))
; Any OS error is uncertain at every step (fnn-indeterminate): the record is
; durable, the transaction is never acknowledged, and the next open decides
; from whichever marker the root holds.  The error arms are covered only
; through their crash images (the run is the successful one, as for
; P-PROFILE).

; Program discipline D1 to D3 (byte-store-programs, section 2.4), on a
; ground instance.
(defconst *fn-bs-p-marker* (fn-bs-marker-program ".stage-marker-1" '(1)))
(assert-event (fn-bs-step-listp *fn-bs-p-marker*))
(assert-event (fn-bs-links-only-fencedp *fn-bs-p-marker*))
(assert-event (fn-bs-never-overwrites-authorityp *fn-bs-p-marker*))
(assert-event (fn-bs-fences-authority-dirsp *fn-bs-p-marker*))

; The program is the decision book's shape and its cut table: the same five
; step kinds in the same order, and the cut names the developer selector
; accepts (fn-hm-marker-cut-names, host/native/io.lisp fnn-post-test-fault).
(defun fn-bs-program-cut-names (steps)
  (declare (xargs :guard t))
  (cond ((atom steps) nil)
        ((and (consp (car steps)) (eq (car (car steps)) :cut)
              (consp (cdr (car steps))))
         (cons (cadr (car steps)) (fn-bs-program-cut-names (cdr steps))))
        (t (fn-bs-program-cut-names (cdr steps)))))
(defun fn-bs-program-step-kinds (steps)
  (declare (xargs :guard t))
  (if (atom steps) nil
    (cons (and (consp (car steps)) (car (car steps)))
          (fn-bs-program-step-kinds (cdr steps)))))
(assert-event (equal (fn-bs-program-cut-names *fn-bs-p-marker*)
                     (fn-hm-marker-cut-names)))
; *fn-hm-marker-program* spells write-all as :write and its cuts as keywords.
(defun fn-bs-hm-step-kinds (steps)
  (declare (xargs :guard t))
  (if (atom steps) nil
    (cons (let ((k (and (consp (car steps)) (car (car steps)))))
            (if (eq k :write) :write-all k))
          (fn-bs-hm-step-kinds (cdr steps)))))
(defun fn-bs-hm-cut-strings (steps)
  (declare (xargs :guard t))
  (cond ((atom steps) nil)
        ((and (consp (car steps)) (eq (car (car steps)) :cut)
              (consp (cdr (car steps))) (symbolp (cadr (car steps))))
         (cons (string-downcase (symbol-name (cadr (car steps))))
               (fn-bs-hm-cut-strings (cdr steps))))
        (t (fn-bs-hm-cut-strings (cdr steps)))))
(assert-event (equal (fn-bs-program-step-kinds *fn-bs-p-marker*)
                     (fn-bs-hm-step-kinds *fn-hm-marker-program*)))
(assert-event (equal (fn-bs-hm-cut-strings *fn-hm-marker-program*)
                     (fn-hm-marker-cut-names)))

; What the open reads (host/native/io.lisp fnn-history-marker-observation):
; (:absent) when the root names no file there, else (:present OCTETS).
(defun fn-bs-hm-observation (img)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ino (fn-bs-durable-entry img :root *fn-bs-history-marker-name*)))
    (if (fn-bs-inop ino)
        (list :present (fn-bs-durable-content img ino))
      (list :absent))))

; The precondition, weaker than P-PROFILE's quiet store: the root directory
; has no pending entry operation, the marker name is absent or names an
; allocated, fenced inode, and the stage name is free.  Other directories
; may carry pending work (a related state after the record program).
(defun fn-bs-marker-inputp (bs stage)
  (declare (xargs :guard t :verify-guards nil))
  (let ((old (fn-bs-durable-entry bs :root *fn-bs-history-marker-name*)))
    (and (stringp stage)
         (natp (fn-bs-next-ino bs))
         (not (fn-bs-lookup bs :staging stage))
         (null (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
         (or (not (fn-bs-inop old))
             (and (< old (fn-bs-next-ino bs))
                  (fn-bs-fencedp bs old))))))

; -----------------------------------------------------------------------------
; The states of the successful run.  B1 after the create, B2 after the write,
; B3 after the stage's fence, B4 after the rename, B5 after the root barrier;
; each :cut repeats the state before it.

(defun fn-bs-marker-b1 (bs stage)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (cons (cons (fn-bs-next-ino bs) nil) (fn-bs-inodes bs))
              (fn-bs-dirs bs)
              (append (fn-bs-pending bs) (list (list :set-entry :staging stage (fn-bs-next-ino bs))))
              (1+ (fn-bs-next-ino bs))))
(defun fn-bs-marker-b2 (bs stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (cons (cons (fn-bs-next-ino bs) nil) (fn-bs-inodes bs))
              (fn-bs-dirs bs)
              (append (fn-bs-pending bs) (list (list :set-entry :staging stage (fn-bs-next-ino bs))
                                               (list :write (fn-bs-next-ino bs) 0 octets)))
              (1+ (fn-bs-next-ino bs))))
(defun fn-bs-marker-b3 (bs stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (cons (cons (fn-bs-next-ino bs) octets) (fn-bs-inodes bs))
              (fn-bs-dirs bs)
              (append (fn-bs-pending bs) (list (list :set-entry :staging stage (fn-bs-next-ino bs))))
              (1+ (fn-bs-next-ino bs))))
(defun fn-bs-marker-b4 (bs stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (cons (cons (fn-bs-next-ino bs) octets) (fn-bs-inodes bs))
              (fn-bs-dirs bs)
              (append (fn-bs-pending bs) (list (list :set-entry :staging stage (fn-bs-next-ino bs))
                                               (list :set-entry :root *fn-bs-history-marker-name*
                                                     (fn-bs-next-ino bs))
                                               (list :del-entry :staging stage)))
              (1+ (fn-bs-next-ino bs))))
(defun fn-bs-marker-b5 (bs stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (cons (cons (fn-bs-next-ino bs) octets) (fn-bs-inodes bs))
              (fn-bs-put-assoc :root
                               (fn-bs-put-assoc *fn-bs-history-marker-name* (fn-bs-next-ino bs)
                                                (cdr (assoc-equal :root (fn-bs-dirs bs))))
                               (fn-bs-dirs bs))
              (append (fn-bs-pending bs) (list (list :set-entry :staging stage (fn-bs-next-ino bs))
                                               (list :del-entry :staging stage)))
              (1+ (fn-bs-next-ino bs))))

; Reading a name through the view is the entry after the pending list, and a
; freshly allocated inode has no pending write.
(encapsulate ()
(local (in-theory (enable fn-bs-invariants-vocabulary)))
(defthm fn-bs-marker-lookup-is-entry-after
  (implies (and dir name)
           (equal (fn-bs-lookup s dir name)
                  (fn-bs-entry-after (fn-bs-pending s) (fn-bs-durable-entry s dir name) dir name)))
  :hints (("Goal" :use ((:instance fn-bs-apply-entries-entry-is-entry-after
                                   (dirs (fn-bs-dirs s)) (ops (fn-bs-pending s))))
           :in-theory (e/d (fn-bs-lookup fn-bs-view fn-bs-durable-entry
                            fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-apply-entries-entry-is-entry-after fn-bs-apply-ops
                            fn-bs-apply-entries fn-bs-entry-after)))))
(defthm fn-bs-marker-fresh-ino-has-no-writes
  (implies (and (fn-bs-writes-knownp ops inodes) (fn-bs-keys-belowp inodes n))
           (not (fn-bs-ops-for-ino ops n)))
  :hints (("Goal" :induct (fn-bs-writes-knownp ops inodes)
           :in-theory (enable fn-bs-writes-knownp fn-bs-ops-for-ino))
          ("Subgoal *1/2" :use ((:instance fn-bs-keys-belowp-excludes-bound
                                           (x inodes) (n n))))))
)

(encapsulate ()
(local (in-theory (enable fn-bs-invariants-vocabulary)))
(local (defthm l-take-own (implies (true-listp x) (equal (fn-bs-take (len x) x) x))))
(local (defthm l-len-consp (implies (consp x) (not (equal (len x) 0)))))
(local (defthm l-nthcdr-nil (equal (nthcdr n nil) nil)))
(local (defthm l-app-nil (implies (true-listp x) (equal (append x nil) x))))
(local (defthm l-octets-true (implies (fn-cbor-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local (defthm l-not-for-ino-id
  (implies (not (fn-bs-ops-for-ino ops n)) (equal (fn-bs-ops-not-for-ino ops n) (true-list-fix ops)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-ino fn-bs-ops-not-for-ino)))))
(local (defthm l-not-for-dir-id
  (implies (not (fn-bs-ops-for-dir ops d)) (equal (fn-bs-ops-not-for-dir ops d) (true-list-fix ops)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir fn-bs-ops-not-for-dir)))))
(local (defthm l-not-for-ino-app
  (equal (fn-bs-ops-not-for-ino (append a b) n) (append (fn-bs-ops-not-for-ino a n) (fn-bs-ops-not-for-ino b n)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-not-for-ino)))))
(local (defthm l-not-for-dir-app
  (equal (fn-bs-ops-not-for-dir (append a b) n) (append (fn-bs-ops-not-for-dir a n) (fn-bs-ops-not-for-dir b n)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-not-for-dir)))))
(local (defthm l-statep-facts
  (implies (fn-bs-statep bs)
           (and (true-listp (fn-bs-pending bs))
                (natp (fn-bs-next-ino bs))
                (not (fn-bs-ops-for-ino (fn-bs-pending bs) (fn-bs-next-ino bs)))))
  :hints (("Goal" :in-theory (enable fn-bs-statep)
           :use ((:instance fn-bs-marker-fresh-ino-has-no-writes (ops (fn-bs-pending bs))
                  (inodes (fn-bs-inodes bs)) (n (fn-bs-next-ino bs))))))))
(defthm fn-bs-marker-run-shape
  (implies (and (fn-bs-statep bs) (stringp stage) (not (fn-bs-lookup bs :staging stage))
                (null (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                (fn-cbor-octet-listp octets) (consp octets))
           (equal (fn-bs-run bs ks (fn-bs-marker-program stage octets) nil groups capacity)
                  (list (cons (fn-bs-marker-b1 bs stage) ks) (cons (fn-bs-marker-b1 bs stage) ks)
                        (cons (fn-bs-marker-b2 bs stage octets) ks) (cons (fn-bs-marker-b2 bs stage octets) ks)
                        (cons (fn-bs-marker-b3 bs stage octets) ks) (cons (fn-bs-marker-b3 bs stage octets) ks)
                        (cons (fn-bs-marker-b4 bs stage octets) ks) (cons (fn-bs-marker-b4 bs stage octets) ks)
                        (cons (fn-bs-marker-b5 bs stage octets) ks) (cons (fn-bs-marker-b5 bs stage octets) ks))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-marker-program fn-bs-step
                            fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fsync-dir fn-bs-rename fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-durable-entry
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-marker-b5
                            fn-bs-ops-for-ino fn-bs-ops-for-dir fn-bs-splice fn-bs-entry-after)
                           (fn-bs-statep fn-bs-lookup)))))
)

; -----------------------------------------------------------------------------
; The marker in every crash image: the old observation before the rename,
; old or new between the rename and the root barrier, new after it.

(encapsulate ()
(local (in-theory (enable fn-bs-invariants-vocabulary)))
(local (defthm l-name-quiet-of-dir-quiet
  (implies (not (fn-bs-ops-for-dir ops dir)) (not (fn-bs-ops-for-name ops dir name)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir fn-bs-ops-for-name)))))
(local (defthm l-for-name-app
  (equal (fn-bs-ops-for-name (append a b) dir name)
         (append (fn-bs-ops-for-name a dir name) (fn-bs-ops-for-name b dir name)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-name)))))
(local (defthm l-statep-fresh
  (implies (fn-bs-statep bs)
           (not (fn-bs-ops-for-ino (fn-bs-pending bs) (fn-bs-next-ino bs))))
  :hints (("Goal" :in-theory (enable fn-bs-statep)
           :use ((:instance fn-bs-marker-fresh-ino-has-no-writes (ops (fn-bs-pending bs))
                  (inodes (fn-bs-inodes bs)) (n (fn-bs-next-ino bs))))))))
(local (defthm l-entry-of-crash
  (let ((e (fn-bs-durable-entry (fn-bs-crash s choices) :root *fn-bs-history-marker-name*)))
    (member-equal e (fn-bs-entry-outcomes
                     (fn-bs-ops-for-name (fn-bs-pending s) :root *fn-bs-history-marker-name*)
                     (fn-bs-durable-entry s :root *fn-bs-history-marker-name*))))
  :hints (("Goal" :use ((:instance fn-bs-crash-with-choices-entry-is-old-or-a-pending-target
                                   (dir :root) (name *fn-bs-history-marker-name*)))
           :in-theory (disable fn-bs-crash-with-choices-entry-is-old-or-a-pending-target fn-bs-crash)))))
(local (defthm l-member-single (iff (member-equal e (list x)) (equal e x))))
(local (defthm l-member-pair (iff (member-equal e (list x y)) (or (equal e x) (equal e y)))))
(defthm fn-bs-marker-crash-before-rename-is-old
  (implies (and (fn-bs-statep bs) (fn-bs-marker-inputp bs stage)
                (member-equal b (list (fn-bs-marker-b1 bs stage) (fn-bs-marker-b2 bs stage octets)
                                      (fn-bs-marker-b3 bs stage octets))))
           (equal (fn-bs-hm-observation (fn-bs-crash b choices))
                  (fn-bs-hm-observation bs)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance l-entry-of-crash (s b))
                 (:instance fn-bs-crash-with-choices-keeps-fenced-content
                  (s b) (ino (fn-bs-durable-entry bs :root *fn-bs-history-marker-name*))))
           :in-theory (e/d (fn-bs-marker-inputp fn-bs-hm-observation fn-bs-fencedp
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3
                            fn-bs-durable-entry fn-bs-durable-content fn-bs-ops-for-ino
                            fn-bs-ops-for-name fn-bs-entry-outcomes)
                           (l-entry-of-crash fn-bs-crash-with-choices-keeps-fenced-content
                            fn-bs-crash fn-bs-statep fn-bs-lookup)))))
(defthm fn-bs-marker-crash-at-rename-is-old-or-new
  (implies (and (fn-bs-statep bs) (fn-bs-marker-inputp bs stage))
           (member-equal (fn-bs-hm-observation (fn-bs-crash (fn-bs-marker-b4 bs stage octets) choices))
                         (list (fn-bs-hm-observation bs) (list :present octets))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance l-entry-of-crash (s (fn-bs-marker-b4 bs stage octets)))
                 (:instance fn-bs-crash-with-choices-keeps-fenced-content
                  (s (fn-bs-marker-b4 bs stage octets))
                  (ino (fn-bs-durable-entry bs :root *fn-bs-history-marker-name*)))
                 (:instance fn-bs-crash-with-choices-keeps-fenced-content
                  (s (fn-bs-marker-b4 bs stage octets)) (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-marker-inputp fn-bs-hm-observation fn-bs-fencedp
                            fn-bs-marker-b4
                            fn-bs-durable-entry fn-bs-durable-content fn-bs-ops-for-ino
                            fn-bs-ops-for-name fn-bs-entry-outcomes)
                           (l-entry-of-crash fn-bs-crash-with-choices-keeps-fenced-content
                            fn-bs-crash fn-bs-statep fn-bs-lookup)))))
(defthm fn-bs-marker-crash-after-barrier-is-new
  (implies (and (fn-bs-statep bs) (fn-bs-marker-inputp bs stage))
           (equal (fn-bs-hm-observation (fn-bs-crash (fn-bs-marker-b5 bs stage octets) choices))
                  (list :present octets)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance l-entry-of-crash (s (fn-bs-marker-b5 bs stage octets)))
                 (:instance fn-bs-crash-with-choices-keeps-fenced-content
                  (s (fn-bs-marker-b5 bs stage octets)) (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-marker-inputp fn-bs-hm-observation fn-bs-fencedp
                            fn-bs-marker-b5
                            fn-bs-durable-entry fn-bs-durable-content fn-bs-ops-for-ino
                            fn-bs-ops-for-name fn-bs-entry-outcomes)
                           (l-entry-of-crash fn-bs-crash-with-choices-keeps-fenced-content
                            fn-bs-crash fn-bs-statep fn-bs-lookup)))))
)

(defthm fn-bs-marker-inputp-facts
  (implies (fn-bs-marker-inputp bs stage)
           (and (stringp stage) (not (fn-bs-lookup bs :staging stage))
                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory '(fn-bs-marker-inputp))))
(defconst *fn-bs-marker-pair-cuts*
  '(:marker-created :marker-created :marker-written :marker-written
    :marker-staged-durable :marker-staged-durable
    :marker-replaced :marker-replaced :marker-durable :marker-durable))
(defthm fn-bs-marker-crash-is-the-history-table
  (implies (and (fn-bs-statep bs) (fn-bs-marker-inputp bs stage)
                (fn-cbor-octet-listp octets) (consp octets)
                (natp k) (< k 10))
           (let* ((obs (fn-bs-hm-observation
                        (fn-bs-crash (car (nth k (fn-bs-run bs ks (fn-bs-marker-program stage octets)
                                                            nil groups capacity)))
                                     choices)))
                  (new (list :present octets)))
             (equal obs (fn-hm-crash-image (nth k *fn-bs-marker-pair-cuts*) (equal obs new)
                                           (fn-bs-hm-observation bs) new))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3) (equal k 4)
                   (equal k 5) (equal k 6) (equal k 7) (equal k 8) (equal k 9))
           :use ((:instance fn-bs-marker-crash-at-rename-is-old-or-new)
                 (:instance fn-bs-marker-crash-before-rename-is-old (b (fn-bs-marker-b1 bs stage)))
                 (:instance fn-bs-marker-crash-before-rename-is-old (b (fn-bs-marker-b2 bs stage octets)))
                 (:instance fn-bs-marker-crash-before-rename-is-old (b (fn-bs-marker-b3 bs stage octets)))
                 fn-bs-marker-crash-after-barrier-is-new)
           :in-theory (e/d ()
                           (fn-bs-marker-inputp fn-bs-marker-lookup-is-entry-after fn-bs-marker-crash-before-rename-is-old fn-bs-marker-crash-after-barrier-is-new fn-bs-marker-crash-at-rename-is-old-or-new
                            fn-bs-hm-observation fn-bs-crash fn-bs-statep fn-bs-lookup
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3
                            fn-bs-marker-b4 fn-bs-marker-b5 fn-bs-marker-program fn-bs-run)))))
(defthm fn-bs-marker-program-crash-is-old-or-new
  (implies (and (fn-bs-statep bs) (fn-bs-marker-inputp bs stage)
                (fn-cbor-octet-listp octets) (consp octets)
                (member-equal p (fn-bs-run bs ks (fn-bs-marker-program stage octets)
                                           nil groups capacity)))
           (member-equal (fn-bs-hm-observation (fn-bs-crash (car p) choices))
                         (list (fn-bs-hm-observation bs) (list :present octets))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-marker-crash-at-rename-is-old-or-new)
                 (:instance fn-bs-marker-crash-before-rename-is-old (b (fn-bs-marker-b1 bs stage)))
                 (:instance fn-bs-marker-crash-before-rename-is-old (b (fn-bs-marker-b2 bs stage octets)))
                 (:instance fn-bs-marker-crash-before-rename-is-old (b (fn-bs-marker-b3 bs stage octets)))
                 fn-bs-marker-crash-after-barrier-is-new)
           :in-theory (e/d ()
                           (fn-bs-marker-inputp fn-bs-marker-lookup-is-entry-after fn-bs-marker-crash-before-rename-is-old fn-bs-marker-crash-after-barrier-is-new fn-bs-marker-crash-at-rename-is-old-or-new
                            fn-bs-hm-observation fn-bs-crash fn-bs-statep fn-bs-lookup
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3
                            fn-bs-marker-b4 fn-bs-marker-b5 fn-bs-marker-program fn-bs-run)))))

; -----------------------------------------------------------------------------
; The open's verdict.  With the program's octets the frame the host writes
; for the durable record SEQUENCE (fn-hm-after-commit), the marker every crash
; image holds is exactly the history step (:commit CUT CHOICE) of
; books/store-history-marker.lisp at the pair's cut, so the rename-atomicity
; table fn-hm-crash-image is the byte model's, not an assumption.  The open
; after recovery therefore admits, and keeps admitting under every later
; history of burns, uncertain publications and commits crashed at any cut
; (fn-hm-run-keeps-every-open-admitted).

(defthm fn-bs-marker-after-commit-is-a-frame
  (implies (and (natp sequence) (< sequence *fn-cbor-max-uint*))
           (and (fn-cbor-octet-listp (fn-hm-after-commit sequence))
                (consp (fn-hm-after-commit sequence))))
  :hints (("Goal" :use ((:instance fn-hm-encode-octet-listp (n (1+ sequence))))
           :in-theory (e/d (fn-hm-after-commit fn-hm-countp fn-hm-encode fn-frame-seal
                            fn-frame-encode fn-frame-protected fn-frame-header)
                           (fn-hm-encode-octet-listp)))))
(defthm fn-bs-marker-crash-is-a-history-step
  (implies (and (fn-bs-statep bs) (fn-bs-marker-inputp bs stage)
                (natp sequence) (< sequence *fn-cbor-max-uint*)
                (natp k) (< k 10))
           (let ((obs (fn-bs-hm-observation
                       (fn-bs-crash (car (nth k (fn-bs-run bs ks
                                                           (fn-bs-marker-program
                                                            stage (fn-hm-after-commit sequence))
                                                           nil groups capacity)))
                                    choices))))
             (equal (cons (1+ sequence) obs)
                    (fn-hm-step (list :commit (nth k *fn-bs-marker-pair-cuts*)
                                      (equal obs (list :present (fn-hm-after-commit sequence))))
                                (cons sequence (fn-bs-hm-observation bs))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-marker-crash-is-the-history-table
                            (octets (fn-hm-after-commit sequence)))
                 fn-bs-marker-after-commit-is-a-frame)
           :in-theory (e/d (fn-hm-step)
                           (fn-bs-marker-crash-is-the-history-table fn-bs-marker-after-commit-is-a-frame
                            fn-hm-after-commit fn-hm-crash-image
                            fn-bs-hm-observation fn-bs-crash fn-bs-run fn-bs-marker-program
                            fn-bs-marker-inputp fn-bs-statep)))))
(defthm fn-bs-marker-crash-open-stays-admitted
  (let ((obs (fn-bs-hm-observation
              (fn-bs-crash (car (nth k (fn-bs-run bs ks
                                                  (fn-bs-marker-program
                                                   stage (fn-hm-after-commit sequence))
                                                  nil groups capacity)))
                           choices))))
    (implies (and (fn-bs-statep bs) (fn-bs-marker-inputp bs stage)
                  (fn-hm-admittedp (cons sequence (fn-bs-hm-observation bs)))
                  (natp sequence)
                  (<= (+ sequence 1 (len post)) *fn-cbor-max-uint*)
                  (natp k) (< k 10))
             (fn-hm-admittedp (fn-hm-run post (cons (1+ sequence) obs)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-marker-crash-is-a-history-step
                 (:instance fn-hm-step-preserves-admitted
                  (st (cons sequence (fn-bs-hm-observation bs)))
                  (op (list :commit (nth k *fn-bs-marker-pair-cuts*)
                            (equal (fn-bs-hm-observation
                                    (fn-bs-crash (car (nth k (fn-bs-run bs ks
                                                                        (fn-bs-marker-program
                                                                         stage (fn-hm-after-commit sequence))
                                                                        nil groups capacity)))
                                                 choices))
                                   (list :present (fn-hm-after-commit sequence))))))
                 (:instance fn-hm-run-keeps-every-open-admitted
                  (ops post)
                  (st (cons (1+ sequence)
                            (fn-bs-hm-observation
                             (fn-bs-crash (car (nth k (fn-bs-run bs ks
                                                                 (fn-bs-marker-program
                                                                  stage (fn-hm-after-commit sequence))
                                                                 nil groups capacity)))
                                          choices))))))
           :in-theory (disable fn-bs-marker-crash-is-a-history-step fn-hm-step-preserves-admitted
                               fn-hm-run-keeps-every-open-admitted
                               fn-hm-after-commit fn-hm-step fn-hm-run fn-hm-admittedp
                               fn-bs-hm-observation fn-bs-crash fn-bs-run fn-bs-marker-program
                               fn-bs-marker-inputp fn-bs-statep))))

(in-theory (disable fn-bs-marker-program fn-bs-marker-inputp fn-bs-hm-observation
                    fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3
                    fn-bs-marker-b4 fn-bs-marker-b5 fn-bs-marker-lookup-is-entry-after))
