; Bounded metadata traversal for the RFC 9172 target graph.
; Inputs are already parsed bindings and an immutable bundle view. Their
; shape/number/kind/context and byte-binding relations are CARRIED premises,
; not whole-bundle revalidation performed by this served-path candidate.
; No actual BP provider/caller is installed by this book.
(in-package "ACL2")
(include-book "bpsec-target")

(defun fn-bps-target-inputp (bundle bindings opaque limits)
  (declare (xargs :guard t))
  (and (fn-bpb-bundlep bundle) (fn-bps-limitsp limits)
       (fn-bps-bindingsp bindings) (fn-bps-uint-listp opaque)
       (no-duplicatesp-equal opaque)
       (no-duplicatesp-equal (fn-bps-binding-numbers bindings))
       (fn-bps-bindings-kind-matchp bundle bindings)
       (fn-bps-binding-known-contextp bindings)))

(defun fn-bps-target-start (bundle bindings opaque limits)
  (declare (xargs :guard (fn-bps-target-inputp bundle bindings opaque limits)))
  (list (cons :status :more) (cons :reason nil) (cons :stage :count-bindings)
        (cons :bundle bundle) (cons :bindings bindings) (cons :opaque opaque)
        (cons :limits limits) (cons :todo bindings) (cons :targets nil)
        (cons :count 0) (cons :bound nil) (cons :pairs nil) (cons :encrypted nil)
        (cons :current nil) (cons :security-block nil) (cons :target 0)
        (cons :target-block nil) (cons :scan nil) (cons :needle nil)
        (cons :search-mode nil) (cons :hit nil) (cons :miss nil)))

(defun fn-bps-graph-stage (stage cursor)
  (declare (xargs :guard t))
  (fn-bps-put :stage stage cursor))

(defun fn-bps-graph-count (cursor)
  (declare (xargs :guard t))
  (let ((count (1+ (nfix (fn-bps-get :count cursor)))))
    (if (< (nfix (fn-bps-field 6 (fn-bps-get :limits cursor))) count)
        (fn-bps-stop :refused :graph-metadata-limit cursor)
      (fn-bps-put :count count cursor))))

(defun fn-bps-graph-action (action cursor)
  (declare (xargs :guard t))
  (if (consp action) (fn-bps-stop (car action) (fn-bps-field 1 action) cursor)
    (fn-bps-graph-stage action cursor)))

(defun fn-bps-graph-search (needle values mode hit miss cursor)
  (declare (xargs :guard t))
  (fn-bps-graph-stage :search
   (fn-bps-put :needle needle (fn-bps-put :scan values (fn-bps-put :search-mode mode
    (fn-bps-put :hit hit (fn-bps-put :miss miss cursor)))))))

(defun fn-bps-graph-search-matchp (needle value mode)
  (declare (xargs :guard t))
  (if (eq mode :bcb-target)
      (and (equal (fn-bps-field 0 value) 12) (equal needle (fn-bps-field 1 value)))
    (equal needle value)))

(defun fn-bps-graph-target-reason (cursor)
  (declare (xargs :guard t))
  (let* ((binding (fn-bps-get :current cursor))
         (asb (if (consp binding) (cdr binding) nil))
         (kind (fn-bps-field 1 asb)) (number (fn-bps-field 0 binding))
         (target (fn-bps-get :target cursor)) (block (fn-bps-get :target-block cursor))
         (type (if (equal target 0) 0 (fn-bpb-block-type block)))
         (flags (nfix (fn-bpb-block-flags (fn-bps-get :security-block cursor)))))
    (cond ((and (not (equal target 0)) (not (consp block))) :missing-target)
          ((and (equal kind 11) (member-equal type '(11 12))) :bib-security-target)
          ((and (equal kind 12) (or (equal target 0) (equal type 12) (equal target number))) :bcb-forbidden-target)
          ((and (equal kind 12) (equal target 1)
                (or (equal (logand flags 1) 0) (not (equal (logand flags 16) 0)))) :payload-bcb-flags)
          (t nil))))

; One unit performs one metadata transition, one lookup comparison, or one
; member probe. No branch invokes LEN, MEMBER or the reference target check.
(defun fn-bps-target-unit (cursor)
  (declare (xargs :guard t))
  (let ((stage (fn-bps-get :stage cursor)) (todo (fn-bps-get :todo cursor))
        (scan (fn-bps-get :scan cursor)) (bundle (fn-bps-get :bundle cursor)))
    (cond
     ((eq stage :count-bindings)
      (if (consp todo)
          (fn-bps-graph-stage :count-targets
           (fn-bps-put :todo (cdr todo)
            (fn-bps-put :targets (fn-bps-field 2 (if (consp (car todo)) (cdar todo) nil))
             (fn-bps-graph-count cursor))))
        (fn-bps-graph-stage :count-opaque (fn-bps-put :todo (fn-bps-get :opaque cursor) cursor))))
     ((eq stage :count-targets)
      (let ((targets (fn-bps-get :targets cursor)))
        (if (consp targets)
            (fn-bps-put :targets (cdr targets) (fn-bps-graph-count cursor))
          (fn-bps-graph-stage :count-bindings cursor))))
     ((eq stage :count-opaque)
      (if (consp todo)
          (fn-bps-put :todo (cdr todo) (fn-bps-graph-count cursor))
        (if (< (nfix (fn-bps-field 6 (fn-bps-get :limits cursor))) (nfix (fn-bps-get :count cursor)))
            (fn-bps-stop :refused :graph-metadata-limit cursor)
          (fn-bps-graph-stage :next-binding (fn-bps-put :todo (fn-bps-get :bindings cursor) cursor)))))
     ((eq stage :next-binding)
      (if (consp todo)
          (fn-bps-graph-stage :security-lookup
           (fn-bps-put :current (car todo) (fn-bps-put :todo (cdr todo)
            (fn-bps-put :bound (cons (fn-bps-field 0 (car todo)) (fn-bps-get :bound cursor))
             (fn-bps-put :scan (fn-bpb-bundle-blocks bundle) cursor)))))
        (fn-bps-graph-stage :coverage-bcb (fn-bps-put :todo (fn-bpb-bundle-blocks bundle) cursor))))
     ((eq stage :security-lookup)
      (cond ((not (consp scan)) (fn-bps-stop :refused :binding-kind cursor))
            ((equal (fn-bps-field 0 (fn-bps-get :current cursor)) (fn-bpb-block-number (car scan)))
             (fn-bps-graph-stage :next-target
              (fn-bps-put :security-block (car scan)
               (fn-bps-put :targets (fn-bps-field 2 (if (consp (fn-bps-get :current cursor))
                                                         (cdr (fn-bps-get :current cursor)) nil)) cursor))))
            (t (fn-bps-put :scan (cdr scan) cursor))))
     ((eq stage :next-target)
      (let ((targets (fn-bps-get :targets cursor)))
        (if (not (consp targets)) (fn-bps-graph-stage :next-binding cursor)
          (let* ((target (car targets))
                 (next (fn-bps-put :target target (fn-bps-put :targets (cdr targets) cursor))))
            (cond ((equal target 0) (fn-bps-graph-stage :check-target (fn-bps-put :target-block nil next)))
                  ((equal target 1) (fn-bps-graph-stage :check-target (fn-bps-put :target-block (fn-bpb-bundle-payload bundle) next)))
                  (t (fn-bps-graph-stage :target-lookup
                      (fn-bps-put :scan (fn-bpb-bundle-blocks bundle) next))))))))
     ((eq stage :target-lookup)
      (cond ((not (consp scan)) (fn-bps-graph-stage :check-target (fn-bps-put :target-block nil cursor)))
            ((equal (fn-bps-get :target cursor) (fn-bpb-block-number (car scan)))
             (fn-bps-graph-stage :check-target (fn-bps-put :target-block (car scan) cursor)))
            (t (fn-bps-put :scan (cdr scan) cursor))))
     ((eq stage :check-target)
      (let ((reason (fn-bps-graph-target-reason cursor)))
        (if reason (fn-bps-stop :refused reason cursor)
          (fn-bps-graph-stage :accept-target cursor))))
     ((eq stage :accept-target)
      (let* ((asb (if (consp (fn-bps-get :current cursor)) (cdr (fn-bps-get :current cursor)) nil))
             (kind (fn-bps-field 1 asb)) (target (fn-bps-get :target cursor)))
        (fn-bps-graph-stage :next-target
         (fn-bps-put :pairs (cons (list kind target) (fn-bps-get :pairs cursor))
          (if (and (equal kind 12) (equal (fn-bpb-block-type (fn-bps-get :target-block cursor)) 11))
              (fn-bps-put :encrypted (cons target (fn-bps-get :encrypted cursor)) cursor) cursor)))))
     ((eq stage :search)
      (cond ((not (consp scan)) (fn-bps-graph-action (fn-bps-get :miss cursor) cursor))
            ((fn-bps-graph-search-matchp (fn-bps-get :needle cursor) (car scan) (fn-bps-get :search-mode cursor))
             (fn-bps-graph-action (fn-bps-get :hit cursor) cursor))
            (t (fn-bps-put :scan (cdr scan) cursor))))
     ((eq stage :coverage-bcb)
      (if (consp todo)
          (let ((next (fn-bps-put :todo (cdr todo) cursor)))
            (if (equal (fn-bpb-block-type (car todo)) 12)
                (fn-bps-graph-search (fn-bpb-block-number (car todo)) (fn-bps-get :bound cursor) :equal
                                     :coverage-bcb '(:unsupported :incomplete-security-coverage) next) next))
        (fn-bps-graph-stage :duplicate-pairs (fn-bps-put :todo (fn-bps-get :pairs cursor) cursor))))
     ((eq stage :duplicate-pairs)
      (if (consp todo)
          (fn-bps-graph-search (car todo) (cdr todo) :equal
                               '(:refused :duplicate-service-target) :duplicate-pairs
                               (fn-bps-put :todo (cdr todo) cursor))
        (fn-bps-graph-stage :encrypted-bound (fn-bps-put :todo (fn-bps-get :encrypted cursor) cursor))))
     ((eq stage :encrypted-bound)
      (if (consp todo)
          (fn-bps-graph-search (car todo) (fn-bps-get :bound cursor) :equal
                               '(:refused :encrypted-bib-parsed) :encrypted-bound (fn-bps-put :todo (cdr todo) cursor))
        (fn-bps-graph-stage :opaque-derived (fn-bps-put :todo (fn-bps-get :opaque cursor) cursor))))
     ((eq stage :opaque-derived)
      (if (consp todo)
          (fn-bps-graph-search (car todo) (fn-bps-get :encrypted cursor) :equal
                               :opaque-derived '(:refused :opaque-set) (fn-bps-put :todo (cdr todo) cursor))
        (fn-bps-graph-stage :derived-opaque (fn-bps-put :todo (fn-bps-get :encrypted cursor) cursor))))
     ((eq stage :derived-opaque)
      (if (consp todo)
          (fn-bps-graph-search (car todo) (fn-bps-get :opaque cursor) :equal
                               :derived-opaque '(:refused :opaque-set) (fn-bps-put :todo (cdr todo) cursor))
        (fn-bps-graph-stage :coverage-bib (fn-bps-put :todo (fn-bpb-bundle-blocks bundle) cursor))))
     ((eq stage :coverage-bib)
      (if (consp todo)
          (let ((next (fn-bps-put :todo (cdr todo) cursor)))
            (if (equal (fn-bpb-block-type (car todo)) 11)
                (fn-bps-graph-search (fn-bpb-block-number (car todo)) (fn-bps-get :bound cursor) :equal
                                     :coverage-bib :coverage-bib-encrypted next) next))
        (fn-bps-graph-stage :overlap (fn-bps-put :todo (fn-bps-get :pairs cursor) cursor))))
     ((eq stage :coverage-bib-encrypted)
      (fn-bps-graph-search (fn-bps-get :needle cursor) (fn-bps-get :encrypted cursor) :equal
                           :coverage-bib '(:unsupported :incomplete-security-coverage) cursor))
     ((eq stage :overlap)
      (if (consp todo)
          (let ((next (fn-bps-put :todo (cdr todo) cursor)))
            (if (equal (fn-bps-field 0 (car todo)) 11)
                (fn-bps-graph-search (fn-bps-field 1 (car todo)) (fn-bps-get :pairs cursor) :bcb-target
                                     '(:refused :unencrypted-bib-overlap) :overlap next) next))
        (fn-bps-stop (if (consp (fn-bps-get :encrypted cursor)) :pending-plaintext :valid) nil cursor)))
     (t (fn-bps-stop :refused :invalid-graph-stage cursor)))))

(defun fn-bps-target-drive (cursor quantum)
  (declare (xargs :guard t :measure (nfix quantum)
                  :hints (("Goal" :in-theory (disable fn-bps-target-unit fn-bps-get)))))
  (if (or (zp (nfix quantum)) (not (eq (fn-bps-get :status cursor) :more))) (list cursor 0)
    (let ((tail (fn-bps-target-drive (fn-bps-target-unit cursor) (1- (nfix quantum)))))
      (list (fn-bps-field 0 tail) (1+ (nfix (fn-bps-field 1 tail)))))))

(defun fn-bps-target-step (cursor quantum)
  (declare (xargs :guard t))
  (let* ((result (fn-bps-target-drive cursor quantum)) (next (fn-bps-field 0 result)))
    (list (fn-bps-get :status next) (fn-bps-get :reason next) next (fn-bps-field 1 result))))

(defthm fn-bps-target-drive-work-does-not-exceed-quantum
  (<= (fn-bps-field 1 (fn-bps-target-drive cursor quantum)) (nfix quantum))
  :hints (("Goal" :induct (fn-bps-target-drive cursor quantum)
           :in-theory (e/d (fn-bps-target-drive fn-bps-field) (fn-bps-target-unit fn-bps-get)))))

(defthm fn-bps-target-drive-work-is-natural
  (natp (fn-bps-field 1 (fn-bps-target-drive cursor quantum)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-bps-target-drive cursor quantum)
           :in-theory (e/d (fn-bps-target-drive fn-bps-field) (fn-bps-target-unit fn-bps-get)))))

(defthm fn-bps-target-drive-normalizes-quantum
  (equal (fn-bps-target-drive cursor (nfix quantum)) (fn-bps-target-drive cursor quantum))
  :hints (("Goal" :expand ((fn-bps-target-drive cursor (nfix quantum))
                          (fn-bps-target-drive cursor quantum))
           :in-theory (disable fn-bps-target-unit fn-bps-get))))

; Quantum cuts preserve the actual unit sequence, complete cursor and exact
; charged work. This does not establish the input/provider invariant or the
; graph's equality with its logical specification.
(local
 (defthm fn-bps-target-drive-two-fields-by-definition
   (equal (list (fn-bps-field 0 (fn-bps-target-drive cursor quantum))
                (fn-bps-field 1 (fn-bps-target-drive cursor quantum)))
          (fn-bps-target-drive cursor quantum))
   :hints (("Goal" :induct (fn-bps-target-drive cursor quantum)
            :in-theory (e/d (fn-bps-target-drive fn-bps-field) (fn-bps-target-unit fn-bps-get))))
   :rule-classes nil))

(defthm fn-bps-target-drive-composes-quanta
  (let* ((first (fn-bps-target-drive cursor q1))
         (second (fn-bps-target-drive (fn-bps-field 0 first) q2)))
    (equal (fn-bps-target-drive cursor (+ (nfix q1) (nfix q2)))
           (list (fn-bps-field 0 second)
                 (+ (fn-bps-field 1 first) (fn-bps-field 1 second)))))
  :hints (("Goal" :induct (fn-bps-target-drive cursor q1)
           :in-theory (e/d (fn-bps-target-drive fn-bps-field)
                           (fn-bps-target-unit fn-bps-get)))
          ("Subgoal *1/1" :use ((:instance fn-bps-target-drive-two-fields-by-definition
                                           (quantum q2))))))
