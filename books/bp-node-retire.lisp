; Retirement of old BP journal generations (spec bp-node-machine 3.6,
; slice E, N16 housekeeping; backlog PKT-059).
;
; After the selection of generation G is durable, the names under the
; journal root that no recovery reads again are removed: every generation
; directory below G ("lifecycle" is generation 0) and every staged
; selection file a killed rotation left (".bp-generation-<pid>-<hex>"; the
; next open never reads one).  ACL2 names them (fn-bpnr-retired-names) and
; plans the removal program (fn-bpnr-retire-ops) from the host's listing of
; each retired directory; host/native/bp-service.lisp
; fnn-bps-retire-generations runs the program one step at a time.  Every
; step is a crash point of the model below: at every prefix of the
; program, the part of the root the open reads (the selection file, the
; selected generation's directory, and any other name the open reads that
; is not retired) is exactly what it was before the program started
; (fn-bpnr-retirement-cut-keeps-open-view).  So a process death anywhere in
; the program, or a failed step, changes no recovery; the next run finishes
; the removal.
(in-package "ACL2")
(include-book "bp-node-rotation")

(defun fn-bpnr-stage-prefix ()
  (declare (xargs :guard t))
  (coerce ".bp-generation-" 'list))

(defun fn-bpnr-stage-namep (name)
  (declare (xargs :guard t))
  (and (stringp name)
       (let ((chars (coerce name 'list)))
         (and (< 15 (len chars))
              (equal (take 15 chars) (fn-bpnr-stage-prefix))))))

; A name the open after the selection of SELECTED never reads.  The two
; names the open does read are excluded by the definition itself, whatever
; the name codec does.
(defun fn-bpnr-retired-namep (name selected)
  (declare (xargs :guard t :verify-guards nil))
  (and (natp selected) (< 0 selected)
       (stringp name)
       (not (equal name (fn-bpnr-generation-directory selected)))
       (not (equal name (fn-bpnr-selection-name)))
       (or (equal name "lifecycle")
           (fn-bpnr-stage-namep name)
           (let ((g (fn-bpnr-generation-of-name name)))
             (and (natp g) (< g selected))))))

(defun fn-bpnr-retired-names (names selected)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom names)
      nil
    (if (fn-bpnr-retired-namep (car names) selected)
        (cons (car names) (fn-bpnr-retired-names (cdr names) selected))
      (fn-bpnr-retired-names (cdr names) selected))))

; The removal program.  LISTINGS maps a retired directory to the entry
; names the host observed in it (bounded by the namespace's work bound); a
; retired name with no listing is a root file.  A directory's files go
; first, then the directory, and one root barrier ends the program.
(defun fn-bpnr-retire-dir-ops (dir files)
  (declare (xargs :guard t))
  (if (atom files)
      (list (list :rmdir dir))
    (cons (list :unlink-in dir (car files))
          (fn-bpnr-retire-dir-ops dir (cdr files)))))

(defun fn-bpnr-retire-ops-aux (retired listings)
  (declare (xargs :guard t))
  (if (atom retired)
      (list (list :barrier))
    (append (let ((listing (and (alistp listings)
                                (assoc-equal (car retired) listings))))
              (if listing
                  (fn-bpnr-retire-dir-ops (car retired) (cdr listing))
                (list (list :unlink (car retired)))))
            (fn-bpnr-retire-ops-aux (cdr retired) listings))))

(defun fn-bpnr-retire-ops (names listings selected)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnr-retire-ops-aux (fn-bpnr-retired-names names selected) listings))

; ---------------------------------------------------------------------------
; The model.  The root is an alist from name to entry: (:file . octets) or
; (:dir . file-alist).  Each step of the program changes the entry of the
; one name it names (fn-bpnr-op-name) and no other.
(defun fn-bpnr-op-name (op)
  (declare (xargs :guard t))
  (if (and (consp op) (consp (cdr op))) (cadr op) nil))

(defun fn-bpnr-op-mutatesp (op)
  (declare (xargs :guard t))
  (and (consp op) (member-equal (car op) '(:rmdir :unlink :unlink-in)) t))

(defun fn-bpnr-tree-drop (name tree)
  (declare (xargs :guard t))
  (cond ((atom tree) nil)
        ((and (consp (car tree)) (equal (caar tree) name))
         (fn-bpnr-tree-drop name (cdr tree)))
        (t (cons (car tree) (fn-bpnr-tree-drop name (cdr tree))))))

(defun fn-bpnr-tree-entry (name tree)
  (declare (xargs :guard t))
  (cond ((atom tree) nil)
        ((and (consp (car tree)) (equal (caar tree) name)) (cdar tree))
        (t (fn-bpnr-tree-entry name (cdr tree)))))

(defun fn-bpnr-op-file (op)
  (declare (xargs :guard t))
  (if (and (consp op) (consp (cdr op)) (consp (cddr op))) (caddr op) nil))

(defun fn-bpnr-apply-op (tree op)
  (declare (xargs :guard t))
  (let ((name (fn-bpnr-op-name op))
        (kind (and (consp op) (car op))))
    (cond ((member-equal kind '(:rmdir :unlink))
           (fn-bpnr-tree-drop name tree))
          ((equal kind :unlink-in)
           (let ((entry (fn-bpnr-tree-entry name tree)))
             (if (and (consp entry) (equal (car entry) :dir))
                 (cons (cons name
                             (cons :dir (fn-bpnr-tree-drop (fn-bpnr-op-file op)
                                                           (cdr entry))))
                       (fn-bpnr-tree-drop name tree))
               tree)))
          (t tree))))

(defun fn-bpnr-apply-ops (tree ops)
  (declare (xargs :guard t))
  (if (atom ops) tree
    (fn-bpnr-apply-ops (fn-bpnr-apply-op tree (car ops)) (cdr ops))))

; What the open reads of the root: the selection plan the selection file
; gives, the selected generation's directory, and every name in EXTRA (the
; root files the open reads besides; the clock-domain and sequence files).
(defun fn-bpnr-tree-plan (tree budget)
  (declare (xargs :guard t :verify-guards nil))
  (let ((entry (fn-bpnr-tree-entry (fn-bpnr-selection-name) tree)))
    (fn-bpnr-selection-plan (and entry t)
                            (and (consp entry) (cdr entry)) budget)))

(defun fn-bpnr-tree-entries (names tree)
  (declare (xargs :guard t))
  (if (atom names) nil
    (cons (fn-bpnr-tree-entry (car names) tree)
          (fn-bpnr-tree-entries (cdr names) tree))))

(defun fn-bpnr-open-view (tree extra budget)
  (declare (xargs :guard t :verify-guards nil))
  (let ((plan (fn-bpnr-tree-plan tree budget)))
    (list plan
          (fn-bpnr-tree-entry (fn-bpnr-plan-directory plan) tree)
          (fn-bpnr-tree-entries extra tree))))

; ---------------------------------------------------------------------------
; Every step names a retired name.
;; Specification only (the host never runs it).
(defun fn-bpnr-ops-within (ops names)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops) t
    (and (or (not (fn-bpnr-op-mutatesp (car ops)))
             (member-equal (fn-bpnr-op-name (car ops)) names))
         (fn-bpnr-ops-within (cdr ops) names))))

(local
 (defthm fn-bpnr-ops-within-append
   (equal (fn-bpnr-ops-within (append a b) names)
          (and (fn-bpnr-ops-within a names) (fn-bpnr-ops-within b names)))))

(local
 (defthm fn-bpnr-retire-dir-ops-within
   (implies (member-equal dir names)
            (fn-bpnr-ops-within (fn-bpnr-retire-dir-ops dir files) names))
   :hints (("Goal" :induct (fn-bpnr-retire-dir-ops dir files)
            :in-theory (union-theories
                        '(fn-bpnr-retire-dir-ops fn-bpnr-ops-within
                          fn-bpnr-op-name car-cons cdr-cons (:e fn-bpnr-op-mutatesp))
                        (theory 'ground-zero))))))

(local
 (defthm fn-bpnr-retire-ops-aux-within
   (implies (subsetp-equal retired names)
            (fn-bpnr-ops-within (fn-bpnr-retire-ops-aux retired listings)
                                names))))

(local
 (defthm fn-bpnr-subsetp-cons
   (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(local
 (defthm fn-bpnr-subsetp-self
   (subsetp-equal x x)))

(defthm fn-bpnr-retire-ops-name-only-retired
  (fn-bpnr-ops-within (fn-bpnr-retire-ops names listings selected)
                      (fn-bpnr-retired-names names selected))
  :hints (("Goal" :use ((:instance fn-bpnr-retire-ops-aux-within
                                   (retired (fn-bpnr-retired-names names selected))
                                   (names (fn-bpnr-retired-names names selected))))
           :in-theory (e/d (fn-bpnr-retire-ops)
                           (fn-bpnr-retired-names fn-bpnr-retire-ops-aux-within)))))

(defthm fn-bpnr-ops-within-take
  (implies (fn-bpnr-ops-within ops names)
           (fn-bpnr-ops-within (take k ops) names))
  :hints (("Goal" :induct (take k ops)
           :in-theory (e/d (take) (fn-bpnr-op-mutatesp)))))

(local
 (defthm fn-bpnr-member-retired-names
   (implies (member-equal name (fn-bpnr-retired-names names selected))
            (fn-bpnr-retired-namep name selected))
   :hints (("Goal" :induct (fn-bpnr-retired-names names selected)
            :in-theory (disable fn-bpnr-retired-namep)))))

; The two names the open reads are never retired.
(defthm fn-bpnr-retired-names-never-the-selected-directory
  (and (not (member-equal (fn-bpnr-generation-directory selected)
                          (fn-bpnr-retired-names names selected)))
       (not (member-equal (fn-bpnr-selection-name)
                          (fn-bpnr-retired-names names selected))))
  :hints (("Goal" :use ((:instance fn-bpnr-member-retired-names
                                   (name (fn-bpnr-generation-directory selected)))
                        (:instance fn-bpnr-member-retired-names
                                   (name (fn-bpnr-selection-name))))
           :in-theory (disable fn-bpnr-member-retired-names
                               fn-bpnr-generation-directory
                               fn-bpnr-generation-of-name
                               fn-bpnr-stage-namep))))

(local
 (defthm fn-bpnr-tree-entry-of-drop
   (implies (not (equal n name))
            (equal (fn-bpnr-tree-entry n (fn-bpnr-tree-drop name tree))
                   (fn-bpnr-tree-entry n tree)))))

(local
 (defthm fn-bpnr-tree-entry-of-apply-op
   (implies (or (not (fn-bpnr-op-mutatesp op))
                (not (equal n (fn-bpnr-op-name op))))
            (equal (fn-bpnr-tree-entry n (fn-bpnr-apply-op tree op))
                   (fn-bpnr-tree-entry n tree)))))

(defthm fn-bpnr-tree-entry-of-apply-ops
  (implies (and (fn-bpnr-ops-within ops names)
                (not (member-equal n names)))
           (equal (fn-bpnr-tree-entry n (fn-bpnr-apply-ops tree ops))
                  (fn-bpnr-tree-entry n tree)))
  :hints (("Goal" :induct (fn-bpnr-apply-ops tree ops)
           :in-theory (disable fn-bpnr-apply-op fn-bpnr-op-mutatesp
                               fn-bpnr-op-name fn-bpnr-tree-entry
                               fn-bpnr-tree-entry-of-apply-op))
          ("Subgoal *1/2" :use ((:instance fn-bpnr-tree-entry-of-apply-op
                                           (op (car ops)))))))

(defthm fn-bpnr-tree-entries-of-apply-ops
   (implies (and (fn-bpnr-ops-within ops names)
                 (not (intersectp-equal extra names)))
            (equal (fn-bpnr-tree-entries extra (fn-bpnr-apply-ops tree ops))
                   (fn-bpnr-tree-entries extra tree)))
   :hints (("Goal" :in-theory (disable fn-bpnr-apply-ops fn-bpnr-tree-entry))))

;; KEYSTONE.  Let the root's selection file select generation G > 0, and
;; let EXTRA be the other names the open reads, none of them retired.  Then
;; at every cut K of the removal program (process death after K steps),
;; the part of the root the open reads is exactly the part before the
;; program: the same selection plan, the same selected directory, the same
;; EXTRA entries.  Recovery is a function of that view, so it is unchanged.
(defthm fn-bpnr-retirement-cut-keeps-open-view
  (implies (and (equal (fn-bpnr-plan-generation (fn-bpnr-tree-plan tree budget))
                       selected)
                (not (intersectp-equal extra
                                       (fn-bpnr-retired-names names selected))))
           (equal (fn-bpnr-open-view
                   (fn-bpnr-apply-ops
                    tree (take k (fn-bpnr-retire-ops names listings selected)))
                   extra budget)
                  (fn-bpnr-open-view tree extra budget)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-ops-within-take
                            (ops (fn-bpnr-retire-ops names listings selected))
                            (names (fn-bpnr-retired-names names selected)))
                 (:instance fn-bpnr-retire-ops-name-only-retired)
                 (:instance fn-bpnr-retired-names-never-the-selected-directory)
                 (:instance fn-bpnr-tree-entries-of-apply-ops
                            (ops (take k (fn-bpnr-retire-ops names listings
                                                             selected)))
                            (names (fn-bpnr-retired-names names selected)))
                 (:instance fn-bpnr-tree-entry-of-apply-ops
                            (ops (take k (fn-bpnr-retire-ops names listings
                                                             selected)))
                            (names (fn-bpnr-retired-names names selected))
                            (n (fn-bpnr-selection-name)))
                 (:instance fn-bpnr-tree-entry-of-apply-ops
                            (ops (take k (fn-bpnr-retire-ops names listings
                                                             selected)))
                            (names (fn-bpnr-retired-names names selected))
                            (n (fn-bpnr-generation-directory selected))))
           :in-theory (e/d (fn-bpnr-open-view fn-bpnr-tree-plan
                                              fn-bpnr-plan-directory)
                           (fn-bpnr-tree-entry-of-apply-ops
                            fn-bpnr-tree-entries-of-apply-ops
                            fn-bpnr-ops-within-take
                            fn-bpnr-retire-ops-name-only-retired
                            fn-bpnr-retired-names-never-the-selected-directory
                            fn-bpnr-retire-ops fn-bpnr-retired-names
                            fn-bpnr-apply-ops fn-bpnr-tree-entry
                            fn-bpnr-tree-entries (:e fn-bpnr-selection-name)
                            fn-bpnr-selection-name
                            fn-bpnr-selection-plan
                            fn-bpnr-plan-generation
                            fn-bpnr-generation-directory take)))))
