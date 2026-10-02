; UNHOOKED cert-roots (2026-10-02): out of the Makefile certify roots -- a Codex-era book that never certified and no image world includes: fn-mxc-put-is-put-chars-of-nthcdr fails at dev adbf57435. The code stays; its completion is queued (build/coordinator/lanedumps/cert-roots.md).
; Full-result refinement of the scheduling cursor to the existing trie update.
(in-package "ACL2")
(include-book "view-delta-cursor")
(include-book "view-delta-concrete")

(defun fn-vcu-frame-work (frames)
 (declare (xargs :guard t))
 (if (consp frames)
  (+ 1 (len (fn-vcu-at 1 (car frames))) (fn-vcu-frame-work (cdr frames))) 0))
(defun fn-vcu-work-left (c)
 (declare (xargs :guard t))
 (let ((phase (fn-vcu-at 0 c)) (key (fn-vcu-at 1 c)))
  (cond ((and (eq phase :scan) (stringp key))
         (+ 3 (* 2 (nfix (- (length key) (nfix (fn-vcu-at 2 c)))))
            (* 2 (acl2-count (fn-vcu-at 3 c))) (len (fn-vcu-at 4 c))
            (fn-vcu-frame-work (fn-vcu-at 5 c))))
        ((eq phase :rebuild)
         (+ 1 (len (fn-vcu-at 4 c)) (fn-vcu-frame-work (fn-vcu-at 5 c))))
        (t 0))))
(defun fn-vcu-livep (c)
 (declare (xargs :guard t))
 (or (eq (fn-vcu-at 0 c) :done) (eq (fn-vcu-at 0 c) :rebuild)
     (and (eq (fn-vcu-at 0 c) :scan) (stringp (fn-vcu-at 1 c)))))

(defthm fn-vcu-step-preserves-live
 (implies (fn-vcu-livep c) (fn-vcu-livep (fn-vcu-step c)))
 :hints (("Goal" :in-theory (enable fn-vcu-livep fn-vcu-step))))
(defthm fn-vcu-step-progress
 (implies (and (fn-vcu-livep c) (not (eq (fn-vcu-at 0 c) :done)))
  (< (fn-vcu-work-left (fn-vcu-step c)) (fn-vcu-work-left c)))
 :hints (("Goal" :in-theory (e/d (fn-vcu-work-left fn-vcu-step fn-vcu-livep
                   fn-vcu-frame-work fn-vcu-c fn-vcu-at fn-vcu-car fn-vcu-cdr)
                   (fn-vcu-pair char)))))

(local (defthm fn-vcu-live-not-done-positive
 (implies (and (fn-vcu-livep c) (not (eq (fn-vcu-at 0 c) :done)))
          (< 0 (fn-vcu-work-left c)))
 :hints (("Goal" :in-theory (enable fn-vcu-livep fn-vcu-work-left)))))

(defthm fn-vcu-drive-finishes-with-sufficient-fuel
 (implies (and (fn-vcu-livep c) (<= (fn-vcu-work-left c) (nfix fuel)))
          (eq (fn-vcu-at 0 (mv-nth 0 (fn-vcu-drive c fuel))) :done))
 :hints (("Goal" :induct (fn-vcu-drive c fuel)
          :in-theory (e/d (fn-vcu-drive)
           (fn-vcu-step fn-vcu-at fn-vcu-livep fn-vcu-work-left
            fn-vcu-step-progress)))
         ("Subgoal *1/2" :use ((:instance fn-vcu-step-progress)))) )

; These denotations are proof-only, never called by the scheduling step.
(defun fn-vcu-rev (x out)
 (declare (xargs :guard t))
 (if (consp x) (fn-vcu-rev (cdr x) (cons (car x) out)) out))
(defun fn-vcu-parents (frames out)
 (declare (xargs :guard t))
 (if (consp frames)
  (let ((frame (car frames)))
   (fn-vcu-parents (cdr frames)
    (fn-vcu-rev (fn-vcu-at 1 frame)
     (cons (cons (fn-vcu-at 0 frame) out) (fn-vcu-at 2 frame)))))
  out))
(defun fn-vcu-reference-at (key i trie weight release)
 (declare (xargs :guard (and (stringp key) (natp i))))
 (fn-mxc-put key i (fn-vcu-pair (fn-mxc-get key i trie) weight release) trie))
(defun fn-vcu-meaning (c)
 (declare (xargs :guard t))
 (let ((phase (fn-vcu-at 0 c)) (key (fn-vcu-at 1 c)))
  (cond ((and (eq phase :scan) (stringp key))
         (fn-vcu-parents (fn-vcu-at 5 c)
          (fn-vcu-rev (fn-vcu-at 4 c)
           (fn-vcu-reference-at key (nfix (fn-vcu-at 2 c)) (fn-vcu-at 3 c)
                                (fn-vcu-at 7 c) (fn-vcu-at 8 c)))))
        ((eq phase :rebuild)
         (fn-vcu-parents (fn-vcu-at 5 c)
          (fn-vcu-rev (fn-vcu-at 4 c) (fn-vcu-at 6 c))))
        (t (fn-vcu-at 6 c)))))

(local (defthm fn-vcu-nfix-natural
 (implies (natp x) (equal (nfix x) x))))

; Reprove the existing index-local string/list bridge in this book scope.
(local (defthm fn-mxc-len-coerce-is-length
  (implies (stringp s) (equal (len (coerce s 'list)) (length s)))))
(local (defthm fn-mxc-shift-less
  (implies (and (integerp i) (integerp n))
           (equal (< (+ -1 i) n) (< i (+ 1 n))))
  :hints (("Goal" :cases ((< i (+ 1 n)))))))
(local (defthm fn-mxc-consp-of-nthcdr
  (implies (natp i)
           (equal (consp (nthcdr i l)) (< i (len l))))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr len)))))
(local (defthm fn-mxc-car-of-nthcdr
  (equal (car (nthcdr i l)) (nth i l))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr nth)))))
(local (defthm fn-mxc-cdr-of-nthcdr
  (implies (natp i)
           (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l)))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr)))))
(local (defthm fn-mxc-char-is-nth
  (equal (char s i) (nth i (coerce s 'list)))
  :hints (("Goal" :in-theory (enable char)))))
(local (defthm fn-mxc-put-is-put-chars-of-nthcdr
  (implies (natp i)
           (equal (fn-mxc-put msgid i article trie)
                  (fn-midx-put-chars (nthcdr i (coerce msgid 'list)) article trie)))
  :hints (("Goal" :induct (fn-mxc-put msgid i article trie)
           :expand ((fn-midx-put-chars (nthcdr i (coerce msgid 'list)) article trie))))))

(local (defthm fn-vcu-reference-at-unfolds
 (implies (and (stringp key) (natp i))
  (equal (fn-vcu-reference-at key i trie weight release)
   (if (< i (length key))
    (fn-midx-branch-put (char key i)
     (fn-vcu-reference-at key (+ 1 i) (fn-midx-branch-get (char key i) trie) weight release) trie)
    (fn-midx-branch-put :fn-midx-value
     (fn-vcu-pair (fn-midx-branch-get :fn-midx-value trie) weight release) trie))))
 :hints (("Goal" :in-theory (e/d (fn-vcu-reference-at fn-mxc-get fn-mxc-put)
                                 (fn-vcu-pair))))))

(defthm fn-vcu-step-preserves-complete-update
 (equal (fn-vcu-meaning (fn-vcu-step c)) (fn-vcu-meaning c))
 :hints (("Goal" :in-theory (e/d (fn-vcu-step fn-vcu-meaning fn-vcu-c fn-vcu-at
                                  fn-vcu-car fn-vcu-cdr fn-vcu-rev fn-vcu-parents
                                  fn-midx-branch-get fn-midx-branch-put
                                  fn-ag-car fn-ag-cdr)
                                 (fn-vcu-reference-at fn-vcu-pair fn-mxc-get fn-mxc-put
                                  fn-vcu-reference-at-unfolds char length nfix))
          :use ((:instance fn-vcu-reference-at-unfolds
                 (key (fn-vcu-at 1 c)) (i (nfix (fn-vcu-at 2 c)))
                 (trie (fn-vcu-at 3 c)) (weight (fn-vcu-at 7 c))
                 (release (fn-vcu-at 8 c)))
                (:instance fn-vcu-reference-at-unfolds
                 (key (fn-vcu-at 1 c)) (i (nfix (fn-vcu-at 2 c)))
                 (trie (fn-vcu-cdr (fn-vcu-at 3 c))) (weight (fn-vcu-at 7 c))
                 (release (fn-vcu-at 8 c)))))))

(defthm fn-vcu-drive-preserves-complete-update
 (equal (fn-vcu-meaning (mv-nth 0 (fn-vcu-drive c fuel))) (fn-vcu-meaning c))
 :hints (("Goal" :induct (fn-vcu-drive c fuel)
          :in-theory (e/d (fn-vcu-drive)
                          (fn-vcu-step fn-vcu-at fn-vcu-meaning)))))

(defthm fn-vcu-begin-meaning-unfolds
 (equal (fn-vcu-meaning (fn-vcu-begin key weight release trie))
        (if release (fn-vdc-unbump key weight trie) (fn-vdc-bump key weight trie)))
 :hints (("Goal" :in-theory
  (e/d (fn-vcu-begin fn-vcu-meaning fn-vcu-c fn-vcu-at fn-vcu-car fn-vcu-cdr
         fn-vcu-rev fn-vcu-parents fn-vcu-reference-at fn-vcu-pair
         fn-vdc-bump fn-vdc-unbump fn-vdc-get fn-vdc-put fn-vd-pairp fn-mxc-lookup)
        (fn-mxc-get fn-mxc-put fn-midx-put-chars fn-vcu-reference-at-unfolds)))))

(local (defthm fn-vcu-done-meaning-by-definition
 (implies (eq (fn-vcu-at 0 c) :done)
          (equal (fn-vcu-meaning c) (fn-vcu-at 6 c)))
 :hints (("Goal" :in-theory (enable fn-vcu-meaning)))))

(defthm fn-vcu-completed-is-original-delta
 (implies (eq (fn-vcu-at 0 (mv-nth 0 (fn-vcu-drive
                (fn-vcu-begin key weight release trie) fuel))) :done)
  (equal (fn-vcu-result (mv-nth 0 (fn-vcu-drive
           (fn-vcu-begin key weight release trie) fuel)))
         (list :done (if release (fn-vdc-unbump key weight trie)
                                 (fn-vdc-bump key weight trie)))))
 :hints (("Goal" :in-theory (e/d (fn-vcu-result)
          (fn-vcu-drive fn-vcu-begin fn-vcu-at fn-vcu-meaning
           fn-vdc-unbump fn-vdc-bump fn-vcu-drive-preserves-complete-update
           fn-vcu-begin-meaning-unfolds))
          :use ((:instance fn-vcu-drive-preserves-complete-update
                  (c (fn-vcu-begin key weight release trie)))
                (:instance fn-vcu-begin-meaning-unfolds)))))
