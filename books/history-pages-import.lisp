; fn: the empty history's image and the import loop (lane arena-store-4,
; 2026-09-28, m3c P1).  Prefix fn-hp-.
;
; KEYSTONE fn-hp-x-init-refines: `fn-hp-x-init' on an empty page store
; makes the empty history's image: one page, the header, every region
; empty (cap 0) at page 1, so the first append answers (:grow 0 1) and the
; step relocates the five regions (tests/acl2/history-pages-step-tests.lisp).
; KEYSTONE fn-hp-x-append-all-refines: the import loop over a list of
; events (building the image from an existing store's records) appends a
; prefix of them, all of them when it answers :ok, the store holding the
; image of the history so extended.  Its work is the sum of the steps'
; (books/history-pages-step.lisp's head); the loop itself is
; tail-recursive.
(in-package "ACL2")
(include-book "history-pages-step")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound
                           fn-scc-encode-is-program)))

; -----------------------------------------------------------------------------
; A. The empty history's image.

(defconst *fn-hp-empty-lens* '(0 0 0 0 0))
(defconst *fn-hp-empty-starts* '(1 1 1 1 1))
(defconst *fn-hp-empty-hdr* (take 19 (fn-hp-hdr2 0 *fn-hp-empty-lens* *fn-hp-empty-starts* 1)))

(defthm fn-hp-regs-nil
  (equal (fn-hp-regs nil salt) '(nil nil nil nil nil))
  :hints (("Goal" :expand ((fn-hp-regs nil salt)))))

(defthm fn-hp-empty-image-facts
  (and (fn-hp-okp nil salt)
       (equal (fn-hp-lens nil salt) *fn-hp-empty-lens*)
       (equal (fn-hp-piw nil salt *fn-hp-empty-starts* 1) (fn-hp-hdr2 0 *fn-hp-empty-lens* *fn-hp-empty-starts* 1))))

(defun fn-hp-x-init (pgs-mem)
  ; The empty history's image on an empty page store, as the host calls it
  ; when it creates the image: (mv VERDICT N LENS STARTS NP pgs-mem).
  ;   :ok     the store grew to one page (`pgs-x-grow-image': zero,
  ;           verified) and the header's 19 words were written there
  ;           (page 0 dirty); (N LENS STARTS NP) = (0 (0 0 0 0 0) (1 1 1 1 1)
  ;           1) is the header answer to carry.  Every region is empty (cap
  ;           0 pages), so the first append answers (:grow 0 1) and
  ;           `fn-hp-x-append-step' relocates the five regions in turn.
  ;   (:refused :image)   the store is not empty: nothing changed.
  ; Work: 2048 zero words and 19 header words.
  (declare (xargs :stobjs pgs-mem
                  :guard-hints (("Goal" :use ((:instance fn-hp-grow-image-lengths (np 0) (npn 1)))
                                 :in-theory (disable fn-hp-grow-image-lengths pgs-x-grow-image)))))
  (if (not (and (equal (pgs-v-length pgs-mem) 0) (equal (pgs-d-length pgs-mem) 0) (equal (pgs-w-length pgs-mem) 0)))
      (mv (list :refused :image) nil nil nil nil pgs-mem)
    (let* ((pgs-mem (pgs-x-grow-image 1 pgs-mem))
           (pgs-mem (fn-hp-x-put 0 *fn-hp-empty-hdr* pgs-mem)))
      (mv :ok 0 *fn-hp-empty-lens* *fn-hp-empty-starts* 1 pgs-mem))))

(local
 (defthm fn-hp-resize-list-len0
   (implies (and (equal (len x) 0) (syntaxp (not (equal x ''nil))))
            (equal (resize-list x n d) (resize-list nil n d)))
   :hints (("Goal" :induct (resize-list x n d)))))

(local
 (defthm fn-hp-x-init-words
   (implies (and (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0))
            (equal (nth *pgs-wi* (fn-hp-x-put 0 *fn-hp-empty-hdr* (pgs-x-grow-image 1 pgs-mem)))
                   (fn-hp-hdr2 0 *fn-hp-empty-lens* *fn-hp-empty-starts* 1)))
   :hints (("Goal" :use ((:instance fn-hp-grow-image-lengths (np 0) (npn 1))
                         (:instance fn-hp-grow-image-words (npn 1))
                         (:instance fn-hp-x-put-words (j 0) (ws *fn-hp-empty-hdr*) (pgs-mem (pgs-x-grow-image 1 pgs-mem))))
            :in-theory (e/d (pgs-w-length) (fn-hp-grow-image-lengths fn-hp-grow-image-words pgs-x-grow-image
                                            fn-hp-x-put fn-hp-x-put-words))))))

(local
 (defthm fn-hp-x-init-dirty-0
   (equal (nth 0 (nth *pgs-di* (fn-hp-x-put 0 *fn-hp-empty-hdr* mem))) 1)
   :hints (("Goal" :in-theory (enable update-pgs-di)))))

(local
 (defthm fn-hp-x-init-vi
   (implies (and (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0) (equal (pgs-d-length pgs-mem) 0))
            (and (equal (nth *pgs-vi* (fn-hp-x-put 0 *fn-hp-empty-hdr* (pgs-x-grow-image 1 pgs-mem)))
                        (nth *pgs-vi* (pgs-x-grow-image 1 pgs-mem)))
                 (equal (pgs-v-length (fn-hp-x-put 0 *fn-hp-empty-hdr* (pgs-x-grow-image 1 pgs-mem))) 1)
                 (equal (pgs-vi 0 (pgs-x-grow-image 1 pgs-mem)) 2)))
   :hints (("Goal" :use ((:instance fn-hp-grow-image-lengths (np 0) (npn 1))
                         (:instance fn-hp-grow-image-vi (q 0) (npn 1))
                         (:instance fn-hp-x-put-lengths (j 0) (ws *fn-hp-empty-hdr*) (pgs-mem (pgs-x-grow-image 1 pgs-mem))))
            :in-theory (disable fn-hp-grow-image-lengths fn-hp-grow-image-vi pgs-x-grow-image
                                fn-hp-x-put fn-hp-x-put-lengths)))))

(defthm fn-hp-vhold-own-words
  (fn-hp-vhold p np mem (nth *pgs-wi* mem))
  :hints (("Goal" :induct (fn-hp-vhold p np mem (nth *pgs-wi* mem)) :in-theory (disable take nthcdr) :expand ((fn-hp-vhold p np mem (nth *pgs-wi* mem))))))

; KEYSTONE (the empty image): on an empty page store, `fn-hp-x-init'
; answering :ok leaves a one-page store whose verified pages hold the empty
; history's image placed at (1 1 1 1 1) in 1 page (for every salt), answers
; that image's header (N 0, the empty lengths), and its header page is
; verified and dirty.
(defthm fn-hp-x-init-refines
  (implies (equal (mv-nth 0 (fn-hp-x-init pgs-mem)) :ok)
           (let* ((res (fn-hp-x-init pgs-mem))
                  (n (mv-nth 1 res)) (lens (mv-nth 2 res)) (starts (mv-nth 3 res)) (np (mv-nth 4 res))
                  (mem2 (mv-nth 5 res)))
             (and (fn-hp-okp nil salt)
                  (equal n (len nil))
                  (equal lens (fn-hp-lens nil salt))
                  (equal starts *fn-hp-empty-starts*) (equal np 1)
                  (fn-hp-starts-okp starts)
                  (adt-placement-ok starts lens np)
                  (equal (pgs-v-length mem2) np)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw nil salt starts np))
                  (equal (pgs-vi 0 mem2) 2)
                  (equal (nth 0 (nth *pgs-di* mem2)) 1))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-init-words) (:instance fn-hp-x-init-vi) (:instance fn-hp-empty-image-facts)
                 (:instance fn-hp-x-init-dirty-0 (mem (pgs-x-grow-image 1 pgs-mem)))
                 (:instance fn-hp-vhold-own-words (p 0) (np 1)
                            (mem (fn-hp-x-put 0 *fn-hp-empty-hdr* (pgs-x-grow-image 1 pgs-mem)))))
           :in-theory (e/d (pgs-vi) (fn-hp-vhold-own-words fn-hp-vhold fn-hp-x-put-words fn-hp-grow-image-words fn-hp-x-init-words fn-hp-x-init-vi fn-hp-empty-image-facts fn-hp-x-init-dirty-0
                                     pgs-x-grow-image fn-hp-x-put fn-hp-piw fn-hp-hdr2 (:e fn-hp-hdr2) fn-hp-okp fn-hp-lens
                                     take nthcdr)))))

; -----------------------------------------------------------------------------
; B. The step's answers have the header answer's types.

(defthm fn-hp-x-append-types
  (implies (and (natp n) (nat-listp lens) (equal (len lens) 5))
           (let ((a (fn-hp-x-append ev salt n lens starts np pgs-mem)))
             (and (natp (mv-nth 1 a)) (nat-listp (mv-nth 2 a)) (equal (len (mv-nth 2 a)) 5))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
           :use ((:instance fn-hp-x-append-ok-unfolds) (:instance fn-hp-x-append-not-ok-unchanged))
           :in-theory (e/d (fn-hp-x-lens-after)
                           (fn-hp-x-append-ok-unfolds fn-hp-x-append-not-ok-unchanged fn-hp-x-append
                            fn-scc-encode fn-hp-pad8 adt-placement-ok fn-hp-x-unfit fn-hp-x-blocks fn-hp-x-aligned
                            fn-sccb-treep fn-hp-pack8 adt-cap fn-hp-mkey fn-hp-u64-listp adt-end-l fn-hp-x-blocks-ready
                            fn-hp-x-put-blocks)))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-nat-listp-lens-after) (:instance fn-hp-len-lens-after))))))

(local
 (defthm fn-hp-nat-listp-update-nth-i
   (implies (and (nat-listp l) (natp v) (natp r) (< r (len l))) (nat-listp (update-nth r v l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(defthm fn-hp-x-relocate-types
  (implies (and (nat-listp starts) (equal (len starts) 5) (natp np) (natp r) (< r 5) (natp c))
           (let ((a (fn-hp-x-relocate r c n lens starts np pgs-mem)))
             (and (nat-listp (mv-nth 1 a)) (equal (len (mv-nth 1 a)) 5) (natp (mv-nth 2 a)))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))
           :use ((:instance fn-hp-x-relocate-ok-unfolds) (:instance fn-hp-x-relocate-not-ok-unchanged))
           :in-theory (disable fn-hp-x-relocate-ok-unfolds fn-hp-x-relocate-not-ok-unchanged fn-hp-x-relocate))))

(defthm fn-hp-x-append-loop-types
  (implies (and (natp n) (nat-listp lens) (equal (len lens) 5) (nat-listp starts) (equal (len starts) 5) (natp np))
           (let ((a (fn-hp-x-append-loop k ev salt n lens starts np pgs-mem)))
             (and (natp (mv-nth 1 a)) (nat-listp (mv-nth 2 a)) (equal (len (mv-nth 2 a)) 5)
                  (nat-listp (mv-nth 3 a)) (equal (len (mv-nth 3 a)) 5) (natp (mv-nth 4 a)))))
  :hints (("Goal" :induct (fn-hp-x-append-loop k ev salt n lens starts np pgs-mem)
           :in-theory (fn-hp-loop-theory fn-hp-x-append-loop))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-x-append-grow-shape)
                       (:instance fn-hp-x-append-grow-mem)
                       (:instance fn-hp-x-append-types)
                       (:instance fn-hp-x-relocate-types (r (cadr (fn-hp-av))) (c (caddr (fn-hp-av)))))
                 :in-theory (fn-hp-loop-theory)))))

(defthm fn-hp-x-append-step-types
  (implies (and (natp n) (nat-listp lens) (equal (len lens) 5) (nat-listp starts) (equal (len starts) 5) (natp np))
           (let ((a (fn-hp-x-append-step ev salt n lens starts np pgs-mem)))
             (and (natp (mv-nth 1 a)) (nat-listp (mv-nth 2 a)) (equal (len (mv-nth 2 a)) 5)
                  (nat-listp (mv-nth 3 a)) (equal (len (mv-nth 3 a)) 5) (natp (mv-nth 4 a)))))
  :hints (("Goal" :in-theory (disable fn-hp-x-append-loop))))

; -----------------------------------------------------------------------------
; C. The import loop.

(defun fn-hp-x-append-all (evs k salt n lens starts np pgs-mem)
  ; The events EVS appended in order, as the host calls it to build an
  ; image from an existing store's records (K: how many were appended
  ; before; the host calls with 0): (mv VERDICT K2 N2 LENS2 STARTS2 NP2
  ; pgs-mem).  Each event is one `fn-hp-x-append-step'; the loop stops at
  ; the first answer other than :ok and returns it, K2 - K events having
  ; been appended; (N2 LENS2 STARTS2 NP2) is the header answer to carry
  ; either way.  Tail-recursive: one frame whatever the length of EVS.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (true-listp evs) (natp k) (natp n) (nat-listp lens) (equal (len lens) 5)
                              (nat-listp starts) (equal (len starts) 5) (natp np))
                  :guard-hints (("Goal" :use ((:instance fn-hp-x-append-step-types (ev (car evs))))
                                 :in-theory (disable fn-hp-x-append-step-types fn-hp-x-append-step)))))
  (if (atom evs)
      (mv :ok k n lens starts np pgs-mem)
    (mv-let (v n2 lens2 starts2 np2 pgs-mem)
      (fn-hp-x-append-step (car evs) salt n lens starts np pgs-mem)
      (if (eq v :ok)
          (fn-hp-x-append-all (cdr evs) (+ 1 k) salt n2 lens2 starts2 np2 pgs-mem)
        (mv v k n2 lens2 starts2 np2 pgs-mem)))))

(defun-nx fn-hp-all-post (h evs salt k lens starts np res)
  ; what the import loop's answer RES = (VERDICT K2 N2 LENS2 STARTS2 NP2
  ; MEM2) means over the history H (LENS STARTS NP: the header answer the
  ; loop was called with, K: its count)
  (let* ((v (mv-nth 0 res)) (j (- (mv-nth 1 res) k)) (n2 (mv-nth 2 res)) (lens2 (mv-nth 3 res))
         (starts2 (mv-nth 4 res)) (np2 (mv-nth 5 res)) (mem2 (mv-nth 6 res))
         (h2 (append h (take j evs))))
    (and (acl2-numberp (mv-nth 1 res)) (natp j) (<= j (len evs))
         (implies (equal v :ok) (equal j (len evs)))
         (not (equal (car v) :grow))
         (fn-hp-okp h2 salt)
         (equal n2 (len h2)) (equal lens2 (fn-hp-lens h2 salt))
         (fn-hp-starts-okp starts2)
         (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h2 salt starts2 np2))
         (implies (and (equal v :ok) (or (< 0 j) (adt-placement-ok starts lens np)))
                  (adt-placement-ok starts2 lens2 np2)))))

(defun-nx fn-hp-all-ind (evs k h salt starts np pgs-mem)
  (declare (xargs :measure (len evs)
                  :hints (("Goal" :in-theory (disable fn-hp-x-append-step)))))
  (if (atom evs)
      (list k h salt starts np pgs-mem)
    (let ((res (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
      (if (equal (mv-nth 0 res) :ok)
          (fn-hp-all-ind (cdr evs) (+ 1 k) (append h (list (car evs))) salt (mv-nth 3 res) (mv-nth 4 res) (mv-nth 5 res))
        (list k h salt starts np pgs-mem)))))

(local
 (defthm fn-hp-events-okp-true-listp
   (implies (fn-hp-events-okp h) (true-listp h))
   :hints (("Goal" :in-theory (disable fn-hp-evp)))))

(local
 (defthm fn-hp-okp-true-listp
   (implies (fn-hp-okp h salt) (true-listp h))
   :hints (("Goal" :in-theory (e/d (fn-hp-okp) (fn-hp-image fn-hp-events-okp))))))

(local
 (defthm fn-hp-append-snoc-take
   (implies (and (consp evs) (natp j))
            (equal (append (append h (list (car evs))) (take j (cdr evs)))
                   (append h (take (+ 1 j) evs))))))

(defthm fn-hp-all-post-nil
  (implies (and (atom evs) (natp k) (fn-hp-okp h salt) (fn-hp-starts-okp starts)
                (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h salt starts np)))
           (fn-hp-all-post h evs salt k (fn-hp-lens h salt) starts np
                           (list :ok k (len h) (fn-hp-lens h salt) starts np mem)))
  :hints (("Goal" :in-theory (disable fn-hp-okp fn-hp-lens fn-hp-piw adt-placement-ok fn-hp-vhold))))

(defthm fn-hp-all-post-stop
  (implies (and (not (equal v :ok)) (not (equal (car v) :grow)) (natp k)
                (fn-hp-okp h salt) (fn-hp-starts-okp starts2)
                (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt starts2 np2)))
           (fn-hp-all-post h evs salt k lens starts np
                           (list v k (len h) (fn-hp-lens h salt) starts2 np2 mem2)))
  :hints (("Goal" :in-theory (disable fn-hp-okp fn-hp-lens fn-hp-piw adt-placement-ok fn-hp-vhold))))

(defthm fn-hp-all-post-cons
  (implies (and (consp evs) (natp k) (fn-hp-okp h salt)
                (fn-hp-all-post (append h (list (car evs))) (cdr evs) salt (+ 1 k) lens2 starts2 np2 res)
                (adt-placement-ok starts2 lens2 np2))
           (fn-hp-all-post h evs salt k lens starts np res))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-append-snoc-take (j (- (mv-nth 1 res) (+ 1 k)))))
           :expand ((:free (h evs k lens starts np) (fn-hp-all-post h evs salt k lens starts np res))
                    (len evs))
           :in-theory (disable fn-hp-okp fn-hp-lens fn-hp-piw adt-placement-ok fn-hp-vhold fn-hp-append-snoc-take
                               take append len fn-hp-starts-okp))))

(in-theory (disable fn-hp-all-post))

(defthm fn-hp-x-append-all-post
  (implies (and (fn-hp-held h starts np pgs-mem) (natp k))
           (fn-hp-all-post h evs salt k (fn-hp-lens h salt) starts np
                           (fn-hp-x-append-all evs k salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
  :hints (("Goal" :induct (fn-hp-all-ind evs k h salt starts np pgs-mem)
           :in-theory (fn-hp-loop-theory fn-hp-x-append-all atom (:induction fn-hp-all-ind)))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-x-append-step-refines (ev (car evs)) (n (len h)) (lens (fn-hp-lens h salt)) (p 0))
                       (:instance fn-hp-all-post-nil (mem pgs-mem))
                       (:instance fn-hp-all-post-stop
                                  (v (mv-nth 0 (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                  (lens (fn-hp-lens h salt))
                                  (starts2 (mv-nth 3 (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                  (np2 (mv-nth 4 (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                  (mem2 (mv-nth 5 (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem))))
                       (:instance fn-hp-all-post-cons
                                  (lens (fn-hp-lens h salt))
                                  (lens2 (fn-hp-lens (append h (list (car evs))) salt))
                                  (starts2 (mv-nth 3 (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                  (np2 (mv-nth 4 (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                  (res (fn-hp-x-append-all (cdr evs) (+ 1 k) salt
                                                           (len (append h (list (car evs))))
                                                           (fn-hp-lens (append h (list (car evs))) salt)
                                                           (mv-nth 3 (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem))
                                                           (mv-nth 4 (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem))
                                                           (mv-nth 5 (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem))))))
                 :expand ((fn-hp-x-append-all evs k salt (len h) (fn-hp-lens h salt) starts np pgs-mem))
                 :in-theory (fn-hp-loop-theory atom)))))

(defmacro fn-hp-st (i)
  `(mv-nth ,i (fn-hp-x-append-step (car evs) salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))

(defthm fn-hp-x-append-all-keeps-verified
  (implies (and (fn-hp-held h starts np pgs-mem) (natp p) (equal (pgs-vi p pgs-mem) 2))
           (equal (pgs-vi p (mv-nth 6 (fn-hp-x-append-all evs k salt (len h) (fn-hp-lens h salt) starts np pgs-mem))) 2))
  :hints (("Goal" :induct (fn-hp-all-ind evs k h salt starts np pgs-mem)
           :in-theory (fn-hp-loop-theory fn-hp-x-append-all atom (:induction fn-hp-all-ind)))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-x-append-step-refines (ev (car evs)) (n (len h)) (lens (fn-hp-lens h salt)))
                       (:instance fn-hp-x-append-loop-keeps-verified (ev (car evs)) (k 5)))
                 :expand ((fn-hp-x-append-all evs k salt (len h) (fn-hp-lens h salt) starts np pgs-mem))
                 :in-theory (fn-hp-loop-theory atom fn-hp-x-append-step)))))

(defthm fn-hp-x-append-all-dirty-verified
  (implies (and (fn-hp-held h starts np pgs-mem)
                (fn-hp-newly-dirty p (mv-nth 6 (fn-hp-x-append-all evs k salt (len h) (fn-hp-lens h salt) starts np pgs-mem))
                                   pgs-mem))
           (equal (pgs-vi p (mv-nth 6 (fn-hp-x-append-all evs k salt (len h) (fn-hp-lens h salt) starts np pgs-mem))) 2))
  :hints (("Goal" :induct (fn-hp-all-ind evs k h salt starts np pgs-mem)
           :in-theory (fn-hp-loop-theory fn-hp-x-append-all atom (:induction fn-hp-all-ind)))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-x-append-step-refines (ev (car evs)) (n (len h)) (lens (fn-hp-lens h salt)))
                       (:instance fn-hp-x-append-all-keeps-verified (evs (cdr evs)) (k (+ 1 k)) (h (append h (list (car evs))))
                                  (starts (fn-hp-st 3)) (np (fn-hp-st 4)) (pgs-mem (fn-hp-st 5))))
                 :expand ((fn-hp-x-append-all evs k salt (len h) (fn-hp-lens h salt) starts np pgs-mem))
                 :in-theory (fn-hp-loop-theory atom)))))

(local (defthm fn-hp-len-pos-when-consp (implies (consp x) (< 0 (len x))) :rule-classes nil))

(defthm fn-hp-all-post-0-unfolds
  (implies (fn-hp-all-post h evs salt 0 lens starts np res)
           (let* ((v (mv-nth 0 res)) (j (mv-nth 1 res)) (n2 (mv-nth 2 res)) (lens2 (mv-nth 3 res))
                  (starts2 (mv-nth 4 res)) (np2 (mv-nth 5 res)) (mem2 (mv-nth 6 res))
                  (h2 (append h (take j evs))))
             (and (natp j) (<= j (len evs))
                  (implies (equal v :ok) (equal j (len evs)))
                  (not (equal (car v) :grow))
                  (fn-hp-okp h2 salt)
                  (equal n2 (len h2)) (equal lens2 (fn-hp-lens h2 salt))
                  (fn-hp-starts-okp starts2)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h2 salt starts2 np2))
                  (implies (and (equal v :ok) (or (consp evs) (adt-placement-ok starts lens np)))
                           (adt-placement-ok starts2 lens2 np2)))))
  :hints (("Goal" :use ((:instance fn-hp-len-pos-when-consp (x evs)))
           :in-theory (e/d (fn-hp-all-post) (fn-hp-okp fn-hp-lens fn-hp-piw adt-placement-ok fn-hp-vhold
                                             take append fn-hp-starts-okp)))))

; KEYSTONE (the import loop): over any page store state whose verified
; pages hold the history H's image placed at STARTS in NP pages, the
; import of EVS appends a prefix of EVS -- J = K2 events, all of them when
; it answers :ok -- and leaves the store's verified pages holding the
; image of H followed by those J events at the answered placement, answers
; that history's header, never answers :grow, and every page it newly
; marks dirty is verified.
(defthm fn-hp-x-append-all-refines
  (implies (and (fn-hp-okp h salt)
                (equal n (len h)) (equal lens (fn-hp-lens h salt))
                (fn-hp-starts-okp starts)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))
           (let* ((res (fn-hp-x-append-all evs 0 salt n lens starts np pgs-mem))
                  (v (mv-nth 0 res)) (j (mv-nth 1 res)) (n2 (mv-nth 2 res)) (lens2 (mv-nth 3 res))
                  (starts2 (mv-nth 4 res)) (np2 (mv-nth 5 res)) (mem2 (mv-nth 6 res))
                  (h2 (append h (take j evs))))
             (and (natp j) (<= j (len evs))
                  (implies (equal v :ok) (equal j (len evs)))
                  (not (equal (car v) :grow))
                  (fn-hp-okp h2 salt)
                  (equal n2 (len h2)) (equal lens2 (fn-hp-lens h2 salt))
                  (fn-hp-starts-okp starts2)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h2 salt starts2 np2))
                  (implies (and (equal v :ok) (or (consp evs) (adt-placement-ok starts lens np)))
                           (adt-placement-ok starts2 lens2 np2))
                  (implies (and (natp p) (equal (nth p (nth *pgs-di* mem2)) 1)
                                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
                           (equal (pgs-vi p mem2) 2)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-all-post (k 0))
                 (:instance fn-hp-x-append-all-dirty-verified (k 0))
                 (:instance fn-hp-all-post-0-unfolds (lens (fn-hp-lens h salt))
                            (res (fn-hp-x-append-all evs 0 salt (len h) (fn-hp-lens h salt) starts np pgs-mem))))
           :in-theory (union-theories '(natp) (theory 'minimal-theory)))))
