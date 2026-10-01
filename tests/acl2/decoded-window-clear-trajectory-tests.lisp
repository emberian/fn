(in-package "ACL2")
(include-book "../../books/decoded-window-clear-trajectory")
(include-book "../../books/decoded-worker-controller")

(defun-nx pwy-clear-test-case (corrupt)
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (input '(115 116 28 177 0 0)) (st (fn-zin-set 7 6 (car init)))
        (first (fn-zin-loop 5 0 6 128 st input (mv-nth 1 init) (mv-nth 2 init) nil))
        (prefix (if corrupt '(65 . 66) (mv-nth 6 first)))
        (b (if corrupt 0 4096))
        (r (fn-zin-loop b (mv-nth 2 first) 6 (nfix (- 128 (len prefix)))
                       (mv-nth 3 first) input (mv-nth 4 first) (mv-nth 5 first) nil))
        (whole (fn-zin-loop b (mv-nth 2 first) 6 128 (mv-nth 3 first) input
                           (mv-nth 4 first) (mv-nth 5 first) prefix)))
  (list first prefix whole
   (list (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r)
         (mv-nth 4 r) (mv-nth 5 r) (append prefix (mv-nth 6 r))))))

; Generic logical LOOP API witness, not fixed-1024 controller reachability.
(local
 (defthm pwy-actual-partial-yield-cleared-prefix-positive
  (let* ((c (pwy-clear-test-case nil)) (first (car c)) (prefix (cadr c)))
   (and (true-listp prefix) (equal (car first) :yield) (< 0 (len prefix))
        (equal (caddr c) (cadddr c)) (equal (car (caddr c)) :full)
        (equal (len (mv-nth 6 (caddr c))) 128)))
  :rule-classes nil))

; Corrupted logical prefix, not an installed concrete output buffer.
(local
 (defthm pwy-corrupted-prefix-properness-removal
  (let* ((c (pwy-clear-test-case t)) (prefix (cadr c)))
   (and (not (true-listp prefix)) (not (equal (caddr c) (cadddr c)))))
  :rule-classes nil))

(defun-nx pwy-clear-fixed-window-case (corrupt)
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (input '(115 116 28 177 0 0)) (st (fn-zin-set 7 6 (car init)))
        (first (fn-zin-loop 1024 0 6 64 st input (mv-nth 1 init) (mv-nth 2 init) nil))
        (prefix (if corrupt '(65 . 66) (mv-nth 6 first)))
        (b (if corrupt 0 1024))
        (r (fn-zin-loop b (mv-nth 2 first) 6 (nfix (- 128 (len prefix)))
                       (mv-nth 3 first) input (mv-nth 4 first) (mv-nth 5 first) nil))
        (whole (fn-zin-loop b (mv-nth 2 first) 6 128 (mv-nth 3 first) input
                           (mv-nth 4 first) (mv-nth 5 first) prefix)))
  (list first prefix whole
   (list (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r)
         (mv-nth 4 r) (mv-nth 5 r) (append prefix (mv-nth 6 r))))))

; Generic logical LOOP API witness, not fixed-1024 controller reachability.
(local
 (defthm pwy-actual-fixed-quantum-cleared-window-positive
  (let* ((c (pwy-clear-fixed-window-case nil)) (first (car c)) (prefix (cadr c)))
   (and (true-listp prefix) (equal (car first) :full)
        (equal (len prefix) 64) (equal (caddr c) (cadddr c))
        (equal (car (caddr c)) :full)
        (equal (len (mv-nth 6 (caddr c))) 128)))
  :rule-classes nil))

(defun-nx pwy-stored-clear-fixed-case ()
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (input '(115 116 28 177 0 0))
        (first (fn-pzw-stored-chunk 1024 4096 0 6 6 251
                  (car init) input (mv-nth 1 init) (mv-nth 2 init) nil))
        (prefix (mv-nth 6 first))
        (st (mv-nth 3 first))
        (credited (fn-zin-set 7 (+ 6 (fn-zin-tin st)) st))
        (room (fn-pzw-room 251 (fn-zin-tout credited)))
        (r (fn-pzw-stored-chunk 1024 4096 (mv-nth 2 first) 6 6 251
                  st input (mv-nth 4 first) (mv-nth 5 first) prefix))
        (whole (fn-zin-feed (fn-pzw-quantum 1024 4096) credited
                  (mv-nth 2 first) 6 (+ (nfix room) (len prefix)) input
                  (mv-nth 4 first) (mv-nth 5 first) prefix)))
  (list first prefix whole
    (list (car r) (mv-nth 1 r) (mv-nth 2 r)
          (fn-zin-set 7 (+ 6 (fn-zin-tin (mv-nth 3 r))) (mv-nth 3 r))
          (mv-nth 4 r) (mv-nth 5 r) (append prefix (mv-nth 6 r))))))

(local
 (defthm pwy-actual-stored-fixed-window-complete-prefix-positive
  (let* ((c (pwy-stored-clear-fixed-case)) (first (car c)) (prefix (cadr c)))
   (and (true-listp prefix) (equal (car first) :full) (equal (len prefix) 64)
        (equal (caddr c) (cadddr c)) (equal (car (caddr c)) :full)
        (equal (len (mv-nth 6 (caddr c))) 128)))
  :rule-classes nil))
(defun-nx pwy-multi-message () '(115 116 28 177 0 0))
(defun-nx pwy-multi-token ()
 (list :decoded-window 23 7 100 6 100 6 128
       (fn-bch-pack (fn-blake3 (pwy-multi-message))) 251 0))
(defun-nx pwy-multi-assigned ()
 (let* ((c (create-fn-pww-carry))
        (c (update-fn-pww-token (pwy-multi-token) c))
        (c (update-fn-pww-phase :assigned c))
        (c (update-fn-pww-borrow-phase :owned c))
        (c (update-fn-pww-root '(logical-captured-fixture) c)))
  (update-fn-pww-source-incarnation 47 c)))
(defun-nx pwy-multi-begin ()
 (fn-dwc-begin (pwy-multi-token) (pwy-multi-assigned)
               (create-pgs-digest-state) (create-fn-zin-st) nil nil nil))
(defun-nx pwy-multi-first-one ()
 (let ((b (pwy-multi-begin)))
  (fn-dwc-one (pwy-multi-token) (nth 1 b) nil (nth 2 b)
              (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (create-fn-ew-buffer))))
(defun-nx pwy-multi-issued-read ()
 (let ((r (pwy-multi-first-one)))
  (fn-dwc-one (pwy-multi-token) (nth 2 r) (nth 3 r) (nth 4 r)
              (nth 5 r) (nth 6 r) (nth 7 r) (nth 8 r) (nth 9 r))))
(defun-nx pwy-multi-codec-current ()
 (let* ((s (pwy-multi-issued-read))
        (r (fn-dwc-read-observation (pwy-multi-token)
             (fn-pww-action-revision (nth 2 s)) :ok (nth 2 s)
             (pwy-multi-message) (nth 4 s) (nth 9 s))))
  (list :fixture nil (nth 1 r) (nth 2 r) (nth 3 r)
        (nth 5 s) (nth 6 s) (nth 7 s) (nth 8 s) (nth 4 r))))
(defun-nx pwy-multi-codec-one ()
 (let ((r (pwy-multi-codec-current)))
  (fn-dwc-one (pwy-multi-token) (nth 2 r) (nth 3 r) (nth 4 r)
              (nth 5 r) (nth 6 r) (nth 7 r) (nth 8 r) (nth 9 r))))
(defun-nx pwy-multi-next (r)
 (fn-dwc-one (pwy-multi-token) (nth 2 r) (nth 3 r) (nth 4 r)
              (nth 5 r) (nth 6 r) (nth 7 r) (nth 8 r) (nth 9 r)))

(local (defthm pwy-multi-four-codec-selected-canonical-positive
 (let* ((r1 (pwy-multi-codec-one)) (r2 (pwy-multi-next r1))
        (r3 (pwy-multi-next r2)) (r4 (pwy-multi-next r3))
        (canonical (fn-pzd-decode nil (pwy-multi-message) 251)))
  (and (equal (car canonical) :ok)
       (equal (fn-zin-tout (nth 5 r1)) 64)
       (equal (fn-zin-tout (nth 5 r2)) 128)
       (equal (fn-zin-tout (nth 5 r3)) 192)
       (equal (fn-zin-tout (nth 5 r4)) 251)
       (equal (take 123 (nth 0 (nth 9 r4))) (nthcdr 128 (cadr canonical)))))
 :rule-classes nil))
(defun-nx pwy-multi-trailer-issued ()
 (let* ((r1 (pwy-multi-codec-one)) (r2 (pwy-multi-next r1))
        (r3 (pwy-multi-next r2)) (r4 (pwy-multi-next r3))
        (h1 (pwy-multi-next r4)) (h2 (pwy-multi-next h1)))
  (pwy-multi-next h2)))
(local
 (defthm pwy-multi-authenticated-publication-canonical-positive
  (let* ((s (pwy-multi-trailer-issued)) (c (nth 2 s))
         (r (fn-dwc-read-observation (pwy-multi-token)
              (fn-pww-action-revision c) :ok c
              (fn-blake3 (pwy-multi-message)) (nth 4 s) (nth 9 s)))
         (canonical (fn-pzd-decode nil (pwy-multi-message) 251)))
   (and (equal (car s) :read)
        (eq (fn-pww-phase c) :running) (eq (fn-pww-borrow-phase c) :owned)
        (equal (fn-pww-token c) (pwy-multi-token))
        (equal (car canonical) :ok)
        (equal (nth 4 r) (nth 9 s))
        (equal (take 123 (nth 0 (nth 4 r))) (nthcdr 128 (cadr canonical)))
        (fn-ewz-publication (fn-pww-controller (nth 1 r)))))
  :rule-classes nil))

; Corrupted logical prefix; no served concrete output representation implied.
(defun-nx pwy-stored-clear-improper-case ()
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (prefix '(65 . 66)) (input '(115 116 28 177 0 0))
        (st (car init)) (credited (fn-zin-set 7 6 st))
        (room (fn-pzw-room 251 (fn-zin-tout credited)))
        (r (fn-pzw-stored-chunk 0 4096 0 6 6 251 st input
               (mv-nth 1 init) (mv-nth 2 init) nil))
        (whole (fn-zin-feed (fn-pzw-quantum 0 4096) credited 0 6
                   (+ (nfix room) (len prefix)) input
                   (mv-nth 1 init) (mv-nth 2 init) prefix)))
  (list prefix whole
    (list (car r) (mv-nth 1 r) (mv-nth 2 r)
          (fn-zin-set 7 (+ 6 (fn-zin-tin (mv-nth 3 r))) (mv-nth 3 r))
          (mv-nth 4 r) (mv-nth 5 r) (append prefix (mv-nth 6 r))))))
(local
 (defthm pwy-stored-prefix-properness-corrupted-state-removal
  (let ((c (pwy-stored-clear-improper-case)))
   (and (not (true-listp (car c)))
        (not (equal (cadr c) (caddr c)))))
  :rule-classes nil))
