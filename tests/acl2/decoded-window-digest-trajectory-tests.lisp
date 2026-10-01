; Complete actual compressed BEGIN/READ/HASH/publication trajectory teeth.
; Logical source adapter and corrupted-state removals do not install a native holder.
(in-package "ACL2")
(include-book "../../books/decoded-window-digest-trajectory")
(defun-nx fn-pwdgt-message () (fn-pzd-stored '(65 66 67)))
(defun-nx fn-pwdgt-begin ()
 (let ((msg (fn-pwdgt-message)))
  (fn-ewz-begin 7 100 (len msg) 100 (len msg) 3 1 23 47 59
                (fn-bch-pack (fn-blake3 msg)) nil (create-pgs-digest-state)
                (create-fn-zin-st) nil nil nil)))
(defun-nx fn-pwdgt-first-read ()
 (let ((b (fn-pwdgt-begin))) (fn-ewz-hash-tick (car b) (cadr b) (nth 2 b))))
(defun-nx fn-pwdgt-consumed (input bad-cv)
 (let* ((f (fn-pwdgt-first-read)) (z (cadr f))
        (h (if bad-cv (update-pgs-dc-cv '(0 0 0 0 0 0 0 0) (nth 2 f)) (nth 2 f))))
  (fn-ewz-read (fn-ewz-effect z h) :ok z input h (create-fn-ew-buffer))))
(defun-nx fn-pwdgt-before-hash ()
 (let* ((b (fn-pwdgt-begin)) (r (fn-pwdgt-consumed (fn-pwdgt-message) nil))
        (c (fn-ewz-codec-tick (cadr r) (fn-pwdgt-message)
                            (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 3 r))))
  (list (cadr c) (nth 2 r) (nth 6 c) (nth 2 c))))
(defun-nx fn-pwdgt-ready ()
 (let* ((b (fn-pwdgt-before-hash))
        (h1 (fn-ewz-hash-tick (car b) (cadr b) (nth 3 b)))
        (h2 (fn-ewz-hash-tick (cadr h1) (nth 2 h1) (nth 3 b))))
  (list (cadr h2) (nth 2 h2) (nth 2 b) (nth 3 b))))

(local (defthm fn-pwdgt-begin-positive
 (let* ((msg (fn-pwdgt-message)) (b (fn-pwdgt-begin)))
 (and (natp 0) (<= 0 63) (fn-b3-octet-listp msg) (equal (len msg) 8)
      (<= (pgs-dcb-word-count 8) (* 128 (expt 2 0)))
      (pgs-dcs-invariantp 0 8 msg (cadr b)) (equal (nth 0 (car b)) :scan)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-read-positive
 (let* ((msg (fn-pwdgt-message)) (f (fn-pwdgt-first-read)) (z (cadr f)) (h (nth 2 f))
       (r (fn-pwdgt-consumed msg nil)))
 (and (pgs-dcs-invariantp 0 (nth 3 (nth 1 z)) msg h)
      (implies (equal (nth 0 (nth 1 z)) :scan)
               (equal msg (fn-shr-win (nth 7 (nth 1 z)) (fn-ewp-demand (nth 1 z)) msg)))
      (pgs-dcs-invariantp 0 (nth 3 (nth 1 (cadr r))) msg (nth 2 r))
      (equal (car r) :continue) (equal (car (cadr r)) :codec)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-hash-positive
 (let* ((msg (fn-pwdgt-message)) (b (fn-pwdgt-before-hash))
       (r (fn-ewz-hash-tick (car b) (cadr b) (nth 3 b))))
 (and (pgs-dcs-invariantp 0 (nth 3 (nth 1 (car b))) msg (cadr b))
      (pgs-dcs-invariantp 0 (nth 3 (nth 1 (cadr r))) msg (nth 2 r))
      (equal (car (car b)) :decoded) (equal (pgs-dc-mode (cadr b)) :return)
      (equal (pgs-dc-mode (nth 2 r)) :root)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-publication-positive
 (let* ((msg (fn-pwdgt-message)) (b (fn-pwdgt-ready)) (z (car b)) (h (cadr b))
       (input (fn-blake3 msg))
       (r (fn-ewz-read (fn-ewz-effect z h) :ok z input h (nth 2 b))))
 (and (pgs-dcs-invariantp 0 (nth 3 (nth 1 z)) msg h)
      (not (fn-ewz-publication z)) (fn-ewz-publication (cadr r))
      (equal (fn-ews-read-trailer 32 0 input) (fn-blake3 msg))
      (equal (nth 6 (nth 1 z)) (fn-bch-pack (fn-blake3 msg)))
      (equal (fn-zin-tout (nth 3 b)) 3)
      (equal (take 2 (nth 0 (nth 3 r))) '(66 67))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-read-source-removal
 (let* ((msg (fn-pwdgt-message)) (f (fn-pwdgt-first-read)) (z (cadr f)) (h (nth 2 f))
       (input (update-nth 7 68 msg)) (r (fn-pwdgt-consumed input nil)))
 (and (pgs-dcs-invariantp 0 (nth 3 (nth 1 z)) msg h)
      (not (implies (equal (nth 0 (nth 1 z)) :scan)
               (equal input (fn-shr-win (nth 7 (nth 1 z)) (fn-ewp-demand (nth 1 z)) msg))))
      (not (pgs-dcs-invariantp 0 (nth 3 (nth 1 (cadr r))) msg (nth 2 r)))
      (equal (car r) :continue) (equal (car (cadr r)) :codec)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-read-carry-removal-corrupted-state
 (let* ((msg (fn-pwdgt-message)) (f (fn-pwdgt-first-read)) (z (cadr f))
       (h (update-pgs-dc-cv '(0 0 0 0 0 0 0 0) (nth 2 f))) (r (fn-pwdgt-consumed msg t)))
 (and (not (pgs-dcs-invariantp 0 (nth 3 (nth 1 z)) msg h))
      (implies (equal (nth 0 (nth 1 z)) :scan)
               (equal msg (fn-shr-win (nth 7 (nth 1 z)) (fn-ewp-demand (nth 1 z)) msg)))
      (not (pgs-dcs-invariantp 0 (nth 3 (nth 1 (cadr r))) msg (nth 2 r)))
      (equal (car r) :continue) (equal (car (cadr r)) :codec)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-hash-carry-removal-corrupted-state
 (let* ((msg (fn-pwdgt-message)) (b (fn-pwdgt-before-hash))
       (h (update-pgs-dc-output nil (cadr b)))
       (r (fn-ewz-hash-tick (car b) h (nth 3 b))))
 (and (not (pgs-dcs-invariantp 0 (nth 3 (nth 1 (car b))) msg h))
      (not (pgs-dcs-invariantp 0 (nth 3 (nth 1 (cadr r))) msg (nth 2 r)))
      (equal (car (car b)) :decoded) (equal (pgs-dc-mode h) :return)
      (equal (pgs-dc-mode (nth 2 r)) :root)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(defun-nx fn-pwdgt-begin-domain-checks (limit msg elen)
 (let ((b (fn-ewz-begin 7 100 elen 100 elen 3 1 23 47 59 0 nil
                       (create-pgs-digest-state) (create-fn-zin-st) nil nil nil)))
  (list (natp limit) (<= limit 63) (fn-b3-octet-listp msg) (equal (len msg) elen)
        (<= (pgs-dcb-word-count elen) (* 128 (expt 2 limit)))
        (pgs-dcs-invariantp limit elen msg (cadr b)))))

(local (defthm fn-pwdgt-begin-natural-limit-removal
 (equal (fn-pwdgt-begin-domain-checks 1/2 (fn-pwdgt-message) 8) '(nil t t t t nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-begin-supported-depth-removal
 (equal (fn-pwdgt-begin-domain-checks 64 (fn-pwdgt-message) 8) '(t nil t t t nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-begin-octet-source-removal
 (equal (fn-pwdgt-begin-domain-checks 0 (update-nth 0 300 (fn-pwdgt-message)) 8) '(t t nil t t nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-begin-source-length-removal
 (equal (fn-pwdgt-begin-domain-checks 0 (fn-pwdgt-message) 9) '(t t t nil t nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-begin-stack-support-removal
 (equal (fn-pwdgt-begin-domain-checks 0 (make-list 1025 :initial-element 9) 1025) '(t t t t nil nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-publication-private-removal
 (let* ((msg (fn-pwdgt-message)) (b (fn-pwdgt-ready)) (z0 (car b)) (h (cadr b))
       (first (fn-ewz-read (fn-ewz-effect z0 h) :ok z0 (fn-blake3 msg) h (nth 2 b)))
       (z (cadr first)) (input (make-list 32 :initial-element 0))
       (r (fn-ewz-read nil :ok z input h (nth 3 first))))
 (and (pgs-dcs-invariantp 0 (nth 3 (nth 1 z)) msg h)
      (fn-ewz-publication z) (fn-ewz-publication (cadr r))
      (not (and (equal (fn-ews-read-trailer 32 0 input) (fn-blake3 msg))
                (equal (nth 6 (nth 1 z)) (fn-bch-pack (fn-blake3 msg)))))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-publication-success-removal-bad-trailer
 (let* ((msg (fn-pwdgt-message)) (b (fn-pwdgt-ready)) (z (car b)) (h (cadr b))
       (input (make-list 32 :initial-element 0))
       (r (fn-ewz-read (fn-ewz-effect z h) :ok z input h (nth 2 b))))
 (and (pgs-dcs-invariantp 0 (nth 3 (nth 1 z)) msg h)
      (not (fn-ewz-publication z)) (not (fn-ewz-publication (cadr r)))
      (not (and (equal (fn-ews-read-trailer 32 0 input) (fn-blake3 msg))
                (equal (nth 6 (nth 1 z)) (fn-bch-pack (fn-blake3 msg)))))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))

(local (defthm fn-pwdgt-publication-carry-removal-corrupted-state
 (let* ((msg (fn-pwdgt-message)) (b (fn-pwdgt-ready)) (input (fn-b3-output-root nil))
       (plan (update-nth 6 (fn-bch-pack input) (nth 1 (car b))))
       (z (update-nth 1 plan (car b)))
       (h (update-pgs-dc-capture (fn-ews-capture plan)
            (update-pgs-dc-answer (fn-bch-pack input) (update-pgs-dc-output nil (cadr b)))))
       (r (fn-ewz-read (fn-ewz-effect z h) :ok z input h (nth 2 b))))
 (and (not (pgs-dcs-invariantp 0 (nth 3 (nth 1 z)) msg h))
      (not (fn-ewz-publication z)) (fn-ewz-publication (cadr r))
      (not (and (equal (fn-ews-read-trailer 32 0 input) (fn-blake3 msg))
                (equal (nth 6 (nth 1 z)) (fn-bch-pack (fn-blake3 msg)))))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil))
