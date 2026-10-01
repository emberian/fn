(in-package "ACL2")
(include-book "../../books/extent-window-stream-semantics")
(include-book "extent-window-stream-tests")

(defun-nx ewsst-begin ()
 (fn-ews-begin 7 100 3 100 3 0 23 47 59 (fn-bch-pack (fn-blake3 '(1 2 3))) (create-pgs-digest-state)))
(defun-nx ewsst-first-read ()
 (let ((r (ewsst-begin))) (fn-ews-tick (car r) (cadr r))))
(defun-nx ewsst-consumed ()
 (let* ((r (ewsst-first-read)) (s (cadr r)) (cursor (caddr r)))
  (fn-ews-read (fn-ews-effect s cursor) :ok s '(1 2 3) cursor (create-fn-ew-buffer))))

; Each positive states the full literal antecedent and conclusion.
(defthm ewsst-begin-trajectory-positive
 (let ((msg '(1 2 3)) (r (ewsst-begin)))
  (and (natp 0) (<= 0 63) (fn-b3-octet-listp msg) (equal (len msg) 3)
       (<= (pgs-dcb-word-count 3) (* 128 (expt 2 0)))
       (pgs-dcs-invariantp 0 3 msg (cadr r)) (equal (nth 0 (car r)) :scan)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil)

(defthm ewsst-canonical-block-positive
 (let* ((r (ewsst-first-read)) (s (cadr r)) (cursor (caddr r)) (msg '(1 2 3)) (input '(1 2 3)))
  (and (pgs-dcs-invariantp 0 (nth 3 s) msg cursor)
       (fn-ews-effect s cursor) (equal (nth 0 s) :scan)
       (equal input (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg))
       (pgs-dcs-blockp (fn-b3x-words 16 0 (fn-ewp-demand s) nil 0 0 input) msg cursor)
       (equal (pgs-dc-mode cursor) :chunk)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil)

(defthm ewsst-read-trajectory-positive
 (let* ((r (ewsst-first-read)) (s (cadr r)) (cursor (caddr r)) (msg '(1 2 3)) (input '(1 2 3))
        (next (ewsst-consumed)))
  (and (pgs-dcs-invariantp 0 (nth 3 s) msg cursor)
       (implies (equal (nth 0 s) :scan) (equal input (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg)))
       (pgs-dcs-invariantp 0 (nth 3 s) msg (nth 2 next))
       (equal (nth 0 next) :continue) (equal (pgs-dc-mode (nth 2 next)) :return)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil)

(defthm ewsst-tick-trajectory-positive
 (let* ((r (ewsst-begin)) (s (car r)) (cursor (cadr r)) (next (ewsst-first-read)))
  (and (pgs-dcs-invariantp 0 (nth 3 s) '(1 2 3) cursor)
       (pgs-dcs-invariantp 0 (nth 3 s) '(1 2 3) (nth 2 next))
       (equal (pgs-dc-mode cursor) :node) (equal (pgs-dc-mode (nth 2 next)) :chunk)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil)

(defthm ewsst-source-publication-positive
 (let* ((ready (ewst-three-ready)) (s (nth 1 ready)) (cursor (nth 2 ready))
        (buffer (nth 3 ready)) (msg '(1 2 3)) (input (fn-blake3 msg))
        (next (fn-ews-read (fn-ews-effect s cursor) :ok s input cursor buffer)))
  (and (pgs-dcs-invariantp 0 (nth 3 s) msg cursor)
       (not (fn-ewp-publication s)) (fn-ewp-publication (nth 1 next))
       (equal (fn-ews-read-trailer 32 0 input) (fn-blake3 msg))
       (equal (nth 6 s) (fn-bch-pack (fn-blake3 msg)))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil)

; Retain the carried semantic invariant, omit only the captured-source slice.
(defthm ewsst-read-without-source-slice-removal
 (let* ((r (ewsst-first-read)) (s (cadr r)) (cursor (caddr r)) (msg '(1 2 3)) (input '(1 2 4))
        (next (fn-ews-read (fn-ews-effect s cursor) :ok s input cursor (create-fn-ew-buffer))))
  (and (pgs-dcs-invariantp 0 (nth 3 s) msg cursor)
       (not (implies (equal (nth 0 s) :scan) (equal input (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg))))
       (not (pgs-dcs-invariantp 0 (nth 3 s) msg (nth 2 next)))
       (equal (nth 0 next) :continue)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
 :rule-classes nil)

(defun-nx ewsst-begin-domain-checks (limit msg elen)
 (let ((r (fn-ews-begin 7 100 elen 100 elen 0 23 47 59 0 (create-pgs-digest-state))))
  (list (natp limit) (<= limit 63) (fn-b3-octet-listp msg) (equal (len msg) elen)
        (<= (pgs-dcb-word-count elen) (* 128 (expt 2 limit)))
        (pgs-dcs-invariantp limit elen msg (cadr r)))))

(defthm ewsst-begin-without-natural-limit-removal
 (equal (ewsst-begin-domain-checks 1/2 '(1 2 3) 3) '(nil t t t t nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp))) :rule-classes nil)
(defthm ewsst-begin-without-supported-depth-removal
 (equal (ewsst-begin-domain-checks 64 '(1 2 3) 3) '(t nil t t t nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp))) :rule-classes nil)
(defthm ewsst-begin-without-octet-source-removal
 (equal (ewsst-begin-domain-checks 0 '(300 2 3) 3) '(t t nil t t nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp))) :rule-classes nil)
(defthm ewsst-begin-without-source-length-removal
 (equal (ewsst-begin-domain-checks 0 '(1 2 3) 4) '(t t t nil t nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp))) :rule-classes nil)
(defthm ewsst-begin-without-stack-support-removal
 (equal (ewsst-begin-domain-checks 0 (make-list 1025 :initial-element 9) 1025) '(t t t t nil nil))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp))) :rule-classes nil)

; Carried semantic evidence alone is omitted; the exact source slice stays.
(defthm ewsst-read-without-semantic-carry-corrupted-state
 (let* ((r (ewsst-first-read)) (s (cadr r))
        (cursor (update-pgs-dc-cv '(0 0 0 0 0 0 0 0) (caddr r)))
        (msg '(1 2 3)) (input '(1 2 3))
        (next (fn-ews-read (fn-ews-effect s cursor) :ok s input cursor (create-fn-ew-buffer))))
  (and (not (pgs-dcs-invariantp 0 (nth 3 s) msg cursor))
       (implies (equal (nth 0 s) :scan) (equal input (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg)))
       (not (pgs-dcs-invariantp 0 (nth 3 s) msg (nth 2 next)))
       (equal (nth 0 next) :continue)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))) :rule-classes nil)

(defthm ewsst-tick-without-semantic-carry-corrupted-state
 (let* ((r (ewsst-consumed)) (s (cadr r)) (cursor (update-pgs-dc-output nil (caddr r)))
        (next (fn-ews-tick s cursor)))
  (and (not (pgs-dcs-invariantp 0 (nth 3 s) '(1 2 3) cursor))
       (not (pgs-dcs-invariantp 0 (nth 3 s) '(1 2 3) (nth 2 next)))
       (equal (pgs-dc-mode cursor) :return) (equal (pgs-dc-mode (nth 2 next)) :root)))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))) :rule-classes nil)

(defthm ewsst-publication-without-prior-private-hypothesis-removal
 (let* ((ready (ewst-three-ready)) (s0 (nth 1 ready)) (cursor (nth 2 ready)) (buffer (nth 3 ready))
        (msg '(1 2 3)) (digest (fn-blake3 msg))
        (s (cadr (fn-ews-read (fn-ews-effect s0 cursor) :ok s0 digest cursor buffer)))
        (next (fn-ews-read nil :ok s (make-list 32 :initial-element 0) cursor buffer)))
  (and (pgs-dcs-invariantp 0 (nth 3 s) msg cursor)
       (fn-ewp-publication s) (fn-ewp-publication (nth 1 next))
       (not (and (equal (fn-ews-read-trailer 32 0 (make-list 32 :initial-element 0)) (fn-blake3 msg))
                 (equal (nth 6 s) (fn-bch-pack (fn-blake3 msg)))))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))) :rule-classes nil)

(defthm ewsst-publication-without-semantic-carry-corrupted-state
 (let* ((ready (ewst-three-ready)) (s0 (nth 1 ready)) (buffer (nth 3 ready)) (msg '(1 2 3))
        (input (fn-b3-output-root nil)) (s (update-nth 6 (fn-bch-pack input) s0))
        (cursor (update-pgs-dc-capture (fn-ews-capture s)
                 (update-pgs-dc-answer (fn-bch-pack input)
                   (update-pgs-dc-output nil (nth 2 ready)))))
        (next (fn-ews-read (fn-ews-effect s cursor) :ok s input cursor buffer)))
  (and (not (pgs-dcs-invariantp 0 (nth 3 s) msg cursor))
       (not (fn-ewp-publication s)) (fn-ewp-publication (nth 1 next))
       (not (and (equal (fn-ews-read-trailer 32 0 input) (fn-blake3 msg))
                 (equal (nth 6 s) (fn-bch-pack (fn-blake3 msg)))))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))) :rule-classes nil)

(defthm ewsst-canonical-without-source-slice-removal
 (let* ((r (ewsst-first-read)) (s (cadr r)) (cursor (caddr r)) (msg '(1 2 3)) (input '(1 2 4)))
  (and (pgs-dcs-invariantp 0 (nth 3 s) msg cursor)
       (fn-ews-effect s cursor)
       (not (equal input (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg)))
       (not (pgs-dcs-blockp (fn-b3x-words 16 0 (fn-ewp-demand s) nil 0 0 input) msg cursor))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))) :rule-classes nil)

(defthm ewsst-canonical-without-issued-effect-removal
 (let* ((r (ewsst-first-read)) (s (update-nth 7 1 (cadr r))) (cursor (caddr r))
        (msg '(1 2 3)) (input '(2 3)))
  (and (pgs-dcs-invariantp 0 (nth 3 s) msg cursor)
       (not (fn-ews-effect s cursor))
       (equal input (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg))
       (not (pgs-dcs-blockp (fn-b3x-words 16 0 (fn-ewp-demand s) nil 0 0 input) msg cursor))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                        pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                        pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))) :rule-classes nil)

(defthm ewsst-canonical-without-domain-corrupted-state
 (let* ((r (ewsst-first-read)) (s (update-nth 7 1 (cadr r)))
        (cursor (update-pgs-dc-pos 1/8 (caddr r))) (msg '(1 2 3)) (input '(2 3)))
  (and (not (pgs-dcs-invariantp 0 (nth 3 s) msg cursor))
       (fn-ews-effect s cursor)
       (equal input (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg))
       (not (pgs-dcs-blockp (fn-b3x-words 16 0 (fn-ewp-demand s) nil 0 0 input) msg cursor))))
 :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                    pgs-dcs-blockp pgs-dcr-span fn-ews-effect fn-ews-boundp
                                    pgs-dcb-next-byte-offset pgs-dcb-read-demand pgs-dc-needs-block))) :rule-classes nil)
