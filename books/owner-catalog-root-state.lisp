; Catalog allocation identity, carried as one pair for the owner lifetime.
; Props (statement-first): reserve preserves a natural counter and all issued
; tokens below it; no earlier token can be reissued. A corrupt counter refuses
; without resetting. Current reserves only the initially unissued incarnation.
; Recovery and reclaim write neither this slot nor its counter.
(in-package "ACL2")
(include-book "catalog-root-incarnation")
(include-book "state-globals")

(defun fn-ocr-initial ()
  (declare (xargs :guard t))
  (cons 0 :unissued))

(defun fn-ocr-counter (r)
  (declare (xargs :guard t))
  (if (consp r) (car r) nil))

(defun fn-ocr-incarnation (r)
  (declare (xargs :guard t))
  (if (consp r) (cdr r) nil))

(defun fn-ocr-issued-belowp (issued next)
  (declare (xargs :guard t))
  (if (atom issued) (null issued)
    (and (fn-cri-tokenp (car issued))
         (natp next) (< (cadar issued) next)
         (fn-ocr-issued-belowp (cdr issued) next))))

(defun fn-ocr-invariantp (r issued)
  (declare (xargs :guard t))
  (and (consp r) (natp (car r))
       (or (eq (cdr r) :unissued)
           (and (fn-cri-tokenp (cdr r)) (< (caddr r) (car r))))
       (fn-ocr-issued-belowp issued (car r))))

(defun fn-ocr-reserve (r)
  (declare (xargs :guard t))
  (mv-let (token next) (fn-cri-reserve (fn-ocr-counter r))
    (if token (mv nil token (cons next token))
      (mv :corrupt-catalog-root-counter nil r))))

(defun fn-ocr-current (r)
  (declare (xargs :guard t))
  (let ((token (fn-ocr-incarnation r)))
    (if (eq token :unissued) (fn-ocr-reserve r)
      (if (fn-cri-tokenp token) (mv nil token r)
        (mv :corrupt-catalog-root-incarnation nil r)))))

(defthm fn-ocr-issued-belowp-monotone
  (implies (and (fn-ocr-issued-belowp issued a) (natp a) (natp b) (<= a b))
           (fn-ocr-issued-belowp issued b)))

(defthm fn-ocr-reserve-preserves-issued-invariant
  (implies (fn-ocr-invariantp r issued)
           (fn-ocr-invariantp (mv-nth 2 (fn-ocr-reserve r))
                              (cons (mv-nth 1 (fn-ocr-reserve r)) issued))))

(defthm fn-ocr-reserve-never-reuses-an-earlier-token
  (implies (and (natp (fn-ocr-counter r)) (natp earlier)
                (< earlier (fn-ocr-counter r)))
           (not (equal (mv-nth 1 (fn-ocr-reserve r))
                       (mv-nth 0 (fn-cri-reserve earlier)))))
  :hints (("Goal" :use ((:instance fn-cri-reserve-never-reuses-an-earlier-token
                                  (next (fn-ocr-counter r)))))))

; The installer frame theorems establish PRESERVED for the actual recovery
; and reclaim entries. This pure consequence makes the reset fault executable.
(defthm fn-ocr-recovery-frame-prevents-token-reuse
  (implies (and (equal recovered r)
                (natp (fn-ocr-counter r)) (natp earlier)
                (< earlier (fn-ocr-counter r)))
           (not (equal (mv-nth 1 (fn-ocr-reserve recovered))
                       (mv-nth 0 (fn-cri-reserve earlier)))))
  :hints (("Goal" :use fn-ocr-reserve-never-reuses-an-earlier-token)))

(defthm fn-ocr-corrupt-counter-refuses-without-reset
  (implies (not (natp (fn-ocr-counter r)))
           (and (equal (mv-nth 0 (fn-ocr-reserve r)) :corrupt-catalog-root-counter)
                (equal (mv-nth 1 (fn-ocr-reserve r)) nil)
                (equal (mv-nth 2 (fn-ocr-reserve r)) r))))

(defun fn-ost-catalog-root (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-catalog-root state)
      (f-get-global 'fn-owner-catalog-root state)
    (fn-ocr-initial)))

(defun fn-ost-install-catalog-root (r state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-catalog-root r state))

(defthm fn-ost-catalog-root-of-install
  (equal (fn-ost-catalog-root (fn-ost-install-catalog-root r state)) r))

(defthm fn-ost-catalog-root-of-other-global-put
  (implies (not (equal key 'fn-owner-catalog-root))
           (equal (fn-ost-catalog-root (f-put-global key v state))
                  (fn-ost-catalog-root state))))

(defthm fn-ost-install-catalog-root-frames-global-association
  (implies (not (equal key 'fn-owner-catalog-root))
           (equal (assoc-equal key (nth 2 (fn-ost-install-catalog-root r state)))
                  (assoc-equal key (nth 2 state)))))

(defthm fn-ost-install-catalog-root-preserves-state-p1
  (implies (state-p1 state)
           (state-p1 (fn-ost-install-catalog-root r state)))
  :hints (("Goal" :in-theory (disable state-p1))))

(in-theory (disable fn-ost-catalog-root fn-ost-install-catalog-root))
