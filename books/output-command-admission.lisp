; Before any command factory: preview exactly the existing wire scanner's
; first framed event, classify the entire command family, and require an
; actual ACL2 tariff descriptor. This never executes a response factory.
; Unknown families/tariffs refuse in accounted mode; absent accounting
; policy retains the existing partial legacy path at its caller.
(in-package "ACL2")
(include-book "wire-scan")
(include-book "nntp-syntax")

(defconst *fn-ocap-command-families*
  '(
    ((78 69 87 78 69 87 83) . :newnews)
    ((78 69 87 71 82 79 85 80 83) . :newgroups)
    ((79 86 69 82) . :overview)
    ((88 79 86 69 82) . :overview)
    ((72 68 82) . :header-range)
    ((88 72 68 82) . :header-range)
    ((88 80 65 84) . :header-pattern)
    ((76 73 83 84) . :list)
    ((76 73 83 84 71 82 79 85 80) . :group-range)
    ((71 82 79 85 80) . :group)
    ((65 82 84 73 67 76 69) . :article)
    ((72 69 65 68) . :head)
    ((66 79 68 89) . :body)
    ((83 84 65 84) . :stat)
    ((78 69 88 84) . :neighbour)
    ((76 65 83 84) . :neighbour)
    ((67 65 80 65 66 73 76 73 84 73 69 83) . :capabilities)
    ((68 65 84 69) . :date)
    ((72 69 76 80) . :help)
    ((81 85 73 84) . :close)
    ((77 79 68 69) . :mode)
    ((65 85 84 72 73 78 70 79) . :authentication)
    ((83 84 65 82 84 84 76 83) . :tls-transition)
    ((67 79 77 80 82 69 83 83) . :compression-transition)
    ((80 79 83 84) . :post)
    ((73 72 65 86 69) . :ihave)
    ((67 72 69 67 75) . :check)
    ((84 65 75 69 84 72 73 83) . :takethis)))

(defun fn-ocap-at (n x)
  (declare (xargs :guard (natp n)))
  (if (consp x) (if (zp n) (car x) (fn-ocap-at (1- n) (cdr x))) nil))

(defun fn-ocap-tokens-family (tokens)
  (declare (xargs :guard t))
  (if (and (consp tokens) (fn-nntp-keyword-tokenp (car tokens)))
      (let ((row (assoc-equal (fn-nntp-upcase-keyword (car tokens))
                              *fn-ocap-command-families*)))
        (if row (cdr row) :extension))
    :protocol-error))

(defun fn-ocap-command-family (line)
  (declare (xargs :guard t))
  (if (fn-nntp-command-inputp line)
      (fn-ocap-tokens-family (fn-nntp-tokenize line))
    :protocol-error))

(defun fn-ocap-preview (wire start end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep wire)
                              (natp start) (natp end) (<= start end)
                              (<= end (fn-octets-len fn-octets)))
                  :verify-guards nil))
  (cond
   ((eq (fn-wire-state-mode wire) :closed)
    (list :preview end :closed nil))
   ((not (eq (fn-wire-state-mode wire) :command))
    (list :preview start :article-input nil))
   (t
    (let* ((r (fn-wire-scan wire start end fn-octets))
           (events (fn-wsp-events r))
           (event (if (consp events) (car events) nil))
           (tag (fn-ocap-at 0 event))
           (line (fn-ocap-at 1 event)))
      (if (eq tag :command)
          (let ((tokens (if (fn-nntp-command-inputp line)
                            (fn-nntp-tokenize line) nil)))
            (list :preview (fn-wsp-next r)
                  (fn-ocap-tokens-family tokens) tokens))
        (list :preview (fn-wsp-next r)
              (if events :protocol-error :partial-input) nil))))))

(verify-guards fn-ocap-preview
  :hints (("Goal" :in-theory (disable fn-wire-scan fn-wire-fast-statep))))

(defun fn-ocap-previewp (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :preview)
       (consp (cdr x)) (natp (cadr x))
       (consp (cddr x)) (keywordp (caddr x))
       (consp (cdddr x)) (null (cddddr x))))

(defun fn-ocap-tariffp (x)
  (declare (xargs :guard t))
  ; This descriptor is produced by the selected actual ACL2 footprint
  ; function, never parsed from an operator's declared per-command price.
  (and (consp x) (eq (car x) :tariff)
       (consp (cdr x)) (keywordp (cadr x))
       (consp (cddr x)) (natp (caddr x))
       (< (caddr x) 18446744073709551616)
       (null (cdddr x))))

; Current producer is explicitly unsupported. A selected family's actual
; footprint producer replaces this at the caller when its tariff is known.
(defun fn-ocap-unpriced-tariff (preview)
  (declare (xargs :guard t))
  (list :unpriced (fn-ocap-at 2 preview)))

(defun fn-ocap-admit-preview (preview tariff capacity)
  (declare (xargs :guard t))
  (cond ((not (fn-ocap-previewp preview))
         (list :refused :invalid-output-preview))
        ((not (and (fn-ocap-tariffp tariff)
                   (eq (fn-ocap-at 2 preview) (fn-ocap-at 1 tariff))))
         (list :refused :unpriced-output-family (fn-ocap-at 2 preview)))
        ((not (and (natp capacity) (< capacity 18446744073709551616)
                   (<= (fn-ocap-at 2 tariff) capacity)))
         (list :refused :output-tariff-unaffordable (fn-ocap-at 2 preview)))
        (t (list :hold (fn-ocap-at 1 preview) (fn-ocap-at 2 preview)))))

(defthm fn-ocap-held-prefix-has-matching-funded-tariff
  (implies (equal (fn-ocap-at 0 (fn-ocap-admit-preview preview tariff capacity)) :hold)
           (and (fn-ocap-previewp preview)
                (fn-ocap-tariffp tariff)
                (equal (fn-ocap-at 2 preview) (fn-ocap-at 1 tariff))
                (natp capacity)
                (<= (fn-ocap-at 2 tariff) capacity)
                (equal (fn-ocap-at 1 (fn-ocap-admit-preview preview tariff capacity))
                       (fn-ocap-at 1 preview)))))

(local
 (defthm fn-ocap-scan-next-closed-range
   (implies (and (natp start) (natp end) (<= start end))
            (and (<= start (fn-wsp-next (fn-wire-scan wire start end fn-octets)))
                 (<= (fn-wsp-next (fn-wire-scan wire start end fn-octets)) end)))
   :hints (("Goal" :cases ((equal start end))
            :use ((:instance fn-wire-scan-next-bounds (i start) (wire-state wire)))
            :in-theory (e/d (fn-wire-scan) (fn-wire-scan-is-span-fold))))))

(defthm fn-ocap-preview-keeps-input-prefix-bounds
  (implies (and (natp start) (<= start end))
           (and (<= start (fn-ocap-at 1 (fn-ocap-preview wire start end fn-octets)))
                (<= (fn-ocap-at 1 (fn-ocap-preview wire start end fn-octets)) end)))
  :hints (("Goal" :cases ((natp end))
           :use fn-ocap-scan-next-closed-range
           :in-theory (e/d (fn-ocap-preview fn-ocap-at fn-wire-scan)
                           (fn-wire-fast-statep fn-wire-scan-is-span-fold
                            fn-ocap-tokens-family fn-ocap-scan-next-closed-range)))))
