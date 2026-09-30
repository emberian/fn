; Five current-format region buffers. POOL uses fn-hpb; four congruent
; column states reuse its guard-verified operations and exact prefix theorem.
(in-package "ACL2")
(include-book "history-page-buffer")

(defstobj fn-hpq0
  (fn-hpq0-w :type (array (unsigned-byte 64) (2048)) :initially 0)
  (fn-hpq0-used :type (integer 0 2048) :initially 0)
  (fn-hpq0-epoch :type t :initially nil)
  (fn-hpq0-lease :type t :initially nil)
  :congruent-to fn-hpb)

(defstobj fn-hpq1
  (fn-hpq1-w :type (array (unsigned-byte 64) (2048)) :initially 0)
  (fn-hpq1-used :type (integer 0 2048) :initially 0)
  (fn-hpq1-epoch :type t :initially nil)
  (fn-hpq1-lease :type t :initially nil)
  :congruent-to fn-hpb)

(defstobj fn-hpq2
  (fn-hpq2-w :type (array (unsigned-byte 64) (2048)) :initially 0)
  (fn-hpq2-used :type (integer 0 2048) :initially 0)
  (fn-hpq2-epoch :type t :initially nil)
  (fn-hpq2-lease :type t :initially nil)
  :congruent-to fn-hpb)

(defstobj fn-hpq3
  (fn-hpq3-w :type (array (unsigned-byte 64) (2048)) :initially 0)
  (fn-hpq3-used :type (integer 0 2048) :initially 0)
  (fn-hpq3-epoch :type t :initially nil)
  (fn-hpq3-lease :type t :initially nil)
  :congruent-to fn-hpb)

(defun fn-hpq-begin (epoch lease fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (let* ((fn-hpq0 (fn-hpb-begin epoch lease fn-hpq0))
         (fn-hpq1 (fn-hpb-begin epoch lease fn-hpq1))
         (fn-hpq2 (fn-hpb-begin epoch lease fn-hpq2))
         (fn-hpq3 (fn-hpb-begin epoch lease fn-hpq3))
         (fn-hpb (fn-hpb-begin epoch lease fn-hpb)))
    (mv fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))

(defun fn-hpq-put (region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                  :guard (and (natp region) (< region 5) (unsigned-byte-p 64 word))))
  (case region
    (0 (mv-let (v fn-hpq0) (fn-hpb-put word fn-hpq0)
         (mv v fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
    (1 (mv-let (v fn-hpq1) (fn-hpb-put word fn-hpq1)
         (mv v fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
    (2 (mv-let (v fn-hpq2) (fn-hpb-put word fn-hpq2)
         (mv v fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
    (3 (mv-let (v fn-hpq3) (fn-hpb-put word fn-hpq3)
         (mv v fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
    (otherwise (mv-let (v fn-hpb) (fn-hpb-put word fn-hpb)
         (mv v fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  ))

; Proof-only selection of one logical concrete state. Never executed by host.
(defun fn-hpq-model-select (region a b c d e)
  (declare (xargs :guard t :verify-guards nil))
  (case region (0 a) (1 b) (2 c) (3 d) (otherwise e)))

(defthm fn-hpq-put-selected-refines-prefix
  (let ((old (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
    (implies (and (natp region) (< region 5)
                  (natp (fn-hpb-used old)) (< (fn-hpb-used old) 2048))
             (and (equal (mv-nth 0 (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
                         :stored)
                  (equal (fn-hpb-prefix
                          (mv-nth (+ 1 region)
                                  (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                         (append (fn-hpb-prefix old) (list word))))))
  :hints (("Goal" :in-theory (disable fn-hpb-prefix fn-hpb-put fn-hpb-used))))

(defthm fn-hpq-put-frames-other-regions
  (implies (and (natp region) (< region 5) (natp other) (< other 5)
                (not (equal region other)))
           (equal (mv-nth (+ 1 other)
                          (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
                  (fn-hpq-model-select other fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  :hints (("Goal" :in-theory (disable fn-hpb-put))))

(defthm fn-hpq-put-keeps-concrete
  (implies (and (natp region) (< region 5) (unsigned-byte-p 64 word)
                (fn-hpbp fn-hpq0)
                (fn-hpbp fn-hpq1)
                (fn-hpbp fn-hpq2)
                (fn-hpbp fn-hpq3)
                (fn-hpbp fn-hpb)
)
           (and (fn-hpbp (mv-nth 1 (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                (fn-hpbp (mv-nth 2 (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                (fn-hpbp (mv-nth 3 (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                (fn-hpbp (mv-nth 4 (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                (fn-hpbp (mv-nth 5 (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))
  :hints (("Goal" :in-theory (e/d (fn-hpq-put)
                                  (fn-hpbp fn-hpb-put)))))

(defthm fn-hpq-put-selected-keeps-identities
  (implies (and (natp region) (< region 5))
           (let ((old (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
                 (new (mv-nth (+ 1 region)
                              (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))
             (and (equal (fn-hpb-epoch new) (fn-hpb-epoch old))
                  (equal (fn-hpb-lease new) (fn-hpb-lease old)))))
  :hints (("Goal" :in-theory (e/d (fn-hpq-put fn-hpq-model-select)
                                  (fn-hpb-put fn-hpb-epoch fn-hpb-lease)))))

(defthm fn-hpq-begin-establishes-empty-regions
  (and (equal (fn-hpb-prefix (mv-nth 0 (fn-hpq-begin epoch lease fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) nil)
       (equal (fn-hpb-prefix (mv-nth 1 (fn-hpq-begin epoch lease fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) nil)
       (equal (fn-hpb-prefix (mv-nth 2 (fn-hpq-begin epoch lease fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) nil)
       (equal (fn-hpb-prefix (mv-nth 3 (fn-hpq-begin epoch lease fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) nil)
       (equal (fn-hpb-prefix (mv-nth 4 (fn-hpq-begin epoch lease fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) nil))
  :hints (("Goal" :in-theory (e/d (fn-hpq-begin) (fn-hpb-prefix fn-hpb-begin)))))

(in-theory (disable fn-hpq-begin fn-hpq-put fn-hpq-model-select))
