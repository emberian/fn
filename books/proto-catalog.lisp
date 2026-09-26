; fn: the catalog prototype, an ATTACHABLE abstract stobj (wave 5, lane
; consolidation-design, 2026-09-26; gpt-6's consolidation review section 3,
; D33).
;
; The question this book answers is not "how are payloads stored" (the arena,
; books/payload-arena.lisp, answers that) but "can the tree keep ONE logical
; interface with SEVERAL executable implementations, choose the
; implementation when the image is built, and keep every certificate proved
; against the interface".  ACL2 8.6 added `attach-stobj' for exactly this:
; an abstract stobj introduced with `:attachable t' executes, in an image
; where `(attach-stobj gen impl)' preceded its introduction, with IMPL's
; foundation and :exec functions, while every theorem about it is stated
; over its :logic functions, which IMPL shares.  See :DOC attach-stobj and
; books/demos/attach-stobj/ in the ACL2 distribution.
;
; `fn-pcat' is that generic.  Its logical side is the ARENA's logical side,
; verbatim: the recognizer `fn-arena$ap' (a true list of octet lists), the
; creator `create-fn-arena$a' (nil), and the seven `fn-arena$a-*' operations
; (count, payload-len, get, payload, seal-list, seal-buffer, clear).  That is
; what makes `fn-arena' a legal attachment for it: attach-stobj requires
; the generic and the implementation to have corresponding logical
; skeletons (the same :logic functions, positionally), and the arena's
; theorems (`fn-arena-seal-keeps-sealed', `fn-arn-store-corr-of-open') are
; theorems about those same :logic functions.
;
; Its OWN foundation is the list-backed implementation: `fn-pcat$c', one
; field holding the payload list, every export a list operation.  This is
; the reference execution (what a theorem is checked against by evaluation
; in a test book, what a developer runs without the arena), and it is the
; implementation `fn-pcat' executes with when no attachment precedes it.
; books/proto-catalog-arena.lisp attaches the arena.
;
; The obligations below are the {CORRESPONDENCE}, {PRESERVED} and
; {GUARD-THM} events `defabsstobj-missing-events' prints for the generic
; over its own foundation; the abstraction relation `fn-pcat$corr' is that
; the field IS the logical value.  No skip-proofs.

(in-package "ACL2")
(include-book "payload-arena")

; -----------------------------------------------------------------------------
; The list-backed foundation.

(defstobj fn-pcat$c
  (fn-pcat$c-items :type t :initially nil)
  :inline t)

(defun fn-pcat$c-wfp (fn-pcat$c)
  (declare (xargs :stobjs fn-pcat$c))
  (fn-arn-payload-listp (fn-pcat$c-items fn-pcat$c)))

(defun fn-pcat$c-count (fn-pcat$c)
  (declare (xargs :stobjs fn-pcat$c :guard (fn-pcat$c-wfp fn-pcat$c)))
  (len (fn-pcat$c-items fn-pcat$c)))

(defun fn-pcat$c-payload-len (h fn-pcat$c)
  (declare (xargs :stobjs fn-pcat$c
                  :guard (and (fn-pcat$c-wfp fn-pcat$c)
                              (natp h) (< h (fn-pcat$c-count fn-pcat$c)))))
  (len (fn-oct-nth h (fn-pcat$c-items fn-pcat$c))))

(defun fn-pcat$c-get (h i fn-pcat$c)
  (declare (xargs :stobjs fn-pcat$c
                  :guard (and (fn-pcat$c-wfp fn-pcat$c)
                              (natp h) (< h (fn-pcat$c-count fn-pcat$c))
                              (natp i) (< i (fn-pcat$c-payload-len h fn-pcat$c)))))
  (fn-oct-nth i (fn-oct-nth h (fn-pcat$c-items fn-pcat$c))))

(defun fn-pcat$c-payload (h fn-pcat$c)
  (declare (xargs :stobjs fn-pcat$c
                  :guard (and (fn-pcat$c-wfp fn-pcat$c)
                              (natp h) (< h (fn-pcat$c-count fn-pcat$c)))))
  (fn-oct-nth h (fn-pcat$c-items fn-pcat$c)))

(defun fn-pcat$c-seal-list (xs fn-pcat$c)
  (declare (xargs :stobjs fn-pcat$c
                  :guard (and (fn-pcat$c-wfp fn-pcat$c) (fn-cbor-octet-listp xs))))
  (update-fn-pcat$c-items (fn-oct-snoc (fn-pcat$c-items fn-pcat$c) xs) fn-pcat$c))

(defun fn-pcat$c-seal-buffer (fn-octets fn-pcat$c)
  (declare (xargs :stobjs (fn-octets fn-pcat$c) :guard (fn-pcat$c-wfp fn-pcat$c)))
  (update-fn-pcat$c-items (fn-oct-snoc (fn-pcat$c-items fn-pcat$c) (fn-octets-list fn-octets))
                          fn-pcat$c))

(defun fn-pcat$c-clear (fn-pcat$c)
  (declare (xargs :stobjs fn-pcat$c))
  (update-fn-pcat$c-items nil fn-pcat$c))

; -----------------------------------------------------------------------------
; The abstraction relation: the field is the logical value.

(defun fn-pcat$corr (fn-pcat$c fn-pcat$a)
  (declare (xargs :stobjs fn-pcat$c :verify-guards nil))
  (and (fn-arn-payload-listp fn-pcat$a)
       (equal (fn-pcat$c-items fn-pcat$c) fn-pcat$a)))

; -----------------------------------------------------------------------------
; The obligations, each as `defabsstobj-missing-events' states it.

(defthm create-fn-pcat{correspondence}
  (fn-pcat$corr (create-fn-pcat$c) (create-fn-arena$a))
  :rule-classes nil)

(defthm create-fn-pcat{preserved}
  (fn-arena$ap (create-fn-arena$a))
  :rule-classes nil)

(defthm fn-pcat-count{correspondence}
  (implies (fn-pcat$corr fn-pcat$c fn-pcat)
           (equal (fn-pcat$c-count fn-pcat$c) (fn-arena$a-count fn-pcat)))
  :rule-classes nil)

(defthm fn-pcat-count{guard-thm}
  (implies (fn-pcat$corr fn-pcat$c fn-pcat)
           (fn-pcat$c-wfp fn-pcat$c))
  :rule-classes nil)

(defthm fn-pcat-payload-len{correspondence}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (natp h) (< h (fn-arena$a-count fn-pcat)))
           (equal (fn-pcat$c-payload-len h fn-pcat$c) (fn-arena$a-payload-len h fn-pcat)))
  :rule-classes nil)

(defthm fn-pcat-payload-len{guard-thm}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (natp h) (< h (fn-arena$a-count fn-pcat)))
           (and (fn-pcat$c-wfp fn-pcat$c)
                (natp h) (< h (fn-pcat$c-count fn-pcat$c))))
  :rule-classes nil)

(defthm fn-pcat-get{correspondence}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (natp h) (< h (fn-arena$a-count fn-pcat))
                (natp i) (< i (fn-arena$a-payload-len h fn-pcat)))
           (equal (fn-pcat$c-get h i fn-pcat$c) (fn-arena$a-get h i fn-pcat)))
  :rule-classes nil)

(defthm fn-pcat-get{guard-thm}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (natp h) (< h (fn-arena$a-count fn-pcat))
                (natp i) (< i (fn-arena$a-payload-len h fn-pcat)))
           (and (fn-pcat$c-wfp fn-pcat$c)
                (natp h) (< h (fn-pcat$c-count fn-pcat$c))
                (natp i) (< i (fn-pcat$c-payload-len h fn-pcat$c))))
  :rule-classes nil)

(defthm fn-pcat-payload{correspondence}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (natp h) (< h (fn-arena$a-count fn-pcat)))
           (equal (fn-pcat$c-payload h fn-pcat$c) (fn-arena$a-payload h fn-pcat)))
  :rule-classes nil)

(defthm fn-pcat-payload{guard-thm}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (natp h) (< h (fn-arena$a-count fn-pcat)))
           (and (fn-pcat$c-wfp fn-pcat$c)
                (natp h) (< h (fn-pcat$c-count fn-pcat$c))))
  :rule-classes nil)

(defthm fn-pcat-seal-list{correspondence}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (fn-cbor-octet-listp xs))
           (fn-pcat$corr (fn-pcat$c-seal-list xs fn-pcat$c)
                         (fn-arena$a-seal-list xs fn-pcat)))
  :rule-classes nil)

(defthm fn-pcat-seal-list{guard-thm}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (fn-cbor-octet-listp xs))
           (and (fn-pcat$c-wfp fn-pcat$c) (fn-cbor-octet-listp xs)))
  :rule-classes nil)

(defthm fn-pcat-seal-list{preserved}
  (implies (and (fn-arena$ap fn-pcat)
                (fn-cbor-octet-listp xs))
           (fn-arena$ap (fn-arena$a-seal-list xs fn-pcat)))
  :rule-classes nil)

(defthm fn-pcat-seal-buffer{correspondence}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (fn-octets-p fn-octets))
           (fn-pcat$corr (fn-pcat$c-seal-buffer fn-octets fn-pcat$c)
                         (fn-arena$a-seal-buffer fn-octets fn-pcat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))

(defthm fn-pcat-seal-buffer{guard-thm}
  (implies (and (fn-pcat$corr fn-pcat$c fn-pcat)
                (fn-octets-p fn-octets))
           (fn-pcat$c-wfp fn-pcat$c))
  :rule-classes nil)

(defthm fn-pcat-seal-buffer{preserved}
  (implies (and (fn-arena$ap fn-pcat)
                (fn-octets-p fn-octets))
           (fn-arena$ap (fn-arena$a-seal-buffer fn-octets fn-pcat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))

(defthm fn-pcat-clear{correspondence}
  (implies (fn-pcat$corr fn-pcat$c fn-pcat)
           (fn-pcat$corr (fn-pcat$c-clear fn-pcat$c) (fn-arena$a-clear fn-pcat)))
  :rule-classes nil)

(defthm fn-pcat-clear{preserved}
  (implies (fn-arena$ap fn-pcat)
           (fn-arena$ap (fn-arena$a-clear fn-pcat)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The generic.  The exports are the arena's, positionally, under new names;
; `:attachable t' is what lets (attach-stobj fn-pcat IMPL), evaluated before
; this book is included, replace the foundation and the :exec functions.

(defabsstobj fn-pcat
  :foundation fn-pcat$c
  :recognizer (fn-pcat-p :logic fn-arena$ap :exec fn-pcat$cp)
  :creator (create-fn-pcat :logic create-fn-arena$a :exec create-fn-pcat$c)
  :corr-fn fn-pcat$corr
  :exports ((fn-pcat-count :logic fn-arena$a-count :exec fn-pcat$c-count)
            (fn-pcat-payload-len :logic fn-arena$a-payload-len :exec fn-pcat$c-payload-len)
            (fn-pcat-get :logic fn-arena$a-get :exec fn-pcat$c-get)
            (fn-pcat-payload :logic fn-arena$a-payload :exec fn-pcat$c-payload)
            (fn-pcat-seal-list :logic fn-arena$a-seal-list :exec fn-pcat$c-seal-list
                               :protect t)
            (fn-pcat-seal-buffer :logic fn-arena$a-seal-buffer :exec fn-pcat$c-seal-buffer
                                 :protect t)
            (fn-pcat-clear :logic fn-arena$a-clear :exec fn-pcat$c-clear :protect t))
  :attachable t)

; -----------------------------------------------------------------------------
; The logical view, opened, in the same form the arena leaves its own: a
; theorem over `fn-pcat' is a theorem over the list.

(defthm fn-pcat-p-is-payload-listp
  (equal (fn-pcat-p x) (fn-arn-payload-listp x)))

(defthm fn-pcat-count-is-len
  (equal (fn-pcat-count fn-pcat) (len fn-pcat)))

(defthm fn-pcat-payload-len-is-len-nth
  (equal (fn-pcat-payload-len h fn-pcat) (len (nth h fn-pcat))))

(defthm fn-pcat-get-is-nth
  (equal (fn-pcat-get h i fn-pcat) (nth i (nth h fn-pcat))))

(defthm fn-pcat-payload-is-nth
  (equal (fn-pcat-payload h fn-pcat) (nth h fn-pcat)))

(defthm fn-pcat-seal-list-is-append
  (implies (fn-pcat-p fn-pcat)
           (equal (fn-pcat-seal-list xs fn-pcat) (append fn-pcat (list xs)))))

(defthm fn-pcat-seal-buffer-is-append
  (implies (fn-pcat-p fn-pcat)
           (equal (fn-pcat-seal-buffer fn-octets fn-pcat) (append fn-pcat (list fn-octets)))))

(defthm fn-pcat-clear-is-nil
  (equal (fn-pcat-clear fn-pcat) nil))

(in-theory (disable fn-pcat-p fn-pcat-count fn-pcat-payload-len fn-pcat-get
                    fn-pcat-payload fn-pcat-seal-list fn-pcat-seal-buffer fn-pcat-clear
                    fn-pcat-p-is-payload-listp))
