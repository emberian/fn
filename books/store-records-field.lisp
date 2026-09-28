; fn: the store's records field over the committed history image (lane
; arena-store-7, 2026-09-28, milestone (b1)).  Prefix fn-sfr-.
;
; The kernel state's RECORDS field (books/store-files.lisp
; fn-sf-records-field) is either
;
;   a snoc-list (books/snoc-list.lisp) of the whole history, or
;   (:hrs-based HANDLE . SNOC)  the committed history image HANDLE names
;                  (books/history-records-disk.lisp `fn-hrs-disk-history':
;                  its decode from the page file) followed by SNOC's list,
;                  the records appended since the image.
;
; `fn-sfr-list' reads the history back.  A based field does not hold the
; image's records as executed data: an unmigrated reader that asks for the
; whole list pays one decode of the image (the lazy full decode); the count
; and the records past the image are O(1) / O(distance from the newest)
; (fn-sfr-count, fn-sfr-last, fn-sfr-nth), and readers move to
; `fn-hrecs-read' one at a time.  fn-sl-of and fn-sl-snoc never build a
; based value, so a field built from a list reads that list back and the
; commit's snoc is the append, for every value.
(in-package "ACL2")
;; The decode's books come in two kinds.  The books the page store and the
;; history image need that other books above store-files also include (the
;; store codec, the frame trailer, BLAKE3, the assumptions) are included
;; first, as they are: a book above that includes one again finds its rules
;; as it always did.  The page store's and the history image's own books
;; (pagestore*, history-pages*, history-records*) are included after, and
;; their rules stay out of the theory this book exports (the last event), so
;; the books above store-files prove what they proved before.  (A theory
;; that disabled the shared books' rules too would leave them disabled in a
;; book above that includes one of them again: the include is redundant.)
(include-book "snoc-list")
(include-book "assumptions")
(include-book "history-columns")
(include-book "sha256")
(include-book "store-checkpoint-buffer")
(deftheory fn-sfr-theory-before-disk (current-theory :here))
(include-book "history-records-disk")
(deftheory fn-sfr-theory-after-disk (current-theory :here))

(defun fn-sfr-basedp (f)
  (declare (xargs :guard t))
  (and (consp f) (eq (car f) :hrs-based) (consp (cdr f)) (fn-hrs-handlep (cadr f))))

(defun fn-sfr-based (handle sfx)
  (declare (xargs :guard t))
  (list* :hrs-based handle sfx))

(defun fn-sfr-handle (f) (declare (xargs :guard t)) (if (consp f) (if (consp (cdr f)) (cadr f) nil) nil))
(defun fn-sfr-suffix (f) (declare (xargs :guard t)) (if (consp f) (if (consp (cdr f)) (cddr f) nil) nil))

(defun fn-sfr-list (f)
  (declare (xargs :guard t))
  (if (fn-sfr-basedp f)
      (append (fn-hrs-disk-history (fn-sfr-handle f)) (fn-sl-list (fn-sfr-suffix f)))
    (fn-sl-list f)))

(defun fn-sfr-snoc (f r)
  ; R appended: one cons on the suffix of a based field.
  (declare (xargs :guard t))
  (if (fn-sfr-basedp f)
      (fn-sfr-based (fn-sfr-handle f) (fn-sl-snoc (fn-sfr-suffix f) r))
    (fn-sl-snoc f r)))

(defun fn-sfr-canonp (f)
  (declare (xargs :guard t))
  (if (fn-sfr-basedp f) (fn-sl-canonp (fn-sfr-suffix f)) (fn-sl-canonp f)))

(defun fn-sfr-count (f)
  ; O(1): the image's count from the handle, the suffix's from its form.
  (declare (xargs :guard t))
  (if (fn-sfr-basedp f)
      (+ (fn-hrs-h-n (fn-sfr-handle f)) (fn-sl-count (fn-sfr-suffix f)))
    (fn-sl-count f)))

(defun fn-sfr-last (f)
  ; The newest record: the suffix's, or the image's last (a lazy decode
  ; only when nothing was appended since the image).
  (declare (xargs :guard t))
  (if (fn-sfr-basedp f)
      (if (< 0 (fn-sl-count (fn-sfr-suffix f)))
          (fn-sl-last (fn-sfr-suffix f))
        (car (last (fn-hrs-disk-history (fn-sfr-handle f)))))
    (fn-sl-last f)))

(defun fn-sfr-nth (i f)
  ; Record I, oldest 0: past the image, the suffix's (O(distance from the
  ; newest)); inside it, the image's (a lazy decode).
  (declare (xargs :guard (natp i)))
  (if (fn-sfr-basedp f)
      (let ((n (fn-hrs-h-n (fn-sfr-handle f))))
        (if (< i n)
            (nth i (fn-hrs-disk-history (fn-sfr-handle f)))
          (fn-sl-nth (- i n) (fn-sfr-suffix f))))
    (fn-sl-nth i f)))

; -----------------------------------------------------------------------------
; The representation facts, for every value.

(defthm fn-sfr-not-basedp-of-fn-sl-of
  (not (fn-sfr-basedp (fn-sl-of x)))
  :hints (("Goal" :in-theory (enable fn-sl-of))))

(defthm fn-sfr-not-basedp-of-fn-sl-snoc
  (not (fn-sfr-basedp (fn-sl-snoc h r)))
  :hints (("Goal" :in-theory (enable fn-sl-snoc fn-sl-of))))

; KEYSTONE (representation).  A field built from a list reads it back.
(defthm fn-sfr-list-of-fn-sl-of
  (equal (fn-sfr-list (fn-sl-of x)) x))

(defthm fn-sfr-canonp-of-fn-sl-of
  (fn-sfr-canonp (fn-sl-of x)))

; KEYSTONE (append).  The commit's snoc is the append, for every value.
(defthm fn-sfr-list-of-fn-sfr-snoc
  (equal (fn-sfr-list (fn-sfr-snoc f r)) (append (fn-sfr-list f) (list r))))

; Over a field built from a list, the snoc builds the appended list's field.
(defthm fn-sfr-snoc-of-fn-sl-of
  (equal (fn-sfr-snoc (fn-sl-of x) r) (fn-sl-of (append x (list r)))))

(defthm fn-sfr-canonp-of-fn-sfr-snoc
  (implies (fn-sfr-canonp f) (fn-sfr-canonp (fn-sfr-snoc f r))))

; KEYSTONE (the based field): the committed image's history, then the
; suffix; with the page file holding H's image and a clean decode
; (fn-hrs-disk-history-is-image), H then the suffix.
(defthm fn-sfr-list-of-fn-sfr-based
  (implies (fn-hrs-handlep handle)
           (equal (fn-sfr-list (fn-sfr-based handle sfx))
                  (append (fn-hrs-disk-history handle) (fn-sl-list sfx)))))

(defthm fn-sfr-list-of-fn-sfr-based-is-image
  (implies (and (fn-hrs-handlep handle) (fn-hrs-disk-holds handle h)
                (mv-nth 0 (fn-hrs-disk-decode handle)))
           (equal (fn-sfr-list (fn-sfr-based handle sfx))
                  (append h (fn-sl-list sfx))))
  :hints (("Goal" :in-theory (disable fn-hrs-disk-history fn-hrs-disk-decode fn-hrs-disk-holds))))

(defthm fn-sfr-count-is-len
  (equal (fn-sfr-count f) (len (fn-sfr-list f))))

(local
 (defthm fn-sfr-car-last-append
   (equal (car (last (append a b)))
          (if (consp b) (car (last b)) (car (last a))))))
(local
 (defthm fn-sfr-len-zero
   (equal (equal (len x) 0) (not (consp x)))))
(local
 (defthm fn-sfr-nth-append
   (implies (natp i)
            (equal (nth i (append a b))
                   (if (< i (len a)) (nth i a) (nth (- i (len a)) b))))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-sfr-last-is-last
  (equal (fn-sfr-last f) (car (last (fn-sfr-list f)))))

(defthm fn-sfr-nth-is-nth
  (implies (natp i)
           (equal (fn-sfr-nth i f) (nth i (fn-sfr-list f))))
  :hints (("Goal" :in-theory (disable fn-hrs-h-n))))

(in-theory (disable fn-sfr-basedp fn-sfr-based fn-sfr-handle fn-sfr-suffix fn-sfr-list fn-sfr-snoc
                    fn-sfr-canonp fn-sfr-count fn-sfr-last fn-sfr-nth))

; The exported theory: exactly what was enabled before the decode's books
; (their own in-theory events undone: pagestore-words disables
; fn-cbor-octet-listp, for one), with this book's rules as it left them;
; of the decode's rules, only what reading the list needs.
(in-theory (union-theories
            (theory 'fn-sfr-theory-before-disk)
            (union-theories
             (set-difference-theories (current-theory :here) (universal-theory 'fn-sfr-theory-after-disk))
             '(fn-hrs-disk-history-len fn-hrs-true-listp-disk-history
               fn-hrs-true-listp-disk-history-tp))))
