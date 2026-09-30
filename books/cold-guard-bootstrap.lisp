; Fixed raw-cold entry guard cache. Selected source inventory, not a theorem
; about an arbitrary image world's translated guards or compiler allocation.
(in-package "ACL2")
(include-book "cold-read-layout")

(defconst *fn-cgb-roster*
  '(fn-crw-supportedp fn-ews-begin fn-ews-effect fn-ews-tick fn-ews-read
    fn-owner-page-read-ledger fn-pwx-tokenp fn-pwx-boundp
    fn-owner-page-window-executor-acquire
    fn-owner-page-window-executor-acquire-funded
    fn-owner-page-window-executor-return
    fn-owner-page-window-executor-release fn-owner-page-window-byte
    fn-owner-page-window-byte-at fn-pwr-cold-descriptor
    fn-owner-page-window-outcome
    fn-owner-page-window-executor-cancel
    fn-owner-page-window-executor-settle-cancelled
    fn-owner-page-window-work-permittedp
    fn-owner-page-window-current-octet fn-owner-page-window-decoded-refusal))

(defun fn-cgb-roster ()
  (declare (xargs :guard t)) *fn-cgb-roster*)

(defun fn-cgb-namep (name)
  (declare (xargs :guard t))
  (and (member-eq name *fn-cgb-roster*) t))

(defun fn-cgb-capacity ()
  (declare (xargs :guard t))
  (fn-crl-table-capacity (len *fn-cgb-roster*)))

; The21-entry roster has7 unary guards on begin, six other single checks,
; and two NAT checks on current-octet; its two bound comparisons are omitted
; by the cheap-guard extractor but still occupy prewarm conjunct cells.
; Each cache spec is one cons; every check is four fields plus its list cell.
; Names/formals/recognizer kinds are image-world pointers, not copied strings.
(defun fn-cgb-retained-conses ()
  (declare (xargs :guard t)) (+ 21 (* 5 (+ 7 6 2))))

; Guard-conjunct extraction: begin's7 leaves and at most1+...+6 copied
; append cells; current-octet has4 leaves and1+2+3 append cells;
; the other19 entries each have one leaf. The roster21 cells
; are separately funded even though the immutable compiled literal can share.
(defun fn-cgb-prewarm-conses ()
  (declare (xargs :guard t)) (+ 21 4 7 1 2 3 4 5 6 4 1 2 3 19))

(defun fn-cgb-baseline-octets ()
  (declare (xargs :guard t))
  (* 2 (+ (fn-crl-table-octets (fn-cgb-capacity) nil)
          (* 16 (+ (fn-cgb-retained-conses) (fn-cgb-prewarm-conses))))))

(defun fn-cgb-arity (name)
  (declare (xargs :guard t))
  (case name
    (fn-crw-supportedp 2) (fn-ews-begin 11)
    ((fn-ews-effect fn-ews-tick) 2) (fn-ews-read 6)
    ((fn-owner-page-read-ledger fn-pwx-tokenp) 1) (fn-pwx-boundp 4)
    ((fn-owner-page-window-executor-acquire
      fn-owner-page-window-executor-acquire-funded
      fn-owner-page-window-executor-return fn-owner-page-window-executor-release) 3)
    (fn-owner-page-window-byte 6) (fn-owner-page-window-byte-at 12)
    (fn-pwr-cold-descriptor 7) (fn-owner-page-window-outcome 4)
    ((fn-owner-page-window-executor-cancel
      fn-owner-page-window-executor-settle-cancelled
      fn-owner-page-window-work-permittedp fn-owner-page-window-current-octet) 3)
    (fn-owner-page-window-decoded-refusal 0) (otherwise 0)))

(defun fn-cgb-check-count (name)
  (declare (xargs :guard t))
  (case name
    (fn-ews-begin 7) (fn-owner-page-window-current-octet 2)
    ((fn-ews-effect fn-ews-tick fn-ews-read fn-owner-page-window-byte
      fn-owner-page-window-byte-at fn-owner-page-window-outcome) 1)
    (otherwise 0)))

; Inspect exactly four fields per row and at most7 rows. These are actual
; cached guard records, not a permission to populate an unknown image cache.
(defun fn-cgb-checksp (n position beginp kind checks)
  (declare (xargs :guard (and (natp n) (natp position))))
  (if (zp n) (null checks)
    (let ((row (if (consp checks) (car checks) nil)))
      (and (consp checks) (consp row) (consp (cdr row))
           (consp (cddr row)) (consp (cdddr row)) (null (cddddr row))
           (equal (car row) (if (and beginp (equal n 1)) 9 position))
           (symbolp (cadr row))
           (equal (caddr row) kind)
           (fn-cgb-checksp (1- n) (+ 1 position) beginp kind (cdr checks))))))

(defun fn-cgb-specp (name spec)
  (declare (xargs :guard t))
  (and (fn-cgb-namep name) (consp spec)
       (equal (car spec) (fn-cgb-arity name))
       (fn-cgb-checksp
        (fn-cgb-check-count name)
        (if (member-eq name '(fn-ews-read fn-owner-page-window-byte
                             fn-owner-page-window-byte-at fn-owner-page-window-outcome)) 2 0)
        (equal name 'fn-ews-begin)
        (if (or (eq name 'fn-ews-begin) (eq name 'fn-owner-page-window-current-octet))
            'natp 'true-listp) (cdr spec))))

; Exact constructor coordinate carried by the admitted bootstrap plan.
(defun fn-cgb-planp (plan)
  (declare (xargs :guard t))
  (and (true-listp plan) (equal (len plan) 8)
       (equal (car plan) :admitted)
       (equal (nth 7 plan) (fn-cgb-capacity))
       (consp (nth 2 plan)) (natp (car (nth 2 plan)))
       (<= (fn-cgb-baseline-octets) (car (nth 2 plan)))))

(defthm fn-cgb-roster-name-is-admitted-by-definition
  (implies (member-eq name (fn-cgb-roster)) (fn-cgb-namep name))
  :rule-classes nil)

(in-theory (disable fn-cgb-roster fn-cgb-namep fn-cgb-capacity
                    fn-cgb-retained-conses fn-cgb-prewarm-conses
                    fn-cgb-baseline-octets fn-cgb-planp fn-cgb-arity
                    fn-cgb-check-count fn-cgb-checksp fn-cgb-specp))
