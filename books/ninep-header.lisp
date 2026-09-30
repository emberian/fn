; Base9P2000 framing, Plan9 intro(5), little-endian size4/type1/tag2.
; Only seven octets are read here. Profile cap applies to a wire message,
; never to article/store size. Body allocation requires a separate issued grant.
(in-package "ACL2")
(include-book "octets-stobj")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-9p-profile-msizep (limit)
 (declare (xargs :guard t))
 (and (integerp limit) (<= 7 limit) (<= limit 4294967295)))

(defun fn-9p-header-result (size type tag begin limit)
 (declare (xargs :guard (and (natp size) (natp tag) (natp begin)) ))
 (cond ((not (fn-9p-profile-msizep limit)) (list :refused :profile-unrepresentable))
       ((< size 7) (list :refused :short-message))
       ((> size limit) (list :refused :message-too-large))
       (t (list :header type tag size (+ begin 7) (+ begin size)))))

; Logical wire reference. No input copy or list traversal runs on the host path.
(defun fn-9p-header-reference (begin end limit octets)
 (declare (xargs :guard (and (natp begin) (natp end) (<= begin end)
                             (<= end (len octets))) :verify-guards nil))
 (cond ((not (fn-9p-profile-msizep limit)) (list :refused :profile-unrepresentable))
       ((< (- end begin) 7) (list :need-header (- 7 (- end begin))))
       (t (fn-9p-header-result (fn-oct-word-at begin 4 octets)
                              (nth (+ begin 4) octets)
                              (fn-oct-word-at (+ begin 5) 2 octets) begin limit))))

; Actual native boundary. GET-WORD and GET are existing guarded concrete
; buffer exports. BEGIN/END describe the already observed buffer window.
(defun fn-9p-header-at (begin end limit fn-octets)
 (declare (xargs :stobjs fn-octets
                 :guard (and (natp begin) (natp end) (<= begin end)
                             (<= end (fn-octets-len fn-octets)))))
 (cond ((not (fn-9p-profile-msizep limit)) (list :refused :profile-unrepresentable))
       ((< (- end begin) 7) (list :need-header (- 7 (- end begin))))
       (t (fn-9p-header-result (fn-octets-get-word begin 4 fn-octets)
                              (fn-octets-get (+ begin 4) fn-octets)
                              (fn-octets-get-word (+ begin 5) 2 fn-octets)
                              begin limit))))

(defthm fn-9p-header-at-is-literal-wire-reference
 (equal (fn-9p-header-at begin end limit fn-octets)
        (fn-9p-header-reference begin end limit fn-octets))
 :hints (("Goal" :in-theory
          (e/d (fn-9p-header-at fn-9p-header-reference)
               (fn-9p-header-result fn-oct-word-at fn-octets-get-word
                fn-octets-get fn-9p-profile-msizep)))))

; A valid header carries a bounded declared end, not an assertion that its
; body has been observed. The host must wait for/fund exactly that range.
(defun fn-9p-body-action (header observed-end)
 (declare (xargs :guard t))
 (if (not (and (true-listp header) (equal (len header) 6)
               (eq (car header) :header) (natp (nth 4 header))
               (natp (nth 5 header)) (<= (nth 4 header) (nth 5 header))
               (natp observed-end)))
     (list :refused :invalid-header)
   (if (< observed-end (nth 5 header))
       (list :need-body (- (nth 5 header) observed-end))
     (list :frame (nth 1 header) (nth 2 header) (nth 4 header) (nth 5 header)))))

(defun fn-9p-prefix-action (header observed-end)
 (declare (xargs :guard t))
 (if (and (consp header) (eq (car header) :header))
     (fn-9p-body-action header observed-end)
   header))
