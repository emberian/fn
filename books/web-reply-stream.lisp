; Replay sources shared by native ARTICLE and the existing 100-number OVER
; window. Program mode; actual-source byte comparisons are not refinements.
(in-package "ACL2")
(include-book "web-article-stream")

(defun fn-wov-start ()
  (declare (xargs :verify-guards nil))
  (list (cons :kind :over) (cons :phase :status) (cons :at 0) (cons :ls 0)
        (cons :prefix nil) (cons :last nil) (cons :fs 0) (cons :cols nil)
        (cons :field 0) (cons :rows nil) (cons :status-end nil)))
(defun fn-wov-octet (o x)
  (declare (xargs :verify-guards nil))
  (let* ((at (fn-was-get :at x)) (ls (fn-was-get :ls x))
         (phase (fn-was-get :phase x)) (prefix (fn-was-get :prefix x))
         (x (fn-was-put :at (1+ at) x))
         (x (if (< (len prefix) 17) (fn-was-put :prefix (append prefix (list o)) x) x))
         (x (if (and (equal phase :rows) (equal o 9))
                (fn-was-put :fs (1+ at) (fn-was-put :field (1+ (fn-was-get :field x))
                  (if (< (fn-was-get :field x) 4)
                      (fn-was-put :cols (append (fn-was-get :cols x)
                                               (list (cons (fn-was-get :fs x) at))) x) x))) x)))
    (if (and (equal o 10) (equal (fn-was-get :last x) 13))
        (let* ((x (case phase
                    (:status (fn-was-put :status-end (max ls (1- at))
                               (fn-was-put :phase
                                 (if (equal (fn-was-code (fn-was-get :prefix x)) 224) :rows :refused) x)))
                    (:rows
                     (if (equal (fn-was-get :prefix x) '(46 13 10))
                         (fn-was-put :phase :done x)
                       (if (>= (len (fn-was-get :rows x)) *fn-wss-window*)
                           ; A generated OVER for the core's 100-number window
                           ; cannot have more rows. Fail the invariant, never
                           ; silently truncate or admit another metadata row.
                           (fn-was-put :phase :invalid x)
                         (let ((cols (if (< (fn-was-get :field x) 4)
                                         (append (fn-was-get :cols x)
                                                 (list (cons (fn-was-get :fs x) (max ls (1- at)))))
                                       (fn-was-get :cols x))))
                           (fn-was-put :rows (cons (take 4 cols) (fn-was-get :rows x)) x)))))
                    (otherwise x))))
          (fn-was-put :ls (1+ at) (fn-was-put :fs (1+ at) (fn-was-put :field 0
            (fn-was-put :cols nil (fn-was-put :prefix nil (fn-was-put :last o x)))))))
      (fn-was-put :last o x))))
(defun fn-wov-scan (i end x fn-web-in)
  (declare (xargs :verify-guards nil :stobjs fn-web-in
                  :measure (nfix (- (nfix end) (nfix i)))))
  (if (>= (nfix i) (nfix end)) x
    (fn-wov-scan (1+ (nfix i)) end (fn-wov-octet (fn-octets-get i fn-web-in) x) fn-web-in)))
(defun fn-wov-rows (group rows)
  (declare (xargs :verify-guards nil))
  (if (consp rows)
      (let* ((row (car rows)) (num (car row)))
        (fn-wr-over-row-segments group (and num (list (cons :s num)))
          (and num (list (cons :v-u num))) (cadr row) (caddr row) (cadddr row)
          (fn-wov-rows group (cdr rows)))) nil))
(defun fn-wls-start ()
  (declare (xargs :verify-guards nil))
  (list (cons :kind :list) (cons :phase :status) (cons :at 0) (cons :ls 0)
        (cons :prefix nil) (cons :last nil) (cons :bs nil) (cons :be nil)
        (cons :status-end nil)))
(defun fn-wls-octet (o x)
  (declare (xargs :verify-guards nil))
  (let* ((at (fn-was-get :at x)) (ls (fn-was-get :ls x))
         (phase (fn-was-get :phase x)) (prefix (fn-was-get :prefix x))
         (x (fn-was-put :at (1+ at) x))
         (x (if (< (len prefix) 17) (fn-was-put :prefix (append prefix (list o)) x) x)))
    (if (and (equal o 10) (equal (fn-was-get :last x) 13))
        (let ((x (case phase
                   (:status (fn-was-put :status-end (max ls (1- at))
                     (fn-was-put :bs (1+ at) (fn-was-put :phase
                       (if (equal (fn-was-code (fn-was-get :prefix x)) 215) :rows :refused) x))))
                   (:rows (if (equal (fn-was-get :prefix x) '(46 13 10))
                              (fn-was-put :be ls (fn-was-put :phase :done x)) x))
                   (otherwise x))))
          (fn-was-put :ls (1+ at) (fn-was-put :prefix nil (fn-was-put :last o x))))
      (fn-was-put :last o x))))
(defun fn-wls-scan (i end x fn-web-in)
  (declare (xargs :verify-guards nil :stobjs fn-web-in
                  :measure (nfix (- (nfix end) (nfix i)))))
  (if (>= (nfix i) (nfix end)) x
    (fn-wls-scan (1+ (nfix i)) end (fn-wls-octet (fn-octets-get i fn-web-in) x) fn-web-in)))

(defun fn-wrs-p (flow)
  (declare (xargs :verify-guards nil))
  (or (member (fn-wss-f-route flow) '(:article :groups))
      (and (equal (fn-wss-f-route flow) :group) (equal (fn-wss-f-stage flow) :over))))
(defun fn-wrs-start (flow)
  (declare (xargs :verify-guards nil))
  (if (equal (fn-wss-f-route flow) :article)
      (fn-was-start (fn-wss-s-login (fn-wss-c-session (fn-wss-f-ctx flow))))
    (if (equal (fn-wss-f-route flow) :groups) (fn-wls-start) (fn-wov-start))))
(defun fn-wrs-scan (scan fn-web-in)
  (declare (xargs :verify-guards nil :stobjs fn-web-in))
  (if (equal (fn-was-get :kind scan) :article)
      (fn-was-scan 0 (fn-octets-len fn-web-in) scan fn-web-in)
    (if (equal (fn-was-get :kind scan) :list)
        (fn-wls-scan 0 (fn-octets-len fn-web-in) scan fn-web-in)
      (fn-wov-scan 0 (fn-octets-len fn-web-in) scan fn-web-in))))
(defun fn-wrs-page (config flow scan)
  (declare (xargs :verify-guards nil))
  (if (equal (fn-was-get :kind scan) :article) (fn-was-page config flow scan)
    (let* ((ctx (fn-wss-f-ctx flow)) (session (fn-wss-c-session ctx))
           (data (fn-wss-f-data flow)) (group (fn-wrq-nth 0 data))
           (lo (nfix (fn-wrq-nth 1 data))) (low (nfix (fn-wrq-nth 2 data)))
           (ok (equal (fn-was-get :phase scan) :done))
           (listp (equal (fn-was-get :kind scan) :list))
           (title (if ok (if listp (fn-wrq-oct "Groups") group) (fn-wrq-oct "The server said no")))
           (main (if ok
                     (if listp
                         (fn-wr-groups-main-segments
                           (and (< (fn-was-get :bs scan) (fn-was-get :be scan))
                                (list (cons :v-list (cons (fn-was-get :bs scan) (fn-was-get :be scan))))))
                       (fn-wr-group-main-segments group (fn-wov-rows group (fn-was-get :rows scan))
                                                  (if (< low lo) (fn-ot-decimal-octets lo) nil)))
                   (fn-wr-outcome-main-segments :no title *fn-wss-msg-unreachable*
                     (and (fn-was-get :status-end scan)
                          (list (cons :s (cons 0 (fn-was-get :status-end scan))))) nil)))
           (segs (fn-wr-frame title (fn-wss-cfg-site config) (fn-wss-c-theme ctx)
                              (and session (fn-wss-s-login session))
                              (and session (fn-wss-s-csrf session)) main)))
      (if (equal (fn-was-get :phase scan) :invalid) (list :invalid)
        (list :respond (if ok 200 503) *fn-wss-html-fields* (fn-wss-bodyp ctx) :page-plan segs)))))

; ---------------------------------------------------------------------------
; Refused and accepted stay distinct (the reader pages' keystones).  A
; replayed reply the server refused (its status line not 211/220, 224 or 215)
; leaves the scan in :refused for every later octet, and a page renders 200
; only from a scan that reached :done; an over-full OVER window is :invalid,
; never a page.  Guard verification and the byte-level refinement of these
; scanners to fn-wss-headers / fn-wr-seq are proof-owed (planning/repair).

(defthm fn-was-get-of-put
  (implies (and key k2)
           (equal (fn-was-get key (fn-was-put k2 v x))
                  (if (equal key k2) v (fn-was-get key x)))))

(local (in-theory (disable fn-was-get fn-was-put)))

(defthm fn-was-octet-refused-stays
  (implies (equal (fn-was-get :phase x) :refused)
           (and (equal (fn-was-get :phase (fn-was-octet o x)) :refused)
                (equal (fn-was-get :kind (fn-was-octet o x)) (fn-was-get :kind x)))))
(defthm fn-wov-octet-refused-stays
  (implies (equal (fn-was-get :phase x) :refused)
           (and (equal (fn-was-get :phase (fn-wov-octet o x)) :refused)
                (equal (fn-was-get :kind (fn-wov-octet o x)) (fn-was-get :kind x)))))
(defthm fn-wls-octet-refused-stays
  (implies (equal (fn-was-get :phase x) :refused)
           (and (equal (fn-was-get :phase (fn-wls-octet o x)) :refused)
                (equal (fn-was-get :kind (fn-wls-octet o x)) (fn-was-get :kind x)))))
(local (in-theory (disable fn-was-octet fn-wov-octet fn-wls-octet)))

(defthm fn-was-scan-refused-stays
  (implies (equal (fn-was-get :phase x) :refused)
           (and (equal (fn-was-get :phase (fn-was-scan i end x fn-web-in)) :refused)
                (equal (fn-was-get :kind (fn-was-scan i end x fn-web-in)) (fn-was-get :kind x)))))
(defthm fn-wov-scan-refused-stays
  (implies (equal (fn-was-get :phase x) :refused)
           (and (equal (fn-was-get :phase (fn-wov-scan i end x fn-web-in)) :refused)
                (equal (fn-was-get :kind (fn-wov-scan i end x fn-web-in)) (fn-was-get :kind x)))))
(defthm fn-wls-scan-refused-stays
  (implies (equal (fn-was-get :phase x) :refused)
           (and (equal (fn-was-get :phase (fn-wls-scan i end x fn-web-in)) :refused)
                (equal (fn-was-get :kind (fn-wls-scan i end x fn-web-in)) (fn-was-get :kind x)))))
(defthm fn-wrs-scan-refused-stays
  (implies (equal (fn-was-get :phase x) :refused)
           (and (equal (fn-was-get :phase (fn-wrs-scan x fn-web-in)) :refused)
                (equal (fn-was-get :kind (fn-wrs-scan x fn-web-in)) (fn-was-get :kind x)))))
(defthm fn-wrs-page-accepted-only-when-done
  (implies (equal (cadr (fn-wrs-page config flow scan)) 200)
           (equal (fn-was-get :phase scan) :done)))
(defthm fn-wrs-page-invalid-exactly
  (equal (equal (fn-wrs-page config flow scan) '(:invalid))
         (and (not (equal (fn-was-get :kind scan) :article))
              (equal (fn-was-get :phase scan) :invalid))))
(defthm fn-wrs-refused-reply-is-never-accepted
  (implies (equal (fn-was-get :phase scan) :refused)
           (and (equal (car (fn-wrs-page config flow (fn-wrs-scan scan fn-web-in))) :respond)
                (not (equal (cadr (fn-wrs-page config flow (fn-wrs-scan scan fn-web-in))) 200)))))
