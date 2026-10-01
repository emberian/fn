(in-package "ACL2")
(include-book "../../books/extent-window-compressed")
(include-book "extent-window-stream-tests")
(include-book "deflate-inflate-vectors")

; Test-only source adapter: only the core-issued read span is supplied.
(defun ewzt-run (fuel archive z reads codec-ticks pgs-digest-state fn-octets fn-ew-buffer
                      fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :verify-guards nil :measure (nfix fuel)
                  :stobjs (pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  (let ((action (fn-ewz-next-action z pgs-digest-state)))
    (cond ((zp fuel)
           (mv (list :fuel z reads codec-ticks) pgs-digest-state fn-octets fn-ew-buffer
               fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          ((member-eq (car action) '(:ready :refused))
           (mv (list action reads codec-ticks (fn-zin-tout fn-zin-st)
                     (if (eq (car action) :ready) (ewst-output (nth 4 z) 0 fn-ew-buffer) nil))
               pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          ((eq (car action) :codec)
           (mv-let (status z fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
             (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
             (declare (ignore status))
             (ewzt-run (1- fuel) archive z reads (1+ codec-ticks)
                       pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
          ((eq (car action) :read)
           (let* ((effect (cadr action))
                  (bytes (fn-b3-firstn (nth 5 effect)
                             (fn-b3-nthcdrx (- (nth 4 effect) 100) archive)))
                  (fn-octets (fn-octets-from-list bytes fn-octets)))
             (mv-let (status z pgs-digest-state fn-ew-buffer)
               (fn-ewz-read effect :ok z fn-octets pgs-digest-state fn-ew-buffer)
               (declare (ignore status))
               (ewzt-run (1- fuel) archive z (+ reads (len bytes)) codec-ticks
                         pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
          (t
           (mv-let (status z pgs-digest-state)
             (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)
             (declare (ignore status))
             (ewzt-run (1- fuel) archive z reads codec-ticks
                       pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))))

(defun ewzt-example (msg archive poff c n offset expected)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (answer pgs-digest-state)
    (with-local-stobj fn-octets
      (mv-let (answer fn-octets pgs-digest-state)
      (with-local-stobj fn-ew-buffer
        (mv-let (answer fn-ew-buffer fn-octets pgs-digest-state)
        (with-local-stobj fn-zin-st
          (mv-let (answer fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
          (with-local-stobj fn-zin-win
            (mv-let (answer fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
            (with-local-stobj fn-zin-tab
              (mv-let (answer fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
              (with-local-stobj fn-zin-out
                (mv-let (answer fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
                  (mv-let (z pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                    (fn-ewz-begin 7 100 (len msg) (+ 100 poff) c n offset 23 47 59 expected nil
                                  pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                    (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                      (ewzt-run 100000 archive z 0 0 pgs-digest-state fn-octets fn-ew-buffer
                                fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                      (mv answer fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
                (mv answer fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
              (mv answer fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
            (mv answer fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
          (mv answer fn-ew-buffer fn-octets pgs-digest-state)))
        (mv answer fn-octets pgs-digest-state)))
      (mv answer pgs-digest-state)))
    answer)))

(assert-event
 (let* ((c '(1 3 0 252 255 65 66 67)) (msg (append '(9 8) c '(7)))
        (digest (fn-blake3 msg))
        (r (ewzt-example msg (append msg digest) 2 (len c) 3 1 (fn-bch-pack digest))))
   (and (equal (car r) '(:ready (23 47 59 :decoded 1 2)))
        (equal (cadr r) (+ (len msg) 32)) (equal (nth 3 r) 3)
        (equal (nth 4 r) '(66 67)))))
(assert-event
 (let* ((msg '(9 8 7)) (digest (fn-blake3 msg))
        (r (ewzt-example msg (append msg digest) 1 0 0 0 (fn-bch-pack digest))))
   (equal (car r) '(:ready (23 47 59 :decoded 0 0)))))
(assert-event
 (let* ((c *dzv-session-z*) (msg (append (make-list 63 :initial-element 17) c '(1 2 3)))
        (digest (fn-blake3 msg))
        (r (ewzt-example msg (append msg digest) 63 (len c) (len *dzv-session*) 3 (fn-bch-pack digest))))
   (and (equal (caar r) :ready) (equal (nth 3 r) (len *dzv-session*))
        (equal (nth 4 r) (nthcdr 3 *dzv-session*)) (equal (cadr r) (+ (len msg) 32)))))

; Valid final block followed by more than one block of compressed trailing
; bytes: decoder stops, but every protected byte is still read and hashed.
(assert-event
 (let* ((c (append '(1 3 0 252 255 65 66 67) (make-list 130 :initial-element 255)))
        (msg (append '(9 8) c '(7))) (digest (fn-blake3 msg))
        (r (ewzt-example msg (append msg digest) 2 (len c) 3 0 (fn-bch-pack digest))))
   (and (equal (car r) '(:ready (23 47 59 :decoded 0 3)))
        (equal (nth 4 r) '(65 66 67)) (equal (nth 3 r) 3)
        (equal (cadr r) (+ (len msg) 32)))))

; Window filled long before EOF: authentication corruption never publishes.
(assert-event
 (let* ((c '(1 3 0 252 255 65 66 67)) (msg (append '(9 8) c '(7)))
        (digest (fn-blake3 msg))
        (r (ewzt-example msg (append (update-nth (1- (len msg)) 6 msg) digest)
                          2 (len c) 3 0 (fn-bch-pack digest))))
   (and (equal (car r) '(:refused :hash :digest)) (equal (nth 4 r) nil))))

; Truncated, malformed, declared-length overflow and underflow are refusals.
(assert-event
 (let* ((cases '(((1) 0) ((7) 0) ((1 3 0 252 255 65 66 67) 2)
                 ((1 3 0 252 255 65 66 67) 4))))
   (and
    (equal (caar (let* ((c (caar cases)) (d (fn-blake3 c)))
                   (ewzt-example c (append c d) 0 (len c) 0 0 (fn-bch-pack d)))) :refused)
    (equal (caar (let* ((c '(7)) (d (fn-blake3 c)))
                   (ewzt-example c (append c d) 0 (len c) 0 0 (fn-bch-pack d)))) :refused)
    (equal (caar (let* ((c '(1 3 0 252 255 65 66 67)) (d (fn-blake3 c)))
                   (ewzt-example c (append c d) 0 (len c) 2 0 (fn-bch-pack d)))) :refused)
    (equal (caar (let* ((c '(1 3 0 252 255 65 66 67)) (d (fn-blake3 c)))
                   (ewzt-example c (append c d) 0 (len c) 4 0 (fn-bch-pack d)))) :refused))))

; A complete nonfinal empty stored block is the accepted sync-flush terminal.
(assert-event
 (let* ((c '(0 0 0 255 255)) (msg (append '(9) c '(8))) (d (fn-blake3 msg)))
   (equal (car (ewzt-example msg (append msg d) 1 (len c) 0 0 (fn-bch-pack d)))
          '(:ready (23 47 59 :decoded 0 0)))))

; Full 16KiB private decoded window, with fixed64 input/scratch across many
; scheduling quanta. No C/N-sized allocation occurs in the controller.
(assert-event
 (let* ((plain (make-list 16450 :initial-element 65)) (c (fn-pzd-stored plain))
        (msg (append '(9) c '(8))) (d (fn-blake3 msg))
        (r (ewzt-example msg (append msg d) 1 (len c) (len plain) 1 (fn-bch-pack d))))
   (and (equal (car r) '(:ready (23 47 59 :decoded 1 16384)))
        (equal (nth 4 r) (make-list 16384 :initial-element 65))
        (equal (cadr r) (+ (len msg) 32)))))

(defconst *ewzt-high-ratio* '(237 193 1 13 0 0 0 194 160 108 239 95 202 30 14 40 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 95 3))

(assert-event
 (let* ((c *ewzt-high-ratio*) (msg (append '(9 8 7) c '(6))) (d (fn-blake3 msg))
        (r (ewzt-example msg (append msg d) 3 (len c) 93100 92900 (fn-bch-pack d))))
   (and (equal (car r) '(:ready (23 47 59 :decoded 92900 200)))
        (equal (nth 4 r) (make-list 200 :initial-element 65))
        (< 1000 (nth 2 r)) (equal (nth 3 r) 93100)
        (equal (cadr r) (+ (len msg) 32)))))
(assert-event
 (let* ((c '(1 3 0 252 255 65 66 67)) (d (fn-blake3 c)))
   (and (equal (car (ewzt-example c (append c d) 0 (len c) 3 0 0))
               '(:refused :hash :commitment))
        (equal (car (ewzt-example c '(1 3) 0 (len c) 3 0 (fn-bch-pack d)))
               '(:refused :hash :read)))))
