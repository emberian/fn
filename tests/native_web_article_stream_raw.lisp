(load "tests/native_web_page_cursor_raw.lisp")
(in-package "ACL2")
(defun assoc-eq (key xs) (assoc key xs :test #'eq))
(defun fn-wm (s) (cons :m (fn-wrq-oct s)))
(defun fn-wt (s) (cons :t (fn-wrq-oct s)))
(defun fn-wrq-rev (x acc) (revappend x acc))
(defun fn-wrq-rev-down (x acc) (revappend (mapcar #'fn-ot-downcase-octet x) acc))
(load-page-forms "books/web-request.lisp" '(fn-wrq-shortp fn-web-req-method))
(defun fn-oct-line-end (at in)
  (loop for i from at below (fn-octets-len in)
        when (= (fn-octets-get i in) 10) return (1+ i)
        finally (return (fn-octets-len in))))
(load-page-forms "books/web-render.lisp"
 '(fn-wr-octets-only fn-wr-txt fn-wr-url fn-wr-span fn-wr-span-or fn-wr-wspan fn-wr-wspan-or
   fn-wr-theme-attr fn-wr-theme-button fn-wr-nav fn-wr-frame fn-wr-note
   fn-wr-header-line fn-wr-wheader-line fn-wr-article-main-segments fn-wr-article-main
   fn-wr-outcome-main-segments fn-wr-outcome-main))
(load-page-forms "books/web-session.lisp"
 '(*fn-wss-shown-fields* *fn-wss-html-fields* fn-wss-field-index fn-wss-put-span fn-wss-slice
   fn-wss-colon fn-wss-content-end fn-wss-skip-ws fn-wss-continued fn-wss-headers fn-wss-prefix-at
   fn-wss-span-has fn-wss-span-slice fn-wss-spanp fn-wss-article-view
   *fn-wss-window* *fn-wss-msg-unreachable* fn-wss-f-stage fn-wss-f-route fn-wss-f-ctx fn-wss-f-data fn-wss-c-session fn-wss-c-request fn-wss-c-theme
   fn-wss-s-login fn-wss-s-csrf fn-wss-cfg-site fn-wss-bodyp))
(load-page-forms "books/web-list-stream.lisp")
(load-page-forms "books/web-article-stream.lisp")
(load-page-forms "books/web-reply-stream.lisp")
(load-page-forms "host/web-host.lisp"
 '(fn-web-host-article-p fn-web-host-article-start fn-web-host-article-scan fn-web-host-article-page
   fn-web-host-window-page-step fn-web-host-replay-slice fn-web-host-replay-forward-p
   fn-web-host-stream-p fn-web-host-stream-start fn-web-host-stream-scan fn-web-host-stream-page))
(defun article-octets (lines)
  (loop for line in lines append (append (fn-wrq-oct line) '(13 10))))
(defun article-scan-chunks (xs width login)
  (loop with scan = (fn-was-start login) with in = (create-fn-octets$c)
        for at from 0 below (length xs) by width do
        (fnn-web-fill in (fnn-octets (subseq xs at (min (length xs) (+ at width)))))
        (setf scan (fn-web-host-article-scan scan in))
        finally (return scan)))
(defun virtual-page (segs xs fuel)
  (loop with in = (create-fn-octets$c) with cursor = (fn-wpc-cursor segs)
        with base = 0 with count = 0 with result = nil
        for rounds from 1 below 1000000 do
        (multiple-value-bind (bytes next total done need)
            (fn-wpc-window-drive fuel cursor base count t nil in)
          (setf cursor next count total result (revappend bytes result))
          (when need
            (assert (<= (- (cdr need) (car need)) 4096))
            (setf base (car need))
            (fnn-web-fill in (fnn-octets (subseq xs base (cdr need)))))
          (when done (return (values (reverse result) count))))))
; Actual native scan/replay/count/write consumer, reusable for captured
; protocol routes. The renderer adapter advances persistent plan tails only.
(defun native-stream-consumer (xs flow config reference &optional (id 41) (max-replay-rounds 150))
    (let* ((conn (fixture-conn id :render 88))
           (face (%make-fnn-web-face :service :service :config config :conns (list conn)))
           (plan (loop for at from 0 below (length xs) by 4096
                       collect (fnn-octets (subseq xs at (min (length xs) (+ at 4096))))))
           (saved-core (symbol-function 'fnn-core)) (saved-call (symbol-function 'fnn-call))
           (saved-render (symbol-function 'fnn-owner-render-next-quantum))
           (saved-unpin (symbol-function 'fnn-owner-response-unpin))
           (saved-poll (symbol-function 'fnn-owner-cold-poll))
           (pins-released 0) (observed-length nil) (peak-in 0) (replay-rounds 0) (cold-issued nil))
      (setf (fnn-web-conn-flow conn) flow (fnn-web-conn-reply-scan conn) (fn-web-host-stream-start flow)
            (fnn-web-conn-captured-plans conn) (list plan) (fnn-web-conn-plan conn) plan
            (fnn-web-conn-leased conn) t)
      (unwind-protect
        (progn
          (setf (symbol-function 'fnn-core)
            (lambda (name &rest args)
              (case name
                ((fn-web-host-article-p fn-web-host-article-start fn-web-host-article-scan
                  fn-web-host-article-page fn-web-host-replay-slice fn-web-host-replay-forward-p) (apply (symbol-function name) args))
                ((fn-web-host-stream-p fn-web-host-stream-start fn-web-host-stream-scan fn-web-host-stream-page)
                 (apply (symbol-function name) args))
                (fn-web-host-page-cursor (apply #'fn-web-host-page-cursor args))
                (fn-web-host-head (setf observed-length (third args)) '(72 69 65 68))
                (otherwise (apply saved-core name args)))))
          (setf (symbol-function 'fnn-call)
            (lambda (name &rest args)
              (if (eq name 'fn-web-host-window-page-step)
                  (multiple-value-list (apply #'fn-web-host-window-page-step args))
                (apply saved-call name args))))
          (setf (symbol-function 'fnn-owner-render-next-quantum)
                (lambda (service cid p class) (declare (ignore service cid class))
                  (if (and (eq (fnn-web-conn-phase conn) :replay) (not cold-issued))
                      (progn (setf cold-issued t) (values nil p nil nil :article-read))
                    (values (car p) (cdr p) (null (cdr p)) nil nil))))
          (setf (symbol-function 'fnn-owner-cold-poll)
                (lambda (service read first issued) (declare (ignore service first issued))
                  (assert (eq read :article-read)) (values :serve 0 0 0)))
          (setf (symbol-function 'fnn-owner-response-unpin)
                (lambda (service cid) (declare (ignore service cid)) (incf pins-released)))
          (loop for rounds below 1000000 until (fnn-web-conn-closedp conn) do
            (case (fnn-web-conn-phase conn)
              (:render (fnn-web-render-step face conn))
              (:feed (fnn-web-feed-step face conn))
              (:replay (incf replay-rounds) (fnn-web-replay-step face conn))
              (:cold (fnn-web-cold-step face conn))
              ((:page-count :page-emit) (fnn-web-page-step face conn))
              (:write (fnn-web-write-ready face conn))
              (otherwise (error "unexpected phase ~s" (fnn-web-conn-phase conn))))
            (setf peak-in (max peak-in (fnn-web-len (fnn-web-conn-in conn))))
            (assert (<= peak-in 4096))
            (assert (zerop (fnn-web-len (fnn-web-conn-out conn))))
            (unless (fnn-web-conn-closedp conn) (assert (zerop pins-released))))
          (assert (fnn-web-conn-closedp conn))
          (assert (= pins-released 1))
          (when (> replay-rounds 0) (assert cold-issued)) (assert (< replay-rounds max-replay-rounds))
          (assert (= observed-length (length reference)))
          (assert (equal (wire-for id) (append '(72 69 65 68) reference))))
        (setf (symbol-function 'fnn-core) saved-core (symbol-function 'fnn-call) saved-call
              (symbol-function 'fnn-owner-render-next-quantum) saved-render
              (symbol-function 'fnn-owner-response-unpin) saved-unpin
              (symbol-function 'fnn-owner-cold-poll) saved-poll))))

(let* ((login (fn-wrq-oct "wren"))
       (prefix (article-octets '("211 1 1 1 fn.test" "220 1 <m@fn>")))
       (header (article-octets '("Subject: =?UTF-8?Q?caf=C3=A9_&?=" "From: Wren <wren@fn>"
                                  "Date: now" "Newsgroups: fn.test" "Message-ID: <m@fn>"
                                  "Subject: ignored" "X-Unshown: ignored" "")))
       (body (append (article-octets '("..first<&" ".not the terminator" "..second'"))
                     (make-list 13003 :initial-element 38) '(13 10)))
       (xs (append prefix header body '(46 13 10)))
       (in (create-fn-octets$c)) (bs (length prefix)) (be (- (length xs) 3))
       (session (list nil nil login (fn-wrq-oct "csrf")))
       (ctx (append (list (list :request :get)) (make-list 8) (list session :auto)))
       (flow (list :article :article ctx (list (fn-wrq-oct "fn.test"))))
       (config (list :web-config (fn-wrq-oct "fn") nil nil 600 16)))
  (fnn-web-fill in (fnn-octets xs))
  (let* ((view (fn-wss-article-view bs be login in))
         (ref-segs (fn-wr-frame (fn-wrq-oct "fn.test") (fn-wrq-oct "fn") :auto login
                      (fn-wss-s-csrf session)
                      (fn-wr-article-main (fn-wrq-oct "fn.test") (first view) (second view)
                                          (third view) (fourth view))))
         (reference (fn-wr-seq ref-segs xs)))
    (dolist (width '(1 2 7 4096))
      (let* ((scan (article-scan-chunks xs width login)) (action (fn-was-page config flow scan)))
        (assert (eq (fn-was-get :phase scan) :done))
        (assert (equal (fn-was-get :fields scan) (first view)))
        (assert (equal (cons (fn-was-get :body scan) (fn-was-get :be scan)) (second view)))
        (assert (equal (fn-was-get :own scan) (third view)))
        (multiple-value-bind (actual count) (virtual-page (sixth action) xs 4096)
          (assert (equal actual reference)) (assert (= count (length reference))))))
    (native-stream-consumer xs flow config reference)))
(format t "NATIVE WEB ARTICLE STREAM RAW PASS: exact reference; scan/replay/cold/count/partial-write; bounded replay rounds; IN <=4096; pin through drain~%")
