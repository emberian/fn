(load "tests/native_web_over_stream_raw.lisp")
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-extent-window-cancel (worker token)
  (declare (ignorable worker token))
  (harness-stub-reached 'fnn-extent-window-cancel "host/native/extent.lisp"))
(defun fnn-owner-cold-window-result-locked (service read)
  (declare (ignorable service read))
  (harness-stub-reached 'fnn-owner-cold-window-result-locked "host/native/owner.lisp"))
;;; ---- derived stubs: END ----
(load-page-forms "books/octet-text.lisp"
 '(fn-ot-digit-value fn-ot-maxp fn-ot-nat-parse-aux fn-ot-nat-parse fn-ot-decimal-parse))
(load-page-forms "books/web-session.lisp"
 '(fn-wss-active-row fn-wss-active-rows-loop fn-wss-active-rows))
(load-page-forms "books/web-render.lisp"
 '(fn-wr-group-row-segments fn-wr-group-rows-step fn-wr-group-rows-loop fn-wr-group-rows
   fn-wr-groups-main-segments fn-wr-groups-main))
(load-page-forms "books/web-list-stream.lisp")
(let* ((login (fn-wrq-oct "wren")) (session (list nil nil login (fn-wrq-oct "csrf")))
       (ctx (append (list (list :request :get)) (make-list 8) (list session :auto)))
       (flow (list :groups :list ctx nil))
       (config (list :web-config (fn-wrq-oct "fn") nil nil 600 16))
       (prefix (article-octets '("215 List of newsgroups follows"))))
  (dolist (size '(0 1 1003))
    (let* ((rows (loop for n from 1 to size append
                    (article-octets (list (format nil "fn.group.~d ~d 1 ~a" n n (if (oddp n) "y" "n"))))))
           (xs (append prefix rows '(46 13 10))) (in (create-fn-octets$c)))
      (fnn-web-fill in (fnn-octets xs))
      (let* ((ref-rows (fn-wss-active-rows (length prefix) (- (length xs) 3) in))
             (reference (fn-wr-seq (fn-wr-frame (fn-wrq-oct "Groups") (fn-wrq-oct "fn") :auto login
                                    (fn-wss-s-csrf session) (fn-wr-groups-main ref-rows)) xs)))
        (native-stream-consumer xs flow config reference (+ 43 size) 1000)
        (dolist (width '(1 7 4096))
          (let ((scan (fn-wrs-start flow)) (window (create-fn-octets$c)))
            (loop for at from 0 below (length xs) by width do
              (fnn-web-fill window (fnn-octets (subseq xs at (min (length xs) (+ at width)))))
              (setf scan (fn-wrs-scan scan window)))
            (assert (eq (fn-was-get :phase scan) :done))
            (assert (null (fn-was-get :rows scan)))
            (assert (null (fn-was-get :fields scan)))
            (assert (= (length scan) 9))
            (let* ((action (fn-wrs-page config flow scan)) (segs (sixth action)))
              (assert (< (length segs) 80))
              (multiple-value-bind (actual count) (virtual-page segs xs 4096)
                (assert (equal actual reference)) (assert (= count (length reference))))))))))
  (assert (fn-web-host-stream-p flow)))
(format t "NATIVE WEB LIST STREAM RAW PASS: exact empty/one/1003-group pages; fixed metadata/dynamic row plan; native cold/count/drain~%")
