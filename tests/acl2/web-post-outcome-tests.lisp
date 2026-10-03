; Source-level browser boundary: same 441 code can mean refused or uncertain.
(in-package "ACL2")
(include-book "../../books/web-session")

(defun-nx web-post-outcome-fixture (line)
 (let* ((input (fn-octets-from-list (append (fn-wrq-chars-octets (coerce line 'list)) '(13 10)) (create-fn-octets)))
        (output (create-fn-octets))
        (flow (fn-wss-flow :post :article nil nil))
        (config (fn-web-config nil nil nil 60 2)))
  (fn-wss-k-submit nil flow '(:reply) config input output)))

(defthm web-post-uncertain-441-stays-uncertain
 (let ((result (web-post-outcome-fixture (fn-proto-text "POST" :uncertain))))
  (and (equal (car (mv-nth 0 result)) :respond)
       (equal (cadr (mv-nth 0 result)) 503)
       (equal (mv-nth 1 result) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-wss-k-submit))))

(defthm web-post-ordinary-441-stays-refused
 (let ((result (web-post-outcome-fixture (fn-proto-text "POST" :refused-unnamed))))
  (and (equal (car (mv-nth 0 result)) :respond)
       (equal (cadr (mv-nth 0 result)) 403)
       (equal (mv-nth 1 result) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-wss-k-submit))))

(defthm web-post-connection-fault-stays-uncertain
 (let ((result (web-post-outcome-fixture (fn-proto-text "(connection)" :fault))))
  (and (equal (car (mv-nth 0 result)) :respond)
       (equal (cadr (mv-nth 0 result)) 503)
       (equal (mv-nth 1 result) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-wss-k-submit))))

(defthm web-post-240-stays-accepted
 (let ((result (web-post-outcome-fixture (fn-proto-text "POST" :received))))
  (and (equal (car (mv-nth 0 result)) :respond)
       (equal (cadr (mv-nth 0 result)) 200)
       (equal (mv-nth 1 result) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-wss-k-submit))))

(defun-nx web-remove-check-fixture (line)
 (let* ((input (fn-octets-from-list (append (fn-wrq-chars-octets (coerce line 'list)) '(13 10)) (create-fn-octets)))
        (output (create-fn-octets))
        (flow (fn-wss-flow :remove :check nil nil))
        (config (fn-web-config nil nil nil 60 2)))
  (fn-wss-k-submit nil flow '(:reply) config input output)))

(defthm web-remove-check-positive-negative-and-unknown
 (and (equal (cadr (mv-nth 0 (web-remove-check-fixture "223 1 <a@example>"))) 200)
      (equal (cadr (mv-nth 0 (web-remove-check-fixture "430 no such article"))) 200)
      (equal (cadr (mv-nth 0 (web-remove-check-fixture (fn-proto-text "(connection)" :fault)))) 503)
      (equal (cadr (mv-nth 0 (web-remove-check-fixture "480 authentication required"))) 503)
      (equal (cadr (mv-nth 0 (web-remove-check-fixture "bad reply"))) 503))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-wss-k-submit))))

(defun-nx web-redeem-lost-fixture ()
 (fn-wss-k-redeem nil
   (fn-wss-flow :redeem :redeeming nil '(nil nil nil 7)) '(:gone)
   (fn-web-config nil nil nil 60 2) (create-fn-octets) (create-fn-octets)))

(defthm web-redeem-lost-after-password-keeps-uncertainty-message
 (let* ((config (fn-web-config nil nil nil 60 2))
        (input (create-fn-octets)) (output (create-fn-octets))
        (actual (web-redeem-lost-fixture))
        (uncertain (fn-wss-redeem-refused :uncertain nil nil config input output))
        (unreachable (fn-wss-redeem-refused :other nil nil config input output)))
  (and (equal (mv-nth 0 actual) (mv-nth 0 uncertain))
       (equal (mv-nth 2 actual) (mv-nth 1 uncertain))
       (not (equal (mv-nth 2 actual) (mv-nth 1 unreachable)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-wss-k-redeem))))
