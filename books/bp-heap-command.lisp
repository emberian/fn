; BP served launcher projection. This does not admit a complete BP command;
; it identifies the Store owner/connection profile for the pre-entry reservation.
(in-package "ACL2")

(defun fn-bph-decimal-characters (chars value)
 (declare (xargs :guard (and (true-listp chars) (natp value))))
 (if (endp chars) value
  (let ((c (car chars)))
   (if (and (characterp c) (<= (char-code #\0) (char-code c))
            (<= (char-code c) (char-code #\9)))
    (fn-bph-decimal-characters (cdr chars)
                              (+ (* 10 value) (- (char-code c) (char-code #\0))))
    nil))))
(defun fn-bph-connections (text)
 (declare (xargs :guard t))
 ;; A concurrency profile integer is represented by the existing u64 format.
 ;; Check the string length before materializing its characters. This is a
 ;; bounded input grammar, not a stored-data or retained-history ceiling.
 (if (and (stringp text) (<= 1 (length text)) (<= (length text) 20))
  (let ((n (fn-bph-decimal-characters (coerce text 'list) 0)))
   (and (posp n) (< n 18446744073709551616) n))
  nil))

(defun fn-bph-command-plan (argv)
 (declare (xargs :guard (true-listp argv)))
 (let* ((node (and (equal (nth 0 argv) "bp-node")
                  (equal (nth 1 argv) "serve")))
        (app (and (equal (nth 0 argv) "bp-app")
                 (equal (nth 1 argv) "receive")))
        (root (nth 4 argv)))
  (cond ((not (or node app)) '(:not-served-bp))
        ((not (and (stringp root) (< 0 (length root)))) '(:refused :store-root))
        ((and node (not (consp (nthcdr 13 argv)))) '(:refused :node-arguments))
        ((and app (not (consp (nthcdr 12 argv)))) '(:refused :app-arguments))
        (t (let ((connections (if node 1 (fn-bph-connections (nth 12 argv)))))
             (if (posp connections) (list :run root connections)
              '(:refused :connections)))))))

(defun fn-bph-refusal-line (reason)
 (declare (xargs :guard t))
 (cond ((equal reason :store-root) "BP served command requires a Store root")
       ((equal reason :node-arguments) "BP node serve requires its complete required arguments")
       ((equal reason :app-arguments) "BP app receive requires its complete required arguments")
       ((equal reason :connections) "BP app owner connections must be a positive u64 decimal")
       (t "BP served command reservation is malformed")))

(defthm fn-bph-connections-representable
 (implies (fn-bph-connections text)
  (and (posp (fn-bph-connections text))
       (< (fn-bph-connections text) 18446744073709551616))))
(defthm fn-bph-command-plan-owns-exact-served-root
 (implies (equal (car (fn-bph-command-plan argv)) :run)
  (and (equal (cadr (fn-bph-command-plan argv)) (nth 4 argv))
       (stringp (nth 4 argv))
       (< 0 (length (nth 4 argv)))
       (or (and (equal (nth 0 argv) "bp-node") (equal (nth 1 argv) "serve")
                (equal (caddr (fn-bph-command-plan argv)) 1))
           (and (equal (nth 0 argv) "bp-app") (equal (nth 1 argv) "receive")
                (equal (caddr (fn-bph-command-plan argv))
                       (fn-bph-connections (nth 12 argv)))))))
 :rule-classes nil)
