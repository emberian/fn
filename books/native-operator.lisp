; fn: bounded native operator command grammar.
;
; This is a command-plan boundary, not a second storage or owner
; implementation.  It takes raw argv octet lists and the raw configuration
; bytes, asks books/native-config.lisp for the one normalized configuration,
; and returns a tagged plan.  A raw host may transport/print this result but
; may not supply defaults, select a command, or decide an outcome.

(in-package "ACL2")
(include-book "native-config")

(defconst *fn-nop-max-arguments* 32)
(defconst *fn-nop-max-argument-octets* 512)
(defconst *fn-nop-max-charge* 4294967295)

(defun fn-nop-argvp (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (and (consp (car argv))
           (<= (len (car argv)) *fn-nop-max-argument-octets*)
           (fn-ncfg-ascii-octetsp (car argv))
           (fn-nop-argvp (cdr argv)))
    (null argv)))

(defun fn-nop-argument-texts (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (cons (fn-record-octets-string (car argv))
            (fn-nop-argument-texts (cdr argv)))
    nil))

(defun fn-nop-result (status reason command config arguments)
  (declare (xargs :guard t))
  (list status reason command config arguments))

(defun fn-native-operator-result-status (result)
  (declare (xargs :guard t)) (fn-ncfg-first result))
(defun fn-native-operator-result-reason (result)
  (declare (xargs :guard t)) (fn-ncfg-second result))
(defun fn-native-operator-result-command (result)
  (declare (xargs :guard t)) (fn-ncfg-third result))
(defun fn-native-operator-result-config (result)
  (declare (xargs :guard t)) (fn-ncfg-nth 3 result))
(defun fn-native-operator-result-arguments (result)
  (declare (xargs :guard t)) (fn-ncfg-nth 4 result))

(defun fn-native-operator-resultp (result)
  (declare (xargs :guard t))
  (and (true-listp result) (equal (len result) 5)
       (member-equal (fn-native-operator-result-status result)
                     '(:accepted :refused :uncertain :fault :usage))))

(defun fn-native-operator-exit-code (result)
  "The tagged result, not a raw host condition, owns the five CLI codes."
  (declare (xargs :guard t))
  (cond ((equal (fn-native-operator-result-status result) :accepted) 0)
        ((equal (fn-native-operator-result-status result) :refused) 1)
        ((equal (fn-native-operator-result-status result) :uncertain) 3)
        ((equal (fn-native-operator-result-status result) :fault) 4)
        ((equal (fn-native-operator-result-status result) :usage) 5)
        (t 4)))

(defun fn-nop-usage (reason command config arguments)
  (declare (xargs :guard t))
  (fn-nop-result :usage reason command config arguments))

(defun fn-nop-refused (reason command config arguments)
  (declare (xargs :guard t))
  (fn-nop-result :refused reason command config arguments))

(defun fn-nop-decimal-aux (octets value)
  (declare (xargs :guard t))
  (if (and (natp value) (consp octets))
      (if (fn-ncfg-digitp (car octets))
          (fn-nop-decimal-aux (cdr octets)
                              (+ (* 10 value) (- (car octets) 48)))
        :bad)
    (if (natp value) value :bad)))

(defun fn-nop-charge (text)
  (declare (xargs :guard t))
  (let ((octets (fn-record-string-octets text)))
    (if (and (consp octets) (<= (len octets) 10))
        (let ((value (fn-nop-decimal-aux octets 0)))
          (if (and (natp value) (<= value *fn-nop-max-charge*)) value :bad))
      :bad)))

(defun fn-nop-parse-post (words message-id payload groups charge)
  "Normalize the public post option grammar without deciding article validity."
  (declare (xargs :guard t))
  (if (consp words)
      (let ((option (car words)) (tail (cdr words)))
        (if (not (consp tail))
            :bad
          (let ((value (car tail)))
            (cond ((equal option "--message-id")
                   (if message-id :bad
                     (fn-nop-parse-post (cdr tail) value payload groups charge)))
                  ((equal option "--payload")
                   (if payload :bad
                     (fn-nop-parse-post (cdr tail) message-id value groups charge)))
                  ((equal option "--group")
                   (fn-nop-parse-post (cdr tail) message-id payload
                                      (cons value groups) charge))
                  ((equal option "--charge")
                   (if charge :bad
                     (let ((parsed (fn-nop-charge value)))
                       (if (equal parsed :bad) :bad
                         (fn-nop-parse-post (cdr tail) message-id payload groups parsed)))))
                  (t :bad)))))
    (if (and message-id payload (consp groups))
        (list :post message-id payload (fn-ncfg-reverse groups) charge)
      :bad)))

(defun fn-nop-parse-run (words once)
  (declare (xargs :guard t))
  (if (consp words)
      (if (and (equal (car words) "--once") (not once))
          (fn-nop-parse-run (cdr words) t)
        :bad)
    (list :run :once once)))

(defun fn-nop-help-subjectp (subject)
  (declare (xargs :guard t))
  (member-equal subject '("help" "run" "post" "status" "recover")))

(defun fn-nop-parse-command (words config)
  "The accepted tag means a bounded command *plan* exists; no host effect ran."
  (declare (xargs :guard t))
  (if (not (consp words))
      (fn-nop-usage :missing-command nil config nil)
    (let ((command (car words)) (rest (cdr words)))
      (cond ((equal command "help")
             (if (or (null rest)
                     (and (equal (len rest) 1) (fn-nop-help-subjectp (car rest))))
                 (fn-nop-result :accepted :plan "help" config
                                (list :help (if (consp rest) (car rest) "help")))
               (fn-nop-usage :invalid-help "help" config rest)))
            ((equal command "run")
             (let ((arguments (fn-nop-parse-run rest nil)))
               (if (equal arguments :bad)
                   (fn-nop-usage :invalid-run-options "run" config rest)
                 (fn-nop-result :accepted :plan "run" config arguments))))
            ((equal command "post")
             (let ((arguments (fn-nop-parse-post rest nil nil nil nil)))
               (if (equal arguments :bad)
                   (fn-nop-usage :invalid-post-options "post" config rest)
                 (fn-nop-result :accepted :plan "post" config arguments))))
            ((equal command "status")
             (if (null rest)
                 (fn-nop-result :accepted :plan "status" config (list :status))
               (fn-nop-usage :unexpected-arguments "status" config rest)))
            ((equal command "recover")
             (if (null rest)
                 (fn-nop-result :accepted :plan "recover" config (list :recover))
               (fn-nop-usage :unexpected-arguments "recover" config rest)))
            (t (fn-nop-usage :unsupported-command command config rest))))))

(defun fn-native-operator-run (config-octets argv-octets)
  "One semantic authority for config defaults, argv grammar, and CLI tag.

A profile the current native owner cannot consume is USAGE, never an accepted
service plan.  `posting.enabled = false' remains explicit unsupported-profile
until owner convergence exposes one ACL2 posting projection to served/control."
  (declare (xargs :guard t))
  (cond ((or (not (fn-ncfg-ascii-octetsp config-octets))
             (< *fn-ncfg-max-octets* (len config-octets)))
         (fn-nop-refused :config-bounds nil nil nil))
        ((or (not (true-listp argv-octets))
             (< *fn-nop-max-arguments* (len argv-octets))
             (not (fn-nop-argvp argv-octets)))
         (fn-nop-usage :argv-bounds nil nil nil))
        (t (let ((loaded (fn-native-config-load config-octets)))
             (if (not (equal (fn-ncfg-first loaded) :accepted))
                 (fn-nop-refused (fn-ncfg-second loaded) nil nil nil)
               (let ((config (fn-ncfg-second loaded)))
                 (if (not (fn-native-config-operator-availablep config))
                     (fn-nop-usage :unsupported-profile nil config nil)
                   (fn-nop-parse-command (fn-nop-argument-texts argv-octets) config))))))))

(in-theory (disable fn-native-operator-run))
