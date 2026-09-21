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

(defun fn-nop-help-text (subject)
  "Bounded operator help output, selected only from ACL2-normalized subjects."
  (declare (xargs :guard t))
  (cond ((equal subject "run") "usage: fn operator CONFIG run [--once]")
        ((equal subject "post")
         "usage: fn operator CONFIG post SOURCE (shared submission unavailable)")
        ((equal subject "status") "usage: fn operator CONFIG status")
        ((equal subject "recover") "usage: fn operator CONFIG recover")
        ((equal subject "help") "usage: fn operator CONFIG help [COMMAND]")
        (t "usage: fn operator CONFIG {help|run|post|status|recover}")))

(defun fn-nop-parse-command (words config)
  "The accepted tag means a bounded command *plan* exists; no host effect ran."
  (declare (xargs :guard t))
  (if (not (consp words))
      (fn-nop-usage :missing-command nil config nil)
    (let ((command (car words)) (rest (cdr words)))
      (cond ((equal command "help")
             (if (or (null rest)
                     (and (equal (len rest) 1) (fn-nop-help-subjectp (car rest))))
                 (let ((subject (if (consp rest) (car rest) "help")))
                   (fn-nop-result :accepted :plan "help" config
                                  (list :help subject (fn-nop-help-text subject))))
               (fn-nop-usage :invalid-help "help" config rest)))
            ((equal command "run")
             (let ((arguments (fn-nop-parse-run rest nil)))
               (if (equal arguments :bad)
                   (fn-nop-usage :invalid-run-options "run" config rest)
                 (fn-nop-result :accepted :plan "run" config arguments))))
            ((equal command "post")
             ; Shared submission is an owner callback.  Do not publish the
             ; old direct-store payload grammar as a native operator contract.
             (fn-nop-usage :shared-submission-unavailable "post" config rest))
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
  (cond ((or (not (true-listp argv-octets))
             (< *fn-nop-max-arguments* (len argv-octets))
             (not (fn-nop-argvp argv-octets)))
         (fn-nop-usage :argv-bounds nil nil nil))
        (t (let ((words (fn-nop-argument-texts argv-octets)))
             ; Help is an ACL2-selected action and deliberately needs no file.
             (if (and (consp words) (equal (car words) "help"))
                 (fn-nop-parse-command words nil)
               (if (or (not (fn-ncfg-ascii-octetsp config-octets))
                       (< *fn-ncfg-max-octets* (len config-octets)))
                   (fn-nop-usage :configuration-bounds nil nil nil)
                 (let ((loaded (fn-native-config-load config-octets)))
                   (if (not (equal (fn-ncfg-first loaded) :accepted))
                       (fn-nop-usage (list :configuration (fn-ncfg-second loaded)) nil nil nil)
                     (let ((config (fn-ncfg-second loaded)))
                       (if (not (fn-native-config-operator-availablep config))
                           (fn-nop-usage :unsupported-profile nil config nil)
                         (fn-nop-parse-command words config))))))))))

(in-theory (disable fn-native-operator-run))

(defun fn-native-operator-result-run-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (equal (fn-native-operator-result-command result) "run")))

(defun fn-native-operator-result-run-store-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-record-string-octets
       (fn-native-config-store (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-run-listener-host-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-record-string-octets
       (fn-native-config-listener-host (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-run-listener-port (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-native-config-listener-port (fn-native-operator-result-config result))
    0))

(defun fn-native-operator-result-run-oncep (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-ncfg-nth 2 (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-run-max-connections (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-native-config-owner-max-connections
       (fn-native-operator-result-config result))
    0))

(defun fn-native-operator-result-native-action (result)
  "The only commands the current raw native module may execute by itself.

`run' retains its normalized plan for the one owner callback.  `post' is usage
until that owner exposes its shared-submission callback.  Neither is translated
into a direct store call, which would create another owner of lifecycle or
submission semantics."
  (declare (xargs :guard t))
  (if (not (equal (fn-native-operator-result-status result) :accepted))
      :none
    (cond ((equal (fn-native-operator-result-command result) "help") :help)
          ((equal (fn-native-operator-result-command result) "run") :run)
          ((equal (fn-native-operator-result-command result) "status") :status)
          ((equal (fn-native-operator-result-command result) "recover") :recover)
          (t :owner-required))))
