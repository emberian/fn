p='tests/native_web_article_stream_raw.lisp';s=open(p).read();s=s.replace('fn-wss-f-route fn-wss-f-ctx','*fn-wss-window* *fn-wss-msg-unreachable* fn-wss-f-stage fn-wss-f-route fn-wss-f-ctx');s=s.replace('(load-page-forms "books/web-article-stream.lisp")','(load-page-forms "books/web-article-stream.lisp")\n(load-page-forms "books/web-reply-stream.lisp")');s=s.replace('fn-web-host-window-page-step fn-web-host-replay-slice fn-web-host-replay-forward-p))','fn-web-host-window-page-step fn-web-host-replay-slice fn-web-host-replay-forward-p\n   fn-web-host-stream-p fn-web-host-stream-start fn-web-host-stream-scan fn-web-host-stream-page))')
a=s.index('    ;; Actual native scan/replay');b=s.index('(format t "NATIVE WEB ARTICLE',a)
block=s[s.index('    (let* ((conn',a):b].rstrip();assert block.endswith(')))))');block=block[:-2]
block=block.replace('(fixture-conn 41 :render 88)','(fixture-conn id :render 88)').replace('(fn-was-start login)','(fn-web-host-stream-start flow)').replace('(wire-for 41)','(wire-for id)')
block=block.replace("(fn-web-host-stream-p (apply #'fn-web-host-article-p args))\n                (fn-web-host-stream-start (apply #'fn-web-host-article-start args))\n                (fn-web-host-stream-scan (apply #'fn-web-host-article-scan args))\n                (fn-web-host-stream-page (apply #'fn-web-host-article-page args))", "((fn-web-host-stream-p fn-web-host-stream-start fn-web-host-stream-scan fn-web-host-stream-page)\n                 (apply (symbol-function name) args))")
helper='''; Actual native scan/replay/count/write consumer, reusable for captured
; protocol routes. The renderer adapter advances persistent plan tails only.
(defun native-stream-consumer (xs flow config reference &optional (id 41))
'''+block+')\n'
s=s[:a]+'    (native-stream-consumer xs flow config reference)))\n'+s[b:]
a=s.index('(let* ((login (fn-wrq-oct "wren"))');s=s[:a]+helper+'\n'+s[a:];open(p,'w').write(s)
p='tests/native_web_over_stream_raw.lisp';s=open(p).read();s=s.replace('    (dolist (width', '    (native-stream-consumer xs flow config reference 42)\n    (dolist (width',1);open(p,'w').write(s)
