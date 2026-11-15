"""Project only the canonical declared codec transition metadata, no runtime edit."""
def rewrite(source):
 if '(defun fn2-layout-decode-transition-bound ' in source:return source
 anchor='(defun fn2-layout-decode-run '
 if source.count(anchor)!=1:raise ValueError('layout decoder anchor drift')
 helper='''; Declared scan transition count; callers separately admit bytes/table work.
(defun fn2-layout-decode-transition-bound (layout)
 (declare (xargs :guard (fn2-layoutp layout)))
 (max 1 (+ (nfix (fn2-layout-max-size layout)) (len layout))))
(defthm fn2-layout-decode-transition-bound-positive
 (and (integerp (fn2-layout-decode-transition-bound layout))
      (< 0 (fn2-layout-decode-transition-bound layout))) :rule-classes :type-prescription)
(in-theory (disable fn2-layout-decode-transition-bound))

'''
 source=source.replace(anchor,helper+anchor,1)
 for old,new in [
  ('        (max-name (fn2-codec-constant name "-MAX-SIZE"))','        (max-name (fn2-codec-constant name "-MAX-SIZE"))\n        (transitions-name (fn2-codec-constant name "-DECODE-TRANSITIONS"))'),
  ('    (defconst ,max-name ,(fn2-layout-max-size layout))','    (defconst ,max-name ,(fn2-layout-max-size layout))\n    (defconst ,transitions-name ,(fn2-layout-decode-transition-bound layout))'),
  (':encode ,encode :decode ,decode :decode-step ,step :start ,start :size ,sizefn',':encode ,encode :decode ,decode :decode-step ,step :decode-transitions ,transitions-name :start ,start :size ,sizefn')]:
  if source.count(old)!=1:raise ValueError('codec metadata declaration drift')
  source=source.replace(old,new,1)
 return source
