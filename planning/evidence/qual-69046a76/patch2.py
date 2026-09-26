import sys
for p in sys.argv[1:]:
    s=open(p).read()
    old='while not o.stdout.readline().startswith(b"LISTENING"):\n    pass'
    new='while True:\n    _l = o.stdout.readline()\n    if not _l:\n        sys.exit("owner exited before LISTENING: init=%r" % (r.returncode, r.stdout[-300:], r.stderr[-300:]))\n    if _l.startswith(b"LISTENING"):\n        break'
    n = s.count(old)
    if n == 0:
        old2 = old.replace("\n    pass", "\n            pass").replace("while", "        while",1)
        old2='        while not o.stdout.readline().startswith(b"LISTENING"):\n            pass'
        new2="\n".join("        "+l for l in new.split("\n"))
        assert old2 in s, p
        s = s.replace(old2, new2)
    else:
        s = s.replace(old, new)
    s = s.replace('init=%r" % (r.returncode', 'init=%r %r %r" % (r.returncode')
    open(p,"w").write(s)
    print(p, "patched")
