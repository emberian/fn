import sys
for p in sys.argv[1:]:
    s=open(p).read()
    old='"init", "--max-article-octets", "4194304", "fn.test"]'
    assert old in s, p
    s=s.replace(old,'"init", *os.environ.get("QUAL_INIT", "--max-article-octets 4194304").split(), "fn.test"]')
    open(p,"w").write(s)
