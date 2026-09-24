import socket,sys
art=open(sys.argv[1],"rb").read().replace(b"\r\n",b"\n").replace(b"\n",b"\r\n")
mid=sys.argv[2]; port=int(sys.argv[3])
s=socket.create_connection(("127.0.0.1",port),timeout=30); f=s.makefile("rb")
print(f.readline())
s.sendall(("IHAVE "+mid+"\r\n").encode()); r=f.readline(); print(r)
if r.startswith(b"335"):
  body=art.replace(b"\r\n.",b"\r\n..")
  if not body.endswith(b"\r\n"): body+=b"\r\n"
  s.sendall(body+b".\r\n"); print(f.readline())
s.sendall(b"QUIT\r\n"); print(f.readline())
