import socket,sys
art=open(sys.argv[1],"rb").read()
mid=sys.argv[2]
s=socket.create_connection(("127.0.0.1",11196),timeout=30); f=s.makefile("rb")
print(f.readline())
s.sendall(("IHAVE "+mid+"\r\n").encode()); r=f.readline(); print(r)
if r.startswith(b"335"):
  body=art.replace(b"\r\n.",b"\r\n..")
  if not body.endswith(b"\r\n"): body+=b"\r\n"
  s.sendall(body+b".\r\n"); print(f.readline())
s.sendall(b"QUIT\r\n"); print(f.readline())
