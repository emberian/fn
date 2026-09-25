import os
def clean(s):
    out=[]; i=0; n=len(s)
    while i<n:
        c=s[i]
        if c==';':
            j=s.find('\n',i); i=n if j<0 else j; continue
        if c=='#' and i+1<n and s[i+1]=='|':
            j=s.find('|#',i+2); 
            if j<0: break
            out.append('\n'*s.count('\n',i,j)); i=j+2; continue
        if c=='#' and i+1<n and s[i+1]=='\\':
            out.append(' CH '); i+=3
            while i<n and s[i].isalnum(): i+=1
            continue
        if c=='"':
            j=i+1
            while j<n and s[j]!='"':
                if s[j]=='\\': j+=1
                j+=1
            out.append('""'+'\n'*s.count('\n',i,j)); i=j+1; continue
        out.append(c); i+=1
    return ''.join(out)
