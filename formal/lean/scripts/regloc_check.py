from fractions import Fraction as Fr
import numpy as np, sys, math
N=21
LAM=Fr(sys.argv[1]) if len(sys.argv)>1 else Fr(449,100000)
BITS=int(sys.argv[2]) if len(sys.argv)>2 else 20
lo_b=[Fr(30901699,100000000),Fr(95105651,100000000),Fr(2126627,2500000),Fr(52573111,100000000),Fr(35355339,50000000)]
hi_b=[Fr(309017,1000000),Fr(23776413,25000000),Fr(85065081,100000000),Fr(6571639,12500000),Fr(70710679,100000000)]
def K(x): return [(Fr(x),(0,0,0,0,0))]
def at(i,e=1): t=[0]*5; t[i]=e; return [(Fr(1),tuple(t))]
def mul(P,Q): return [(a*b,tuple(x+y for x,y in zip(e,f))) for a,e in P for b,f in Q]
C,S=at(0),at(1)
c2=K(Fr(-1,2))+[(Fr(-1),(1,0,0,0,0))]
s2=[(Fr(2),(1,1,0,0,0))]
neg=lambda P: mul(K(-1),P)
pt=[[K(1),[],[]],[C,S,[]],[c2,s2,[]],[c2,neg(s2),[]],[C,neg(S),[]],[[],[],K(1)],[[],[],K(-1)]]
def wq(e,k,l):
    if k==l: return []
    if min(k,l)>4: return K(Fr(1,2)**e)
    if max(k,l)>4: return at(4,e)
    if (k+5-l)%5%3==1: return at(2,e)
    return at(3,e)
mu=lambda k: [(Fr(2),(1,0,3,0,0)),(Fr(-1),(0,0,0,3,0)),(Fr(-2),(1,0,0,3,0))] if k<5 else K(Fr(-1,8))
def g(k,l): return sum((mul(pt[k][c],pt[l][c]) for c in range(3)),[])
def HP(i,j):
    k,a,l,b=i//3,i%3,j//3,j%3
    r=[]
    if a==b:
        r+=mul(K(Fr(1,2)),wq(3,k,l))+mul(K(2),g(k,l))
        if k==l: r+=mul(K(Fr(-1,2)),mu(k))
    r+=mul(mul(mul(K(Fr(3,2)),wq(5,k,l))+K(0 if k==l else -2),pt[l][a]),pt[k][b])
    if k==l:
        for m in range(7): r+=mul(mul(mul(K(Fr(3,2)),wq(5,k,m)),pt[m][a]),pt[m][b])
    return r
c1=(math.sqrt(5)-1)/4; s1=math.sin(2*math.pi/5)
phi=lambda t:1/math.sqrt(2-2*t)
av=[c1,s1,phi(c1),phi(-0.5-c1),phi(0)]
def evf(P,v): return sum(float(a)*math.prod(x**e for x,e in zip(v,es)) for a,es in P)
if __name__=='__main__' and 'test' in sys.argv:
    H=np.array([[ (evf(HP(i,j),av)+evf(HP(j,i),av))/2 for j in range(N)] for i in range(N)])
    # direct Qhess+2Pen
    c2v=-0.5-c1; s2v=2*s1*c1
    P=np.array([[1,0,0],[c1,s1,0],[c2v,s2v,0],[c2v,-s2v,0],[c1,-s1,0],[0,0,1],[0,0,-1]])
    G=P@P.T
    W=np.array([[0 if i==j else phi(G[i,j])**3 for j in range(7)] for i in range(7)])
    A=np.array([[0 if i==j else phi(G[i,j])**5 for j in range(7)] for i in range(7)])
    mu_=[sum(W[i,j]*G[i,j] for j in range(7)) for i in range(7)]
    h=np.random.randn(7,3)
    Q=0.5*sum(W[i,j]*h[i]@h[j] for i in range(7) for j in range(7))-0.5*sum(mu_[i]*h[i]@h[i] for i in range(7))+sum(1.5*A[i,j]*(P[i]@h[j]+h[i]@P[j])**2 for i in range(7) for j in range(i+1,7))
    gg=lambda a,b: sum(P[i,a]*h[i,b]-P[i,b]*h[i,a] for i in range(7))
    Pen=sum((P[i]@h[i])**2 for i in range(7))+gg(0,1)**2+gg(0,2)**2+gg(1,2)**2
    x=h.reshape(21)
    print(Q+2*Pen, x@H@x, np.linalg.eigvalsh(H)[:3])
    sys.exit()
def monQ(b,e):
    r=Fr(1)
    for x,k in zip(b,e): r*=x**k
    return r
def lo(P): return sum((a*monQ(lo_b if a>=0 else hi_b,e) for a,e in P),Fr(0))
def hi(P): return sum((a*monQ(hi_b if a>=0 else lo_b,e) for a,e in P),Fr(0))
HPs=[[HP(i,j) for j in range(N)] for i in range(N)]
LO=[[lo(HPs[min(i,j)][max(i,j)]) for j in range(N)] for i in range(N)]
HI=[[hi(HPs[min(i,j)][max(i,j)]) for j in range(N)] for i in range(N)]
M0=[[(LO[i][j]+HI[i][j])/2 for j in range(N)] for i in range(N)]
dl=[[(HI[i][j]-LO[i][j])/2 for j in range(N)] for i in range(N)]
print('max rad',float(max(max(r) for r in dl)),file=sys.stderr)
MU=Fr(5,100000)
A=np.array([[float(M0[i][j]-(LAM+MU if i==j else 0)) for j in range(N)] for i in range(N)])
print('min eig',np.linalg.eigvalsh(np.array([[float(M0[i][j]) for j in range(N)] for i in range(N)]))[:3],file=sys.stderr)
Lf,Df=np.eye(N),np.zeros(N)
for j in range(N):
    Df[j]=A[j,j]-sum(Lf[j,k]**2*Df[k] for k in range(j))
    for i in range(j+1,N):
        Lf[i,j]=(A[i,j]-sum(Lf[i,k]*Lf[j,k]*Df[k] for k in range(j)))/Df[j]
rd=lambda x: Fr(round(x*2**BITS),2**BITS)
L=[[rd(Lf[i][j]) if i>j else Fr(int(i==j)) for j in range(N)] for i in range(N)]
D=[rd(Df[i]) for i in range(N)]
R=[[M0[i][j]-(LAM if i==j else 0)-sum(L[i][k]*D[k]*L[j][k] for k in range(N)) for j in range(N)] for i in range(N)]
slack=min(R[i][i]-dl[i][i]-sum(abs(R[i][j])+dl[i][j] for j in range(N) if j!=i) for i in range(N))
print('slack',float(slack), 'D>=0',all(d>=0 for d in D),file=sys.stderr)
fr=lambda x: str(x.numerator) if x.denominator==1 else f'{x.numerator}/{x.denominator}'
lst=lambda xs:'['+', '.join(xs)+']'
print('def Ld : List (List ℚ) := '+lst(lst(fr(L[i][j]) for j in range(i)) for i in range(N)))
print('def Dd : List ℚ := '+lst(fr(x) for x in D))
# exact LDL check
if 'exact' in sys.argv:
    A=[[M0[i][j]-(Fr(454,100000) if i==j else 0) for j in range(N)] for i in range(N)]
    piv=[]
    M=[r[:] for r in A]
    import time; t=time.time()
    for k in range(N):
        d=M[k][k]; piv.append(d)
        for i in range(k+1,N):
            for j in range(k+1,N):
                M[i][j]-=M[i][k]*M[k][j]/d
    print('pivots>0',all(p>0 for p in piv), min(float(p) for p in piv), 'maxdigits', max(len(str(M[i][j].denominator)) for i in range(N) for j in range(N)), time.time()-t, file=sys.stderr)
    print('dl rowsum max', float(max(sum(dl[i][j] for j in range(N)) for i in range(N))),file=sys.stderr)
