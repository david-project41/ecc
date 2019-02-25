#--------------KRIPTOGRAFI KURVA ELIPTIK----------------------------------------
#
#    Implementasi Kriptografi Kurva Eliptik menggunakan Python
#
#    Kurva               E: Y^2 = X^3 + AX + B
#    Atas Lapangan Hingga : Zp (Bilangan Bulat modulo prima p)
#
#    COPYRIGHT (c) 2018 oleh David Iman Fauzan <14610015@student.uin-suka.ac.id>
#-------------------------------------------------------------------------------


import collections

# MATEMATIKA DASAR -------------------------------------------------------------
def gcd(a,b):                           # Algoritma Euclid
    while b != 0:
        r = a%b
        a = b
        b = r
    return a

def egcd(a,b):                          # Algoritma Euclid yang diperluas
    if b == 0:
        d,x,y = a,1,0
    else:
        x2, x1, y2, y1 = 1, 0, 0, 1
        while b > 0:
            q = a//b
            r = a-q*b
            x = x2-q*x1
            y = y2-q*y1
            a,b,x2,x1,y2,y1 = b,r,x1,x,y1,y
        d,x,y = a,x2,y2
    return d,x,y

def testPrima(a):           # Tes Keprimaan Biasa
    for i in range(2,a-1):
        if a%i == 0:
            return False
            break
    else:
        return True

def inv(a,m):           # Invers Bilanga Bilat Modulo m
    d,x,y = egcd(a,m)
    if d == 1:
        return x%m
    else:
        return None

def sisaKuadratik(n,p):   # Sisa Kuadratik
    for i in range(1,p):
        if i*i%p == n:
            return (i,p-i)
    raise Exception("Akar kuadrat tidak ditemukan\n"
                    "masukan nilai yang lain")

Titik = collections.namedtuple("Titik",["x","y"])


# Definisi Kurva Eliptik E:Y^2 = X^3 + AX + B modulo p
class KurvaEliptik:
    
    def __init__(self, a,b,p):
        assert 4*a**3 + 27*b**2 != 0
        self.a = a
        self.b = b
        self.p = p
        self.IDENTITAS = Titik(None,None) # Titik di infinity didefinisikan dengan Titik (None, None)


    def cek_titik(self, P): # Fungsi untuk mengecek apakah titik P berada di kurva E
        if P == self.IDENTITAS: return True
        l = (P.y ** 2) % self.p
        r = ((P.x ** 3) + self.a * P.x + self.b) % self.p
        return l == r

    def at(self, x): # Fungsi untuk mencari titik di kurva E dengan memasukkan nilai koordinat x
        yKuadrat = (x ** 3 + self.a * x + self.b) % self.p
        y, my = sisaKuadratik(yKuadrat, self.p)
        return Titik(x, y), Titik(x, my)

    def neg(self, P): # Fungsi untuk mencari invers dari titik P
        return Titik(P.x, -P.y % self.p)

    def tambah(self, P1, P2): # Fungsi untuk menjumlahkan antara titik P1 dan P2
        if P1 == self.IDENTITAS: return P2
        if P2 == self.IDENTITAS: return P1
        if P1.x == P2.x and P1.y != P2.y :
            return self.IDENTITAS
        if P1.x == P2.x:
            l = (3 * P1.x * P1.x + self.a) * inv(2 * P1.y, self.p) % self.p
        else:
            l = (P2.y - P1.y) * inv(P2.x - P1.x, self.p) % self.p
        x = (l * l - P1.x - P2.x) % self.p
        y = (l * (P1.x - x) - P1.y) % self.p
        return Titik(x, y)

    def kali(self, P, n): # Fungsi untuk mengalikan titik P dengan skalar n (menjumlahkan P dengan dirinya sendiri sebanyak n)
        Q,R = P, self.IDENTITAS
        while n>0:
            if n%2 == 1: R=self.tambah(R,Q)
            Q=self.tambah(Q,Q)
            n=n//2
        return R

    def order(self, P):
        for i in range(1, self.p + 1):
            if self.kali(P, i) == self.IDENTITAS:
                return i
            pass
        raise Exception("Order tidak valid")

    def Point_Compress(self, P):
        if P == self.IDENTITAS: return self.IDENTITAS
        else: return Titik(P.x, P.y%2)

    def Point_Decompress(self, P):
        z=((P.x ** 3) + self.a * P.x + self.b) % self.p
        y,my = sisaKuadratik(z, self.p)
        if y%2 == P.y:return Titik(P.x,y)
        else: return Titik(P.x, my)

# Protokol Pertukaran Kunci Diffie-Hellman ----------------------------------------------
class DiffieHellman:

    def __init__(self, E, P):
        self.E = E
        self.P = P

    def gen(self, n):
        return self.E.kali(self.P, n)

    def secret(self, n, Q):
        return self.E.kali(Q, n)


# Sistem Kriptografi ElGamal
class ElGamal:

    def __init__(self, E, P):
        self.E = E
        self.P = P
        #self.n = E.order(P)

    def gen(self, n):
        return self.E.kali(self.P,n)

    def enc(self, M, Q, k):
        return (self.E.kali(self.P, k), self.E.tambah(M, self.E.kali(Q, k)))

    def dec(self, cipher, n):
        C1, C2 = cipher
        return self.E.tambah(C2, self.E.neg(self.E.kali(C1, n)))

# Elliptic Curve Integrated Encription Sceme
class ECIES:

    def __init__(self, E, P):
        self.E = E
        self.P = P
        self.n = E.order(P)

    def gen(self, m):
        return self.E.kali(self.P, m)

    def enc(self, Q, x, k):
        y1 = self.E.Point_Compress(self.E.kali(self.P, k))
        y2 = (x*(self.E.kali(Q,k).x))%self.E.p
        return (y1,y2)

    def dec(self, cipher, m):
        t = self.E.Point_Decompress(cipher[0])
        x0 = self.E.kali(t, m).x
        return (cipher[1]*inv(x0, self.E.p))%self.E.p

# Elliptik Curve Digital Signature Algoritma
class ECDSA:

    def __init__(self, E, A):
        self.E = E
        self.A = A
        self.q = E.order(A)

    def gen(self, m):
        return self.E.kali(self.A, m)

    def sign(self, hashval, m, k):

        kA = self.E.kali(self.A, k)
        return (kA.x%self.q, inv(k, self.q) * (hashval + kA.x * m) % self.q)

    def validate(self, hashval, sig, B):
        w = inv(sig[1], self.q)
        i,j = hashval * w % self.q, sig[0] * w % self.q
        kA = self.E.tambah(self.E.kali(self.A, i), self.E.kali(B, j))
        return kA.x % self.q == sig[0]

    def Hash(self, x):
        if type(x) is str: m = x.encode()
        else: m=bytearray(x)
        h = 0
        for index,value in enumerate(m):
            h = h + value
        return h%self.q

if __name__ == "__main__":
    pass



