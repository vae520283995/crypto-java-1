package com.raugfer.crypto;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

public class secp256k1_2 {

    private static final BigInteger a = BigInteger.ZERO;
    private static final BigInteger b = BigInteger.valueOf(7L);
    private static final BigInteger P = new BigInteger("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F", 16);
    private static final BigInteger n = new BigInteger("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", 16);
    private static final BigInteger h = BigInteger.ONE;
    private static final BigInteger Gx = new BigInteger("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798", 16);
    private static final BigInteger Gy = new BigInteger("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8", 16);

    private static final BigInteger beta = new BigInteger("7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE", 16);

    private static final boolean USE_ENDOMORPHISM = a.signum() == 0;

    static class JacobianPoint {
        private final BigInteger x;
        private final BigInteger y;
        private final BigInteger z;

        private List<JacobianPoint> precomputes;

        public JacobianPoint(BigInteger x, BigInteger y, BigInteger z) {
            this.x = x;
            this.y = y;
            this.z = z;
        }
  static final JacobianPoint BASE = new JacobianPoint(Gx, Gy, BigInteger.ONE);
        static final JacobianPoint ZERO = new JacobianPoint(BigInteger.ZERO, BigInteger.ONE, BigInteger.ZERO);

        static JacobianPoint fromAffine(Point p) {
            return new JacobianPoint(p.x, p.y, BigInteger.ONE);
        }

        Point toAffine() {
            return toAffine(invert(this.z));
        }

        Point toAffine(BigInteger invZ) {
            BigInteger invZ2 = invZ.pow(2);
            BigInteger x = mod(this.x.multiply(invZ2));
            BigInteger y = mod(this.y.multiply(invZ2).multiply(invZ));
            return new Point(x, y);
        }

        JacobianPoint negate() {
            return new JacobianPoint(this.x, mod(this.y.negate()), this.z);
        }

        JacobianPoint doubleAdd() {
            BigInteger X1 = this.x;
            BigInteger Y1 = this.y;
            BigInteger Z1 = this.z;
            BigInteger A = X1.pow(2);
            BigInteger B = Y1.pow(2);
            BigInteger C = B.pow(2);
            BigInteger D = BigInteger.valueOf(2L).multiply((X1.add(B)).pow(2).subtract(A).subtract(C));
            BigInteger E = BigInteger.valueOf(3L).multiply(A);
            BigInteger F = E.pow(2);
            BigInteger X3 = mod(F.subtract(BigInteger.valueOf(2L).multiply(D)));
            BigInteger Y3 = mod(E.multiply(D.subtract(X3)).subtract(BigInteger.valueOf(8L).multiply(C)));
            BigInteger Z3 = mod(BigInteger.valueOf(2L).multiply(Y1).multiply(Z1));
            return new JacobianPoint(X3, Y3, Z3);

          }

        JacobianPoint add(JacobianPoint other) {
            if (other == null) {
                throw new IllegalArgumentException("JacobianPoint#add: expected JacobianPoint");
            }
            BigInteger X1 = this.x;
            BigInteger Y1 = this.y;
            BigInteger Z1 = this.z;
            BigInteger X2 = other.x;
            BigInteger Y2 = other.y;
            BigInteger Z2 = other.z;
            if (X2.signum() == 0 || Y2.signum() == 0) return this;
            if (X1.signum() == 0 || Y1.signum() == 0) return other;
            BigInteger Z1Z1 = Z1.pow(2);
            BigInteger Z2Z2 = Z2.pow(2);
            BigInteger U1 = X1.multiply(Z2Z2);
            BigInteger U2 = X2.multiply(Z1Z1);
            BigInteger S1 = Y1.multiply(Z2).multiply(Z2Z2);
            BigInteger S2 = Y2.multiply(Z1).multiply(Z1Z1);
            BigInteger H = mod(U2.subtract(U1));
            BigInteger r = mod(S2.subtract(S1));
            if (H.signum() == 0) {
                if (r.signum() == 0) {
                    return this.doubleAdd();
                } else {
                    return JacobianPoint.ZERO;
                }
            }
            BigInteger HH = mod(H.pow(2));
            BigInteger HHH = mod(H.multiply(HH));
            BigInteger V = U1.multiply(HH);
            BigInteger X3 = mod(r.pow(2).subtract(HHH).subtract(BigInteger.valueOf(2L).multiply(V)));
            BigInteger Y3 = mod(r.multiply(V.subtract(X3)).subtract(S1.multiply(HHH)));
            BigInteger Z3 = mod(Z1.multiply(Z2).multiply(H));
            return new JacobianPoint(X3, Y3, Z3);
        }

        JacobianPoint multiplyUnsafe(BigInteger scalar) {
            BigInteger n = mod(scalar, secp256k1_2.n);
            if (n.signum() <= 0) {
                throw new IllegalArgumentException("Point#multiply: invalid scalar, expected positive integer");
            }
            if (!USE_ENDOMORPHISM) {
                JacobianPoint p = JacobianPoint.ZERO;
                JacobianPoint d = this;
                while (n.signum() > 0) {
                    if (n.and(BigInteger.ONE).signum() == 1) p = p.add(d);
                    d = d.doubleAdd();
                    n = n.shiftRight(1);
                }
                return p;
            }
            Object[] k = splitScalarEndo(n);
            boolean k1neg = (boolean) k[0];
            BigInteger k1 = (BigInteger) k[1];
            boolean k2neg = (boolean) k[2];
            BigInteger k2 = (BigInteger) k[3];
            JacobianPoint k1p = JacobianPoint.ZERO;
            JacobianPoint k2p = JacobianPoint.ZERO;
            JacobianPoint d = this;
            while (k1.signum() > 0 || k2.signum() > 0) {
                if (k1.and(BigInteger.ONE).signum() == 1) k1p = k1p.add(d);
                if (k2.and(BigInteger.ONE).signum() == 1) k2p = k2p.add(d);
                d = d.doubleAdd();
                k1 = k1.shiftRight(1);
                k2 = k2.shiftRight(1);
            }
            if (k1neg) k1p = k1p.negate();
            if (k2neg) k2p = k2p.negate();
            k2p = new JacobianPoint(mod(k2p.x.multiply(beta)), k2p.y, k2p.z);
            return k1p.add(k2p);
        }

        JacobianPoint multiplyDA(BigInteger n) {
            JacobianPoint p = JacobianPoint.ZERO;
            JacobianPoint d = this;
            while (n.signum() > 0) {
                if (n.and(BigInteger.ONE).signum() == 1) p = p.add(d);
                d = d.doubleAdd();
                n = n.shiftRight(1);
            }
            return p;
        }

        JacobianPoint multiplyCT(BigInteger n) {
            JacobianPoint dbl = new JacobianPoint(this.x, this.y, this.z);
            JacobianPoint p = JacobianPoint.ZERO;
            JacobianPoint f = JacobianPoint.ZERO;
            for (int i = 0; i < 256; i++) {
                if (n.and(BigInteger.ONE).signum() == 1) p = p.add(dbl);
                else f = f.add(dbl);
                n = n.shiftRight(1);
                dbl = dbl.doubleAdd();
            }
            return p;
        }

        List<JacobianPoint> getPrecomputes() {
            if (this.precomputes != null) return this.precomputes;
            this.precomputes = new ArrayList<>();
            JacobianPoint dbl = this;
            for (int i = 0; i < 256; i++) {
                this.precomputes.add(dbl);
                dbl = dbl.doubleAdd();
            }
            return this.precomputes;
        }

        JacobianPoint multiplyPreCT(BigInteger n) {
            JacobianPoint dbl;
            JacobianPoint p = JacobianPoint.ZERO;
            JacobianPoint f = JacobianPoint.ZERO;
            List<JacobianPoint> dbls = this.getPrecomputes();
            for (int i = 0; i < 256; i++) {
                dbl = dbls.get(i);
                if (n.and(BigInteger.ONE).signum() == 1) p = p.add(dbl);
                else f = f.add(dbl);
                n = n.shiftRight(1);
            }
            return p;
        }
    }

    static class Point {
        private final BigInteger x;
        private final BigInteger y;

        private List<Point> precomputes;
        private List<JacobianPoint> precomputesJ;
        private List<JacobianPoint> precomputesW;

        public Point(BigInteger x, BigInteger y) {
            this.x = x;
            this.y = y;
        }

        static final Point BASE = new Point(Gx, Gy);
        static final Point ZERO = new Point(BigInteger.ZERO, BigInteger.ZERO);

        Point doubleAdd() {
            BigInteger X1 = this.x;
            BigInteger Y1 = this.y;
            BigInteger lam = mod(BigInteger.valueOf(3L).multiply(X1.pow(2)).multiply(invert(BigInteger.valueOf(2).multiply(Y1), P)));
            BigInteger X3 = mod(lam.multiply(lam).subtract(BigInteger.valueOf(2L).multiply(X1)));
            BigInteger Y3 = mod(lam.multiply(X1.subtract(X3)).subtract(Y1));
            return new Point(X3, Y3);
        }

        Point add(Point other) {
            Point a = this, b = other;
            BigInteger X1 = a.x, Y1 = a.y, X2 = b.x, Y2 = b.y;
            if (X1.signum() == 0 || Y1.signum() == 0) return b;
            if (X2.signum() == 0 || Y2.signum() == 0) return a;
            if (X1.compareTo(X2) == 0 && Y1.compareTo(Y2) == 0) return this.doubleAdd();
            if (X1.compareTo(X2) == 0 && Y1.compareTo(Y2.negate()) == 0) return Point.ZERO;
            BigInteger lam = mod((Y2.subtract(Y1)).multiply(invert(X2.subtract(X1), P)));
            BigInteger X3 = mod(lam.multiply(lam).subtract(X1).subtract(X2));
            BigInteger Y3 = mod(lam.multiply(X1.subtract(X3)).subtract(Y1));
            return new Point(X3, Y3);
        }

        Point multiplyDA(BigInteger n) {
            Point p = Point.ZERO;
            Point d = this;
            while (n.signum() > 0) {
                if (n.and(BigInteger.ONE).signum() == 1) p = p.add(d);
                d = d.doubleAdd();
                n = n.shiftRight(1);
            }
            return p;
        }

        Point multiplyCT(BigInteger n) {
            Point dbl = new Point(this.x, this.y);
            Point p = Point.ZERO;
            Point f = Point.ZERO;
            for (int i = 0; i < 256; i++) {
                if (n.and(BigInteger.ONE).signum() == 1) p = p.add(dbl);
                else f = f.add(dbl);
                n = n.shiftRight(1);
                dbl = dbl.doubleAdd();
            }
            return p;
        }

        List<Point> getPrecomputes() {
            if (this.precomputes != null) return this.precomputes;
            this.precomputes = new ArrayList<>();
            Point dbl = this;
            for (int i = 0; i < 256; i++) {
                this.precomputes.add(dbl);
                dbl = dbl.doubleAdd();
            }
            return this.precomputes;
        }

        Point multiplyPreCT(BigInteger n) {
            Point dbl;
            Point p = Point.ZERO;
            Point f = Point.ZERO;
            List<Point> dbls = this.getPrecomputes();
            for (int i = 0; i < 256; i++) {
                dbl = dbls.get(i);
                if (n.and(BigInteger.ONE).signum() == 1) p = p.add(dbl);
                else f = f.add(dbl);
                n = n.shiftRight(1);
            }
            return p;
        }

        List<JacobianPoint> getPrecomputesJ() {
            if (this.precomputesJ != null) return this.precomputesJ;
            this.precomputesJ = new ArrayList<>();
            JacobianPoint dbl = JacobianPoint.fromAffine(this);
            for (int i = 0; i < 256; i++) {
                this.precomputesJ.add(dbl);
                dbl = dbl.doubleAdd();
            }
            return this.precomputesJ;
        }

        Point multiplyPreCTJ(BigInteger n) {
            JacobianPoint dbl;
            JacobianPoint p = JacobianPoint.ZERO;
            JacobianPoint f = JacobianPoint.ZERO;
            List<JacobianPoint> dbls = this.getPrecomputesJ();
            for (int i = 0; i < 256; i++) {
                dbl = dbls.get(i);
                if (n.and(BigInteger.ONE).signum() == 1) p = p.add(dbl);
                else f = f.add(dbl);
                n = n.shiftRight(1);
            }
            return p.toAffine();
        }

        List<JacobianPoint> precomputeWindow(int W) {
            if (this.precomputesW != null) return this.precomputesW;
            int windows = 256 / W + 1;
            List<JacobianPoint> points = new ArrayList<>();
            JacobianPoint p = JacobianPoint.fromAffine(this);
            JacobianPoint base;
            for (int window = 0; window < windows; window++) {
                base = p;
                points.add(base);
                for (int i = 1; i < (int) Math.pow(2, W - 1); i++) {
                    base = base.add(p);
                    points.add(base);
                }
                p = base.doubleAdd();
            }
            this.precomputesW = points;
            return points;
        }

        JacobianPoint[] wNAF(BigInteger n) {
            return wNAF(n, 8);
        }

        JacobianPoint[] wNAF(BigInteger n, int W) {
            if (256 % W != 0) {
                throw new IllegalArgumentException("Point#wNAF: Invalid precomputation window, must be power of 2");
            }
            List<JacobianPoint> precomputes = this.precomputeWindow(W);

            JacobianPoint p = JacobianPoint.ZERO;
            JacobianPoint f = JacobianPoint.ZERO;

            int windows = 256 / W + 1;
            int windowSize = (int) Math.pow(2, W - 1);
            BigInteger mask = BigInteger.valueOf(2L).pow(W).subtract(BigInteger.ONE);
            int maxNumber = (int) Math.pow(2, W);

            for (int window = 0; window < windows; window++) {
                int offset = window * windowSize;
                int wbits = n.and(mask).intValue();

                n = n.shiftRight(W);

                if (wbits > windowSize) {
                    wbits -= maxNumber;
                    n = n.add(BigInteger.ONE);
                }

                if (wbits == 0) {
                    f = f.add(precomputes.get(offset));
                } else {
                    JacobianPoint cached = precomputes.get(offset + Math.abs(wbits) - 1);
                    p = p.add(wbits < 0 ? cached.negate() : cached);
                }
            }
            return new JacobianPoint[]{p, f};
        }

        Point multiplywNAF(BigInteger n) {
            JacobianPoint[] pf = this.wNAF(n);
            return pf[0].toAffine();
        }
    }

    private static BigInteger mod(BigInteger a) {
        return mod(a, P);
    }

    private static BigInteger mod(BigInteger a, BigInteger b) {
        BigInteger result = a.remainder(b);
        return result.signum() >= 0 ? result : b.add(result);
    }

    private static BigInteger[] egcd(BigInteger a, BigInteger b) {
        BigInteger x = BigInteger.ZERO, y = BigInteger.ONE, u = BigInteger.ONE, v = BigInteger.ZERO;
        while (a.signum() != 0) {
            BigInteger q = b.divide(a);
            BigInteger r = b.remainder(a);
            BigInteger m = x.subtract(u.multiply(q));
            BigInteger n = y.subtract(v.multiply(q));
            b = a;
            a = r;
            x = u;
            y = v;
            u = m;
            v = n;
        }
        return new BigInteger[]{b, x, y};
    }

    private static BigInteger invert(BigInteger number) {
        return invert(number, P);
    }

    private static BigInteger invert(BigInteger number, BigInteger modulo) {
        if (number.signum() == 0 || modulo.signum() <= 0) {
            throw new IllegalArgumentException("invert: expected positive integers");
        }
        BigInteger[] result = egcd(mod(number, modulo), modulo);
        if (result[0].compareTo(BigInteger.ONE) != 0) {
            throw new IllegalArgumentException("invert: does not exist");
        }
        return mod(result[1], modulo);
    }

    private static Object[] splitScalarEndo(BigInteger k) {
        BigInteger a1 = new BigInteger("3086D221A7D46BCDE86C90E49284EB15", 16);
        BigInteger b1 = new BigInteger("-E4437ED6010E88286F547FA90ABFE4C3", 16);
        BigInteger a2 = new BigInteger("114CA50F7A8E2F3F657C1108D9D44CFD8", 16);
        BigInteger b2 = a1;
        BigInteger c1 = b2.multiply(k).divide(n);
        BigInteger c2 = b1.negate().multiply(k).divide(n);
        BigInteger k1 = k.subtract(c1.multiply(a1)).subtract(c2.multiply(a2));
        BigInteger k2 = c1.negate().multiply(b1).subtract(c2.multiply(b2));
        boolean k1neg = k1.signum() < 0;
        boolean k2neg = k2.signum() < 0;
        return new Object[]{k1neg, k1neg ? k1.negate() : k1, k2neg, k2neg ? k2.negate() : k2};
    }

    public static void main(String[] args) {


//        Point.BASE.multiplyPreCT(BigInteger.valueOf(2L));
//        Point.BASE.multiplyPreCTJ(BigInteger.valueOf(2L));
//        JacobianPoint jacobianPoint = JacobianPoint.BASE.multiplyPreCT(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
//        Point.BASE.multiplywNAF(BigInteger.valueOf(2L));
        JacobianPoint jacobianPoint = JacobianPoint.BASE.multiplyUnsafe(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
        long a = System.nanoTime();
//        Point publicKey = getPublicKey(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
//        secp256k1.gen(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
//        G.multiplyCT(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
//        G.multiplyCT(BigInteger.valueOf(2L));
//        G.multiplyPreCT(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
//        JacobianPoint.BASE.multiplyDA(BigInteger.valueOf(2L));
//        Point.BASE.multiplyPreCT(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
        for (int i = 0; i < 10000; i++) {
//            jacobianPoint.multiplyPreCT(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
            jacobianPoint.multiplyUnsafe(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
//        jacobianPoint.multiplyDA(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
//            Point.BASE.multiplywNAF(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
        }
        // 25032093
        // 20418850
//            Point.BASE.multiplyPreCTJ(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
//        JacobianPoint.BASE.multiplyPreCT(BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L)));
        // 16767959 16848185
        // 16758986 15969785

        // 15784598
        // 15708339
        long b = System.nanoTime();
        System.out.println((b - a) / 1000);
//        System.out.println(publicKey.x);
//        System.out.println(publicKey.y);
//        System.out.println(gen[0]);
//        System.out.println(gen[1]);
    }
}
