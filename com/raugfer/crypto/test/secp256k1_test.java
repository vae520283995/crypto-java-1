package com.raugfer.crypto.test;

import com.raugfer.crypto.secp256k1;
import com.raugfer.crypto.secp256k1_1;

import java.math.BigInteger;

public class secp256k1_test {

    public static void main(String[] args) {
//        test1();
        long sum = 0;
        for (int i = 0; i < 1; i++) {
            long time = test5();
            sum += time;
        }
        System.out.println(sum / 1);

        long sum1 = 0;
        for (int i = 0; i < 10000; i++) {
            long time = test5();
            sum1 += time;
        }
        System.out.println(sum1 / 10000);
//        test3();
    }

    private static long test1() {
        callback cb = () -> {
            BigInteger[] gen = secp256k1.gen(BigInteger.valueOf(2).pow(255).subtract(BigInteger.valueOf(19)));
        };
        return benchmark(cb);
    }

    private static long test2() {
        callback cb = () -> {
            BigInteger[] gen = secp256k1_1.gen(BigInteger.valueOf(2).pow(255).subtract(BigInteger.valueOf(19)));
//            BigInteger[] gen = secp256k1_1.gen(BigInteger.valueOf(2));
        };
        return benchmark(cb);
    }

    private static long test3() {
        callback cb = () -> {
            secp256k1_1.invert(BigInteger.valueOf(2).pow(255).subtract(BigInteger.valueOf(19)), secp256k1_1.n);
        };
        return benchmark(cb);
    }
    private static long test4() {
        callback cb = () -> {
            BigInteger.valueOf(2).pow(255).subtract(BigInteger.valueOf(19)).modInverse(secp256k1_1.n);
        };
        return benchmark(cb);
    }

    private static long test5() {
        callback cb = () -> {
            BigInteger[] gen = secp256k1_1.mul_ct(secp256k1_1.G, BigInteger.valueOf(2).pow(255).subtract(BigInteger.valueOf(19)));
//            System.out.println(gen[0]);
//            System.out.println(gen[1]);
//            BigInteger[] gen = secp256k1_1.mul_ct(secp256k1_1.G, BigInteger.valueOf(2));
        };
        return benchmark(cb);
    }

    private static long test6() {
        callback cb = () -> {
            BigInteger[] gen = secp256k1_1.mul_ct_j(secp256k1_1.G, BigInteger.valueOf(2).pow(255).subtract(BigInteger.valueOf(19)));
//            System.out.println(gen[0]);
//            System.out.println(gen[1]);
//            BigInteger[] gen = secp256k1_1.mul_ct_j(secp256k1_1.G, BigInteger.valueOf(2));
        };
        return benchmark(cb);
    }

    public interface callback {
        void call();
    }

    private static long benchmark(callback cb) {
        long a = System.nanoTime();
        cb.call();
        long b = System.nanoTime();
        return (b - a) / 1000;
    }
}
