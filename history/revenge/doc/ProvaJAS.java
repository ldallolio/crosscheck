/*
import java.util.ArrayList;
import java.util.List;

import edu.jas.arith.BigRational;
import edu.jas.gb.GroebnerBase;
import edu.jas.gb.GroebnerBaseSeq;
import edu.jas.poly.GenPolynomial;
import edu.jas.poly.GenPolynomialRing;

public class ProvaJAS {

	public static void main(String[] args) {
		BigRational fac = new BigRational();
		String[] vars = new String[] { "x", "a" };
		GenPolynomialRing<BigRational> ring = new GenPolynomialRing<BigRational>(
				fac, 2, vars);
		GenPolynomial<BigRational> poly = ring.univariate(1).multiply(
				BigRational.valueOf(2)).sum(BigRational.valueOf(1));
		GenPolynomial<BigRational> poly2 = ring.univariate(0).multiply(
				BigRational.valueOf(3)).sum(BigRational.valueOf(5));
		List<GenPolynomial<BigRational>> L = new ArrayList<GenPolynomial<BigRational>>();
		L.add(poly);
		L.add(poly2);
		System.out.println("L = " + L);
		GroebnerBase<BigRational> bb = new GroebnerBaseSeq<BigRational>();
		List<GenPolynomial<BigRational>> G = bb.GB(L);
		System.out.println("G = " + G);
	}
}
*/