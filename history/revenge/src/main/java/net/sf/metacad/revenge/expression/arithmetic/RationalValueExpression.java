package net.sf.metacad.revenge.expression.arithmetic;

import java.util.Map;

import org.apache.commons.lang.builder.CompareToBuilder;
import org.apache.commons.lang.builder.EqualsBuilder;
import org.apache.commons.lang.builder.HashCodeBuilder;

import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.NumberExpressionBase;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.NumericType;

public class RationalValueExpression extends NumberExpressionBase
		implements RationalExpression, ArithmeticExpression, Comparable<ArithmeticExpression> {

	private static final long serialVersionUID = -1L;
	private final int numerator;
	private final int denominator;

	private RationalValueExpression(int numerator, int denominator) {
		this.numerator = numerator;
		this.denominator = denominator;
	}

	public static RationalExpression create(int numerator, int denominator) {
		if (numerator == 0 && denominator != 0) {
			return new IntegerValueExpression(0);
		} else if (numerator == 0 && denominator == 0) {
			throw new IllegalStateException("Rational 0/0 is undefined");
		} else if (numerator != 0 && denominator == 0) {
			throw new IllegalStateException("Rational (<>0)/0 is infinite");
		} else if (denominator == 1) {
			return new IntegerValueExpression(numerator);
		} else if (denominator == -1) {
			return new IntegerValueExpression(-numerator);
		} else if (numerator == denominator) {
			return new IntegerValueExpression(1);
		} else if (numerator % denominator == 0) {
			return new IntegerValueExpression(numerator / denominator);
		} else if (denominator < 0) {
			return new RationalValueExpression(-numerator, -denominator);
		} else {
			return new RationalValueExpression(numerator, denominator);
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (!this.getClass().isAssignableFrom(obj.getClass())) {
			return false;
		}
		if (this == obj) {
			return true;
		}
		RationalValueExpression rhs = (RationalValueExpression) obj;
		return new EqualsBuilder().append(numerator, rhs.numerator).append(denominator, rhs.denominator).isEquals();
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder().append(numerator).append(denominator).toHashCode();
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		visitor.arithmeticCondition(this);
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		// Example : for (i = 1:3) x = 5
		// becomes x = 5
		visitor.arithmeticCondition(this);
	}

	@Override
	public CodeType type() {
		return NumericType.RATIONAL;
	}

	@Override
	public String toString() {
		return Integer.toString(numerator) + "/" + Integer.toString(denominator);
	}

	@Override
	public int compareTo(ArithmeticExpression o) {
		if (o instanceof IntegerValueExpression) {
			IntegerValueExpression other = (IntegerValueExpression) o;
			return new CompareToBuilder().append(numerator, other.value * denominator).toComparison();
		}
		if (o instanceof RationalValueExpression) {
			RationalValueExpression other = (RationalValueExpression) o;
			return new CompareToBuilder().append(numerator * other.denominator, other.numerator * denominator)
					.toComparison();
		}
		throw new UnsupportedOperationException(
				"Comparison between : [" + this.getClass() + "] and : [" + o.getClass() + "] not yet implemented.");
	}

	@Override
	public int numerator() {
		return numerator;
	}

	@Override
	public int denominator() {
		return denominator;
	}

}
