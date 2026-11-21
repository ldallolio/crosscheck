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

// TODO generalize with numbers
public class IntegerValueExpression extends NumberExpressionBase
		implements IntegerExpression, ArithmeticExpression, Comparable<ArithmeticExpression>, RationalExpression {

	private static final long serialVersionUID = -1610836900333050116L;
	public final int value;

	public IntegerValueExpression(int value) {
		this.value = value;
	}

	@Override
	public boolean equals(Object obj) {
		if (!this.getClass().isAssignableFrom(obj.getClass())) {
			return false;
		}
		if (this == obj) {
			return true;
		}
		IntegerValueExpression rhs = (IntegerValueExpression) obj;
		return new EqualsBuilder().append(value, rhs.value).isEquals();
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder().append(value).toHashCode();
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
		return NumericType.INT;
	}

	@Override
	public String toString() {
		return Integer.toString(value);
	}

	@Override
	public int compareTo(ArithmeticExpression o) {
		if (o instanceof IntegerValueExpression) {
			IntegerValueExpression other = (IntegerValueExpression) o;
			return new CompareToBuilder().append(value, other.value).toComparison();
		}
		if (o instanceof RationalExpression) {
			RationalExpression other = (RationalExpression) o;
			return new CompareToBuilder().append(value * other.denominator(), other.numerator()).toComparison();
		}
		throw new UnsupportedOperationException(
				"Comparison between : [" + this.getClass() + "] and : [" + o.getClass() + "] not yet implemented.");
	}

	@Override
	public int numerator() {
		return value;
	}

	@Override
	public int denominator() {
		return 1;
	}

}
