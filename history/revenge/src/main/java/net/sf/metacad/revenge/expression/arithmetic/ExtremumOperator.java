package net.sf.metacad.revenge.expression.arithmetic;

import net.sf.metacad.revenge.expression.BinaryOperator;
import net.sf.metacad.revenge.expression.Operator;

// TODO merge with BinaryArithmeticOperator ?
public enum ExtremumOperator implements BinaryOperator {
	MIN, MAX;

	@Override
	public Operator cloneOperator() {
		try {
			return (Operator) clone();
		} catch (CloneNotSupportedException e) {
			throw new IllegalStateException(e);
		}
	}
}
