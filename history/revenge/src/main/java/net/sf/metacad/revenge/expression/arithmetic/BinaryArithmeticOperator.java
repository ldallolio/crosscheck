package net.sf.metacad.revenge.expression.arithmetic;

import net.sf.metacad.revenge.expression.BinaryOperator;
import net.sf.metacad.revenge.expression.Operator;

public enum BinaryArithmeticOperator implements BinaryOperator {
	PLUS, MINUS, TIMES, DIV, EXP;

	@Override
	public Operator cloneOperator() {
		try {
			return (Operator) this.clone();
		} catch (CloneNotSupportedException e) {
			throw new IllegalStateException(e);
		}
	}

}
