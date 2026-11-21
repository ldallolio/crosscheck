package net.sf.metacad.revenge.expression.logic;

import net.sf.metacad.revenge.expression.BinaryOperator;
import net.sf.metacad.revenge.expression.Operator;

/**
 * Something that takes a couple of operands and makes a boolean expression.
 * 
 * @author Luca Dall'Olio
 * 
 */
public enum BinaryBooleanOperator implements BinaryOperator {
	AND, OR, XOR;

	@Override
	public Operator cloneOperator() {
		try {
			return (Operator) this.clone();
		} catch (CloneNotSupportedException e) {
			throw new IllegalStateException(e);
		}
	}
}
