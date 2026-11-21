package net.sf.metacad.revenge.expression.logic;

import net.sf.metacad.revenge.expression.BinaryOperator;
import net.sf.metacad.revenge.expression.Operator;
import net.sf.metacad.revenge.expression.arithmetic.UnaryArithmeticOperator;

/**
 * Something that takes a couple of operands and makes a comparison.
 *
 * @author Luca Dall'Olio
 *
 */
public enum ComparisonOperator implements BinaryOperator {
	EQUAL, NOTEQUAL, GREATERTHAN, LESSERTHAN, GREATEREQUALTHAN, LESSEREQUALTHAN;

	@Override
	public Operator cloneOperator() {
		try {
			return (Operator) clone();
		} catch (CloneNotSupportedException e) {
			throw new IllegalStateException(e);
		}
	}

	/**
	 * Swaps left and right side of a comparison, adapting operator as needed
	 */
	public ComparisonOperator swap() {
		ComparisonOperator operatorSwapped;
		switch (this) {
		case EQUAL:
		case NOTEQUAL:
			operatorSwapped = this;
			break;
		case GREATEREQUALTHAN:
			operatorSwapped = ComparisonOperator.LESSEREQUALTHAN;
			break;
		case GREATERTHAN:
			operatorSwapped = ComparisonOperator.LESSERTHAN;
			break;
		case LESSEREQUALTHAN:
			operatorSwapped = ComparisonOperator.GREATEREQUALTHAN;
			break;
		case LESSERTHAN:
			operatorSwapped = ComparisonOperator.GREATERTHAN;
			break;
		default:
			throw new UnsupportedOperationException("Operator : [" + this + "] not yet handled.");
		}
		return operatorSwapped;
	}

	public UnaryArithmeticOperator minimizingOperator() {
		UnaryArithmeticOperator arithmeticOperation;
		switch (this) {
		case GREATERTHAN:
		case GREATEREQUALTHAN:
			arithmeticOperation = UnaryArithmeticOperator.CEIL;
			break;
		case LESSERTHAN:
		case LESSEREQUALTHAN:
			arithmeticOperation = UnaryArithmeticOperator.FLOOR;
			break;
		default:
			throw new UnsupportedOperationException("Operator : [" + this + "] not yet handled.");
		}
		return arithmeticOperation;
	}
}
